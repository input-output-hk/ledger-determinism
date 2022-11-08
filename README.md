# TODO

Hoping to work on the following -

- Andre's suggestion of making our frameworks compatible (ie. doing this in agda instead)
- Incorporate context into the model (Arguably, blocks, rather than transactions, are the actual atomic units of ledger update. Transactions are 
only the ledger update atomic units within a single block - we neeeed to reconcile this)
- Given a differentiable ledger (in the ``Differentiable`` sense), what (if anything) can we say about the impact of 
ordering of the application of transaction on the resulting state?
- Given a ledger specification, maybe also make a category of all valid ledger states and ``Nothing`` (which is both initial and final)
- Make a category of all ledger specifications (where maps preserve ``initState`` and ``updateState``)
Note : If we make this a restriction category (where an inputs corresponding to the output of ``Nothing`` are not considered as part of the domain), 
in a permutation-deterministic ledger where equality on maps is extensional, a map can be defined by a pair of type ``(Set Tx, DomRest)``, which 
pairs a set of transactions with the domain of application (corresponding to the collection of states to which this set can be applied)
Note : consider initial transactions instead of initial states
- Define threads. What are they? monomorphisms or epimorphisms in the category? 
- Threads and provenance connection
- Multi-threads
- Threads as constraint-emitting things
- Embed ledger category into category of state machines
- When can threads represent accounts?
# ledger-determinism
