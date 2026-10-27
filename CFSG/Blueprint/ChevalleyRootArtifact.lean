module

public import CFSG.Blueprint.ChevalleyPinned

public section

namespace CFSG.Blueprint.Chevalley

@[expose] def g2ArtifactRoots : List (List ℤ) :=
  [([-2, -3] : List ℤ), ([-1, -3] : List ℤ), ([-1, -2] : List ℤ), ([-1, -1] : List ℤ),
    ([-1, 0] : List ℤ), ([0, -1] : List ℤ), ([0, 1] : List ℤ), ([1, 0] : List ℤ),
    ([1, 1] : List ℤ), ([1, 2] : List ℤ), ([1, 3] : List ℤ), ([2, 3] : List ℤ)]

@[expose] def f4ArtifactRoots : List (List ℤ) :=
  [([-2, -3, -4, -2] : List ℤ), ([-1, -3, -4, -2] : List ℤ), ([-1, -2, -4, -2] : List ℤ),
    ([-1, -2, -3, -2] : List ℤ), ([-1, -2, -3, -1] : List ℤ), ([-1, -2, -2, -2] : List ℤ),
    ([-1, -2, -2, -1] : List ℤ), ([-1, -2, -2, 0] : List ℤ), ([-1, -1, -2, -2] : List ℤ),
    ([-1, -1, -2, -1] : List ℤ), ([-1, -1, -2, 0] : List ℤ), ([-1, -1, -1, -1] : List ℤ),
    ([-1, -1, -1, 0] : List ℤ), ([-1, -1, 0, 0] : List ℤ), ([-1, 0, 0, 0] : List ℤ),
    ([0, -1, -2, -2] : List ℤ), ([0, -1, -2, -1] : List ℤ), ([0, -1, -2, 0] : List ℤ),
    ([0, -1, -1, -1] : List ℤ), ([0, -1, -1, 0] : List ℤ), ([0, -1, 0, 0] : List ℤ),
    ([0, 0, -1, -1] : List ℤ), ([0, 0, -1, 0] : List ℤ), ([0, 0, 0, -1] : List ℤ),
    ([0, 0, 0, 1] : List ℤ), ([0, 0, 1, 0] : List ℤ), ([0, 0, 1, 1] : List ℤ),
    ([0, 1, 0, 0] : List ℤ), ([0, 1, 1, 0] : List ℤ), ([0, 1, 1, 1] : List ℤ),
    ([0, 1, 2, 0] : List ℤ), ([0, 1, 2, 1] : List ℤ), ([0, 1, 2, 2] : List ℤ),
    ([1, 0, 0, 0] : List ℤ), ([1, 1, 0, 0] : List ℤ), ([1, 1, 1, 0] : List ℤ),
    ([1, 1, 1, 1] : List ℤ), ([1, 1, 2, 0] : List ℤ), ([1, 1, 2, 1] : List ℤ),
    ([1, 1, 2, 2] : List ℤ), ([1, 2, 2, 0] : List ℤ), ([1, 2, 2, 1] : List ℤ),
    ([1, 2, 2, 2] : List ℤ), ([1, 2, 3, 1] : List ℤ), ([1, 2, 3, 2] : List ℤ),
    ([1, 2, 4, 2] : List ℤ), ([1, 3, 4, 2] : List ℤ), ([2, 3, 4, 2] : List ℤ)]

@[expose] def d4ArtifactRoots : List (List ℤ) :=
  [([-1, -1, -2, -1] : List ℤ), ([-1, -1, -1, -1] : List ℤ), ([-1, -1, -1, 0] : List ℤ),
    ([-1, 0, -1, -1] : List ℤ), ([-1, 0, -1, 0] : List ℤ), ([-1, 0, 0, 0] : List ℤ),
    ([0, -1, -1, -1] : List ℤ), ([0, -1, -1, 0] : List ℤ), ([0, -1, 0, 0] : List ℤ),
    ([0, 0, -1, -1] : List ℤ), ([0, 0, -1, 0] : List ℤ), ([0, 0, 0, -1] : List ℤ),
    ([0, 0, 0, 1] : List ℤ), ([0, 0, 1, 0] : List ℤ), ([0, 0, 1, 1] : List ℤ),
    ([0, 1, 0, 0] : List ℤ), ([0, 1, 1, 0] : List ℤ), ([0, 1, 1, 1] : List ℤ),
    ([1, 0, 0, 0] : List ℤ), ([1, 0, 1, 0] : List ℤ), ([1, 0, 1, 1] : List ℤ),
    ([1, 1, 1, 0] : List ℤ), ([1, 1, 1, 1] : List ℤ), ([1, 1, 2, 1] : List ℤ)]

@[expose] def e6ArtifactRoots : List (List ℤ) :=
  [([-1, -2, -2, -3, -2, -1] : List ℤ), ([-1, -1, -2, -3, -2, -1] : List ℤ),
    ([-1, -1, -2, -2, -2, -1] : List ℤ), ([-1, -1, -2, -2, -1, -1] : List ℤ),
    ([-1, -1, -2, -2, -1, 0] : List ℤ), ([-1, -1, -1, -2, -2, -1] : List ℤ),
    ([-1, -1, -1, -2, -1, -1] : List ℤ), ([-1, -1, -1, -2, -1, 0] : List ℤ),
    ([-1, -1, -1, -1, -1, -1] : List ℤ), ([-1, -1, -1, -1, -1, 0] : List ℤ),
    ([-1, -1, -1, -1, 0, 0] : List ℤ), ([-1, 0, -1, -1, -1, -1] : List ℤ),
    ([-1, 0, -1, -1, -1, 0] : List ℤ), ([-1, 0, -1, -1, 0, 0] : List ℤ),
    ([-1, 0, -1, 0, 0, 0] : List ℤ), ([-1, 0, 0, 0, 0, 0] : List ℤ),
    ([0, -1, -1, -2, -2, -1] : List ℤ), ([0, -1, -1, -2, -1, -1] : List ℤ),
    ([0, -1, -1, -2, -1, 0] : List ℤ), ([0, -1, -1, -1, -1, -1] : List ℤ),
    ([0, -1, -1, -1, -1, 0] : List ℤ), ([0, -1, -1, -1, 0, 0] : List ℤ),
    ([0, -1, 0, -1, -1, -1] : List ℤ), ([0, -1, 0, -1, -1, 0] : List ℤ),
    ([0, -1, 0, -1, 0, 0] : List ℤ), ([0, -1, 0, 0, 0, 0] : List ℤ),
    ([0, 0, -1, -1, -1, -1] : List ℤ), ([0, 0, -1, -1, -1, 0] : List ℤ),
    ([0, 0, -1, -1, 0, 0] : List ℤ), ([0, 0, -1, 0, 0, 0] : List ℤ),
    ([0, 0, 0, -1, -1, -1] : List ℤ), ([0, 0, 0, -1, -1, 0] : List ℤ),
    ([0, 0, 0, -1, 0, 0] : List ℤ), ([0, 0, 0, 0, -1, -1] : List ℤ),
    ([0, 0, 0, 0, -1, 0] : List ℤ), ([0, 0, 0, 0, 0, -1] : List ℤ),
    ([0, 0, 0, 0, 0, 1] : List ℤ), ([0, 0, 0, 0, 1, 0] : List ℤ), ([0, 0, 0, 0, 1, 1] : List ℤ),
    ([0, 0, 0, 1, 0, 0] : List ℤ), ([0, 0, 0, 1, 1, 0] : List ℤ), ([0, 0, 0, 1, 1, 1] : List ℤ),
    ([0, 0, 1, 0, 0, 0] : List ℤ), ([0, 0, 1, 1, 0, 0] : List ℤ), ([0, 0, 1, 1, 1, 0] : List ℤ),
    ([0, 0, 1, 1, 1, 1] : List ℤ), ([0, 1, 0, 0, 0, 0] : List ℤ), ([0, 1, 0, 1, 0, 0] : List ℤ),
    ([0, 1, 0, 1, 1, 0] : List ℤ), ([0, 1, 0, 1, 1, 1] : List ℤ), ([0, 1, 1, 1, 0, 0] : List ℤ),
    ([0, 1, 1, 1, 1, 0] : List ℤ), ([0, 1, 1, 1, 1, 1] : List ℤ), ([0, 1, 1, 2, 1, 0] : List ℤ),
    ([0, 1, 1, 2, 1, 1] : List ℤ), ([0, 1, 1, 2, 2, 1] : List ℤ), ([1, 0, 0, 0, 0, 0] : List ℤ),
    ([1, 0, 1, 0, 0, 0] : List ℤ), ([1, 0, 1, 1, 0, 0] : List ℤ), ([1, 0, 1, 1, 1, 0] : List ℤ),
    ([1, 0, 1, 1, 1, 1] : List ℤ), ([1, 1, 1, 1, 0, 0] : List ℤ), ([1, 1, 1, 1, 1, 0] : List ℤ),
    ([1, 1, 1, 1, 1, 1] : List ℤ), ([1, 1, 1, 2, 1, 0] : List ℤ), ([1, 1, 1, 2, 1, 1] : List ℤ),
    ([1, 1, 1, 2, 2, 1] : List ℤ), ([1, 1, 2, 2, 1, 0] : List ℤ), ([1, 1, 2, 2, 1, 1] : List ℤ),
    ([1, 1, 2, 2, 2, 1] : List ℤ), ([1, 1, 2, 3, 2, 1] : List ℤ), ([1, 2, 2, 3, 2, 1] : List ℤ)]

@[expose] def e7ArtifactRoots : List (List ℤ) :=
  [([-2, -2, -3, -4, -3, -2, -1] : List ℤ), ([-1, -2, -3, -4, -3, -2, -1] : List ℤ),
    ([-1, -2, -2, -4, -3, -2, -1] : List ℤ), ([-1, -2, -2, -3, -3, -2, -1] : List ℤ),
    ([-1, -2, -2, -3, -2, -2, -1] : List ℤ), ([-1, -2, -2, -3, -2, -1, -1] : List ℤ),
    ([-1, -2, -2, -3, -2, -1, 0] : List ℤ), ([-1, -1, -2, -3, -3, -2, -1] : List ℤ),
    ([-1, -1, -2, -3, -2, -2, -1] : List ℤ), ([-1, -1, -2, -3, -2, -1, -1] : List ℤ),
    ([-1, -1, -2, -3, -2, -1, 0] : List ℤ), ([-1, -1, -2, -2, -2, -2, -1] : List ℤ),
    ([-1, -1, -2, -2, -2, -1, -1] : List ℤ), ([-1, -1, -2, -2, -2, -1, 0] : List ℤ),
    ([-1, -1, -2, -2, -1, -1, -1] : List ℤ), ([-1, -1, -2, -2, -1, -1, 0] : List ℤ),
    ([-1, -1, -2, -2, -1, 0, 0] : List ℤ), ([-1, -1, -1, -2, -2, -2, -1] : List ℤ),
    ([-1, -1, -1, -2, -2, -1, -1] : List ℤ), ([-1, -1, -1, -2, -2, -1, 0] : List ℤ),
    ([-1, -1, -1, -2, -1, -1, -1] : List ℤ), ([-1, -1, -1, -2, -1, -1, 0] : List ℤ),
    ([-1, -1, -1, -2, -1, 0, 0] : List ℤ), ([-1, -1, -1, -1, -1, -1, -1] : List ℤ),
    ([-1, -1, -1, -1, -1, -1, 0] : List ℤ), ([-1, -1, -1, -1, -1, 0, 0] : List ℤ),
    ([-1, -1, -1, -1, 0, 0, 0] : List ℤ), ([-1, 0, -1, -1, -1, -1, -1] : List ℤ),
    ([-1, 0, -1, -1, -1, -1, 0] : List ℤ), ([-1, 0, -1, -1, -1, 0, 0] : List ℤ),
    ([-1, 0, -1, -1, 0, 0, 0] : List ℤ), ([-1, 0, -1, 0, 0, 0, 0] : List ℤ),
    ([-1, 0, 0, 0, 0, 0, 0] : List ℤ), ([0, -1, -1, -2, -2, -2, -1] : List ℤ),
    ([0, -1, -1, -2, -2, -1, -1] : List ℤ), ([0, -1, -1, -2, -2, -1, 0] : List ℤ),
    ([0, -1, -1, -2, -1, -1, -1] : List ℤ), ([0, -1, -1, -2, -1, -1, 0] : List ℤ),
    ([0, -1, -1, -2, -1, 0, 0] : List ℤ), ([0, -1, -1, -1, -1, -1, -1] : List ℤ),
    ([0, -1, -1, -1, -1, -1, 0] : List ℤ), ([0, -1, -1, -1, -1, 0, 0] : List ℤ),
    ([0, -1, -1, -1, 0, 0, 0] : List ℤ), ([0, -1, 0, -1, -1, -1, -1] : List ℤ),
    ([0, -1, 0, -1, -1, -1, 0] : List ℤ), ([0, -1, 0, -1, -1, 0, 0] : List ℤ),
    ([0, -1, 0, -1, 0, 0, 0] : List ℤ), ([0, -1, 0, 0, 0, 0, 0] : List ℤ),
    ([0, 0, -1, -1, -1, -1, -1] : List ℤ), ([0, 0, -1, -1, -1, -1, 0] : List ℤ),
    ([0, 0, -1, -1, -1, 0, 0] : List ℤ), ([0, 0, -1, -1, 0, 0, 0] : List ℤ),
    ([0, 0, -1, 0, 0, 0, 0] : List ℤ), ([0, 0, 0, -1, -1, -1, -1] : List ℤ),
    ([0, 0, 0, -1, -1, -1, 0] : List ℤ), ([0, 0, 0, -1, -1, 0, 0] : List ℤ),
    ([0, 0, 0, -1, 0, 0, 0] : List ℤ), ([0, 0, 0, 0, -1, -1, -1] : List ℤ),
    ([0, 0, 0, 0, -1, -1, 0] : List ℤ), ([0, 0, 0, 0, -1, 0, 0] : List ℤ),
    ([0, 0, 0, 0, 0, -1, -1] : List ℤ), ([0, 0, 0, 0, 0, -1, 0] : List ℤ),
    ([0, 0, 0, 0, 0, 0, -1] : List ℤ), ([0, 0, 0, 0, 0, 0, 1] : List ℤ),
    ([0, 0, 0, 0, 0, 1, 0] : List ℤ), ([0, 0, 0, 0, 0, 1, 1] : List ℤ),
    ([0, 0, 0, 0, 1, 0, 0] : List ℤ), ([0, 0, 0, 0, 1, 1, 0] : List ℤ),
    ([0, 0, 0, 0, 1, 1, 1] : List ℤ), ([0, 0, 0, 1, 0, 0, 0] : List ℤ),
    ([0, 0, 0, 1, 1, 0, 0] : List ℤ), ([0, 0, 0, 1, 1, 1, 0] : List ℤ),
    ([0, 0, 0, 1, 1, 1, 1] : List ℤ), ([0, 0, 1, 0, 0, 0, 0] : List ℤ),
    ([0, 0, 1, 1, 0, 0, 0] : List ℤ), ([0, 0, 1, 1, 1, 0, 0] : List ℤ),
    ([0, 0, 1, 1, 1, 1, 0] : List ℤ), ([0, 0, 1, 1, 1, 1, 1] : List ℤ),
    ([0, 1, 0, 0, 0, 0, 0] : List ℤ), ([0, 1, 0, 1, 0, 0, 0] : List ℤ),
    ([0, 1, 0, 1, 1, 0, 0] : List ℤ), ([0, 1, 0, 1, 1, 1, 0] : List ℤ),
    ([0, 1, 0, 1, 1, 1, 1] : List ℤ), ([0, 1, 1, 1, 0, 0, 0] : List ℤ),
    ([0, 1, 1, 1, 1, 0, 0] : List ℤ), ([0, 1, 1, 1, 1, 1, 0] : List ℤ),
    ([0, 1, 1, 1, 1, 1, 1] : List ℤ), ([0, 1, 1, 2, 1, 0, 0] : List ℤ),
    ([0, 1, 1, 2, 1, 1, 0] : List ℤ), ([0, 1, 1, 2, 1, 1, 1] : List ℤ),
    ([0, 1, 1, 2, 2, 1, 0] : List ℤ), ([0, 1, 1, 2, 2, 1, 1] : List ℤ),
    ([0, 1, 1, 2, 2, 2, 1] : List ℤ), ([1, 0, 0, 0, 0, 0, 0] : List ℤ),
    ([1, 0, 1, 0, 0, 0, 0] : List ℤ), ([1, 0, 1, 1, 0, 0, 0] : List ℤ),
    ([1, 0, 1, 1, 1, 0, 0] : List ℤ), ([1, 0, 1, 1, 1, 1, 0] : List ℤ),
    ([1, 0, 1, 1, 1, 1, 1] : List ℤ), ([1, 1, 1, 1, 0, 0, 0] : List ℤ),
    ([1, 1, 1, 1, 1, 0, 0] : List ℤ), ([1, 1, 1, 1, 1, 1, 0] : List ℤ),
    ([1, 1, 1, 1, 1, 1, 1] : List ℤ), ([1, 1, 1, 2, 1, 0, 0] : List ℤ),
    ([1, 1, 1, 2, 1, 1, 0] : List ℤ), ([1, 1, 1, 2, 1, 1, 1] : List ℤ),
    ([1, 1, 1, 2, 2, 1, 0] : List ℤ), ([1, 1, 1, 2, 2, 1, 1] : List ℤ),
    ([1, 1, 1, 2, 2, 2, 1] : List ℤ), ([1, 1, 2, 2, 1, 0, 0] : List ℤ),
    ([1, 1, 2, 2, 1, 1, 0] : List ℤ), ([1, 1, 2, 2, 1, 1, 1] : List ℤ),
    ([1, 1, 2, 2, 2, 1, 0] : List ℤ), ([1, 1, 2, 2, 2, 1, 1] : List ℤ),
    ([1, 1, 2, 2, 2, 2, 1] : List ℤ), ([1, 1, 2, 3, 2, 1, 0] : List ℤ),
    ([1, 1, 2, 3, 2, 1, 1] : List ℤ), ([1, 1, 2, 3, 2, 2, 1] : List ℤ),
    ([1, 1, 2, 3, 3, 2, 1] : List ℤ), ([1, 2, 2, 3, 2, 1, 0] : List ℤ),
    ([1, 2, 2, 3, 2, 1, 1] : List ℤ), ([1, 2, 2, 3, 2, 2, 1] : List ℤ),
    ([1, 2, 2, 3, 3, 2, 1] : List ℤ), ([1, 2, 2, 4, 3, 2, 1] : List ℤ),
    ([1, 2, 3, 4, 3, 2, 1] : List ℤ), ([2, 2, 3, 4, 3, 2, 1] : List ℤ)]

@[expose] def e8ArtifactRoots : List (List ℤ) :=
  [([-2, -3, -4, -6, -5, -4, -3, -2] : List ℤ), ([-2, -3, -4, -6, -5, -4, -3, -1] : List ℤ),
    ([-2, -3, -4, -6, -5, -4, -2, -1] : List ℤ), ([-2, -3, -4, -6, -5, -3, -2, -1] : List ℤ),
    ([-2, -3, -4, -6, -4, -3, -2, -1] : List ℤ), ([-2, -3, -4, -5, -4, -3, -2, -1] : List ℤ),
    ([-2, -3, -3, -5, -4, -3, -2, -1] : List ℤ), ([-2, -2, -4, -5, -4, -3, -2, -1] : List ℤ),
    ([-2, -2, -3, -5, -4, -3, -2, -1] : List ℤ), ([-2, -2, -3, -4, -4, -3, -2, -1] : List ℤ),
    ([-2, -2, -3, -4, -3, -3, -2, -1] : List ℤ), ([-2, -2, -3, -4, -3, -2, -2, -1] : List ℤ),
    ([-2, -2, -3, -4, -3, -2, -1, -1] : List ℤ), ([-2, -2, -3, -4, -3, -2, -1, 0] : List ℤ),
    ([-1, -3, -3, -5, -4, -3, -2, -1] : List ℤ), ([-1, -2, -3, -5, -4, -3, -2, -1] : List ℤ),
    ([-1, -2, -3, -4, -4, -3, -2, -1] : List ℤ), ([-1, -2, -3, -4, -3, -3, -2, -1] : List ℤ),
    ([-1, -2, -3, -4, -3, -2, -2, -1] : List ℤ), ([-1, -2, -3, -4, -3, -2, -1, -1] : List ℤ),
    ([-1, -2, -3, -4, -3, -2, -1, 0] : List ℤ), ([-1, -2, -2, -4, -4, -3, -2, -1] : List ℤ),
    ([-1, -2, -2, -4, -3, -3, -2, -1] : List ℤ), ([-1, -2, -2, -4, -3, -2, -2, -1] : List ℤ),
    ([-1, -2, -2, -4, -3, -2, -1, -1] : List ℤ), ([-1, -2, -2, -4, -3, -2, -1, 0] : List ℤ),
    ([-1, -2, -2, -3, -3, -3, -2, -1] : List ℤ), ([-1, -2, -2, -3, -3, -2, -2, -1] : List ℤ),
    ([-1, -2, -2, -3, -3, -2, -1, -1] : List ℤ), ([-1, -2, -2, -3, -3, -2, -1, 0] : List ℤ),
    ([-1, -2, -2, -3, -2, -2, -2, -1] : List ℤ), ([-1, -2, -2, -3, -2, -2, -1, -1] : List ℤ),
    ([-1, -2, -2, -3, -2, -2, -1, 0] : List ℤ), ([-1, -2, -2, -3, -2, -1, -1, -1] : List ℤ),
    ([-1, -2, -2, -3, -2, -1, -1, 0] : List ℤ), ([-1, -2, -2, -3, -2, -1, 0, 0] : List ℤ),
    ([-1, -1, -2, -3, -3, -3, -2, -1] : List ℤ), ([-1, -1, -2, -3, -3, -2, -2, -1] : List ℤ),
    ([-1, -1, -2, -3, -3, -2, -1, -1] : List ℤ), ([-1, -1, -2, -3, -3, -2, -1, 0] : List ℤ),
    ([-1, -1, -2, -3, -2, -2, -2, -1] : List ℤ), ([-1, -1, -2, -3, -2, -2, -1, -1] : List ℤ),
    ([-1, -1, -2, -3, -2, -2, -1, 0] : List ℤ), ([-1, -1, -2, -3, -2, -1, -1, -1] : List ℤ),
    ([-1, -1, -2, -3, -2, -1, -1, 0] : List ℤ), ([-1, -1, -2, -3, -2, -1, 0, 0] : List ℤ),
    ([-1, -1, -2, -2, -2, -2, -2, -1] : List ℤ), ([-1, -1, -2, -2, -2, -2, -1, -1] : List ℤ),
    ([-1, -1, -2, -2, -2, -2, -1, 0] : List ℤ), ([-1, -1, -2, -2, -2, -1, -1, -1] : List ℤ),
    ([-1, -1, -2, -2, -2, -1, -1, 0] : List ℤ), ([-1, -1, -2, -2, -2, -1, 0, 0] : List ℤ),
    ([-1, -1, -2, -2, -1, -1, -1, -1] : List ℤ), ([-1, -1, -2, -2, -1, -1, -1, 0] : List ℤ),
    ([-1, -1, -2, -2, -1, -1, 0, 0] : List ℤ), ([-1, -1, -2, -2, -1, 0, 0, 0] : List ℤ),
    ([-1, -1, -1, -2, -2, -2, -2, -1] : List ℤ), ([-1, -1, -1, -2, -2, -2, -1, -1] : List ℤ),
    ([-1, -1, -1, -2, -2, -2, -1, 0] : List ℤ), ([-1, -1, -1, -2, -2, -1, -1, -1] : List ℤ),
    ([-1, -1, -1, -2, -2, -1, -1, 0] : List ℤ), ([-1, -1, -1, -2, -2, -1, 0, 0] : List ℤ),
    ([-1, -1, -1, -2, -1, -1, -1, -1] : List ℤ), ([-1, -1, -1, -2, -1, -1, -1, 0] : List ℤ),
    ([-1, -1, -1, -2, -1, -1, 0, 0] : List ℤ), ([-1, -1, -1, -2, -1, 0, 0, 0] : List ℤ),
    ([-1, -1, -1, -1, -1, -1, -1, -1] : List ℤ), ([-1, -1, -1, -1, -1, -1, -1, 0] : List ℤ),
    ([-1, -1, -1, -1, -1, -1, 0, 0] : List ℤ), ([-1, -1, -1, -1, -1, 0, 0, 0] : List ℤ),
    ([-1, -1, -1, -1, 0, 0, 0, 0] : List ℤ), ([-1, 0, -1, -1, -1, -1, -1, -1] : List ℤ),
    ([-1, 0, -1, -1, -1, -1, -1, 0] : List ℤ), ([-1, 0, -1, -1, -1, -1, 0, 0] : List ℤ),
    ([-1, 0, -1, -1, -1, 0, 0, 0] : List ℤ), ([-1, 0, -1, -1, 0, 0, 0, 0] : List ℤ),
    ([-1, 0, -1, 0, 0, 0, 0, 0] : List ℤ), ([-1, 0, 0, 0, 0, 0, 0, 0] : List ℤ),
    ([0, -1, -1, -2, -2, -2, -2, -1] : List ℤ), ([0, -1, -1, -2, -2, -2, -1, -1] : List ℤ),
    ([0, -1, -1, -2, -2, -2, -1, 0] : List ℤ), ([0, -1, -1, -2, -2, -1, -1, -1] : List ℤ),
    ([0, -1, -1, -2, -2, -1, -1, 0] : List ℤ), ([0, -1, -1, -2, -2, -1, 0, 0] : List ℤ),
    ([0, -1, -1, -2, -1, -1, -1, -1] : List ℤ), ([0, -1, -1, -2, -1, -1, -1, 0] : List ℤ),
    ([0, -1, -1, -2, -1, -1, 0, 0] : List ℤ), ([0, -1, -1, -2, -1, 0, 0, 0] : List ℤ),
    ([0, -1, -1, -1, -1, -1, -1, -1] : List ℤ), ([0, -1, -1, -1, -1, -1, -1, 0] : List ℤ),
    ([0, -1, -1, -1, -1, -1, 0, 0] : List ℤ), ([0, -1, -1, -1, -1, 0, 0, 0] : List ℤ),
    ([0, -1, -1, -1, 0, 0, 0, 0] : List ℤ), ([0, -1, 0, -1, -1, -1, -1, -1] : List ℤ),
    ([0, -1, 0, -1, -1, -1, -1, 0] : List ℤ), ([0, -1, 0, -1, -1, -1, 0, 0] : List ℤ),
    ([0, -1, 0, -1, -1, 0, 0, 0] : List ℤ), ([0, -1, 0, -1, 0, 0, 0, 0] : List ℤ),
    ([0, -1, 0, 0, 0, 0, 0, 0] : List ℤ), ([0, 0, -1, -1, -1, -1, -1, -1] : List ℤ),
    ([0, 0, -1, -1, -1, -1, -1, 0] : List ℤ), ([0, 0, -1, -1, -1, -1, 0, 0] : List ℤ),
    ([0, 0, -1, -1, -1, 0, 0, 0] : List ℤ), ([0, 0, -1, -1, 0, 0, 0, 0] : List ℤ),
    ([0, 0, -1, 0, 0, 0, 0, 0] : List ℤ), ([0, 0, 0, -1, -1, -1, -1, -1] : List ℤ),
    ([0, 0, 0, -1, -1, -1, -1, 0] : List ℤ), ([0, 0, 0, -1, -1, -1, 0, 0] : List ℤ),
    ([0, 0, 0, -1, -1, 0, 0, 0] : List ℤ), ([0, 0, 0, -1, 0, 0, 0, 0] : List ℤ),
    ([0, 0, 0, 0, -1, -1, -1, -1] : List ℤ), ([0, 0, 0, 0, -1, -1, -1, 0] : List ℤ),
    ([0, 0, 0, 0, -1, -1, 0, 0] : List ℤ), ([0, 0, 0, 0, -1, 0, 0, 0] : List ℤ),
    ([0, 0, 0, 0, 0, -1, -1, -1] : List ℤ), ([0, 0, 0, 0, 0, -1, -1, 0] : List ℤ),
    ([0, 0, 0, 0, 0, -1, 0, 0] : List ℤ), ([0, 0, 0, 0, 0, 0, -1, -1] : List ℤ),
    ([0, 0, 0, 0, 0, 0, -1, 0] : List ℤ), ([0, 0, 0, 0, 0, 0, 0, -1] : List ℤ),
    ([0, 0, 0, 0, 0, 0, 0, 1] : List ℤ), ([0, 0, 0, 0, 0, 0, 1, 0] : List ℤ),
    ([0, 0, 0, 0, 0, 0, 1, 1] : List ℤ), ([0, 0, 0, 0, 0, 1, 0, 0] : List ℤ),
    ([0, 0, 0, 0, 0, 1, 1, 0] : List ℤ), ([0, 0, 0, 0, 0, 1, 1, 1] : List ℤ),
    ([0, 0, 0, 0, 1, 0, 0, 0] : List ℤ), ([0, 0, 0, 0, 1, 1, 0, 0] : List ℤ),
    ([0, 0, 0, 0, 1, 1, 1, 0] : List ℤ), ([0, 0, 0, 0, 1, 1, 1, 1] : List ℤ),
    ([0, 0, 0, 1, 0, 0, 0, 0] : List ℤ), ([0, 0, 0, 1, 1, 0, 0, 0] : List ℤ),
    ([0, 0, 0, 1, 1, 1, 0, 0] : List ℤ), ([0, 0, 0, 1, 1, 1, 1, 0] : List ℤ),
    ([0, 0, 0, 1, 1, 1, 1, 1] : List ℤ), ([0, 0, 1, 0, 0, 0, 0, 0] : List ℤ),
    ([0, 0, 1, 1, 0, 0, 0, 0] : List ℤ), ([0, 0, 1, 1, 1, 0, 0, 0] : List ℤ),
    ([0, 0, 1, 1, 1, 1, 0, 0] : List ℤ), ([0, 0, 1, 1, 1, 1, 1, 0] : List ℤ),
    ([0, 0, 1, 1, 1, 1, 1, 1] : List ℤ), ([0, 1, 0, 0, 0, 0, 0, 0] : List ℤ),
    ([0, 1, 0, 1, 0, 0, 0, 0] : List ℤ), ([0, 1, 0, 1, 1, 0, 0, 0] : List ℤ),
    ([0, 1, 0, 1, 1, 1, 0, 0] : List ℤ), ([0, 1, 0, 1, 1, 1, 1, 0] : List ℤ),
    ([0, 1, 0, 1, 1, 1, 1, 1] : List ℤ), ([0, 1, 1, 1, 0, 0, 0, 0] : List ℤ),
    ([0, 1, 1, 1, 1, 0, 0, 0] : List ℤ), ([0, 1, 1, 1, 1, 1, 0, 0] : List ℤ),
    ([0, 1, 1, 1, 1, 1, 1, 0] : List ℤ), ([0, 1, 1, 1, 1, 1, 1, 1] : List ℤ),
    ([0, 1, 1, 2, 1, 0, 0, 0] : List ℤ), ([0, 1, 1, 2, 1, 1, 0, 0] : List ℤ),
    ([0, 1, 1, 2, 1, 1, 1, 0] : List ℤ), ([0, 1, 1, 2, 1, 1, 1, 1] : List ℤ),
    ([0, 1, 1, 2, 2, 1, 0, 0] : List ℤ), ([0, 1, 1, 2, 2, 1, 1, 0] : List ℤ),
    ([0, 1, 1, 2, 2, 1, 1, 1] : List ℤ), ([0, 1, 1, 2, 2, 2, 1, 0] : List ℤ),
    ([0, 1, 1, 2, 2, 2, 1, 1] : List ℤ), ([0, 1, 1, 2, 2, 2, 2, 1] : List ℤ),
    ([1, 0, 0, 0, 0, 0, 0, 0] : List ℤ), ([1, 0, 1, 0, 0, 0, 0, 0] : List ℤ),
    ([1, 0, 1, 1, 0, 0, 0, 0] : List ℤ), ([1, 0, 1, 1, 1, 0, 0, 0] : List ℤ),
    ([1, 0, 1, 1, 1, 1, 0, 0] : List ℤ), ([1, 0, 1, 1, 1, 1, 1, 0] : List ℤ),
    ([1, 0, 1, 1, 1, 1, 1, 1] : List ℤ), ([1, 1, 1, 1, 0, 0, 0, 0] : List ℤ),
    ([1, 1, 1, 1, 1, 0, 0, 0] : List ℤ), ([1, 1, 1, 1, 1, 1, 0, 0] : List ℤ),
    ([1, 1, 1, 1, 1, 1, 1, 0] : List ℤ), ([1, 1, 1, 1, 1, 1, 1, 1] : List ℤ),
    ([1, 1, 1, 2, 1, 0, 0, 0] : List ℤ), ([1, 1, 1, 2, 1, 1, 0, 0] : List ℤ),
    ([1, 1, 1, 2, 1, 1, 1, 0] : List ℤ), ([1, 1, 1, 2, 1, 1, 1, 1] : List ℤ),
    ([1, 1, 1, 2, 2, 1, 0, 0] : List ℤ), ([1, 1, 1, 2, 2, 1, 1, 0] : List ℤ),
    ([1, 1, 1, 2, 2, 1, 1, 1] : List ℤ), ([1, 1, 1, 2, 2, 2, 1, 0] : List ℤ),
    ([1, 1, 1, 2, 2, 2, 1, 1] : List ℤ), ([1, 1, 1, 2, 2, 2, 2, 1] : List ℤ),
    ([1, 1, 2, 2, 1, 0, 0, 0] : List ℤ), ([1, 1, 2, 2, 1, 1, 0, 0] : List ℤ),
    ([1, 1, 2, 2, 1, 1, 1, 0] : List ℤ), ([1, 1, 2, 2, 1, 1, 1, 1] : List ℤ),
    ([1, 1, 2, 2, 2, 1, 0, 0] : List ℤ), ([1, 1, 2, 2, 2, 1, 1, 0] : List ℤ),
    ([1, 1, 2, 2, 2, 1, 1, 1] : List ℤ), ([1, 1, 2, 2, 2, 2, 1, 0] : List ℤ),
    ([1, 1, 2, 2, 2, 2, 1, 1] : List ℤ), ([1, 1, 2, 2, 2, 2, 2, 1] : List ℤ),
    ([1, 1, 2, 3, 2, 1, 0, 0] : List ℤ), ([1, 1, 2, 3, 2, 1, 1, 0] : List ℤ),
    ([1, 1, 2, 3, 2, 1, 1, 1] : List ℤ), ([1, 1, 2, 3, 2, 2, 1, 0] : List ℤ),
    ([1, 1, 2, 3, 2, 2, 1, 1] : List ℤ), ([1, 1, 2, 3, 2, 2, 2, 1] : List ℤ),
    ([1, 1, 2, 3, 3, 2, 1, 0] : List ℤ), ([1, 1, 2, 3, 3, 2, 1, 1] : List ℤ),
    ([1, 1, 2, 3, 3, 2, 2, 1] : List ℤ), ([1, 1, 2, 3, 3, 3, 2, 1] : List ℤ),
    ([1, 2, 2, 3, 2, 1, 0, 0] : List ℤ), ([1, 2, 2, 3, 2, 1, 1, 0] : List ℤ),
    ([1, 2, 2, 3, 2, 1, 1, 1] : List ℤ), ([1, 2, 2, 3, 2, 2, 1, 0] : List ℤ),
    ([1, 2, 2, 3, 2, 2, 1, 1] : List ℤ), ([1, 2, 2, 3, 2, 2, 2, 1] : List ℤ),
    ([1, 2, 2, 3, 3, 2, 1, 0] : List ℤ), ([1, 2, 2, 3, 3, 2, 1, 1] : List ℤ),
    ([1, 2, 2, 3, 3, 2, 2, 1] : List ℤ), ([1, 2, 2, 3, 3, 3, 2, 1] : List ℤ),
    ([1, 2, 2, 4, 3, 2, 1, 0] : List ℤ), ([1, 2, 2, 4, 3, 2, 1, 1] : List ℤ),
    ([1, 2, 2, 4, 3, 2, 2, 1] : List ℤ), ([1, 2, 2, 4, 3, 3, 2, 1] : List ℤ),
    ([1, 2, 2, 4, 4, 3, 2, 1] : List ℤ), ([1, 2, 3, 4, 3, 2, 1, 0] : List ℤ),
    ([1, 2, 3, 4, 3, 2, 1, 1] : List ℤ), ([1, 2, 3, 4, 3, 2, 2, 1] : List ℤ),
    ([1, 2, 3, 4, 3, 3, 2, 1] : List ℤ), ([1, 2, 3, 4, 4, 3, 2, 1] : List ℤ),
    ([1, 2, 3, 5, 4, 3, 2, 1] : List ℤ), ([1, 3, 3, 5, 4, 3, 2, 1] : List ℤ),
    ([2, 2, 3, 4, 3, 2, 1, 0] : List ℤ), ([2, 2, 3, 4, 3, 2, 1, 1] : List ℤ),
    ([2, 2, 3, 4, 3, 2, 2, 1] : List ℤ), ([2, 2, 3, 4, 3, 3, 2, 1] : List ℤ),
    ([2, 2, 3, 4, 4, 3, 2, 1] : List ℤ), ([2, 2, 3, 5, 4, 3, 2, 1] : List ℤ),
    ([2, 2, 4, 5, 4, 3, 2, 1] : List ℤ), ([2, 3, 3, 5, 4, 3, 2, 1] : List ℤ),
    ([2, 3, 4, 5, 4, 3, 2, 1] : List ℤ), ([2, 3, 4, 6, 4, 3, 2, 1] : List ℤ),
    ([2, 3, 4, 6, 5, 3, 2, 1] : List ℤ), ([2, 3, 4, 6, 5, 4, 2, 1] : List ℤ),
    ([2, 3, 4, 6, 5, 4, 3, 1] : List ℤ), ([2, 3, 4, 6, 5, 4, 3, 2] : List ℤ)]

namespace Tag

@[expose] def artifactRoots : Tag → List (List ℤ)
  | G2 => g2ArtifactRoots
  | F4 => f4ArtifactRoots
  | D4 => d4ArtifactRoots
  | E6 => e6ArtifactRoots
  | E7 => e7ArtifactRoots
  | E8 => e8ArtifactRoots

theorem artifactRoots_eq : ∀ τ : Tag,
    τ.artifactRoots = τ.witnesses.roots.map fun c => List.ofFn (decodeVec (τ := τ) c)
  | G2 => by decide +kernel
  | F4 => by decide +kernel
  | D4 => by decide +kernel
  | E6 => by decide +kernel
  | E7 => by decide +kernel
  | E8 => by decide +kernel

theorem witnesses_perm : ∀ τ : Tag, τ.witnesses.roots.Perm τ.rootCertificate.roots
  | G2 => by decide +kernel
  | F4 => by decide +kernel
  | D4 => by decide +kernel
  | E6 => by decide +kernel
  | E7 => by decide +kernel
  | E8 => by decide +kernel

theorem length_artifactRoots : ∀ τ : Tag, τ.artifactRoots.length = τ.rootCount
  | G2 => rfl
  | F4 => rfl
  | D4 => rfl
  | E6 => rfl
  | E7 => rfl
  | E8 => rfl

end Tag

theorem RootCertificate.map_range_root {τ : Tag} (C : RootCertificate τ) :
    (List.range C.roots.length).map (fun k => List.ofFn (C.root k)) =
      C.roots.map fun c => List.ofFn (decodeVec (τ := τ) c) := by
  refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, RootCertificate.root]
  rw [List.getD_eq_getElem]

theorem isRoot_iff_mem_artifactRoots {τ : Tag} {v : Fin τ.rank → ℤ} :
    IsRoot τ v ↔ List.ofFn v ∈ τ.artifactRoots := by
  rw [τ.artifactRoots_eq, (τ.witnesses_perm.map _).mem_iff,
    RootCertificate.isRoot_iff τ.rootCertificate_check, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨τ.rootCertificate.roots[k], List.getElem_mem hk, ?_⟩
    rw [RootCertificate.root, List.getD_eq_getElem]
  · rintro ⟨c, hc, hcv⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    refine ⟨k, hk, List.ofFn_injective ?_⟩
    rw [RootCertificate.root, List.getD_eq_getElem]
    exact hcv

theorem length_of_mem_artifactRoots {τ : Tag} {l : List ℤ} (hl : l ∈ τ.artifactRoots) :
    l.length = τ.rank := by
  rw [τ.artifactRoots_eq, List.mem_map] at hl
  obtain ⟨c, -, rfl⟩ := hl
  exact List.length_ofFn

theorem nodup_artifactRoots (τ : Tag) : τ.artifactRoots.Nodup := by
  have h := τ.rootCertificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at h
  rw [RootCertificate.map_range_root] at h
  rw [τ.artifactRoots_eq]
  exact (τ.witnesses_perm.map _).nodup_iff.2 h

theorem artifact_root_certificate (τ : Tag) :
    (∀ v : Fin τ.rank → ℤ, IsRoot τ v ↔ List.ofFn v ∈ τ.artifactRoots) ∧
      (∀ l ∈ τ.artifactRoots, l.length = τ.rank) ∧ τ.artifactRoots.Nodup ∧
      τ.artifactRoots.length = τ.rootCount ∧
      (∀ v : Fin τ.rank → ℤ, IsRoot τ v → v ≠ 0 ∧ ((∀ j, 0 ≤ v j) ∨ ∀ j, v j ≤ 0)) ∧
      ∀ (i : Fin τ.rank) (α : Fin τ.rank → ℤ), IsRoot τ α → α ≠ Pi.single i 1 →
        α ≠ -Pi.single i 1 → ∃ p q : ℕ, p + q ≤ 3 ∧
          ∀ k : ℤ, IsRoot τ (α + k • Pi.single i 1) ↔ -(q : ℤ) ≤ k ∧ k ≤ p :=
  ⟨fun _ => isRoot_iff_mem_artifactRoots, fun _ hl => length_of_mem_artifactRoots hl,
    nodup_artifactRoots τ, τ.length_artifactRoots, fun _ hv => ⟨hv.ne_zero, hv.nonneg_or_nonpos⟩,
    fun i _ hα hne hne' => exists_string_interval hα i hne hne'⟩

theorem g2_root_certificate :
    (∀ v : Fin Tag.G2.rank → ℤ, IsRoot .G2 v ↔ List.ofFn v ∈ g2ArtifactRoots) ∧
      (∀ l ∈ g2ArtifactRoots, l.length = 2) ∧ g2ArtifactRoots.Nodup ∧
      g2ArtifactRoots.length = 12 ∧
      (∀ v : Fin Tag.G2.rank → ℤ, IsRoot .G2 v → v ≠ 0 ∧ ((∀ j, 0 ≤ v j) ∨ ∀ j, v j ≤ 0)) ∧
      ∀ (i : Fin Tag.G2.rank) (α : Fin Tag.G2.rank → ℤ), IsRoot .G2 α → α ≠ Pi.single i 1 →
        α ≠ -Pi.single i 1 → ∃ p q : ℕ, p + q ≤ 3 ∧
          ∀ k : ℤ, IsRoot .G2 (α + k • Pi.single i 1) ↔ -(q : ℤ) ≤ k ∧ k ≤ p :=
  artifact_root_certificate .G2

theorem f4_root_certificate :
    (∀ v : Fin Tag.F4.rank → ℤ, IsRoot .F4 v ↔ List.ofFn v ∈ f4ArtifactRoots) ∧
      (∀ l ∈ f4ArtifactRoots, l.length = 4) ∧ f4ArtifactRoots.Nodup ∧
      f4ArtifactRoots.length = 48 ∧
      (∀ v : Fin Tag.F4.rank → ℤ, IsRoot .F4 v → v ≠ 0 ∧ ((∀ j, 0 ≤ v j) ∨ ∀ j, v j ≤ 0)) ∧
      ∀ (i : Fin Tag.F4.rank) (α : Fin Tag.F4.rank → ℤ), IsRoot .F4 α → α ≠ Pi.single i 1 →
        α ≠ -Pi.single i 1 → ∃ p q : ℕ, p + q ≤ 3 ∧
          ∀ k : ℤ, IsRoot .F4 (α + k • Pi.single i 1) ↔ -(q : ℤ) ≤ k ∧ k ≤ p :=
  artifact_root_certificate .F4

theorem d4_root_certificate :
    (∀ v : Fin Tag.D4.rank → ℤ, IsRoot .D4 v ↔ List.ofFn v ∈ d4ArtifactRoots) ∧
      (∀ l ∈ d4ArtifactRoots, l.length = 4) ∧ d4ArtifactRoots.Nodup ∧
      d4ArtifactRoots.length = 24 ∧
      (∀ v : Fin Tag.D4.rank → ℤ, IsRoot .D4 v → v ≠ 0 ∧ ((∀ j, 0 ≤ v j) ∨ ∀ j, v j ≤ 0)) ∧
      ∀ (i : Fin Tag.D4.rank) (α : Fin Tag.D4.rank → ℤ), IsRoot .D4 α → α ≠ Pi.single i 1 →
        α ≠ -Pi.single i 1 → ∃ p q : ℕ, p + q ≤ 3 ∧
          ∀ k : ℤ, IsRoot .D4 (α + k • Pi.single i 1) ↔ -(q : ℤ) ≤ k ∧ k ≤ p :=
  artifact_root_certificate .D4

theorem e6_root_certificate :
    (∀ v : Fin Tag.E6.rank → ℤ, IsRoot .E6 v ↔ List.ofFn v ∈ e6ArtifactRoots) ∧
      (∀ l ∈ e6ArtifactRoots, l.length = 6) ∧ e6ArtifactRoots.Nodup ∧
      e6ArtifactRoots.length = 72 ∧
      (∀ v : Fin Tag.E6.rank → ℤ, IsRoot .E6 v → v ≠ 0 ∧ ((∀ j, 0 ≤ v j) ∨ ∀ j, v j ≤ 0)) ∧
      ∀ (i : Fin Tag.E6.rank) (α : Fin Tag.E6.rank → ℤ), IsRoot .E6 α → α ≠ Pi.single i 1 →
        α ≠ -Pi.single i 1 → ∃ p q : ℕ, p + q ≤ 3 ∧
          ∀ k : ℤ, IsRoot .E6 (α + k • Pi.single i 1) ↔ -(q : ℤ) ≤ k ∧ k ≤ p :=
  artifact_root_certificate .E6

theorem e7_root_certificate :
    (∀ v : Fin Tag.E7.rank → ℤ, IsRoot .E7 v ↔ List.ofFn v ∈ e7ArtifactRoots) ∧
      (∀ l ∈ e7ArtifactRoots, l.length = 7) ∧ e7ArtifactRoots.Nodup ∧
      e7ArtifactRoots.length = 126 ∧
      (∀ v : Fin Tag.E7.rank → ℤ, IsRoot .E7 v → v ≠ 0 ∧ ((∀ j, 0 ≤ v j) ∨ ∀ j, v j ≤ 0)) ∧
      ∀ (i : Fin Tag.E7.rank) (α : Fin Tag.E7.rank → ℤ), IsRoot .E7 α → α ≠ Pi.single i 1 →
        α ≠ -Pi.single i 1 → ∃ p q : ℕ, p + q ≤ 3 ∧
          ∀ k : ℤ, IsRoot .E7 (α + k • Pi.single i 1) ↔ -(q : ℤ) ≤ k ∧ k ≤ p :=
  artifact_root_certificate .E7

theorem e8_root_certificate :
    (∀ v : Fin Tag.E8.rank → ℤ, IsRoot .E8 v ↔ List.ofFn v ∈ e8ArtifactRoots) ∧
      (∀ l ∈ e8ArtifactRoots, l.length = 8) ∧ e8ArtifactRoots.Nodup ∧
      e8ArtifactRoots.length = 240 ∧
      (∀ v : Fin Tag.E8.rank → ℤ, IsRoot .E8 v → v ≠ 0 ∧ ((∀ j, 0 ≤ v j) ∨ ∀ j, v j ≤ 0)) ∧
      ∀ (i : Fin Tag.E8.rank) (α : Fin Tag.E8.rank → ℤ), IsRoot .E8 α → α ≠ Pi.single i 1 →
        α ≠ -Pi.single i 1 → ∃ p q : ℕ, p + q ≤ 3 ∧
          ∀ k : ℤ, IsRoot .E8 (α + k • Pi.single i 1) ↔ -(q : ℤ) ≤ k ∧ k ≤ p :=
  artifact_root_certificate .E8

end CFSG.Blueprint.Chevalley
