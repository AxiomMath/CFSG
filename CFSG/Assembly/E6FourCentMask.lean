module

public import CFSG.Assembly.E6FourCentData
public import CFSG.Assembly.E6FourCentTorus

public section

namespace CFSG.Assembly

open CFSG.Blueprint.Chevalley

@[expose] def e6RootVec (k : ℕ) : Fin Tag.E6.rank → ℤ :=
  fun i => (E6FourCentChk.rtsLit.getD k []).getD i 0

@[expose] def e6MaskRoots (c : ℕ) : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | ∃ k, k < 72 ∧ c.testBit k = true ∧ e6RootVec k = γ}

@[expose] def e6SolMask (v : Fin Tag.E6.rank → ZMod 5) : ℕ :=
  (List.range 72).foldr
    (fun k acc => if e6Pair v (e6RootVec k) = 0 then acc ||| (1 <<< k) else acc) 0

@[expose] def e6SolCoords (n : ℕ) : List ℕ :=
  [2 * (n % 5 + 2 * (n / 5 % 5) + 2 * (n / 25 % 5) + n / 125 % 5) % 5, n % 5, n / 5 % 5,
    n / 25 % 5, n / 125 % 5,
    2 * (n % 5 + n / 5 % 5 + 2 * (n / 25 % 5) + 2 * (n / 125 % 5)) % 5]

@[expose] def e6SolVec (n : ℕ) : Fin Tag.E6.rank → ZMod 5 :=
  fun i => (((e6SolCoords n).getD i 0 : ℕ) : ZMod 5)

end CFSG.Assembly

end
