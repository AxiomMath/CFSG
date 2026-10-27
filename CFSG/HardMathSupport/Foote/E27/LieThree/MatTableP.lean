module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatTable

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix CFSG.Sporadic.He.Native

abbrev MP (p d : ℕ) : Type := Matrix (Fin d) (Fin d) (ZMod p)

@[expose] def normKey (p : ℕ) (X : AM) : Array ℕ :=
  X.foldl (fun acc row => acc ++ row.map (· % p)) #[]

@[expose] def buildTabH (p d : ℕ) (gens : Array AM) (fuel : ℕ) : RawTab := Id.run do
  let m := gens.size
  let mut elts : Array AM := #[idM d]
  let mut par : Array (ℕ × ℕ) := #[(0, 0)]
  let mut L : Array (Array ℕ) := Array.replicate m #[]
  let mut idx : Std.HashMap (Array ℕ) ℕ := Std.HashMap.emptyWithCapacity.insert (normKey p (idM d)) 0
  for i in [0:fuel] do
    if i < elts.size then
      for j in [0:m] do
        let q := mulM p d gens[j]! elts[i]!
        let k := normKey p q
        match idx[k]? with
        | some t => L := L.modify j (·.push t)
        | none =>
          L := L.modify j (·.push elts.size)
          idx := idx.insert k elts.size
          par := par.push (i, j)
          elts := elts.push q
  return ⟨elts, par, L⟩

@[expose] def kappa (p : ℕ) (pos : List (ℕ × ℕ)) (X : AM) : ℕ :=
  pos.foldr (fun rc acc => acc * p + (X[rc.1]!)[rc.2]! % p) 0

@[expose] def distOK (p d : ℕ) (pos : List (ℕ × ℕ)) (elts : Array AM) : Bool :=
  let n := elts.size
  let inv : Array ℕ := Id.run do
    let mut a : Array ℕ := Array.replicate (p ^ pos.length) n
    for i in [0:n] do
      a := a.set! (kappa p pos elts[i]!) i
    return a
  pos.all (fun rc => decide (rc.1 < d) && decide (rc.2 < d)) &&
    (List.range n).all fun i => inv[kappa p pos elts[i]!]! == i

theorem kappa_congr {p d : ℕ} {pos : List (ℕ × ℕ)} (hpos : ∀ rc ∈ pos, rc.1 < d ∧ rc.2 < d)
    {X Y : AM} (h : toMat p d X = toMat p d Y) : kappa p pos X = kappa p pos Y := by
  induction pos with
  | nil => rfl
  | cons rc pos ih =>
    unfold kappa at ih ⊢
    simp only [List.foldr_cons]
    have h1 := hpos rc (List.mem_cons_self)
    have := congrFun (congrFun h ⟨rc.1, h1.1⟩) ⟨rc.2, h1.2⟩
    rw [toMat_apply, toMat_apply, ZMod.natCast_eq_natCast_iff'] at this
    rw [ih (fun r hr => hpos r (List.mem_cons_of_mem _ hr)), this]

theorem distOK_spec {p d : ℕ} {pos : List (ℕ × ℕ)} {elts : Array AM}
    (h : distOK p d pos elts = true) :
    (∀ rc ∈ pos, rc.1 < d ∧ rc.2 < d) ∧ ∀ i < elts.size, ∀ k < elts.size,
      kappa p pos elts[i]! = kappa p pos elts[k]! → i = k := by
  unfold distOK at h
  generalize (Id.run do
    let mut a : Array ℕ := Array.replicate (p ^ pos.length) elts.size
    for i in [0:elts.size] do
      a := a.set! (kappa p pos elts[i]!) i
    return a) = inv at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range] at h
  refine ⟨fun rc hrc => h.1 rc hrc, fun i hi k hk hik => ?_⟩
  have h1 := h.2 i hi
  have h2 := h.2 k hk
  rw [← h1, ← h2, hik]

@[expose] def tabOKP (p d : ℕ) (pos : List (ℕ × ℕ)) (gens : Array AM) (T : RawTab) : Bool :=
  let n := T.elts.size
  (T.par.size == n) && matEqB p d T.elts[0]! (idM d) &&
  (List.range n).all (fun i => (i == 0) ||
    (decide ((T.par[i]!).1 < i) && decide ((T.par[i]!).2 < gens.size) &&
      matEqB p d T.elts[i]! (mulM p d gens[(T.par[i]!).2]! T.elts[(T.par[i]!).1]!))) &&
  (List.range gens.size).all (fun j => (List.range n).all fun i =>
    decide ((T.L[j]!)[i]! < n) &&
      matEqB p d (mulM p d gens[j]! T.elts[i]!) T.elts[(T.L[j]!)[i]!]!) &&
  distOK p d pos T.elts

section Spec

variable {p d : ℕ} {G : Type*} [Group G]

theorem tabData_of_checkP (mat : G →* MP p d) (hinj : Function.Injective mat)
    (gens : Array AM) (T : RawTab) (g : ℕ → G)
    (hg : ∀ j < gens.size, mat (g j) = toMat p d gens[j]!) (pos : List (ℕ × ℕ)) (hc : tabOKP p d pos gens T = true) :
    TabData g T.par T.L T.elts.size gens.size ∧
      ∀ i < T.elts.size, mat (tabElt g T.par i) = toMat p d T.elts[i]! := by
  unfold tabOKP at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨hpar, h0⟩, htree⟩, hleft⟩, hdist⟩ := hc
  have heq : ∀ i < T.elts.size, mat (tabElt g T.par i) = toMat p d T.elts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [tabElt_zero, map_one, matEqB_true h0, toMat_idM]
      · rcases htree i hi with h1 | ⟨⟨hp, hj⟩, hel⟩
        · exact absurd h1 hi0
        · rw [tabElt_succ g T.par hp, map_mul, hg _ hj, ih _ hp (by omega), matEqB_true hel,
            toMat_mulM]
  refine ⟨⟨fun i hi hin => ?_, fun j hj i hi => ?_, fun i hi k hk hik => ?_⟩, heq⟩
  · rcases htree i hin with h1 | ⟨⟨hp, hj⟩, -⟩
    · omega
    · exact ⟨hp, hj⟩
  · obtain ⟨hlt, hmat⟩ := hleft j hj i hi
    refine ⟨hlt, hinj ?_⟩
    rw [map_mul, hg j hj, heq i hi, heq _ hlt]
    have := matEqB_true hmat
    rw [toMat_mulM] at this
    exact this
  · obtain ⟨hposOK, hdinj⟩ := distOK_spec hdist
    refine hdinj i hi k hk (kappa_congr hposOK ?_)
    rw [← heq i hi, ← heq k hk, hik]

end Spec

end CFSG.HardMathSupport.Foote.E27
