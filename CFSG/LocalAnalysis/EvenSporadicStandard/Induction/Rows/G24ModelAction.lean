module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ClosedFamilyAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.GLVecAction
public import Certificates.Certificate27210

public section

namespace CFSG.EvenSporadicStandard.G24Model

open CFSG.Fischer CFSG.EvenSporadicStandard.Induction.AutBound
open scoped Pointwise

attribute [local instance] glVecAction

theorem f4_code (c : F4) : f4 (c.code : Nat) = c := by
  obtain ⟨⟨n, hn⟩⟩ := c
  simp [f4, Nat.mod_eq_of_lt hn]

theorem f4_eq_zero_iff {n : Nat} (hn : n < 4) : f4 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have h1 : (f4 n).code = (0 : F4).code := congrArg F4.code h
    have h2 : n % 4 = 0 := congrArg Fin.val h1
    rwa [Nat.mod_eq_of_lt hn] at h2
  · rintro rfl
    rfl

theorem mem_lineVecs {k : Nat} {v : Vec} :
    v ∈ lineVecs k ↔ ∃ c d : F4, ¬ (c = 0 ∧ d = 0) ∧
      v = fun i => c * uVec k i + d * wVec k i := by
  constructor
  · intro h
    simp only [lineVecs, List.mem_flatMap, List.mem_filterMap, List.mem_range] at h
    obtain ⟨c, hc, d, hd, h⟩ := h
    by_cases hcd : c = 0 ∧ d = 0
    · simp [hcd] at h
    · simp only [hcd, ↓reduceIte, Option.some.injEq] at h
      refine ⟨f4 c, f4 d, fun ⟨h1, h2⟩ => hcd ⟨?_, ?_⟩, h.symm⟩
      · exact (f4_eq_zero_iff hc).1 h1
      · exact (f4_eq_zero_iff hd).1 h2
  · rintro ⟨c, d, hcd, rfl⟩
    simp only [lineVecs, List.mem_flatMap, List.mem_filterMap, List.mem_range]
    refine ⟨c.code, c.code.2, d.code, d.code.2, ?_⟩
    have hne : ¬ ((c.code : Nat) = 0 ∧ (d.code : Nat) = 0) := by
      rintro ⟨h1, h2⟩
      apply hcd
      constructor
      · rw [← f4_code c, h1]
        rfl
      · rw [← f4_code d, h2]
        rfl
    simp only [hne, ↓reduceIte, Option.some.injEq]
    funext i
    simp [comb, f4_code]

theorem vecList_injective : Function.Injective vecList := by
  intro v w h
  funext i
  have := List.map_inj_left.1 h i (List.mem_finRange i)
  exact this

theorem getElem!_ofFn' {α : Type*} [Inhabited α] {m : Nat} (f : Fin m → α) {i : Nat}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi)]
  simp

theorem hexOK_parts :
    (∀ k : Fin nLines, (lineOf k).card = 15 ∧ (0 : Vec) ∉ lineVecs k) ∧
      (∀ k k' : Fin nLines, k ≠ k' → lineKeys[(k : Nat)]! ≠ lineKeys[(k' : Nat)]!) ∧
      ∀ (j : Fin 16) (k : Fin nLines), (Gmat j).mulVec (uVec k) ∈ lineVecs (pgFin j k) ∧
        (Gmat j).mulVec (wVec k) ∈ lineVecs (pgFin j k) := by
  have h := Certificates.certificate27210
  unfold hexOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := of_decide_eq_true h1
  have key : ∀ (j : Fin 16) (k : Fin nLines) (v : Vec),
      imgIn (Gmat j) v lineLists[(pgFin j k : Nat)]! = true →
        (Gmat j).mulVec v ∈ lineVecs (pgFin j k) := by
    intro j k v hv
    have h3 := of_decide_eq_true hv
    rw [lineLists, getElem!_ofFn' _ (pgFin j k).2] at h3
    obtain ⟨w, hw, hw'⟩ := List.mem_map.1 h3
    rwa [vecList_injective hw'] at hw
  refine ⟨h1'.1, h1'.2, fun j k => ?_⟩
  have h4 := (List.all_eq_true.1 ((List.all_eq_true.1 h2) j (List.mem_finRange j))) k
    (List.mem_finRange k)
  rw [Bool.and_eq_true] at h4
  exact ⟨key j k _ h4.1, key j k _ h4.2⟩

theorem lineOf_injective : Function.Injective lineOf := by
  intro k k' h
  by_contra hne
  apply hexOK_parts.2.1 k k' hne
  have e : ∀ k : Fin nLines, lineKeys[(k : Nat)]! = keyOfSet (lineOf k) := fun k => by
    rw [lineKeys, getElem!_ofFn' _ k.2]
  rw [e, e, h]

theorem glSmul_def (g : GL (Fin 14) F4) (v : Vec) :
    g • v = Matrix.mulVec (g : Matrix (Fin 14) (Fin 14) F4) v :=
  rfl

theorem smul_lineOf_subset (g : GL (Fin 14) F4) (j : Fin 16)
    (hg : (g : Matrix (Fin 14) (Fin 14) F4) = Gmat j) (k : Fin nLines) :
    g • lineOf k ⊆ lineOf (pgFin j k) := by
  intro x hx
  rw [Finset.mem_smul_finset] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  have hv' : v ∈ lineVecs k := List.mem_toFinset.1 hv
  have hv0 : v ≠ 0 := fun h => (hexOK_parts.1 k).2 (h ▸ hv')
  obtain ⟨c, d, hcd, hvdef⟩ := mem_lineVecs.1 hv'
  obtain ⟨hu, hw⟩ := hexOK_parts.2.2 j k
  rw [← hg] at hu hw
  obtain ⟨a₁, b₁, -, hu'⟩ := mem_lineVecs.1 hu
  obtain ⟨a₂, b₂, -, hw'⟩ := mem_lineVecs.1 hw
  have hv2 : v = c • uVec k + d • wVec k := by
    rw [hvdef]
    funext i
    simp
  have himg : g • v = fun i => (c * a₁ + d * a₂) * uVec (pgFin j k) i +
      (c * b₁ + d * b₂) * wVec (pgFin j k) i := by
    rw [glSmul_def, hv2, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hu', hw']
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [himg]
  refine List.mem_toFinset.2 (mem_lineVecs.2 ⟨_, _, fun ⟨h1, h2⟩ => ?_, rfl⟩)
  apply hv0
  apply MulAction.injective g
  show g • v = g • (0 : Vec)
  rw [himg, smul_zero]
  funext i
  simp [h1, h2]

theorem smul_lineOf (g : GL (Fin 14) F4) (j : Fin 16)
    (hg : (g : Matrix (Fin 14) (Fin 14) F4) = Gmat j) (k : Fin nLines) :
    g • lineOf k = lineOf (pgFin j k) :=
  Finset.eq_of_subset_of_card_le (smul_lineOf_subset g j hg k) (by
    rw [Finset.card_smul_finset, (hexOK_parts.1 k).1, (hexOK_parts.1 (pgFin j k)).1])

theorem exists_hexHom {S : Set (GL (Fin 14) F4)}
    (hS : ∀ u ∈ S, ∃ j : Fin 16, (u : Matrix (Fin 14) (Fin 14) F4) = Gmat j) :
    ∃ π : Subgroup.closure S →* Equiv.Perm (Fin nLines),
      ∀ (g : Subgroup.closure S) (k : Fin nLines), (g : GL (Fin 14) F4) • lineOf k =
        lineOf (π g k) := by
  refine exists_permHom_of_closure lineOf lineOf_injective (S := S) ?_
  intro u hu k
  obtain ⟨j, hj⟩ := hS u hu
  exact ⟨pgFin j k, smul_lineOf u j hj k⟩

theorem hom_apply_gen {S : Set (GL (Fin 14) F4)}
    {π : Subgroup.closure S →* Equiv.Perm (Fin nLines)}
    (hπ : ∀ (g : Subgroup.closure S) (k : Fin nLines), (g : GL (Fin 14) F4) • lineOf k =
      lineOf (π g k)) {u : GL (Fin 14) F4} (hu : u ∈ S) {j : Fin 16}
    (hj : (u : Matrix (Fin 14) (Fin 14) F4) = Gmat j) (k : Fin nLines) :
    π ⟨u, Subgroup.subset_closure hu⟩ k = pgFin j k := by
  apply lineOf_injective
  rw [← hπ ⟨u, Subgroup.subset_closure hu⟩ k]
  exact smul_lineOf u j hj k

end CFSG.EvenSporadicStandard.G24Model
