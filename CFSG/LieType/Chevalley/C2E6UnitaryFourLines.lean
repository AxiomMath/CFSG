module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourDefs
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def kc (c : Fin 4) : K := F4.mk c

@[expose] def vc (f : Fin 4 → Fin 4) : V := fun i => kc (f i)

theorem eta_V (v : V) : v = ![v 0, v 1, v 2, v 3] := by
  funext i
  fin_cases i <;> rfl

@[expose] def uCode : Fin 45 → Fin 4 → Fin 4 :=
  ![![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 2, 0, 0], ![1, 3, 0, 0],
    ![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 0, 2, 0], ![1, 2, 2, 0],
    ![1, 0, 3, 0], ![1, 3, 3, 0], ![1, 0, 0, 1], ![0, 1, 0, 1], ![1, 1, 0, 1], ![1, 2, 0, 1],
    ![1, 3, 0, 1], ![0, 0, 1, 1], ![1, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 0, 2, 1],
    ![1, 2, 2, 1], ![1, 0, 3, 1], ![1, 3, 3, 1], ![0, 1, 0, 2], ![0, 0, 1, 2], ![0, 1, 1, 2],
    ![1, 2, 1, 2], ![1, 3, 1, 2], ![1, 1, 2, 2], ![1, 3, 2, 2], ![1, 1, 3, 2], ![1, 2, 3, 2],
    ![0, 1, 0, 3], ![0, 0, 1, 3], ![0, 1, 1, 3], ![1, 2, 1, 3], ![1, 3, 1, 3], ![1, 1, 2, 3],
    ![1, 3, 2, 3], ![1, 1, 3, 3], ![1, 2, 3, 3]]

@[expose] def uVec (k : Fin 45) : V := vc (uCode k)

@[expose] noncomputable def uLine (k : Fin 45) : Submodule K V := K ∙ uVec k

theorem uVec_ne_zero : ∀ k, uVec k ≠ 0 := by decide

theorem herm_uVec_self : ∀ k, herm (uVec k) (uVec k) = 0 := by decide

theorem eq_of_smul_uVec : ∀ (k k' : Fin 45) (c : K), c • uVec k = uVec k' → k = k' := by
  decide +kernel

theorem exists_smul_uVec_aux : ∀ a b c d : K, ![a, b, c, d] ≠ 0 →
    herm ![a, b, c, d] ![a, b, c, d] = 0 → ∃ (k : Fin 45) (t : K), t • uVec k = ![a, b, c, d] := by
  decide +kernel

theorem exists_smul_uVec {v : V} (hv : v ≠ 0) (hh : herm v v = 0) :
    ∃ (k : Fin 45) (t : K), t • uVec k = v := by
  rw [eta_V v] at hv hh ⊢
  exact exists_smul_uVec_aux _ _ _ _ hv hh

@[expose] def plA : Fin 27 → Fin 45 :=
  ![0, 6, 0, 0, 1, 1, 2, 3, 3, 4, 4, 5, 5, 6, 7,
    7, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

@[expose] def plB : Fin 27 → Fin 45 :=
  ![2, 1, 6, 8, 2, 8, 14, 19, 20, 23, 24, 25, 26, 14, 15,
    16, 14, 15, 16, 17, 24, 17, 23, 18, 26, 18, 25]

@[expose] def plLine : Fin 27 → Fin 5 → Fin 45 :=
  ![![0, 2, 3, 4, 5], ![1, 6, 19, 28, 37], ![0, 6, 7, 10, 12], ![0, 8, 9, 11, 13],
    ![1, 2, 15, 27, 36], ![1, 8, 21, 29, 38], ![2, 14, 16, 17, 18], ![3, 19, 22, 32, 43],
    ![3, 20, 21, 33, 44], ![4, 23, 34, 38, 40], ![4, 24, 35, 37, 39], ![5, 25, 29, 30, 41],
    ![5, 26, 28, 31, 42], ![6, 14, 20, 23, 25], ![7, 15, 22, 30, 40], ![7, 16, 21, 35, 42],
    ![8, 14, 22, 24, 26], ![9, 15, 20, 31, 39], ![9, 16, 19, 34, 41], ![10, 17, 31, 38, 43],
    ![10, 24, 33, 36, 41], ![11, 17, 30, 37, 44], ![11, 23, 32, 36, 42], ![12, 18, 29, 32, 39],
    ![12, 26, 27, 34, 44], ![13, 18, 28, 33, 40], ![13, 25, 27, 35, 43]]

@[expose] noncomputable def uPlane (j : Fin 27) : Submodule K V :=
  Submodule.span K {uVec (plA j), uVec (plB j)}

@[expose] def UOn (k : Fin 45) (j : Fin 27) : Prop := ∃ i, plLine j i = k

instance : DecidableRel UOn := fun _ _ => inferInstanceAs (Decidable (∃ _, _))

theorem herm_plA_plB : ∀ j, herm (uVec (plA j)) (uVec (plB j)) = 0 := by decide

theorem plA_ne_plB : ∀ j, plA j ≠ plB j := by decide

theorem uOn_iff_aux : ∀ (k : Fin 45) (j : Fin 27),
    (∃ c₁ c₂ : K, c₁ • uVec (plA j) + c₂ • uVec (plB j) = uVec k) ↔ UOn k j := by
  decide +kernel

theorem exists_uOn_aux : ∀ k k' : Fin 45, k ≠ k' → herm (uVec k) (uVec k') = 0 →
    ∃ j, UOn k j ∧ UOn k' j := by
  decide +kernel

theorem eq_of_uOn_iff : ∀ j j' : Fin 27, (∀ k, UOn k j ↔ UOn k j') → j = j' := by
  decide +kernel

theorem finrank_span_pair_of_not_mem {a b : V} (ha : a ≠ 0) (hb : b ∉ K ∙ a) :
    finrank K (Submodule.span K {a, b}) = 2 := by
  have hli : LinearIndependent K ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right ha, rfl⟩
    · refine absurd ?_ hb
      rw [Submodule.mem_span_singleton]
      refine ⟨-(t⁻¹ * s), ?_⟩
      have : t • b = -(s • a) := eq_neg_of_add_eq_zero_right hst
      rw [← neg_mul, mul_smul, neg_smul, ← smul_neg, ← this, smul_smul, inv_mul_cancel₀ ht,
        one_smul]
  have h := finrank_span_eq_card hli
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Fintype.card_fin] at h

theorem exists_pair_of_finrank_eq_two_K {P : Submodule K V} (hP : finrank K P = 2) :
    ∃ a ∈ P, ∃ b ∈ P, a ≠ 0 ∧ b ∉ K ∙ a := by
  have hne : P ≠ ⊥ := by
    rintro rfl
    simp at hP
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : K ∙ a < P := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem a P).mpr ha) fun h => ?_
    have := finrank_span_singleton (K := K) ha0
    rw [h, hP] at this
    omega
  obtain ⟨b, hb, hba⟩ := IsConcreteLE.exists_of_lt hlt
  exact ⟨a, ha, b, hb, ha0, hba⟩

theorem mem_uLine {k : Fin 45} {x : V} : x ∈ uLine k ↔ ∃ c : K, c • uVec k = x :=
  Submodule.mem_span_singleton

theorem finrank_uLine (k : Fin 45) : finrank K (uLine k) = 1 :=
  finrank_span_singleton (uVec_ne_zero k)

theorem isTotallyIsotropic_uLine (k : Fin 45) : IsTotallyIsotropic (uLine k) := by
  intro x hx y hy
  obtain ⟨c, rfl⟩ := mem_uLine.mp hx
  obtain ⟨d, rfl⟩ := mem_uLine.mp hy
  rw [herm_smul_left, herm_smul_right, herm_uVec_self, mul_zero, mul_zero]

theorem uVec_not_mem_uLine {k k' : Fin 45} (h : k ≠ k') : uVec k' ∉ uLine k := by
  intro hk
  obtain ⟨c, hc⟩ := mem_uLine.mp hk
  exact h (eq_of_smul_uVec k k' c hc)

theorem isTotallyIsotropic_span_pair {a b : V} (ha : herm a a = 0) (hb : herm b b = 0)
    (hab : herm a b = 0) : IsTotallyIsotropic (Submodule.span K {a, b}) := by
  have hba : herm b a = 0 := by rw [herm_swap, hab, bar_zero]
  intro x hx y hy
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab, hba,
    mul_zero, add_zero]

theorem isTotallyIsotropic_uPlane (j : Fin 27) : IsTotallyIsotropic (uPlane j) :=
  isTotallyIsotropic_span_pair (herm_uVec_self _) (herm_uVec_self _) (herm_plA_plB j)

theorem finrank_uPlane (j : Fin 27) : finrank K (uPlane j) = 2 :=
  finrank_span_pair_of_not_mem (uVec_ne_zero _) (uVec_not_mem_uLine (plA_ne_plB j))

theorem uVec_mem_uPlane_iff {k : Fin 45} {j : Fin 27} : uVec k ∈ uPlane j ↔ UOn k j := by
  rw [uPlane, Submodule.mem_span_pair, uOn_iff_aux]

theorem uLine_le_uPlane_iff {k : Fin 45} {j : Fin 27} : uLine k ≤ uPlane j ↔ UOn k j := by
  rw [uLine, Submodule.span_singleton_le_iff_mem, uVec_mem_uPlane_iff]

theorem uLine_injective : Function.Injective uLine := by
  intro k k' h
  by_contra hk
  exact uVec_not_mem_uLine hk (h ▸ Submodule.mem_span_singleton_self (uVec k'))

theorem uPlane_injective : Function.Injective uPlane := by
  intro j j' h
  refine eq_of_uOn_iff j j' fun k => ?_
  rw [← uVec_mem_uPlane_iff, ← uVec_mem_uPlane_iff, h]

theorem exists_uVec_mem {U : Submodule K V} {v : V} (hv : v ∈ U) (hv0 : v ≠ 0)
    (hh : herm v v = 0) : ∃ k, uVec k ∈ U ∧ v ∈ uLine k := by
  obtain ⟨k, t, hkt⟩ := exists_smul_uVec hv0 hh
  have ht : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hkt
    exact hv0 hkt.symm
  refine ⟨k, ?_, mem_uLine.mpr ⟨t, hkt⟩⟩
  have : uVec k = t⁻¹ • v := by rw [← hkt, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [this]
  exact U.smul_mem _ hv

theorem exists_uLine_eq {ℓ : Submodule K V} (hℓ : IsTotallyIsotropic ℓ)
    (h1 : finrank K ℓ = 1) : ∃ k, ℓ = uLine k := by
  have hne : ℓ ≠ ⊥ := by
    rintro rfl
    simp at h1
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨k, hk, -⟩ := exists_uVec_mem hv hv0 (hℓ v hv v hv)
  exact ⟨k, eq_span_singleton_of_mem_of_finrank_eq_one h1 hk (uVec_ne_zero k)⟩

theorem exists_uPlane_eq {P : Submodule K V} (hP : IsTotallyIsotropic P)
    (h2 : finrank K P = 2) : ∃ j, P = uPlane j := by
  obtain ⟨a, ha, b, hb, ha0, hba⟩ := exists_pair_of_finrank_eq_two_K h2
  have hb0 : b ≠ 0 := fun h => hba (h ▸ Submodule.zero_mem _)
  obtain ⟨k, hk, hak⟩ := exists_uVec_mem ha ha0 (hP a ha a ha)
  obtain ⟨k', hk', hbk'⟩ := exists_uVec_mem hb hb0 (hP b hb b hb)
  have hkk' : k ≠ k' := by
    rintro rfl
    refine hba ?_
    have hle : uLine k ≤ K ∙ a := by
      rw [eq_span_singleton_of_mem_of_finrank_eq_one (finrank_uLine k) hak ha0]
    exact hle hbk'
  obtain ⟨j, hj, hj'⟩ := exists_uOn_aux k k' hkk' (hP _ hk _ hk')
  have hfin : finrank K (Submodule.span K {uVec k, uVec k'}) = 2 :=
    finrank_span_pair_of_not_mem (uVec_ne_zero k) (uVec_not_mem_uLine hkk')
  have hle : Submodule.span K {uVec k, uVec k'} ≤ P := by
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hk, hk'⟩
  have hle' : Submodule.span K {uVec k, uVec k'} ≤ uPlane j := by
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨uVec_mem_uPlane_iff.mpr hj, uVec_mem_uPlane_iff.mpr hj'⟩
  refine ⟨j, ?_⟩
  rw [← Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, h2]),
    Submodule.eq_of_le_of_finrank_eq hle' (by rw [hfin, finrank_uPlane])]

end CFSG.LieType.Chevalley.C2E6Overlap
