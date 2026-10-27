module

public import CFSG.GH74.GLS.LU.StdPairUni
public import CFSG.GH74.L5U5.IdentUnitary

public section

namespace CFSG.GH74.GLS.LU

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

@[expose] def IsCentralInvolutionIn {G : Type*} [Group G] (a : G) (U : Subgroup G) : Prop :=
  a ∈ U ∧ orderOf a = 2 ∧ ∀ u ∈ U, u * a = a * u

@[expose] def IsLinearA3Neighborhood {G : Type} [Group G] (K : Type) [Field K] (z u : G)
    (Y : Fin 3 → Subgroup G) : Prop :=
  (∀ i, Nonempty (SL(2, K) ≃* Y i)) ∧ IsCentralInvolutionIn z (Y 0) ∧
    IsCentralInvolutionIn z (Y 2) ∧ IsCentralInvolutionIn u (Y 1) ∧ z ≠ u ∧ z * u = u * z ∧
    (∀ x ∈ Y 0, ∀ y ∈ Y 2, x * y = y * x) ∧
    (∃ α : SL(3, K) →* G, α.ker ≤ Subgroup.center SL(3, K) ∧ α.range = Y 0 ⊔ Y 1) ∧
    (∃ α : SL(3, K) →* G, α.ker ≤ Subgroup.center SL(3, K) ∧ α.range = Y 1 ⊔ Y 2)

@[expose] def IsUnitaryA3Neighborhood {G : Type} [Group G] (q : ℕ) (K F : Type) [Field K]
    [Field F] (z u : G) (Y : Fin 3 → Subgroup G) : Prop :=
  (∀ i, Nonempty (SL(2, F) ≃* Y i)) ∧ IsCentralInvolutionIn z (Y 0) ∧
    IsCentralInvolutionIn z (Y 2) ∧ IsCentralInvolutionIn u (Y 1) ∧ z ≠ u ∧ z * u = u * z ∧
    (∀ x ∈ Y 0, ∀ y ∈ Y 2, x * y = y * x) ∧
    (∃ α : ↥(StatedSU 3 q K) →* G, α.ker ≤ Subgroup.center ↥(StatedSU 3 q K) ∧
      α.range = Y 0 ⊔ Y 1) ∧
    (∃ α : ↥(StatedSU 3 q K) →* G, α.ker ≤ Subgroup.center ↥(StatedSU 3 q K) ∧
      α.range = Y 1 ⊔ Y 2)

section Linear

variable {G : Type} [Group G] {K : Type} [Field K] [Finite K] {z u : G} {Y : Fin 3 → Subgroup G}

theorem IsLinearA3Neighborhood.standardPairs (h : IsLinearA3Neighborhood K z u Y)
    (hK4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) :
    (∃ W, LinearBlockStandardPair K W (Y 0) (Y 1)) ∧
      (∃ W, LinearBlockStandardPair K W (Y 1) (Y 2)) ∧ ∃ x ∈ Y 1, x * z ≠ z * x := by
  obtain ⟨hiso, hz0, hz2, hu1, hzu, hcomm, -, ⟨α, hα, hαr⟩, ⟨β, hβ, hβr⟩⟩ := h
  obtain ⟨e0⟩ := hiso 0
  obtain ⟨e1⟩ := hiso 1
  obtain ⟨e2⟩ := hiso 2
  have h1 := linearBlockStandardPair_of_central_involutions hK4 h2 α hα
    (U := Y 0) (V := Y 1) (hαr ▸ le_sup_left) (hαr ▸ le_sup_right) e0 e1 hz0.1 hu1.1 hz0.2.1
    hu1.2.1 hz0.2.2 hu1.2.2 hzu hcomm
  have h2' := linearBlockStandardPair_of_central_involutions hK4 h2 β hβ
    (U := Y 1) (V := Y 2) (hβr ▸ le_sup_left) (hβr ▸ le_sup_right) e1 e2 hu1.1 hz2.1 hu1.2.1
    hz2.2.1 hu1.2.2 hz2.2.2 hzu.symm hcomm.symm
  exact ⟨⟨_, h1.1⟩, ⟨_, h2'.1⟩, h2'.2⟩

theorem IsLinearA3Neighborhood.comm_pairs (h : IsLinearA3Neighborhood K z u Y)
    (hK4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) :
    (∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ Y i, ∀ y ∈ Y j, x * y = y * x) ∧
      ∀ i j : Fin 3, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (Y i) (Y j) := by
  obtain ⟨hP01, hP12, -⟩ := h.standardPairs hK4 h2
  obtain ⟨-, -, -, -, -, -, hY02, -⟩ := h
  refine ⟨?_, ?_⟩
  · intro i j hij x hx y hy
    have hi' : i = 0 := Fin.ext (by omega)
    have hj' : j = 2 := Fin.ext (by omega)
    subst hi' hj'
    exact hY02 x hx y hy
  · intro i j hij
    have hcases : (i : ℕ) = 0 ∧ (j : ℕ) = 1 ∨ (i : ℕ) = 1 ∧ (j : ℕ) = 2 := by omega
    rcases hcases with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = 0 := Fin.ext hi
      have hj' : j = 1 := Fin.ext hj
      subst hi' hj'
      exact hP01
    · have hi' : i = 1 := Fin.ext hi
      have hj' : j = 2 := Fin.ext hj
      subst hi' hj'
      exact hP12

theorem IsLinearA3Neighborhood.exists_surjection (h : IsLinearA3Neighborhood K z u Y)
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hq : 5 ≤ p ^ f) :
    ∃ ψ : SL(4, K) →* G, ψ.range = ⨆ i, Y i ∧ ψ.ker ≤ Subgroup.center SL(4, K) ∧
      CFSG.IsQuasisimple ↥(⨆ i, Y i) ∧
      LieModel (↥(⨆ i, Y i) ⧸ Subgroup.center ↥(⨆ i, Y i)) StatedLieTag.PSL 4 p f := by
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard
    (by rw [hK]; exact (hp.odd_of_ne_two hp2).pow)
  obtain ⟨hcomm, hpair⟩ := h.comm_pairs (by rw [hK]; omega) h2
  exact CFSG.GH74.L5U5.exists_surjection_iSup p f hp hK (by omega) (n := 3) (by norm_num) Y hcomm
    hpair

theorem IsLinearA3Neighborhood.exists_noncommuting (h : IsLinearA3Neighborhood K z u Y)
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hq : 5 ≤ p ^ f) :
    ∃ x ∈ Y 1, x * z ≠ z * x := by
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard
    (by rw [hK]; exact (hp.odd_of_ne_two hp2).pow)
  exact (h.standardPairs (by rw [hK]; omega) h2).2.2

end Linear

section Unitary

variable {G : Type} [Group G] {K F : Type} [Field K] [Finite K] [Field F] [Finite F] {p f : ℕ}
  [Fact p.Prime] [CharP K p] {z u : G} {Y : Fin 3 → Subgroup G}

theorem exists_su_hom_of_statedSU (hK : Nat.card K = (p ^ f) ^ 2) {X : Type} [Group X]
    (α : ↥(StatedSU 3 (p ^ f) K) →* X)
    (hker : α.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) K)) :
    ∃ α' : Su K p f 3 →* X, α'.ker ≤ Subgroup.center (Su K p f 3) ∧ α'.range = α.range := by
  let e : Su K p f 3 ≃* ↥(StatedSU 3 (p ^ f) K) := MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)
  refine ⟨α.comp e.toMonoidHom, ?_, ?_⟩
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (MulEquivClass.apply_mem_center_iff e).1 (hker hx)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by simp⟩

theorem IsUnitaryA3Neighborhood.standardPairs (h : IsUnitaryA3Neighborhood (p ^ f) K F z u Y)
    (hK : Nat.card K = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) :
    (∃ W, UnitaryBlockStandardPair K p f W (Y 0) (Y 1)) ∧
      (∃ W, UnitaryBlockStandardPair K p f W (Y 1) (Y 2)) ∧ ∃ x ∈ Y 1, x * z ≠ z * x := by
  obtain ⟨hiso, hz0, hz2, hu1, hzu, hcomm, -, ⟨α, hα, hαr⟩, ⟨β, hβ, hβr⟩⟩ := h
  obtain ⟨e0⟩ := hiso 0
  obtain ⟨e1⟩ := hiso 1
  obtain ⟨e2⟩ := hiso 2
  obtain ⟨α', hα', hαr'⟩ := exists_su_hom_of_statedSU hK α hα
  obtain ⟨β', hβ', hβr'⟩ := exists_su_hom_of_statedSU hK β hβ
  have h1 := unitaryBlockStandardPair_of_central_involutions hK hp hF (by omega) α' hα'
    (U := Y 0) (V := Y 1) (by rw [hαr', hαr]; exact le_sup_left)
    (by rw [hαr', hαr]; exact le_sup_right) e0 e1 hz0.1 hu1.1 hz0.2.1 hu1.2.1 hz0.2.2 hu1.2.2 hzu
    hcomm
  have h2 := unitaryBlockStandardPair_of_central_involutions hK hp hF (by omega) β' hβ'
    (U := Y 1) (V := Y 2) (by rw [hβr', hβr]; exact le_sup_left)
    (by rw [hβr', hβr]; exact le_sup_right) e1 e2 hu1.1 hz2.1 hu1.2.1 hz2.2.1 hu1.2.2 hz2.2.2
    hzu.symm hcomm.symm
  exact ⟨⟨_, h1.1⟩, ⟨_, h2.1⟩, h2.2⟩

theorem IsUnitaryA3Neighborhood.comm_pairs (h : IsUnitaryA3Neighborhood (p ^ f) K F z u Y)
    (hK : Nat.card K = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) :
    (∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ Y i, ∀ y ∈ Y j, x * y = y * x) ∧
      ∀ i j : Fin 3, (j : ℕ) = i + 1 → ∃ W, UnitaryBlockStandardPair K p f W (Y i) (Y j) := by
  obtain ⟨hP01, hP12, -⟩ := h.standardPairs hK hF hp hq
  obtain ⟨-, -, -, -, -, -, hY02, -⟩ := h
  refine ⟨?_, ?_⟩
  · intro i j hij x hx y hy
    have hi' : i = 0 := Fin.ext (by omega)
    have hj' : j = 2 := Fin.ext (by omega)
    subst hi' hj'
    exact hY02 x hx y hy
  · intro i j hij
    have hcases : (i : ℕ) = 0 ∧ (j : ℕ) = 1 ∨ (i : ℕ) = 1 ∧ (j : ℕ) = 2 := by omega
    rcases hcases with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = 0 := Fin.ext hi
      have hj' : j = 1 := Fin.ext hj
      subst hi' hj'
      exact hP01
    · have hi' : i = 1 := Fin.ext hi
      have hj' : j = 2 := Fin.ext hj
      subst hi' hj'
      exact hP12

theorem IsUnitaryA3Neighborhood.exists_surjection (h : IsUnitaryA3Neighborhood (p ^ f) K F z u Y)
    (hK : Nat.card K = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∃ ψ : Su K p f 4 →* G, ψ.range = ⨆ i, Y i ∧ ψ.ker ≤ Subgroup.center (Su K p f 4) ∧
      CFSG.IsQuasisimple ↥(⨆ i, Y i) ∧
      LieModel (↥(⨆ i, Y i) ⧸ Subgroup.center ↥(⨆ i, Y i)) StatedLieTag.PSU 4 p f := by
  obtain ⟨hcomm, hpair⟩ := h.comm_pairs hK hF hp hq
  exact CFSG.GH74.L5U5.exists_surjection_iSup_unitary K p f hK hq (n := 3) (by norm_num) Y hcomm
    hpair

theorem IsUnitaryA3Neighborhood.exists_noncommuting
    (h : IsUnitaryA3Neighborhood (p ^ f) K F z u Y) (hK : Nat.card K = (p ^ f) ^ 2)
    (hF : Nat.card F = p ^ f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) : ∃ x ∈ Y 1, x * z ≠ z * x :=
  (h.standardPairs hK hF hp hq).2.2

end Unitary

end CFSG.GH74.GLS.LU
