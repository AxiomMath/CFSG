module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExArith

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def Lie23To89At (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), StatedLieAdmissible t n 2 f →
    LieModel X t n 2 f → ∀ τ : X, orderOf τ = 2 →
      23 ∣ Nat.card ↥(centralizer ({τ} : Set X)) → 89 ∣ Nat.card ↥(centralizer ({τ} : Set X))

theorem prime_dvd_card_centralizer_of_classesCover {X G : Type} [Group X] [Group G]
    (e : X ≃* G) {reps : List G} {p : ℕ} [hp : Fact p.Prime]
    (hcov : ∀ x : G, x * x = 1 → x ≠ 1 → ∃ y ∈ reps, IsConj y x)
    (hz : ∀ y ∈ reps, ∃ z : G, orderOf z = p ∧ Commute z y)
    {τ : X} (hτ : orderOf τ = 2) : p ∣ Nat.card ↥(centralizer ({τ} : Set X)) := by
  have hτ2 : τ * τ = 1 := by rw [← sq, ← hτ]; exact pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hg2 : e τ * e τ = 1 := by rw [← map_mul, hτ2, map_one]
  have hg1 : e τ ≠ 1 := fun h => hτ1 (by simpa using h)
  obtain ⟨y, hy, hyc⟩ := hcov (e τ) hg2 hg1
  obtain ⟨c, hc⟩ := isConj_iff.1 hyc
  obtain ⟨z, hzo, hzy⟩ := hz y hy
  have hcomm : Commute (MulAut.conj c z) (e τ) := by
    have := hzy.map (MulAut.conj c)
    rwa [MulAut.conj_apply, MulAut.conj_apply, hc] at this
  have hw : Commute (e.symm (MulAut.conj c z)) τ := by
    have := hcomm.map e.symm
    rwa [MulEquiv.symm_apply_apply] at this
  have hwo : orderOf (e.symm (MulAut.conj c z)) = p := by
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hzo]
  have hmem : e.symm (MulAut.conj c z) ∈ centralizer ({τ} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 hw.eq
  have := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥(centralizer ({τ} : Set X)))
  rwa [Subgroup.orderOf_mk, hwo] at this

section Order


set_option linter.unusedSectionVars false

theorem eleven_dvd_of_twentythree_dvd_card {X : Type} [Group X] {t : StatedLieTag} {f : ℕ}
    (ht : t ∈ [.G2, .F4, .E6, .E7, .E8, .twistedE6, .trialityD4, .twistedB2, .twistedF4])
    (hadm : StatedLieAdmissible t 0 2 f) (hM : LieModel X t 0 2 f) (h : 23 ∣ Nat.card X) :
    11 ∣ f := by
  obtain ⟨-, hmul, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput X t 0 2 f
    hadm hM
  refine eleven_dvd_of_twentythree_dvd_lieOrderNumerator ht ?_
  rw [← hmul]
  exact Dvd.dvd.mul_right h _

theorem not_twentythree_dvd_card_of_tits {X : Type} [Group X] {f : ℕ}
    (hadm : StatedLieAdmissible .Tits 0 2 f) (hM : LieModel X .Tits 0 2 f) :
    ¬ 23 ∣ Nat.card X := by
  intro h
  obtain ⟨-, hmul, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput X .Tits 0 2 f
    hadm hM
  apply not_twentythree_dvd_lieOrderNumerator_Tits (2 ^ f)
  rw [← hmul]
  exact Dvd.dvd.mul_right h _

end Order

end CFSG.ComponentClassification.CatFC.DS81.Ex
