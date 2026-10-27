module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Base
public import CFSG.ClassicalInvolution.Q3.Q3MTModel4
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Sec

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Ih8Model

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}

theorem exactMembers3 (M : Ih8Model Ω t k e) (hΩ : Q3T7M.HM Ω) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) : ExactMembers Ω :=
  Q3T8.Sect.exactMembers_of_card_eq hΩ fun L hL => by
    obtain ⟨R, hR, rfl⟩ := (M.mem_iff L).mp hL
    exact Q3MT.card_map3 M hΩ hG2 hD4 hR

theorem gen3 (M : Ih8Model Ω t k e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls) :
    CFSG.ClassicalInvolution.ModelFacts.Gen3 R :=
  Uniform.ih8Model_gen3 M hG2 hD4 hR

theorem ker_pow_three (M : Ih8Model Ω t k e) (hD4 : t ≠ .trialityD4) :
    ∀ x ∈ M.ψ.ker, x ^ 3 = 1 → x = 1 :=
  Uniform.ih8Model_ker_pow_three M hD4

noncomputable def ofOmegaLie {X : Type} [Group X] {Φ : Set (Subgroup X)} (hΦ : Q3T7M.HM Φ)
    (D : OmegaLie Φ) (hcard : D.card = 1) (hgen : omegaGen Φ = ⊤) (i : Fin D.card) :
    Ih8Model Φ (D.tag i) (D.rank i) (D.exp i) where
  isFundTag := D.isFundTag i
  admissible := D.admissible i
  exp_eq := D.exp_eq i
  ψ := D.hom i
  ker_le_center := D.ker_le_center i
  surj := D.hom_surjective_of_gen hcard hgen i
  cls := D.cls i
  cls_sub := fun _ hR => hR.1
  mem_iff := fun _ => D.mem_iff_exists_cls hcard i
  cls_conj := fun _ hR g => D.cls_conj hΦ.conjInvariant i hR g

theorem exists_datum_of_hasLieType {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (hΦ : Q3T7M.HM Φ) (hgen : omegaGen Φ = ⊤) {t : StatedLieTag} {k : ℕ}
    (h : HasLieType 3 1 Φ t k) : ∃ e, Nonempty (Ih8Model Φ t k e) := by
  obtain ⟨D, hcard, i, rfl, rfl⟩ := h
  exact ⟨D.exp i, ⟨ofOmegaLie hΦ D hcard hgen i⟩⟩

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Ih8Model

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.OmegaLie

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

theorem facts3 {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} (hΦ : Q3T7M.HM Φ)
    (D : OmegaLie Φ) (hcard : D.card = 1) (hgen : omegaGen Φ = ⊤) (i : Fin D.card)
    (hG2 : D.tag i ≠ .G2) (hD4 : D.tag i ≠ .trialityD4) {R : Subgroup (D.model i).K}
    (hR : R ∈ D.cls i) :
    CFSG.ClassicalInvolution.ModelFacts.Gen3 R ∧
      (∀ x ∈ (D.hom i).ker, x ^ 3 = 1 → x = 1) ∧
      (∀ r ∈ R, ∀ s ∈ R, D.hom i r = D.hom i s → r = s) ∧
      Nonempty (↥R ≃* SL(2, GaloisField 3 (D.exp i))) := by
  have M := Ih8Model.ofOmegaLie hΦ D hcard hgen i
  exact ⟨(Ih8Model.ofOmegaLie hΦ D hcard hgen i).gen3 hG2 hD4 hR,
    (Ih8Model.ofOmegaLie hΦ D hcard hgen i).ker_pow_three hD4,
    fun r hr s hs h =>
      Q3MT.injOn_map3 (Ih8Model.ofOmegaLie hΦ D hcard hgen i) hΦ hG2 hD4 hR r hr s hs h,
    (Ih8Model.ofOmegaLie hΦ D hcard hgen i).cls_equiv_sl2 (by norm_num) hG2 hD4 hR⟩

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.OmegaLie
