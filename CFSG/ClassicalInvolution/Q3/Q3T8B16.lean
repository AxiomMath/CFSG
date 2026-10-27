module

public import CFSG.ClassicalInvolution.Q3.Q3T8B15
public import CFSG.ClassicalInvolution.Q3.Q3UFix
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.Uniform.ULieType
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform

section Vacuous


variable {G : Type} [Group G] [Finite G] {c z b : G} {B : Subgroup G}

theorem hyp51At_of_vacuous_component (hB : CFSG.Open.IsElemAbelian 2 B) (hcB : c ∈ B)
    (hc1 : c ≠ 1) (hzB : z ∈ B) (hz1 : z ≠ 1) (hzc : z ≠ c)
    (hzC : z ∈ Subgroup.centralizer ({c} : Set G)) (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c)
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) {Q : Subgroup (OddQuot c)}
    (hQ : CFSG.IsComponent Q) (hzQ : oddQuotMk c ⟨z, hzC⟩ ∈ Q)
    (hbQ : ∀ y ∈ Q, oddQuotMk c ⟨b, hbC⟩ * y = y * oddQuotMk c ⟨b, hbC⟩) :
    Asc77.Hyp51At B c := by
  have hQeq : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L → L = Q := by
    intro L hL hm
    by_contra hne
    obtain ⟨y, hyL, hy⟩ := hm _ (oddQuotMk_mem_modOdd hzB hzC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hzB hz1 hzc hzC)
    exact hy (Q3.commute_of_ne_isComponent hQ hL (Ne.symm hne) hzQ hyL)
  refine ⟨fun L L' hL hL' hm hm' => ?_, fun L hL hm => ?_⟩
  · exact (hQeq L hL hm).trans (hQeq L' hL' hm').symm
  · exfalso
    have hLQ := hQeq L hL hm
    subst hLQ
    exact not_movedByAll_of_centralizes hB hcB hc1 hbB hb1 hbc hbC hbQ hm

end Vacuous

section InvolDich


@[expose] def InvolDichSect : Prop :=
  ∀ (Y : Type) [Group Y] (Φ : Set (Subgroup Y)) (D : LieSystemDataU 3 1 (Fin 1) Y Φ),
    (CompIs 3 1 (D.kind 0) .PSL 3 ∨ D.kind 0 = Q3.CompData.m11) →
      ∀ J' ∈ Φ, ∀ u : Y, IsUniqueInvolution J' u →
        ∀ β : MulAut Y, β * β = 1 → (∀ x ∈ J', β x = x) → β = 1 ∨ β = MulAut.conj u

end InvolDich

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
