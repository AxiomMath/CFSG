module

public import CFSG.ClassicalInvolution.Asc77.AscR10D3b
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups commutatorElement



section TD4

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem quotViol_false_of_trialityD4_three {n : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 n 3 1)
    (hΩ : HypOmegaModU (.sl2 3 1) Φ) (hcard : ∀ L ∈ Φ, Nat.card L = 24) {c : Q3.CompData}
    (hc : c = Q3.CompData.model .trialityD4 n) (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) {R S : Subgroup c.G} (hR : R ∈ c.fund)
    (hS : S ∈ c.fund) {z j a : X} (h : QuotViol Φ (R.map ψ) (S.map ψ) z j a) : False := by
  subst hc
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn : n = 0 := hadm.2.2
  subst hn
  have hinj : Function.Injective ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inr rfl) 0 (le_refl 1) ψ hker
  have hrange : R.map ψ ⊔ S.map ψ ≤ ψ.range :=
    sup_le (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)
  obtain ⟨ã, hã⟩ := hrange (mem_sup_of_mem_pairNormalizers h.ha)
  set R' : Subgroup (Q3.CompData.model .trialityD4 0).G := conjSub ã S with hR'
  have hR'cls : R' ∈ (Q3.CompData.model .trialityD4 0).fund :=
    RouteD.conjSub_mem_fundamentalSubgroups hS ã
  have hR'map : R'.map ψ = conjSub a (S.map ψ) := by
    rw [hR', AscQuot.map_conjSub, hã]
  have hR'Φ : R'.map ψ ∈ Φ := by
    rw [hR'map]; exact hΩ.conjInvariant a _ h.mem_right
  have hzR' : IsUniqueInvolution (R'.map ψ) z := by
    rw [hR'map]
    have := h.hj.conj a
    rwa [h.haj] at this
  obtain ⟨c, hcz, hc⟩ := isUniqueInvolution_of_map hinj h.hz
  obtain ⟨c', hc'z, hc'⟩ := isUniqueInvolution_of_map hinj hzR'
  have hcc : c' = c := hinj (hc'z.trans hcz.symm)
  rw [hcc] at hc'
  have hne : R' ≠ R := fun e => h.hne (by rw [← hR'map, e])
  by_cases hconj : ∃ g, R' = R.map (MulAut.conj g).toMonoidHom
  · obtain ⟨g, hg⟩ := hconj
    have hg' : R' = conjSub g R := hg
    rw [hg'] at hc' hne
    exact hne (noTwinsFund_td4 hp2 hadm R hR c hc g hc')
  · have hcardR : Nat.card R = 24 := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact hcard _ h.mem_left
    have hcardR' : Nat.card R' = 24 := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact hcard _ hR'Φ
    exact d4OrdersDiffer 3 .trialityD4 0 1 rfl hadm R hR R' hR'cls hconj
      (hcardR.trans hcardR'.symm)

end TD4

section Residual

@[expose] def QV3ModelV : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), HypOmegaModU (.sl2 3 1) Φ →
    ∀ {ι : Type} (D : Q3.LieSystemData3 ι X Φ) (i : ι)
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t →
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
      D.kind i = Q3.CompData.model t n → t ≠ .G2 →
        ∀ (R S : Subgroup (D.kind i).G), R ∈ (D.kind i).fund → S ∈ (D.kind i).fund →
          ∀ z j a : X, QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a → False

theorem qv3Comp_of_qv3ModelV (hM : QV3ModelV) : QV3Comp := by
  intro X _ _ Φ hΦ ι D i R S hR hS z j a h
  rcases D.valid i with ⟨t, n, hft, hadm, hk⟩ | hk | hk
  · by_cases ht : t = .G2
    · subst ht
      obtain ⟨-, -, hn, -⟩ := hadm
      subst hn
      exact hk
    · exact (hM X Φ hΦ D i t n hft hadm hk ht R S hR hS z j a h).elim
  · exact (quotViol_false_of_sl23 hk (D.hom i) hR hS h).elim
  · exact (quotViol_false_of_m11 hk (D.hom i) (D.ker_le_center i) hR hS h).elim

theorem qv3ModelV_of_dich3
    (hDich : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t →
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 → t ≠ .G2 → t ≠ .trialityD4 →
        StdDich3 t n) : QV3ModelV := by
  intro X _ _ Φ hΦ ι D i t n hft hadm hk ht2 R S hR hS z j a h
  by_cases ht4 : t = .trialityD4
  · subst ht4
    exact quotViol_false_of_trialityD4_three hadm hΦ D.card_eq hk (D.hom i)
      (D.ker_le_center i) hR hS h
  · exact quotViol_false_of_dich3 (hDich t n hft hadm ht2 ht4) hft hadm ht2 ht4 hΦ D.card_eq hk
      (D.hom i) (D.ker_le_center i) hR hS h

theorem g2Comp3_of_qv3ModelV (hM : QV3ModelV) : G2Comp3 :=
  g2Comp3_of_qv3Comp (qv3Comp_of_qv3ModelV hM)

theorem res10aNoConj9_of_qv3ModelV (p f : ℕ) [Fact p.Prime] (hM : QV3ModelV) :
    Q3.CIT3Inductive → p ^ f = 9 → Res10aNoConj p f :=
  res10aNoConj9_of_qv3Comp p f (qv3Comp_of_qv3ModelV hM)

theorem res10aNoConj9_of_dich3 (p f : ℕ) [Fact p.Prime]
    (hDich : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t →
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 → t ≠ .G2 → t ≠ .trialityD4 →
        StdDich3 t n) :
    Q3.CIT3Inductive → p ^ f = 9 → Res10aNoConj p f :=
  res10aNoConj9_of_qv3ModelV p f (qv3ModelV_of_dich3 hDich)

end Residual

end CFSG.ClassicalInvolution.Asc77.T3CII
