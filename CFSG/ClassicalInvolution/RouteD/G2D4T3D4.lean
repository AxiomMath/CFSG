module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Model
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactComp

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem noTwinsFund_of_td4_tag (hp2 : p ≠ 2) {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n e : ℕ} (ht : t = .trialityD4) (hadm : StatedLieAdmissible t n p e) :
    NoTwinsFund p e t n := by
  subst ht
  have hn : n = 0 := hadm.2.2
  subst hn
  exact noTwinsFund_td4 hp2 hadm

variable {X : Type} [Group X] [Finite X] {f : ℕ} {Φ : Set (Subgroup X)} {z j a : X}

theorem quotViol_false_of_trialityD4 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ)
    (D : OmegaLie p f Φ) {i : Fin D.card} (ht : D.tag i = .trialityD4)
    {R S : Subgroup (D.model i).K} (hR : R ∈ D.cls i) (hS : S ∈ D.cls i)
    (h : QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a) : False := by
  set ψ := D.hom i with hψ
  have hi : D.tag i = .G2 ∨ D.tag i = .trialityD4 := Or.inr ht
  have hinj : Function.Injective ψ := hom_injective_of_g2d4 hp D hi
  have hΩ : HypOmega p f Φ := hΦ.toExact (D.exactMembers hp hq hΦ)
  have hrange : R.map ψ ⊔ S.map ψ ≤ ψ.range :=
    sup_le (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)
  obtain ⟨ã, hã⟩ := hrange (mem_sup_of_mem_pairNormalizers h.ha)
  set R' : Subgroup (D.model i).K := conjSub ã S with hR'
  have hR'cls : R' ∈ D.cls i := D.cls_conj hΦ.conjInvariant i hS ã
  have hR'map : R'.map ψ = conjSub a (S.map ψ) := by
    rw [hR', AscQuot.map_conjSub, hã]
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
    exact hne (noTwinsFund_of_td4_tag hp ht (D.admissible i) R hR.1 c hc g hc')
  · have hcardR : Nat.card R = Nat.card SL(2, GaloisField p f) := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact natCard_member hΩ hR.2
    have hcardR' : Nat.card R' = Nat.card SL(2, GaloisField p f) := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact natCard_member hΩ hR'cls.2
    exact d4OrdersDiffer p (D.tag i) (D.rank i) (D.exp i) ht (D.admissible i) R hR.1 R' hR'cls.1
      hconj (hcardR.trans hcardR'.symm)

end CFSG.ClassicalInvolution.G2D4Models
