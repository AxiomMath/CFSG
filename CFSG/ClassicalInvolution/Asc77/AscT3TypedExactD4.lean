module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactComp
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedG2Gen
public import CFSG.ClassicalInvolution.Asc77.AscIHD4
public import CFSG.ClassicalInvolution.Asc77.AscIHWitness

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

section Model

variable {p : ℕ} [Fact p.Prime]

theorem isCoatom_normalizer_of_td4 (hD4 : D4NormalizerMax p)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ} (ht : t = .trialityD4)
    (hadm : StatedLieAdmissible t n p e) (hp : p ≠ 2)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) :
    IsCoatom (Subgroup.normalizer (R : Set (modelUniv t n p e Fact.out).K)) := by
  subst ht
  have hn : n = 0 := hadm.2.2
  subst hn
  exact hD4 e hadm hp R hR

end Model

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}
  {z j a : X}

theorem QuotViol.false_of_trialityD4 (hD4 : D4NormalizerMax p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) {i : Fin D.card} (ht : D.tag i = .trialityD4)
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
  ·
    obtain ⟨g, hg⟩ := hconj
    have hg' : R' = conjSub g R := hg
    have hcoatom : IsCoatom (Subgroup.normalizer (R : Set (D.model i).K)) :=
      isCoatom_normalizer_of_td4 hD4 ht (D.admissible i) hp hR.1
    have hZ := RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp hi (D.rank i) (D.admissible i).2.1
    rw [hg'] at hc' hne
    exact hne (conjSub_eq_of_same_involution hc hc' hZ hcoatom)
  ·
    have hcardR : Nat.card R = Nat.card SL(2, GaloisField p f) := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact natCard_member hΩ hR.2
    have hcardR' : Nat.card R' = Nat.card SL(2, GaloisField p f) := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact natCard_member hΩ hR'cls.2
    exact d4OrdersDiffer p (D.tag i) (D.rank i) (D.exp i) ht (D.admissible i) R hR.1 R' hR'cls.1
      hconj (hcardR.trans hcardR'.symm)

end CFSG.ClassicalInvolution.Asc77.T3Typed
