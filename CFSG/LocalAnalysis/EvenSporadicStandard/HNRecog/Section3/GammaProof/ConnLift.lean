module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.ConnOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.GzNE

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_exists_lift (H : GammaHyps a z) {v : Gbar z}
    (hv : v ∉ _root_.commutator (Gbar z)) (hv2 : v ^ 2 = 1) :
    ∃ (y : G) (hy : y ∈ Gx z), IsConj a y ∧ barOf z ⟨y, hy⟩ = v := by
  obtain ⟨q, hqz, hqQ, hqA⟩ := exists_mem_Gx_not_mem_Qz H.hF1.self H.hF2.self
  have hqout : barOf z ⟨q, hqz⟩ ∉ _root_.commutator (Gbar z) :=
    gamma_barOf_not_mem_commutator H.h H.hOrb.self H.hNo.self hqz hqQ hqA
  have hqsq : (⟨q, hqz⟩ : ↥(Gx z)) ^ 2 = 1 := by
    apply Subtype.ext
    show q ^ 2 = 1
    exact H.sq_a hqA
  have hq2 : barOf z ⟨q, hqz⟩ ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    rw [hqsq]
    rfl
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar H.h
  obtain ⟨β, -, hβ⟩ := exists_conj_of_outer_of_mulEquiv e hqout hv hq2 hv2
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective β
  have hgb : barOf z g = β := hg
  let y : ↥(Gx z) := g * ⟨q, hqz⟩ * g⁻¹
  have hybar : barOf z y = barOf z g * barOf z ⟨q, hqz⟩ * (barOf z g)⁻¹ := by
    simp [y, barOf, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  refine ⟨(y : G), y.2, hqA.trans (isConj_iff.mpr ⟨(g : G), by simp [y]⟩), ?_⟩
  change barOf z y = v
  rw [hybar, hgb]
  exact hβ

end CFSG.EvenSporadicStandard.HNRecog.Section3
