module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClInner
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriAux
import CFSG.HardMathSupport.Solomon.Coordinator.L514Y0Comp
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

theorem glaPComponent_self_of_dvd_card {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    {K : Subgroup Y} (hp : p.Prime) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hdvd : p ∣ Nat.card ↥K) : GLAPComponent p K K := by
  set O : Subgroup ↥K := GLAPPrimeCore p ↥K with hO
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hc := CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥K
    rw [← hO, htop, Subgroup.card_top] at hc
    exact absurd (Nat.eq_one_of_dvd_coprimes hc (dvd_refl p) hdvd) hp.ne_one
  haveI hnt : Nontrivial (↥K ⧸ O) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hOtop
  have hqq : CFSG.Open.IsQuasisimple (↥K ⧸ O) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_of_surjective_of_nontrivial
      hq (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  have hL : (K.subgroupOf K).map (QuotientGroup.mk' O) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective O
  refine ⟨le_rfl, IsSubnormal.refl K, ?_, ?_⟩
  · rw [hL]
    exact ⟨le_top, IsSubnormal.refl _,
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        Subgroup.topEquiv.symm hqq⟩
  · intro J hJ _ heq
    rw [hL] at heq
    have hsup : J.subgroupOf K ⊔ O = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' O) (J.subgroupOf K)
      rw [heq, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hOZ : O ≤ Subgroup.center ↥K := by
      rcases CFSG.HardMathSupport.Solomon.Coordinator.l514y0_normal_le_center_or_top hq O with h | h
      · exact h
      · exact absurd h hOtop
    have hsup' : J.subgroupOf K ⊔ Subgroup.center ↥K = ⊤ :=
      top_le_iff.1 (hsup ▸ sup_le_sup_left hOZ _)
    have htop := CFSG.HardMathSupport.Solomon.Coordinator.l514y0_eq_top_of_sup_center hq.1 hsup'
    exact absurd (Subgroup.subgroupOf_eq_top.1 htop) (not_le_of_gt hJ)

section Certificates

theorem innDiagOn_of_mem_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} {X J : Subgroup G}
    {b : G} (hp : p.Prime) (hJ : GLAPComponent p X J) (hchevJ : IsChevSimple 2 (PSimple p J))
    (hbnorm : b ∈ Subgroup.normalizer (J : Set G))
    (hbJ : b ∈ Subgroup.centralizer (J : Set G)) :
    InnDiagOn p (Subgroup.zpowers b) J :=
  innDiagOn_of_innerOn hp hJ hchevJ hbnorm (innerOn_of_mem_centralizer hbJ)

theorem innDiagOn_zpowers_of_mem_zpowers {G : Type} [Group G] [Finite G] {p : ℕ}
    {X J : Subgroup G} {d b : G} (hp : p.Prime) (hJ : GLAPComponent p X J)
    (hchevJ : IsChevSimple 2 (PSimple p J)) (hbnorm : b ∈ Subgroup.normalizer (J : Set G))
    (hdJ : J ≤ Subgroup.centralizer ({d} : Set G)) (hbn : b ∈ Subgroup.zpowers d) :
    InnDiagOn p (Subgroup.zpowers b) J := by
  have hcent : b ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hdj : d * j = j * d :=
      Subgroup.mem_centralizer_iff.1 (hdJ hj) d (Set.mem_singleton d)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbn
    rw [← hk]
    exact (Commute.zpow_right (show Commute j d from hdj.symm) k).eq
  exact innDiagOn_of_mem_centralizer hp hJ hchevJ hbnorm hcent

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end