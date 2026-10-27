module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Comp
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.D1RankTwoCentre
import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.GH74.Uniqueness.SU
open scoped commutatorElement

theorem CentralAxis.exists_order_prime_central {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {R S : Subgroup G} (hR : IsPGroup p R) (hSR : S ≤ R)
    (hnorm : ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S) (hS : S ≠ ⊥) :
    ∃ w ∈ S, orderOf w = p ∧ ∀ r ∈ R, r * w = w * r := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hcS, hc1, hcc⟩ := SU1.exists_central_of_normal hp hR hSR hnorm hS
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR ⟨c, hSR hcS⟩
  have hkc : orderOf c = p ^ k := by
    rw [← Subgroup.orderOf_mk c (hSR hcS)]
    exact hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hc1 (orderOf_eq_one_iff.mp (by simpa using hkc))
  have hpd : p ∣ orderOf c := by
    rw [hkc]
    exact dvd_pow_self p hk0
  refine ⟨c ^ (orderOf c / p), S.pow_mem hcS _, orderOf_pow_orderOf_div ?_ hpd, fun r hr => ?_⟩
  · rw [hkc]
    exact (pow_pos hp.pos k).ne'
  · exact (Commute.pow_right (show Commute r c from hcc r hr) _).eq

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem CentralAxis.not_mem_of_map_eq (hd : D1CaseTwoDataU p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤) {S : Subgroup G}
    (hS : (S.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L)
    {z : H} (hzp : orderOf (z : G) = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))) :
    (z : G) ∉ S := by
  intro hzS
  have hp := hd.cfg.red.prime
  have himg : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L := by
    rw [← hS]
    exact Subgroup.mem_map_of_mem _ (show z ∈ S.subgroupOf H from hzS)
  have hZ : (⟨_, himg.2⟩ : L) ∈ Subgroup.center L :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hzL y y.2)
  rw [hd.cfg.red.center_eq_bot_of_isCyclic hL (hd.cyclic L hL), Subgroup.mem_bot] at hZ
  have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p) z = 1 := congrArg Subtype.val hZ
  have h2 := orderOf_mk_of_coprime hp (primeComplementCore (G := H) p)
    (primeComplementCore_coprime p) ((Subgroup.orderOf_coe z).symm.trans hzp)
  rw [h1, orderOf_one] at h2
  exact hp.one_lt.ne h2

theorem D1CaseTwoDataU.exists_central_elemAbelian (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hGrp : CaseTwoGroupFacts) (hd : D1CaseTwoDataU p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) (hRP : R = (P : Subgroup G)) :
    ∃ E : Subgroup G, E ≤ (P : Subgroup G) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ e ∈ E, ∀ x ∈ (P : Subgroup G), e * x = x * e := by
  have hp := hd.cfg.red.prime
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  obtain ⟨S, hSR, hSnorm, -, hSlt, hSmap⟩ := hd.exists_normalCyclic_of_comp hOut hS hGrp hL hLX
  have hSne : S ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hSlt
    exact absurd hSlt (by have := hp.two_le; omega)
  obtain ⟨w, hwS, hwp, hwc⟩ :=
    CentralAxis.exists_order_prime_central hp hd.cfg.ext.isPGroup hSR hSnorm hSne
  have hzS : (z : G) ∉ S := CentralAxis.not_mem_of_map_eq hd hL hSmap hzp hzL
  have hzw : (z : G) ∉ Subgroup.zpowers w := fun h => hzS (Subgroup.zpowers_le.mpr hwS h)
  have hwR : w ∈ R := hSR hwS
  have hzc : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.mp (hRz hwR)
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers hp
    (a := w) (y := (z : G)) (hwp ▸ pow_orderOf_eq_one w) (hzp ▸ pow_orderOf_eq_one (z : G))
    (fun h => hp.one_lt.ne (by rw [← hwp, h, orderOf_one])) hzw hzc
  refine ⟨Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G), sup_le ?_ ?_, hel, hcard, ?_⟩
  · exact Subgroup.zpowers_le.mpr (hRP ▸ hwR)
  · exact Subgroup.zpowers_le.mpr (hRP ▸ hzR)
  · intro e he x hx
    have hxR : x ∈ R := hRP ▸ hx
    have hcent : Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G) ≤
        Subgroup.centralizer (R : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun r hr => hwc r hr
      · exact Subgroup.mem_centralizer_iff.mpr fun r hr =>
          Subgroup.mem_centralizer_singleton_iff.mp (hRz hr)
    exact (Subgroup.mem_centralizer_iff.mp (hcent he) x hxR).symm

theorem D1CaseTwoDataU.sylow_le_commutator (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hGrp : CaseTwoGroupFacts) (hd : D1CaseTwoDataU p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) (hRP : R = (P : Subgroup G)) :
    (P : Subgroup G) ≤ ⁅M, M⁆ := by
  obtain ⟨E, hEP, hE, hEcard, hEcent⟩ := hd.exists_central_elemAbelian hOut hS hGrp hz hRP
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have h3 : 3 ≤ Open.pRank p (P : Subgroup G) := by
    rw [← hRP]
    exact hd.cfg.ext.three_le_pRank
  have hU : rankThreeGamma 2 p (P : Subgroup G) ≤ M :=
    (rankThreeGamma_two_le_GLBWeakCore hp hEP hE hEcard hEcent h3).trans hd.cfg.ext.weakCore_le
  exact sylow_le_commutator_of_gamma_two hd.cfg.glob hd.cfg.loc.sigma hd.cfg.loc.isCoreMaxLocal hU

end CFSG.LocalAnalysis.RankThreeTheoremC
