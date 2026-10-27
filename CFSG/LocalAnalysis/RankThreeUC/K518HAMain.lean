module

public import CFSG.LocalAnalysis.RankThreeUC.K518HAAct
public import CFSG.LocalAnalysis.RankThreeUC.K518HDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCentral
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviTransport
public import CFSG.LocalAnalysis.RankThreeUC.K518HADisp
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.Tits.GN516.SimpleBQ
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

private theorem center_quotient_eq_bot {L : Type} [Group L] (hq : CFSG.Open.IsQuasisimple L) :
    Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (L ⧸ Subgroup.center L)) with h | h
  · exact h
  · exfalso
    have hcomm : commutator (L ⧸ Subgroup.center L) = ⊤ := by
      have hp := hq.1
      rw [commutator_def] at hp ⊢
      rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' (Subgroup.center L))
        (QuotientGroup.mk'_surjective _), ← Subgroup.map_commutator, hp,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hbot : commutator (L ⧸ Subgroup.center L) = ⊥ := by
      rw [commutator_def, ← le_bot_iff]
      refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
      have h1 : g₁ ∈ Subgroup.center (L ⧸ Subgroup.center L) := by rw [h]; exact Subgroup.mem_top _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 h1 g₂).symm
    haveI := hq.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (L ⧸ Subgroup.center L)
    apply hab
    have ha : a ∈ commutator (L ⧸ Subgroup.center L) := by rw [hcomm]; exact Subgroup.mem_top _
    have hb : b ∈ commutator (L ⧸ Subgroup.center L) := by rw [hcomm]; exact Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at ha hb
    rw [ha, hb]


set_option linter.unusedSectionVars false

theorem k518Crit_of_rk (h1 : K518RkSL2) (h2 : K518RkSU3) : K518Crit := by
  intro Y _ _ L S P hL hcl hrk hS hP p hp hp2 _hpZ r hrL hrS hr hr1 hr2 hr3
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hperf : commutator ↥L = ⊤ := hq.1
  have hZb : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := center_quotient_eq_bot hq
  have hinj : Function.Injective (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →*
      MulAut (↥L ⧸ Subgroup.center ↥L)) := conj_injective_of_center_eq_bot hZb
  set N : Subgroup Y := Subgroup.normalizer (L : Set Y) with hN
  set cb : MulAut (↥L ⧸ Subgroup.center ↥L) := actQ L ⟨r, hrL⟩ with hcb
  obtain ⟨k, hk⟩ := hr
  have hcbord : ∃ j : ℕ, orderOf cb = p ^ j := by
    have h := orderOf_map_dvd (actQ L) (⟨r, hrL⟩ : ↥N)
    rw [Subgroup.orderOf_mk, hk] at h
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h
    exact ⟨j, hj⟩
  have hnotinn : cb ∉ (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →*
      MulAut (↥L ⧸ Subgroup.center ↥L)).range := by
    rintro ⟨yb, hyb⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
    have h3 : cb = actQ L ⟨(y : Y), Subgroup.le_normalizer y.2⟩ := by
      rw [actQ_of_mem]
      exact hyb.symm
    have h5 : actQ L (⟨r, hrL⟩ * (⟨(y : Y), Subgroup.le_normalizer y.2⟩ : ↥N)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h3, mul_inv_cancel]
    have h6 := (actQ_eq_one_iff L hperf _).1 h5
    apply hr1
    have e : r = (r * (y : Y)⁻¹) * (y : Y) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h6) (Subgroup.mem_sup_left y.2)
  rcases hasRkModel_or_smallAut hcl hrk with hmodel | ⟨m, hm, hmcard⟩
  swap
  · exfalso
    obtain ⟨j, hj⟩ := hcbord
    apply hnotinn
    refine mem_range_conj_of_card hZb hmcard hj ?_
    rcases hm with rfl | rfl
    · have h2' : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
      simpa using Nat.Coprime.pow_right 2 h2'
    · exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  haveI : Finite (MulAut (↥L ⧸ Subgroup.center ↥L)) :=
    Finite.of_injective (fun f : MulAut (↥L ⧸ Subgroup.center ↥L) => (f : _ → _))
      (fun f g h => MulEquiv.ext fun x => congrFun h x)
  set mk : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hmk
  obtain ⟨T0, hT0⟩ := CFSG.AGLEmbeddingD2.McLaughlin.Lie.exists_sylow_of_isSylowTwoOf hS
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  set T : Sylow 2 (↥L ⧸ Subgroup.center ↥L) := T0.mapSurjective hsurj with hT
  have hTcoe : (T : Subgroup (↥L ⧸ Subgroup.center ↥L)) = (S.subgroupOf L).map mk := by
    rw [hT, Sylow.coe_mapSurjective, hT0]
  have hmin := isMinOverBorel_map_of_isMinOverBorel hS hP
  rw [← hTcoe] at hmin
  have hSstab : ∀ x : ↥L, x ∈ S.subgroupOf L → conjAut L r hrL x ∈ S.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.1 hrS _).1 hx
  have hSstab' : ∀ x : ↥L, x ∈ S.subgroupOf L → (conjAut L r hrL).symm x ∈ S.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hrS) (x : Y)).1 hx
    change r⁻¹ * (x : Y) * r ∈ S
    simpa using h
  have hcT : (T : Subgroup (↥L ⧸ Subgroup.center ↥L)).map cb.toMonoidHom = T := by
    rw [hTcoe]
    ext y
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨conjAut L r hrL s, hSstab s hs, (actQ_mk L ⟨r, hrL⟩ s).symm⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨mk ((conjAut L r hrL).symm s), ⟨_, hSstab' s hs, rfl⟩, ?_⟩
      show actQ L ⟨r, hrL⟩ (QuotientGroup.mk ((conjAut L r hrL).symm s)) = mk s
      rw [actQ_mk, MulEquiv.apply_symm_apply]
      rfl
  have e1 : cb ^ p = actQ L ⟨r ^ p, N.pow_mem hrL p⟩ := by
    rw [hcb, ← map_pow]
    rfl
  obtain ⟨z, hz, x, hx, hrp⟩ : ∃ z ∈ Subgroup.centralizer (L : Set Y), ∃ x ∈ L, r ^ p = z * x := by
    have hmem : r ^ p ∈ (Subgroup.centralizer (L : Set Y) ⊔ L : Subgroup Y) := by
      rwa [sup_comm]
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (Subgroup.centralizer_le_normalizer _)] at hmem
    obtain ⟨z, hz, x, hx, h⟩ := hmem
    exact ⟨z, hz, x, hx, h.symm⟩
  set l : ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk ⟨x, hx⟩ with hldef
  have hcbp : cb ^ p = MulAut.conj l := by
    rw [e1]
    have e2 : (⟨r ^ p, N.pow_mem hrL p⟩ : ↥N) =
        ⟨z, Subgroup.centralizer_le_normalizer _ hz⟩ * ⟨x, Subgroup.le_normalizer hx⟩ :=
      Subtype.ext hrp
    rw [e2, map_mul, (actQ_eq_one_iff L hperf _).2 hz, one_mul]
    exact actQ_of_mem L ⟨x, hx⟩
  have hl1 : l ≠ 1 := by
    intro h
    have h' : actQ L ⟨r ^ p, N.pow_mem hrL p⟩ = 1 := by rw [← e1, hcbp, h, map_one]
    exact hr3 ((actQ_eq_one_iff L hperf _).1 h')
  have hlp : ∃ j : ℕ, orderOf l = p ^ j := by
    obtain ⟨j, hj⟩ := hcbord
    have h3 : orderOf l ∣ p ^ j := by
      have h4 : orderOf (cb ^ p) ∣ orderOf cb := orderOf_pow_dvd p
      rw [hcbp, orderOf_injective _ hinj, hj] at h4
      exact h4
    obtain ⟨j', -, hj'⟩ := (Nat.dvd_prime_pow hp).1 h3
    exact ⟨j', hj'⟩
  have hstabp : (T : Subgroup (↥L ⧸ Subgroup.center ↥L)).map (cb ^ p).toMonoidHom = T :=
    map_eq_of_mem_stabSub ((stabSub (T : Subgroup (↥L ⧸ Subgroup.center ↥L))).pow_mem
      (mem_stabSub_of_map_eq hcT) p)
  have hl : l ∈ Subgroup.normalizer ((T : Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set _) := by
    apply Subgroup.mem_normalizer_fintype
    intro t ht
    have h3 : (cb ^ p) t ∈ (T : Subgroup (↥L ⧸ Subgroup.center ↥L)).map (cb ^ p).toMonoidHom :=
      ⟨t, ht, rfl⟩
    rw [hstabp] at h3
    have h4 : (cb ^ p) t = l * t * l⁻¹ := by rw [hcbp, MulAut.conj_apply]
    rwa [h4] at h3
  have hcInn : cb ∉ (pElementSubgroup 2 ((P.subgroupOf L).map mk)).map
      (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →* MulAut (↥L ⧸ Subgroup.center ↥L)) :=
    fun h => hnotinn (Subgroup.map_le_range _ _ h)
  have key := critModel hmodel hZb h1 h2 hp hp2 T hmin hl hl1 hlp cb hcbord hcT hcInn
  set R : Subgroup Y := pElementSubgroup 2 P with hR
  have hRL : R ≤ L := (pElementSubgroup_le P).trans hP.1
  set J : Subgroup Y := R ⊔ Subgroup.zpowers r with hJ
  have hJN : J ≤ N := sup_le (hRL.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.2 hrL)
  set φ : ↥J →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
    (actQ L).comp (Subgroup.inclusion hJN) with hφ
  have hRe : R = (pElementSubgroup 2 (P.subgroupOf L)).map L.subtype := by
    rw [hR, ← CFSG.AGLEmbeddingD2.Tits.GN516.pElementSubgroup_map_injective L.subtype
      L.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hP.1]
  have hrange : (pElementSubgroup 2 ((P.subgroupOf L).map mk)).map
      (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →* MulAut (↥L ⧸ Subgroup.center ↥L)) ⊔
        Subgroup.zpowers cb ≤ φ.range := by
    refine sup_le ?_ ?_
    · rintro _ ⟨yb, hyb, rfl⟩
      rw [← CFSG.AGLEmbeddingD2.Tits.GN516.map_pElementSubgroup_two] at hyb
      obtain ⟨x', hx', rfl⟩ := hyb
      have hxR : (x' : Y) ∈ R := by
        rw [hRe]
        exact ⟨x', hx', rfl⟩
      exact ⟨⟨(x' : Y), Subgroup.mem_sup_left hxR⟩, actQ_of_mem L x'⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨r, Subgroup.mem_sup_right (Subgroup.mem_zpowers r)⟩, rfl⟩
  have h3 : 2 ≤ CFSG.Open.pRank p ((⊤ : Subgroup ↥J).map φ) := by
    rw [← MonoidHom.range_eq_map]
    exact key.trans (CFSG.SectionRank.pRank_mono hp.one_lt hrange)
  have h4 := CFSG.LocalAnalysis.RankThreeUC.S15.two_le_pRank_of_map φ hp hp2 ⊤ h3
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup J] at h4

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
