module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalH
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalT
public import CFSG.StronglyEmbedded.UniqueCosetBasic
public import CFSG.Milestones.SE_simple_strong_embedding_models
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate113
public import Certificates.Certificate43

public section

namespace CFSG.ComponentClassification.GrSLit.ONanBal

open Subgroup CFSG.OddStandard CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.F2
  CFSG.OddStandard.ONanRec.F2.AlpE CFSG.ABGLocalTools

theorem comm_tE_W : ∀ e ∈ WEL, e⁻¹ * (tE * e * tE⁻¹) = 1 ∨ e⁻¹ * (tE * e * tE⁻¹) = zc := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G}

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0

theorem comm_t_W (D : FusCtx G v1 v2 v3 s t) {w : G} (hw : w ∈ alpW v1 v2 v3) :
    w⁻¹ * (t * w * t⁻¹) ∈ zpowers 𝔷 := by
  obtain ⟨e, he, rfl⟩ := D.exists_phi_WEL hw
  have h := comm_tE_W e he
  have e1 : (D.E.φ e)⁻¹ * (t * D.E.φ e * t⁻¹) = D.E.φ (e⁻¹ * (tE * e * tE⁻¹)) := by
    simp only [map_mul, map_inv, D.phi_t]
  rw [e1]
  rcases h with h | h
  · rw [h, map_one]
    exact one_mem _
  · rw [h, ← D.z_eq]
    exact mem_zpowers _

theorem exists_conj_W_le_P (D : FusCtx G v1 v2 v3 s t) (hone : OneClass G) :
    ∃ g : G, (∀ w ∈ alpW v1 v2 v3, g * w * g⁻¹ ∈ alpP v1 v2 v3 s t) ∧
      ∃ a ∈ alpW v1 v2 v3, g * a * g⁻¹ ∉ alpW v1 v2 v3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  set Cx := centralizer ({𝔵} : Set G) with hCx
  have hWCx : ∀ {w : G}, w ∈ alpW v1 v2 v3 → w ∈ Cx := fun hw =>
    mem_centralizer_singleton_iff.2 (D.comm_V (D.W_le_V hw) D.x_mem_V)
  have hxP : zpowers 𝔵 ≤ alpP v1 v2 v3 s t := zpowers_le.2 D.xel_mem
  have hxV : zpowers 𝔵 ≤ alpV v1 v2 v3 := zpowers_le.2 D.x_mem_V
  obtain ⟨Q, hQ⟩ := D.isSylowOf_P0.exists_sylow_eq_subgroupOf
  have hPhat : IsSylowOf 2 (liftQ 𝔵 (alpP v1 v2 v3 s t)) ⊤ := by
    have h := CFSG.ComponentClassification.GHarris.isSylowOf_top
      (Q.mapSurjective (πQ_surjective 𝔵))
    rwa [Sylow.coe_mapSurjective, hQ, Subgroup.inf_subgroupOf_right] at h
  have hWP : liftQ 𝔵 (alpW v1 v2 v3) ≤ liftQ 𝔵 (alpP v1 v2 v3 s t) := liftQ_mono D.W_le_P
  have hwc : ∀ c : KQ 𝔵, (liftQ 𝔵 (alpW v1 v2 v3)).map (MulAut.conj c).toMonoidHom ≤
      liftQ 𝔵 (alpP v1 v2 v3 s t) → (liftQ 𝔵 (alpW v1 v2 v3)).map (MulAut.conj c).toMonoidHom =
        liftQ 𝔵 (alpW v1 v2 v3) := by
    intro c hc
    obtain ⟨k, rfl⟩ := πQ_surjective 𝔵 c
    have hconjQ : ∀ w : Cx, (MulAut.conj (πQ 𝔵 k)).toMonoidHom (πQ 𝔵 w) = πQ 𝔵 (k * w * k⁻¹) := by
      intro w
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    have hkP : ∀ w ∈ alpW v1 v2 v3, (k : G) * w * (k : G)⁻¹ ∈ alpP v1 v2 v3 s t := by
      intro w hw
      have h1 : πQ 𝔵 (k * ⟨w, hWCx hw⟩ * k⁻¹) ∈ liftQ 𝔵 (alpP v1 v2 v3 s t) := by
        rw [← hconjQ]
        exact hc ⟨_, πQ_mem_liftQ (k := ⟨w, hWCx hw⟩) hw, rfl⟩
      exact mem_of_πQ_mem_liftQ hxP h1
    have hkW := hcon k hkP
    apply eq_of_le_of_card_ge
    · rintro _ ⟨_, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := mem_liftQ_iff.1 hy
      rw [hconjQ]
      exact πQ_mem_liftQ (hkW w hw)
    · rw [card_map_of_injective (MulAut.conj _).injective]
  have hv1W : v1 ^ 2 ∈ alpW v1 v2 v3 := subset_closure (by simp)
  have htCx : t ∈ Cx := D.t_mem_Cx
  set a := πQ 𝔵 ⟨v1 ^ 2, hWCx hv1W⟩ with ha
  set b := πQ 𝔵 ⟨t, htCx⟩ with hb
  have haW : a ∈ liftQ 𝔵 (alpW v1 v2 v3) := πQ_mem_liftQ hv1W
  have hca : a ∈ centralizer (liftQ 𝔵 (alpW v1 v2 v3) : Set (KQ 𝔵)) := by
    rw [mem_centralizer_iff]
    intro e he
    obtain ⟨w, hw, rfl⟩ := mem_liftQ_iff.1 he
    rw [ha, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (D.comm_V (D.W_le_V hw) (D.W_le_V hv1W))
  have hcb : b ∈ centralizer (liftQ 𝔵 (alpW v1 v2 v3) : Set (KQ 𝔵)) := by
    rw [mem_centralizer_iff]
    intro e he
    obtain ⟨w, hw, rfl⟩ := mem_liftQ_iff.1 he
    rw [hb, ← map_mul, ← map_mul, πQ_eq_iff]
    have h1 := comm_t_W D hw
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 h1
    have htz : Commute t (𝔷 ^ m) := by
      refine Commute.zpow_right ?_ m
      exact (AlpEmb.centre_alpP D.E D.hF D.z_mem_P).2 (Or.inr rfl) t (AlpEmb.invRep_mem D.E 5)
    have e : ((w : G) * t)⁻¹ * (t * (w : G)) = 𝔷 ^ m := by
      calc ((w : G) * t)⁻¹ * (t * (w : G))
          = ((w : G) * t)⁻¹ * ((w : G) * ((w : G)⁻¹ * (t * w * t⁻¹)) * t) := by group
        _ = ((w : G) * t)⁻¹ * ((w : G) * 𝔷 ^ m * t) := by rw [← hm]
        _ = t⁻¹ * (𝔷 ^ m * t) := by group
        _ = t⁻¹ * (t * 𝔷 ^ m) := by rw [← htz.eq]
        _ = 𝔷 ^ m := by group
    show ((w : G) * t)⁻¹ * (t * (w : G)) ∈ zpowers 𝔵
    rw [e]
    have hz : 𝔷 ∈ zpowers 𝔵 := by
      rw [← D.xel_sq]
      exact mul_mem (mem_zpowers _) (mem_zpowers _)
    exact zpow_mem hz m
  have hao : orderOf a = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ha, ← map_mul, πQ_eq_one_iff]
      show v1 ^ 2 * v1 ^ 2 ∈ zpowers 𝔵
      rw [← pow_add, D.fr.v1_four]
      exact one_mem _
    · rw [ha, Ne, πQ_eq_one_iff]
      show v1 ^ 2 ∉ zpowers 𝔵
      have hv : v1 ^ 2 = D.E.φ (gen 0 ^ 2) := by rw [map_pow, AlpEmb.φ_v1]
      rw [hv]
      exact D.notMem_zpowers_x_of_phi v1sqE_notMem
  have htV : t ∉ alpV v1 v2 v3 := fun h =>
    absurd (D.le_two_of_invRep_mem_V (i := 5) h) (by decide)
  have hbo : orderOf b = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, hb, ← map_mul, πQ_eq_one_iff]
      show t * t ∈ zpowers 𝔵
      rw [← pow_two, D.fr.t_two]
      exact one_mem _
    · rw [hb, Ne, πQ_eq_one_iff]
      exact fun h => htV (hxV h)
  obtain ⟨c, hc⟩ := isConj_iff.1 (D.oneClass_quot hone a b hao hbo)
  obtain ⟨n, hn, hnab⟩ := fuseOfWeaklyClosed hPhat hWP hwc hca hcb ⟨c, hc⟩
  have hbW : b ∈ liftQ 𝔵 (alpW v1 v2 v3) := by
    rw [← hnab]
    have := (mem_normalizer_iff.1 (inv_mem hn) a).1 haW
    rwa [inv_inv] at this
  exact htV (mem_of_πQ_mem_liftQ hxV (liftQ_mono D.W_le_V hbW))

theorem mem_normalizer_tW_of_conj_le
    (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) {g : G}
    (hg : ∀ w ∈ alpW v1 v2 v3, g * w * g⁻¹ ∈ alpP v1 v2 v3 s t) :
    g ∈ normalizer (tW (alpW v1 v2 v3) : Set G) := by
  set T := tW (alpW v1 v2 v3) with hT
  set K := T.map (MulAut.conj g⁻¹).toMonoidHom with hK
  have hmemK : ∀ k : G, k ∈ K ↔ g * k * g⁻¹ ∈ T := by
    intro k
    constructor
    · rintro ⟨k₀, hk₀, rfl⟩
      have e : g * ((MulAut.conj g⁻¹).toMonoidHom k₀) * g⁻¹ = k₀ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hk₀
    · intro hk
      refine ⟨g * k * g⁻¹, hk, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hNT : ∀ {p : G}, p ∈ alpP v1 v2 v3 s t → p ∈ normalizer (T : Set G) := fun hp =>
    mem_normalizer_tW (D.P_le_normalizer_W hp)
  have hWK : alpW v1 v2 v3 ≤ normalizer (K : Set G) := by
    intro w hw
    rw [mem_normalizer_iff]
    intro k
    rw [hmemK, hmemK]
    have e : g * (w * k * w⁻¹) * g⁻¹ = (g * w * g⁻¹) * (g * k * g⁻¹) * (g * w * g⁻¹)⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.1 (hNT (hg w hw)) _
  have hKo : Odd (Nat.card K) := by
    rw [hK, card_map_of_injective (MulAut.conj _).injective]
    exact odd_card_tW D hF hone
  have hKT : K ≤ T := le_tW_of_le_normalizer D hF hone hKo hWK
  have heq : K = T := eq_of_le_of_card_ge hKT (by
    rw [hK, card_map_of_injective (MulAut.conj _).injective])
  have hginv : g⁻¹ ∈ normalizer (T : Set G) := (mem_normalizer_iff_map_conj_eq).2 heq
  simpa using inv_mem hginv

theorem centralizer_z_le (D : FusCtx G v1 v2 v3 s t) (hone : OneClass G) {H : Subgroup G}
    (hθ : theta 𝔷 ≤ H) (hx : centralizer ({𝔵} : Set G) ≤ H) (hst : s * t ∈ H) :
    centralizer ({𝔷} : Set G) ≤ H := by
  intro g hg
  obtain ⟨o, ho, hoc⟩ := exists_conj_x_mod_theta D hone hg
  have hoH : o ∈ H := hθ ho
  have e : g = o⁻¹ * (o * g) := by group
  rcases hoc with h | h
  · rw [e]
    exact mul_mem (inv_mem hoH) (hx (mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h)))
  · have h' : (o * g * (s * t)) * 𝔵 * (o * g * (s * t))⁻¹ = 𝔵 := by
      calc (o * g * (s * t)) * 𝔵 * (o * g * (s * t))⁻¹
          = (o * g) * (s * t * 𝔵 * (s * t)⁻¹) * (o * g)⁻¹ := by group
        _ = (o * g) * 𝔵⁻¹ * (o * g)⁻¹ := by rw [D.st_inv_x]
        _ = ((o * g) * 𝔵 * (o * g)⁻¹)⁻¹ := by group
        _ = 𝔵 := by rw [h, inv_inv]
    have hm := hx (mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h'))
    have e2 : g = o⁻¹ * (o * g * (s * t)) * (s * t)⁻¹ := by group
    rw [e2]
    exact mul_mem (mul_mem (inv_mem hoH) hm) (inv_mem hst)

theorem theta_z_eq_bot
    [IsSimpleGroup G] (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) :
    theta 𝔷 = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := tW (alpW v1 v2 v3) with hT
  have hzW : 𝔷 ∈ alpW v1 v2 v3 := sq_mul_sq_mem_alpW v1 v2 v3
  have hθT : theta 𝔷 ≤ T := theta_le_tW hzW (D.rep_ne_one 0)
  by_cases hT1 : T = ⊥
  · rw [hT1] at hθT
    exact le_bot_iff.1 hθT
  set H := normalizer (T : Set G) with hH
  have hTH : T ≤ H := le_normalizer
  have hWH : normalizer (alpW v1 v2 v3 : Set G) ≤ H := fun n hn => mem_normalizer_tW hn
  have hPH : alpP v1 v2 v3 s t ≤ H := D.P_le_normalizer_W.trans hWH
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hTn : T.Normal := normalizer_eq_top_iff.1 htop
    rcases hTn.eq_bot_or_eq_top with h | h
    · exact hT1 h
    · have hodd := odd_card_tW D hF hone
      rw [← hT, h, card_top] at hodd
      have h2 : 2 ∣ Nat.card G := D.orderOf_rep 0 ▸ orderOf_dvd_natCard 𝔷
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨g, hgP, a, haW, hgW⟩ := exists_conj_W_le_P D hone
  have hgH : g ∈ H := mem_normalizer_tW_of_conj_le D hF hone hgP
  obtain ⟨honeH, hCx⟩ := oneClass_and_centralizer_x_le D hF hone hWH
    ((theta_x_le_theta_z D hone).trans (hθT.trans hTH)) haW hgH (hgP a haW) hgW
  have hstH : s * t ∈ H := hPH (AlpEmb.invRep_mem D.E 4)
  have hCz := centralizer_z_le D hone (hθT.trans hTH) hCx hstH
  have hzH : 𝔷 ∈ H := hPH D.z_mem_P
  have hcent : ∀ u ∈ H, orderOf u = 2 → centralizer ({u} : Set G) ≤ H := by
    intro u hu hu2
    have hzo : orderOf (⟨𝔷, hzH⟩ : H) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact D.orderOf_rep 0
    have huo : orderOf (⟨u, hu⟩ : H) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hu2
    obtain ⟨k, hk⟩ := isConj_iff.1 (honeH ⟨𝔷, hzH⟩ ⟨u, hu⟩ hzo huo)
    have hk' : (k : G) * 𝔷 * (k : G)⁻¹ = u := congrArg Subtype.val hk
    intro c hc
    have hc' : (k : G)⁻¹ * c * k ∈ centralizer ({𝔷} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      rw [← hk'] at hc
      calc (k : G)⁻¹ * c * k * 𝔷 = (k : G)⁻¹ * (c * ((k : G) * 𝔷 * (k : G)⁻¹)) * k := by group
        _ = (k : G)⁻¹ * (((k : G) * 𝔷 * (k : G)⁻¹) * c) * k := by rw [hc]
        _ = 𝔷 * ((k : G)⁻¹ * c * k) := by group
    have e : c = k * ((k : G)⁻¹ * c * k) * (k : G)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem k.2 (hCz hc')) (inv_mem k.2)
  have hSE : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder H := by
    refine CFSG.StronglyEmbedded.UniqueCoset.isStronglyEmbeddedOrder_of_involutions hHtop hzH
      (D.orderOf_rep 0) ?_
    intro u hu hu2 c hcu
    have hcu2 : orderOf (c⁻¹ * u * c) = 2 := by
      rw [show c⁻¹ * u * c = MulAut.conj c⁻¹ u by simp, MulEquiv.orderOf_eq, hu2]
    have huo : orderOf (⟨u, hu⟩ : H) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hu2
    have hcuo : orderOf (⟨c⁻¹ * u * c, hcu⟩ : H) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hcu2
    obtain ⟨h, hh⟩ := isConj_iff.1 (honeH ⟨u, hu⟩ ⟨c⁻¹ * u * c, hcu⟩ huo hcuo)
    have hh' : (h : G) * u * (h : G)⁻¹ = c⁻¹ * u * c := congrArg Subtype.val hh
    have hch : c * h ∈ centralizer ({u} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c * h * u = c * ((h : G) * u * (h : G)⁻¹) * h := by group
        _ = c * (c⁻¹ * u * c) * h := by rw [hh']
        _ = u * (c * h) := by group
    have e : c = (c * h) * (h : G)⁻¹ := by group
    rw [e]
    exact mul_mem (hcent u hu hu2 hch) (inv_mem h.2)
  have hB := CFSG.Milestones.bender_suzuki H hSE
  have htP : t ∈ (D.P : Subgroup G) := by
    rw [D.hP]
    exact AlpEmb.invRep_mem D.E 5
  have hcomm := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hB D.P htP
    (by rw [← pow_two]; exact D.fr.t_two)
  have hcen : ∀ c ∈ alpP v1 v2 v3 s t, c * t = t * c := by
    intro c hc
    have hc' : c ∈ (D.P : Subgroup G) := by
      rw [D.hP]
      exact hc
    exact ((hcomm c hc').eq).symm
  rcases (AlpEmb.centre_alpP D.E D.hF (AlpEmb.invRep_mem D.E 5)).1 hcen with h | h
  · exact absurd h (D.rep_ne_one 5)
  · exfalso
    have hzV : v1 ^ 2 * v3 ^ 2 ∈ alpV v1 v2 v3 := D.rep_mem_V (i := 0) (by decide)
    have htV : invRep v1 v2 v3 s t 5 ∈ alpV v1 v2 v3 := by
      have e : invRep v1 v2 v3 s t 5 = v1 ^ 2 * v3 ^ 2 := h
      rw [e]
      exact hzV
    exact absurd (D.le_two_of_invRep_mem_V htV) (by decide)

end CFSG.ComponentClassification.GrSLit.ONanBal
