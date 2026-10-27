module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.L193Basic
public import CFSG.GH74.Uniqueness.SU.SU1BgNormalEp2
public import CFSG.GH74.Uniqueness.SU.SU1Graph

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.L193

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20
open scoped commutatorElement

section FactA

variable {G : Type} [Group G] [Finite G] {z t g : G} {p : ℕ}

omit [Finite G] in
theorem isPGroup_zpowers {p : ℕ} {x : G} (hx : x ^ p = 1) : IsPGroup p ↥(zpowers x) := by
  intro a
  refine ⟨1, ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  rfl

omit [Finite G] in
theorem pow_eq_one_of_elem {p : ℕ} {U : Subgroup G} (hU : IsElementaryAbelian p ↥U) {u : G} (hu : u ∈ U) : u ^ p = 1 := by
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hU.exponent_dvd_p ⟨u, hu⟩
  exact congrArg Subtype.val h

@[expose] def IsU (z : G) (p : ℕ) (U : Subgroup G) : Prop :=
  U ≤ Op p (Cen z) ∧ (U.subgroupOf (Op p (Cen z))).Normal ∧ IsElementaryAbelian p ↥U ∧ Nat.card ↥U = p ^ 2

omit [Finite G] in
theorem mem_Qof {p : ℕ} {M U : Subgroup G} {x : G} : x ∈ Qof p M U ↔ x ∈ Op p M ∧ ∀ u ∈ U, x * u = u * x := by
  unfold Qof
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun h u hu => (h u hu).symm, fun h u hu => (h u hu).symm⟩

theorem factA (h : Ab G z t g p) {U : Subgroup G} (hU : IsU z p U)
    {x : G} (hxP : x ∈ Op p (Cen z)) (hxU : ∀ u ∈ U, x * u = u * x) (hxt : t * x = x * t) (hxp : x ^ p = 1)
    (hx1 : x ≠ 1) : False := by
  have hpr : Fact p.Prime := ⟨h.prime⟩
  have hxM : x ∈ Cen z := Subgroup.map_subtype_le _ hxP
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxM
  have hXel : IsElementaryAbelian p ↥(zpowers x) := isElementaryAbelian_zpowers hxp
  have hXp : IsPGroup p ↥(zpowers x) := isPGroup_zpowers hxp
  have hXQ : zpowers x ≤ Qof p (Cen z) U := by
    rw [Subgroup.zpowers_le]
    exact mem_Qof.mpr ⟨hxP, hxU⟩
  have hXne : zpowers x ≠ ⊥ := fun hb => hx1 (by
    have : x ∈ zpowers x := Subgroup.mem_zpowers x
    rw [hb] at this
    exact Subgroup.mem_bot.mp this)
  have hNX : normalizer ((zpowers x : Subgroup G) : Set G) ≤ Cen z :=
    h.cons.nG U hU.1 hU.2.1 hU.2.2.1 hU.2.2.2 _ (hXQ.trans le_sup_left) hXne ⟨p, h.prime, hXel⟩
  have hxN : x ∈ conjugate (Cen z) g := by
    rw [← h.cen_t_eq]; exact Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm
  have hXN : zpowers x ≤ conjugate (Cen z) g := by rw [Subgroup.zpowers_le]; exact hxN
  have hDp : IsPGroup p ↥(Op p (conjugate (Cen z) g)) := isPGroup_Op p _
  have hDM : Op p (conjugate (Cen z) g) ≤ Cen z := by
    intro d hd
    have hzd := axb_helper (p := p) h.odd h.z2 h.z_ne_one hDp hXp
      (fun d hd => Op_norm p _ h.z_mem_N hd) (fun x' hx' d hd => Op_norm p _ (hXN hx') hd)
      (fun x' hx' => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
        exact ((Commute.zpow_left (show Commute x z from hxz) k).eq).symm)
      (fun d hd hdc => by
        have hdX : d ∈ normalizer ((zpowers x : Subgroup G) : Set G) :=
          Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x' hx' => (hdc x' hx').symm)
        have := Subgroup.mem_centralizer_singleton_iff.mp (hNX hdX)
        exact this.symm) d hd
    exact Subgroup.mem_centralizer_singleton_iff.mpr hzd.symm
  obtain ⟨T, hTM, hTp, hDT, hPT⟩ := exists_pgroup_ge (p := p) hDM hDp
  have hPnT : ((Op p (Cen z)).subgroupOf T).Normal := ⟨fun n hn g' => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Op_norm p _ (hTM g'.2) hn⟩
  have hrank : 2 ≤ pRank p ↥((Op p (Cen z)).subgroupOf T) := by
    have h3 : 3 ≤ Open.pRank p (Op p (Cen z)) := by
      have := h.rank
      rwa [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank h.prime] at this
    have h2 := rank_subgroupOf h.prime hPT (k := 2) (by omega)
    rwa [← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank h.prime] at h2
  rcases CFSG.GH74.Uniqueness.SU.SU1.b_normal_Ep2 p h.prime ↥T hTp _ hPnT hrank with
    ⟨E, hEn, hEQ, hEel, hEc⟩ | ⟨hp2, -⟩
  swap
  · exact h.odd hp2
  set U₁ : Subgroup G := E.map T.subtype with hU₁
  have hU₁P : U₁ ≤ Op p (Cen z) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hEQ he)
  have hU₁T : ∀ τ ∈ T, ∀ u ∈ U₁, τ * u * τ⁻¹ ∈ U₁ := by
    rintro τ hτ _ ⟨e, he, rfl⟩
    exact ⟨⟨τ, hτ⟩ * e * ⟨τ, hτ⟩⁻¹, hEn.conj_mem e he _, rfl⟩
  have hU₁n : (U₁.subgroupOf (Op p (Cen z))).Normal := ⟨fun n hn g' => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hU₁T g' (hPT g'.2) n hn⟩
  have hU₁el : IsElementaryAbelian p ↥U₁ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U₁).mpr
      (CFSG.SectionRank.isElemAbelian_map
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mp hEel) T.subtype)
  have hU₁c : Nat.card ↥U₁ = p ^ 2 := by
    rw [hU₁, Subgroup.card_map_of_injective T.subtype_injective, hEc]
  have hU₁comm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hU₁el.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVD : conjugate U₁ g ≤ Op p (conjugate (Cen z) g) := (conjugate_mono hU₁P g).trans (op_conjugate_le p (Cen z) g)
  have hVc : Nat.card ↥(conjugate U₁ g) = p ^ 2 := by rw [card_conjugate, hU₁c]
  have hVT : conjugate U₁ g ≤ T := hVD.trans hDT
  have hCv : ∀ v ∈ conjugate U₁ g, v ≠ 1 → ∀ c : G, c * v = v * c → c ∈ conjugate (Cen z) g := by
    intro v hv hv1 c hc
    rw [mem_conjugate_iff'] at hv
    have hu1 : g * v * g⁻¹ ≠ 1 := fun hu1 => hv1 (by
      have : v = g⁻¹ * (g * v * g⁻¹) * g := by group
      rw [this, hu1]; group)
    have hup : (g * v * g⁻¹) ^ p = 1 := pow_eq_one_of_elem hU₁el hv
    have hXQ' : zpowers (g * v * g⁻¹) ≤ Qof p (Cen z) U₁ := by
      rw [Subgroup.zpowers_le]
      exact mem_Qof.mpr ⟨hU₁P hv, fun w hw => hU₁comm _ hv w hw⟩
    have hNX' := h.cons.nG U₁ hU₁P hU₁n hU₁el hU₁c (zpowers (g * v * g⁻¹)) (hXQ'.trans le_sup_left)
      (fun hb => hu1 (by
        have : g * v * g⁻¹ ∈ zpowers (g * v * g⁻¹) := Subgroup.mem_zpowers _
        rw [hb] at this
        exact Subgroup.mem_bot.mp this)) ⟨p, h.prime, isElementaryAbelian_zpowers hup⟩
    rw [mem_conjugate_iff']
    apply hNX'
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcomm : Commute (g * c * g⁻¹) (g * v * g⁻¹) := by
      show (g * c * g⁻¹) * (g * v * g⁻¹) = (g * v * g⁻¹) * (g * c * g⁻¹)
      calc (g * c * g⁻¹) * (g * v * g⁻¹) = g * (c * v) * g⁻¹ := by group
        _ = g * (v * c) * g⁻¹ := by rw [hc]
        _ = (g * v * g⁻¹) * (g * c * g⁻¹) := by group
    exact ((hcomm.symm.zpow_left k).eq)
  have hNE : CFSG.GH74.Uniqueness.SU.SU1.IsNormalEp2 p T U₁ :=
    ⟨hU₁P.trans hPT, fun τ hτ => by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      refine ⟨fun hu => hU₁T τ hτ u hu, fun hu => ?_⟩
      have := hU₁T τ⁻¹ (T.inv_mem hτ) _ hu
      have e : τ⁻¹ * (τ * u * τ⁻¹) * τ⁻¹⁻¹ = u := by group
      rwa [e] at this,
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U₁).mp hU₁el, hU₁c⟩
  have hrel := (CFSG.GH74.Uniqueness.SU.SU1.ig10_20_ii h.prime hTp hNE).2.1
  obtain ⟨v, hvV, hv1, hvC⟩ : ∃ v ∈ conjugate U₁ g, v ≠ 1 ∧ ∀ u ∈ U₁, v * u = u * v := by
    by_contra hno
    push Not at hno
    have hK : centralizer (U₁ : Set G) ⊓ conjugate U₁ g = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      by_contra hv1
      have hv1' : v ≠ 1 := fun h1 => hv1 (by rw [h1]; exact Subgroup.one_mem _)
      obtain ⟨u, hu, hne⟩ := hno v hv.2 hv1'
      exact hne (Subgroup.mem_centralizer_iff.mp hv.1 u hu).symm
    have h1 : (centralizer (U₁ : Set G)).relIndex (conjugate U₁ g) = p ^ 2 := by
      rw [← Subgroup.inf_relIndex_right, hK, Subgroup.relIndex_bot_left, hVc]
    have h2 : (centralizer (U₁ : Set G)).relIndex (conjugate U₁ g) ≤ (centralizer (U₁ : Set G)).relIndex T := by
      have : (centralizer (U₁ : Set G)).IsFiniteRelIndex T := Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
      exact Subgroup.relIndex_le_of_le_right hVT Subgroup.relIndex_ne_zero
    have hp2 : p ^ 2 ≤ p := by omega
    have := h.prime.two_le
    nlinarith
  have hU₁N : U₁ ≤ conjugate (Cen z) g := fun u hu => hCv v hvV hv1 u (hvC u hu).symm
  have hZU : zpowers z ⊔ U₁ ≤ conjugate (Cen z) g :=
    sup_le (by rw [Subgroup.zpowers_le]; exact h.z_mem_N) hU₁N
  have hU₁Q : U₁ ≤ Qof p (Cen z) U₁ := fun u hu => mem_Qof.mpr ⟨hU₁P hu, fun w hw => hU₁comm u hu w hw⟩
  exact h.N_ne (h.cons.b U₁ hU₁P hU₁n hU₁el hU₁c g U₁ hU₁Q hU₁el (by rw [hU₁c]) hZU)

end FactA

end CFSG.GH74.GLS.Stage2.Final.Thm4.L193
