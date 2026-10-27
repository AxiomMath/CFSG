module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11M
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem11L

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem stage_g_ch611_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h6210 : Stmt6_2_10_F4) (hG31 : Ch6G31O2)
    (h4 : (V ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)).relIndex V ≠ 2) :
    M ≤ Subgroup.normalizer (V : Set G) ∧
    uCh611 T L V ≤ T ⊓ L ∧
    (∀ t ∈ T ⊓ L, ∃ u ∈ uCh611 T L V, ∃ v ∈ V, t = u * v) ∧
    (∃ d ∈ L, d ^ 3 = 1 ∧ d ∈ Subgroup.normalizer (ch6ZS T L V : Set G) ∧
      d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
      d ∈ Subgroup.normalizer (uCh611 T L V : Set G) ∧
      (∀ x ∈ V, d * x * d⁻¹ = x → x = 1) ∧
      (∀ v ∈ V, d * v * d⁻¹ * v⁻¹ ∈ ch6ZS T L V → v ∈ ch6ZS T L V) ∧
      (∀ u ∈ uCh611 T L V, d * u * d⁻¹ * u⁻¹ ∈ ch6ZS T L V → u ∈ ch6ZS T L V)) ∧
    (∃ u₁ ∈ uCh611 T L V, u₁ ∉ ch6ZS T L V ∧
      ∀ t ∈ T, t * u₁ * t⁻¹ * u₁⁻¹ ∈ ch6ZS T L V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRV := h.pCore_eq_ch611_F4 h331 h432 h512 h614 h615 h6210 hG31 h4
  obtain ⟨hOL, hMV⟩ := h.pCoreOf_L_eq_ch611 hRV
  obtain ⟨hUsq, hUcomm, hU16, hCUV, -, -⟩ :=
    h.stage_e_ch611_F4 h331 h432 h512 h614 h615 h6210 hG31 h4
  have hTLUR := h.TL_sub_UR_ch611_F4 h331 h432 h512 h614 h615 h6210 hG31 h4
  set U := uCh611 T L V with hUdef
  set ZS := ch6ZS T L V with hZSdef
  have hV := h.toHyp611.isElemAbelian
  have hZSU : ZS ≤ U := le_conjClosure _ _
  have hZSV : ZS ≤ V := inf_le_left
  have hUT : U ≤ T := h.uCh611_le_T_F4 h331 h432 h512 h614 h615
  have hVL : V ≤ L := hOL ▸ pCoreOf_le 2 L
  have hVTL : V ≤ T ⊓ L := le_inf h.toHyp611.le_T hVL

  have hUTL : U ≤ T ⊓ L := by
    intro u hu
    have huZ : u ∈ Subgroup.centralizer (ZS : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => hUcomm z (hZSU hz) u hu
    obtain ⟨t', ht', hr⟩ := h.exists_mem_TL_ch611_F4 h331 h432 h512 h614 h615 (hUT hu) huZ
    have hrV : t'⁻¹ * u ∈ V := by
      rw [← hRV]
      exact ⟨T.mul_mem (T.inv_mem ht'.1) (hUT hu), hr⟩
    have e : u = t' * (t'⁻¹ * u) := by group
    rw [e]
    exact (T ⊓ L).mul_mem ht' (hVTL hrV)
  have hTLUV : ∀ t ∈ T ⊓ L, ∃ u ∈ U, ∃ v ∈ V, t = u * v := by
    intro t ht
    obtain ⟨u, hu, r, hr, rfl⟩ := hTLUR t ht
    exact ⟨u, hu, r, hRV ▸ hr, rfl⟩

  have hinv : ∀ t ∈ T ⊓ L, t ^ 2 = 1 → t ∈ V ∨ t ∈ U := by
    intro t ht ht2
    obtain ⟨u, hu, v, hv, rfl⟩ := hTLUV t ht
    have hu2 := hUsq u hu
    have hv2 := hV.2 v hv
    have hcomm : u * v = v * u := by
      have h1 : u * v * (u * v) = 1 := by rw [← pow_two]; exact ht2
      have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu2)
      have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv2)
      calc u * v = u * v * (u * v) * (v⁻¹ * u⁻¹) := by group
        _ = v * u := by rw [h1, one_mul, hui, hvi]
    by_cases huC : u ∈ Subgroup.centralizer (V : Set G)
    · left
      have huZ : u ∈ U ⊓ Subgroup.centralizer (V : Set G) := ⟨hu, huC⟩
      rw [hCUV] at huZ
      exact V.mul_mem (hZSV huZ) hv
    · right
      exact U.mul_mem hu (hZSU (h.mem_ZS_of_comm_ch611 (hUTL hu) huC hv hcomm))

  obtain ⟨d, hdL, hd3, hdZ, hdTL, hdV, hdVZ, hdT⟩ := h.exists_diag_ch611
  have hdN : d ∈ Subgroup.normalizer (U : Set G) := by
    set K := U.map (MulAut.conj d).toMonoidHom with hK
    have hKU : ∀ k ∈ K, k ∈ V ∨ k ∈ U := by
      rintro k ⟨u, hu, rfl⟩
      have hk : (MulAut.conj d).toMonoidHom u = d * u * d⁻¹ := rfl
      rw [hk]
      refine hinv _ ((Subgroup.mem_normalizer_iff.mp hdTL u).mp (hUTL hu)) ?_
      rw [conj_pow, hUsq u hu, mul_one, mul_inv_cancel]
    have hcK : Nat.card K = 16 := by
      rw [hK, Subgroup.card_map_of_injective (MulAut.conj d).injective, hU16]
    rcases le_or_le_of_subset_union_ch611 hKU with hKV | hKU'
    · exfalso
      have hKeq : K = V := Subgroup.eq_of_le_of_card_ge hKV
        (by rw [hcK, h.natural.card_eq]; norm_num)
      have hUV : U ≤ V := by
        intro u hu
        have h1 : d * u * d⁻¹ ∈ V := hKeq ▸ (⟨u, hu, rfl⟩ : d * u * d⁻¹ ∈ K)
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _
          (h.data.le_normalizer hdL)) _).mp h1
        simpa [mul_assoc] using this
      have h1 : U ⊓ Subgroup.centralizer (V : Set G) = U := inf_eq_left.mpr fun u hu =>
        Subgroup.mem_centralizer_iff.mpr fun w hw =>
          B2F.isElemAbelian_comm hV hw (hUV hu)
      rw [hCUV] at h1
      have : Nat.card ↥ZS = Nat.card ↥U := by rw [h1]
      rw [h.toHyp611Nat.card_ZS, hU16] at this
      norm_num at this
    · have hKeq : K = U := Subgroup.eq_of_le_of_card_ge hKU' (by rw [hcK, hU16])
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hKU' ⟨x, hx, rfl⟩
      · intro hx
        rw [← hKeq] at hx
        obtain ⟨u, hu, hux⟩ := hx
        have : u = x := by
          have := congrArg (fun y => d⁻¹ * y * d) hux
          simpa [mul_assoc] using this
        rwa [← this]
  have hdU : ∀ u ∈ U, d * u * d⁻¹ * u⁻¹ ∈ ZS → u ∈ ZS := by
    intro u hu hdu
    have huC : u ∈ Subgroup.centralizer (V : Set G) :=
      hdT u (hUTL hu) (Subgroup.mem_centralizer_iff.mpr fun w hw =>
        B2F.isElemAbelian_comm hV hw (hZSV hdu))
    have huZ : u ∈ U ⊓ Subgroup.centralizer (V : Set G) := ⟨hu, huC⟩
    rw [hCUV] at huZ
    exact huZ

  have hu₁ : ∃ u₁ ∈ U, u₁ ∉ ZS ∧ ∀ t ∈ T, t * u₁ * t⁻¹ * u₁⁻¹ ∈ ZS := by
    have hZSn : (ZS.subgroupOf U).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hUcomm _ g.2 _ (hZSU hx), mul_inv_cancel_right]
      exact hx⟩
    have hTU : T ≤ Subgroup.normalizer (U : Set G) := fun t ht =>
      hCh611_le_normalizer_u T L V (T_le_hCh611 T ht)
    have hTZ : T ≤ Subgroup.normalizer (ZS : Set G) := h.toHyp611Nat.T_le_normalizer_ZS
    let ρS := actQuot U ZS T hTU hTZ
    let _ : MulAction ↥T (↥U ⧸ ZS.subgroupOf U) := MulAction.compHom _ ρS
    have hT2 : IsPGroup 2 ↥T := h.sylow.1
    have hmod := hT2.card_modEq_card_fixedPoints (↥U ⧸ ZS.subgroupOf U)
    have hcard : Nat.card (↥U ⧸ ZS.subgroupOf U) = 4 := by
      have h1 := Subgroup.card_mul_index (ZS.subgroupOf U)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZSU).toEquiv, h.toHyp611Nat.card_ZS,
        hU16] at h1
      rw [← Subgroup.index_eq_card]
      norm_num at h1
      omega
    rw [hcard] at hmod
    have h1fix : (1 : ↥U ⧸ ZS.subgroupOf U) ∈ MulAction.fixedPoints ↥T (↥U ⧸ ZS.subgroupOf U) :=
      fun t => map_one (ρS t)
    obtain ⟨x, hxfix, hx1⟩ : ∃ x ∈ MulAction.fixedPoints ↥T (↥U ⧸ ZS.subgroupOf U), x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsub : MulAction.fixedPoints ↥T (↥U ⧸ ZS.subgroupOf U) = {1} := by
        ext y
        exact ⟨fun hy => hcon y hy, fun hy => hy ▸ h1fix⟩
      have : Nat.card (MulAction.fixedPoints ↥T (↥U ⧸ ZS.subgroupOf U)) = 1 := by
        rw [hsub, Nat.card_unique]
      rw [this] at hmod
      exact absurd hmod (by decide)
    induction x using QuotientGroup.induction_on with
    | H u =>
      refine ⟨u, u.2, fun huZ => hx1 ?_, fun t ht => ?_⟩
      · rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact huZ
      · have := hxfix ⟨t, ht⟩
        exact (actQuot_mk_eq_iff (hKU := hTU) (hKZ := hTZ) ⟨t, ht⟩ u).mp this
  exact ⟨hMV, hUTL, hTLUV, ⟨d, hdL, hd3, hdZ, hdTL, hdN, hdV, hdVZ, hdU⟩, hu₁⟩

end Hyp6Sec2

end CFSG.Quasithin.H13
