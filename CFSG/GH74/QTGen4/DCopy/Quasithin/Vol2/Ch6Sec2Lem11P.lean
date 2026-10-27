module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11P
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem11M

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem exists_data611_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h6210 : Stmt6_2_10_F4) (hG31 : Ch6G31O2)
    (h4 : (V ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)).relIndex V ≠ 2) :
    ∃ d u₁ z : G, Data611 G T M L V d u₁ z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm := h.normal_ch611_F4 h331 h432 h512 h614 h615
  have hcomm := h.commMod_ch611_F4 h331 h432 h512 h614 h615
  obtain ⟨-, htop, -⟩ := h.stage_g31_ch611_F4 h331 h432 h512 h614 h615 h6210 hG31 h4
  obtain ⟨hUsq, hUcomm, hU16, hCUV, hCU, -⟩ :=
    h.stage_e_ch611_F4 h331 h432 h512 h614 h615 h6210 hG31 h4
  obtain ⟨hVC, -, hVUc, hCQ⟩ := h.step_a_ch611_F4 h331 h432 h512 h614 h615 h6210 h4
  obtain ⟨hMV, hUTL, -, ⟨d, hdL, hd3, hdZ, -, hdU, hdV, -, hdUZ⟩, ⟨u₁, hu₁U, hu₁Z, hu₁T⟩⟩ :=
    h.stage_g_ch611_F4 h331 h432 h512 h614 h615 h6210 hG31 h4
  have hRV := h.pCore_eq_ch611_F4 h331 h432 h512 h614 h615 h6210 hG31 h4
  set Z := zCh611 T with hZdef
  set H := hCh611 T with hHdef
  set U := uCh611 T L V with hUdef
  set ZS := ch6ZS T L V with hZSdef
  have hZ2 : Nat.card Z = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hZZS : Z ≤ ZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  have hZSU : ZS ≤ U := le_conjClosure _ _
  have hTH : T ≤ H := T_le_hCh611 T
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := hCh611_le_normalizer_u T L V
  refine ⟨d, u₁, z, ⟨h, hUcomm, hUsq, hU16, hCUV, ?_, ?_, ?_, ?_, hMV,
    (stmt6_2_1_F4 h432 G T M L V h).1.trans (stmt6_2_1_F4 h432 G T M L V h).2, ?_, ?_, hdL, hd3, hdU,
    hdV, hdUZ, hdZ, hu₁U, hu₁Z, hu₁T, hzZ, hz1, hZ2, hZZS, ?_⟩⟩
  ·
    intro x hxH hx
    exact hCU (mem_centralizerMod.mpr ⟨hxH, hCh611_le_normalizer_z T hxH, hx⟩)
  ·
    intro x hxH hxU
    have hxC : x ∈ centralizerMod Z H U := by
      refine mem_centralizerMod.mpr ⟨hxH, hCh611_le_normalizer_z T hxH, fun u hu => ?_⟩
      rw [← Subgroup.mem_centralizer_iff.mp hxU u hu, mul_inv_cancel_right, mul_inv_cancel]
      exact Z.one_mem
    rw [show centralizerMod Z H U = pCoreOf 2 H from hCQ] at hxC
    exact hxC
  ·
    intro v hv u hu
    have := hVUc (Subgroup.commutator_mem_commutator hv hu)
    rwa [commutatorElement_def] at this
  ·
    intro v hv hvU
    have hvC : v ∈ V ⊓ centralizerMod Z H U := by
      refine ⟨hv, mem_centralizerMod.mpr ⟨h.V_le_hCh611 hv,
        hCh611_le_normalizer_z T (h.V_le_hCh611 hv), fun u hu => ?_⟩⟩
      rw [← Subgroup.mem_centralizer_iff.mp hvU u hu, mul_inv_cancel_right, mul_inv_cancel]
      exact Z.one_mem
    rw [show V ⊓ centralizerMod Z H U = ZS from hVC] at hvC
    exact hvC
  ·
    intro t ht htU
    have htZ : t ∈ Subgroup.centralizer (ZS : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun x hx => Subgroup.mem_centralizer_iff.mp htU x (hZSU hx)
    obtain ⟨t', ht', hr⟩ := h.exists_mem_TL_ch611_F4 h331 h432 h512 h614 h615 ht htZ
    have hrV : t'⁻¹ * t ∈ V := by
      rw [← hRV]
      exact ⟨T.mul_mem (T.inv_mem ht'.1) ht, hr⟩
    have hVL : V ≤ L := (h.pCoreOf_L_eq_ch611 hRV).1 ▸ pCoreOf_le 2 L
    have e : t = t' * (t'⁻¹ * t) := by group
    rw [e]
    exact L.mul_mem ht'.2 (hVL hrV)
  ·
    intro hTL
    have h8 := h.relIndex_Q_T_F4 h331 h615
    have h4' := h.relIndex_TL_ch611
    have e : T ⊓ L = T := inf_eq_left.mpr hTL
    rw [e] at h4'
    have e2 : (ch6Q T V).relIndex T = (Subgroup.centralizer (V : Set G)).relIndex T := by
      rw [show ch6Q T V = T ⊓ Subgroup.centralizer (V : Set G) from rfl,
        Subgroup.inf_relIndex_left]
    rw [e2, h4'] at h8
    norm_num at h8
  ·
    intro α hα
    have hmap : (Z.subgroupOf U).map (α : ↥U →* ↥U) = Z.subgroupOf U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : (y : G) ∈ Z := Subgroup.mem_subgroupOf.mp hy
        rw [Subgroup.mem_subgroupOf, show ((α : ↥U →* ↥U) y) = α y from rfl, hα y hy']
        exact hy'
      · intro hx
        refine ⟨x, hx, ?_⟩
        rw [show ((α : ↥U →* ↥U) x) = α x from rfl, hα x (Subgroup.mem_subgroupOf.mp hx)]
    set φ := QuotientGroup.congr (Z.subgroupOf U) (Z.subgroupOf U) α hmap with hφ
    obtain ⟨k, hk⟩ : φ ∈ (rhoCh611 T L V).range := htop ▸ Subgroup.mem_top φ
    refine ⟨k, k.2, fun u => ?_⟩
    have h1 : rhoCh611 T L V k (u : ↥U ⧸ Z.subgroupOf U) = φ (u : ↥U ⧸ Z.subgroupOf U) := by
      rw [hk]
    rw [show rhoCh611 T L V k (u : ↥U ⧸ Z.subgroupOf U) = _ from actQuot_mk k u, hφ,
      QuotientGroup.congr_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h1' : (k : G) * ((u : G)⁻¹ * (k : G)⁻¹) * (α u : G) ∈ zCh611 T := by simpa using h1
    have h2 := (zCh611 T).inv_mem h1'
    have e : ((k : G) * ((u : G)⁻¹ * (k : G)⁻¹) * (α u : G))⁻¹ =
        ((α u : G))⁻¹ * ((k : G) * u * (k : G)⁻¹) := by group
    rwa [e] at h2

end Hyp6Sec2

end CFSG.Quasithin.H13
