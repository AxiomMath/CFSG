module

public import CFSG.GH74.GLS.C3.Layer1.P34RealCtx
public import CFSG.GH74.GLS.C3.Layer1.P34RealAut

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.P34Real
open scoped commutatorElement

variable {G : Type} [Group G] {K : Subgroup G}

structure Base89 (u : G) (K T : Subgroup G) : Prop where
  KC : K ≤ centralizer ({u} : Set G)
  KN : ∀ c ∈ centralizer ({u} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  cen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))
  sylowT : IsSylowOf 2 T (centralizer ({u} : Set G))
  sylowP : IsSylowOf 2 (T ⊓ K) K
  u_mem : u ∈ T

@[expose] def Qs (u : G) (K T : Subgroup G) : Subgroup G := T ⊓ CxK u K

theorem Qs_le_T {u : G} {K T : Subgroup G} : Qs u K T ≤ T := inf_le_left

namespace Base89

variable {u : G} {T : Subgroup G} (H : Base89 u K T)

include H in
theorem T_le_C : T ≤ centralizer ({u} : Set G) := H.sylowT.le

include H in
theorem P_le_C : T ⊓ K ≤ centralizer ({u} : Set G) := inf_le_right.trans H.KC

include H in
theorem T_inf_pPrimeCoreOf [Finite G] : T ⊓ pPrimeCoreOf 2 K = ⊥ :=
  Back.Setup91.inf_pPrimeCoreOf_eq_bot K H.sylowT.isPGroup

include H in
theorem act_inj_P [Finite G] {p₁ p₂ : G} (h₁ : p₁ ∈ T ⊓ K) (h₂ : p₂ ∈ T ⊓ K)
    (h : act H.KN p₁ = act H.KN p₂) : p₁ = p₂ := by
  have hO := eq_of_act_eq_of_mem_K H.KN H.KC H.cen h₁.2 h₂.2 h
  have hT : p₁⁻¹ * p₂ ∈ T ⊓ pPrimeCoreOf 2 K := ⟨T.mul_mem (T.inv_mem h₁.1) h₂.1, hO⟩
  rw [H.T_inf_pPrimeCoreOf, Subgroup.mem_bot] at hT
  exact inv_mul_eq_one.1 hT

include H in
theorem mem_Qs {q : G} : q ∈ Qs u K T ↔ q ∈ T ∧ act H.KN q = 1 := by
  constructor
  · rintro ⟨hqT, hq⟩
    exact ⟨hqT, (act_eq_one_iff H.KN (H.T_le_C hqT)).2 hq⟩
  · rintro ⟨hqT, hq⟩
    exact ⟨hqT, (act_eq_one_iff H.KN (H.T_le_C hqT)).1 hq⟩

include H in
theorem P_comm_Qs [Finite G] {p q : G} (hp : p ∈ T ⊓ K) (hq : q ∈ Qs u K T) : p * q = q * p := by
  have hqT : q ∈ T := ((H.mem_Qs).1 hq).1
  have hcomm := (U1a.mem_CMK_iff.1 (hq.2)).2.2.2 p hp.2
  have h1 : ⁅p, q⁆ ∈ T ⊓ pPrimeCoreOf 2 K := by
    refine ⟨?_, hcomm⟩
    have : ⁅p, q⁆ = p * (q * p⁻¹ * q⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact T.mul_mem hp.1 (T.mul_mem (T.mul_mem hqT (T.inv_mem hp.1)) (T.inv_mem hqT))
  rw [H.T_inf_pPrimeCoreOf, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

@[expose] noncomputable def B : Subgroup (MulAut (kBar K)) :=
  (T.subgroupOf (centralizer ({u} : Set G))).map (Back.actHom H.KN)

include H in
theorem mem_B {v : MulAut (kBar K)} : v ∈ H.B ↔ ∃ t ∈ T, act H.KN t = v := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨(m : G), hm, ?_⟩
    rw [act_of_mem H.KN m.2]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, H.T_le_C ht⟩, ht, ?_⟩
    rw [act_of_mem H.KN (H.T_le_C ht)]

include H in
theorem B_isPGroup : IsPGroup 2 ↥H.B := by
  have hT2 : IsPGroup 2 ↥(T.subgroupOf (centralizer ({u} : Set G))) :=
    H.sylowT.isPGroup.comap_subtype
  exact hT2.of_surjective ((Back.actHom H.KN).subgroupMap _)
    ((Back.actHom H.KN).subgroupMap_surjective _)

include H in
theorem B_inf_inn [Finite G] :
    H.B ⊓ innAut (kBar K) = ((T ⊓ K).subgroupOf (centralizer ({u} : Set G))).map
      (Back.actHom H.KN) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC := H.T_le_C
  have hPC := H.P_le_C
  have hSylK : IsSylowOf 2 ((T ⊓ K).subgroupOf (centralizer ({u} : Set G)))
      (K.subgroupOf (centralizer ({u} : Set G))) := by
    rw [← isSylowOf_map_subtype_iff (centralizer ({u} : Set G)),
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC,
      inf_eq_left.2 H.KC]
    exact H.sylowP
  have hSyl : IsSylowOf 2 (((T ⊓ K).subgroupOf (centralizer ({u} : Set G))).map
      (Back.actHom H.KN)) (innAut (kBar K)) := by
    have := isSylowOf_map_hom (Back.actHom H.KN) hSylK
    rwa [map_actHom_K H.KC H.KN] at this
  have hPT : (T ⊓ K).subgroupOf (centralizer ({u} : Set G)) ≤
      T.subgroupOf (centralizer ({u} : Set G)) := fun a ha =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 ha).1
  have hPB : ((T ⊓ K).subgroupOf (centralizer ({u} : Set G))).map (Back.actHom H.KN) ≤
      H.B ⊓ innAut (kBar K) := le_inf (Subgroup.map_mono hPT) hSyl.le
  exact hSyl.eq_of_le hPB inf_le_right H.B_isPGroup.to_inf_left

include H in
theorem mem_B_inf_inn [Finite G] {v : MulAut (kBar K)} :
    v ∈ H.B ⊓ innAut (kBar K) ↔ ∃ p ∈ T ⊓ K, act H.KN p = v := by
  rw [H.B_inf_inn]
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨(m : G), hm, ?_⟩
    rw [act_of_mem H.KN m.2]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, H.P_le_C hp⟩, hp, ?_⟩
    rw [act_of_mem H.KN (H.P_le_C hp)]

include H in
theorem sylow_Pbar [Finite G] : IsSylowOf 2 (H.B ⊓ innAut (kBar K)) (innAut (kBar K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSylK : IsSylowOf 2 ((T ⊓ K).subgroupOf (centralizer ({u} : Set G)))
      (K.subgroupOf (centralizer ({u} : Set G))) := by
    rw [← isSylowOf_map_subtype_iff (centralizer ({u} : Set G)),
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 H.P_le_C, inf_eq_left.2 H.KC]
    exact H.sylowP
  rw [H.B_inf_inn]
  have := isSylowOf_map_hom (Back.actHom H.KN) hSylK
  rwa [map_actHom_K H.KC H.KN] at this

include H in
theorem fiber_mem_Qs {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) (h : act H.KN t = act H.KN t') :
    t'⁻¹ * t ∈ Qs u K T := by
  refine (H.mem_Qs).2 ⟨T.mul_mem (T.inv_mem ht') ht, ?_⟩
  rw [act_mul H.KN (Subgroup.inv_mem _ (H.T_le_C ht')) (H.T_le_C ht), act_inv H.KN (H.T_le_C ht'), h]
  group

include H in
theorem act_Qs {q : G} (hq : q ∈ Qs u K T) : act H.KN q = 1 := ((H.mem_Qs).1 hq).2

include H in
theorem act_u : act H.KN u = 1 := by
  have huC : u ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 rfl
  rw [act_of_mem H.KN huC]
  refine (Back.actHom_eq_one_iff_commutator_mem H.KN ⟨u, huC⟩).2 (fun k hk => ?_)
  have huk : k * u = u * k := mem_centralizer_singleton_iff.1 (H.KC hk)
  have : ⁅k, u⁆ = 1 := by
    rw [commutatorElement_def, huk]
    group
  rw [this]
  exact (pPrimeCoreOf 2 K).one_mem

include H in
theorem u_mem_Qs : u ∈ Qs u K T := (H.mem_Qs).2 ⟨H.u_mem, H.act_u⟩

include H in
theorem Qs_norm {t a : G} (ht : t ∈ T) (ha : a ∈ Qs u K T) : t * a * t⁻¹ ∈ Qs u K T := by
  have haT := (H.mem_Qs).1 ha
  refine (H.mem_Qs).2 ⟨T.mul_mem (T.mul_mem ht haT.1) (T.inv_mem ht), ?_⟩
  rw [act_conj H.KN (H.T_le_C ht) (H.T_le_C haT.1), haT.2]
  group

end Base89

end CFSG.GH74.GLS.C3.Layer1.P89
