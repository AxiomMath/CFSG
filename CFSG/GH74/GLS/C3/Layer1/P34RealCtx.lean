module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Transport

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] {C K : Subgroup G}

open Classical in
@[expose] noncomputable def act (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (g : G) :
    MulAut (kBar K) :=
  if h : g ∈ C then Back.actHom hKN ⟨g, h⟩ else 1

section Act

variable (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)

theorem act_of_mem {g : G} (hg : g ∈ C) : act hKN g = Back.actHom hKN ⟨g, hg⟩ := by
  simp [act, hg]

theorem act_one : act hKN (1 : G) = 1 := by
  rw [act_of_mem hKN C.one_mem]
  exact map_one _

theorem act_mul {g h : G} (hg : g ∈ C) (hh : h ∈ C) : act hKN (g * h) = act hKN g * act hKN h := by
  rw [act_of_mem hKN (C.mul_mem hg hh), act_of_mem hKN hg, act_of_mem hKN hh,
    ← (Back.actHom hKN).map_mul]
  rfl

theorem act_inv {g : G} (hg : g ∈ C) : act hKN g⁻¹ = (act hKN g)⁻¹ := by
  rw [act_of_mem hKN (C.inv_mem hg), act_of_mem hKN hg, ← map_inv]
  rfl

theorem act_conj {c g : G} (hc : c ∈ C) (hg : g ∈ C) :
    act hKN (c * g * c⁻¹) = act hKN c * act hKN g * (act hKN c)⁻¹ := by
  rw [act_mul hKN (C.mul_mem hc hg) (C.inv_mem hc), act_mul hKN hc hg, act_inv hKN hc]

theorem act_zpow {g : G} (hg : g ∈ C) (n : ℤ) : act hKN (g ^ n) = (act hKN g) ^ n := by
  rw [act_of_mem hKN (Subgroup.zpow_mem _ hg n), act_of_mem hKN hg, ← map_zpow]
  rfl

theorem act_of_mem_K (hKC : K ≤ C) {k : G} (hk : k ∈ K) :
    act hKN k = MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) := by
  rw [act_of_mem hKN (hKC hk)]
  exact Back.actHom_of_mem hKN hk (hKC hk)

theorem act_eq_one_iff {g : G} (hg : g ∈ C) : act hKN g = 1 ↔ g ∈ CMK C K := by
  rw [act_of_mem hKN hg]
  have h := Subgroup.ext_iff.1 (Back.actHom_ker hKN) ⟨g, hg⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] at h
  exact h

theorem act_mem_inn (hKC : K ≤ C) {k : G} (hk : k ∈ K) : act hKN k ∈ innAut (kBar K) := by
  rw [act_of_mem_K hKN hKC hk]
  exact ⟨_, rfl⟩

theorem eq_of_act_eq_of_mem_K (hKC : K ≤ C)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))) {k₁ k₂ : G} (h₁ : k₁ ∈ K)
    (h₂ : k₂ ∈ K) (h : act hKN k₁ = act hKN k₂) :
    k₁⁻¹ * k₂ ∈ pPrimeCoreOf 2 K := by
  rw [act_of_mem_K hKN hKC h₁, act_of_mem_K hKN hKC h₂] at h
  have h3 := hcen h
  have h4 : (⟨k₁, h₁⟩ : ↥K)⁻¹ * ⟨k₂, h₂⟩ ∈ pPrimeCore 2 ↥K := by
    rw [← QuotientGroup.eq]
    exact h3
  exact Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨K.mul_mem (K.inv_mem h₁) h₂, h4⟩

end Act

theorem CMK_conj (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) {g n : G} (hg : g ∈ C)
    (hn : n ∈ CMK C K) : g * n * g⁻¹ ∈ CMK C K := by
  have hnC : n ∈ C := hn.1
  rw [← act_eq_one_iff hKN (C.mul_mem (C.mul_mem hg hnC) (C.inv_mem hg)),
    act_conj hKN hg hnC, (act_eq_one_iff hKN hnC).2 hn]
  group

structure Real34 (x : G) (K T : Subgroup G) (f : G) : Prop where
  KC : K ≤ centralizer ({x} : Set G)
  KN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  cen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))
  sylowT : IsSylowOf 2 T (centralizer ({x} : Set G))
  sylowP : IsSylowOf 2 (T ⊓ K) K
  x_mem : x ∈ T
  f_mem : f ∈ T
  f_order : orderOf f = 2
  f_cent : ∀ p ∈ T ⊓ K, f * p = p * f
  f_fa : P34.IsFAutL2A7 (kBar K) (act KN f)

namespace Real34

variable {x : G} {T : Subgroup G} {f : G} (H : Real34 x K T f)

include H in
theorem T_le_C : T ≤ centralizer ({x} : Set G) := H.sylowT.le

include H in
theorem P_le_C : T ⊓ K ≤ centralizer ({x} : Set G) := inf_le_right.trans H.KC

include H in
theorem T_inf_pPrimeCoreOf [Finite G] : T ⊓ pPrimeCoreOf 2 K = ⊥ :=
  Back.Setup91.inf_pPrimeCoreOf_eq_bot K H.sylowT.isPGroup

include H in
theorem f_sq : f * f = 1 := by
  have := pow_orderOf_eq_one f
  rwa [H.f_order, sq] at this

include H in
theorem act_f_ne_one : act H.KN f ≠ 1 := H.f_fa.1

include H in
theorem act_f_order : orderOf (act H.KN f) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfC : f ∈ centralizer ({x} : Set G) := H.T_le_C H.f_mem
  refine orderOf_eq_prime ?_ H.act_f_ne_one
  rw [sq, ← act_mul H.KN hfC hfC, H.f_sq, act_one]

include H in
theorem act_f_not_inn [Finite G] : act H.KN f ∉ innAut (kBar K) := not_mem_innAut_of_isFAutL2A7 H.f_fa

include H in
theorem act_inj_P [Finite G] {p₁ p₂ : G} (h₁ : p₁ ∈ T ⊓ K) (h₂ : p₂ ∈ T ⊓ K)
    (h : act H.KN p₁ = act H.KN p₂) : p₁ = p₂ := by
  have hO := eq_of_act_eq_of_mem_K H.KN H.KC H.cen h₁.2 h₂.2 h
  have hT : p₁⁻¹ * p₂ ∈ T ⊓ pPrimeCoreOf 2 K := ⟨T.mul_mem (T.inv_mem h₁.1) h₂.1, hO⟩
  rw [H.T_inf_pPrimeCoreOf, Subgroup.mem_bot] at hT
  exact inv_mul_eq_one.1 hT

@[expose] def Q (_ : Real34 x K T f) : Subgroup G := T ⊓ CMK (centralizer ({x} : Set G)) K

include H in
theorem mem_Q {q : G} : q ∈ H.Q ↔ q ∈ T ∧ act H.KN q = 1 := by
  constructor
  · rintro ⟨hqT, hq⟩
    exact ⟨hqT, (act_eq_one_iff H.KN (H.T_le_C hqT)).2 hq⟩
  · rintro ⟨hqT, hq⟩
    exact ⟨hqT, (act_eq_one_iff H.KN (H.T_le_C hqT)).1 hq⟩

include H in
theorem P_comm_Q [Finite G] {p q : G} (hp : p ∈ T ⊓ K) (hq : q ∈ H.Q) : p * q = q * p := by
  have hqT : q ∈ T := ((H.mem_Q).1 hq).1
  have hqC : q ∈ centralizer ({x} : Set G) := H.T_le_C hqT
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
  (T.subgroupOf (centralizer ({x} : Set G))).map (Back.actHom H.KN)

include H in
theorem mem_B {u : MulAut (kBar K)} : u ∈ H.B ↔ ∃ t ∈ T, act H.KN t = u := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨(m : G), hm, ?_⟩
    rw [act_of_mem H.KN m.2]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, H.T_le_C ht⟩, ht, ?_⟩
    rw [act_of_mem H.KN (H.T_le_C ht)]

include H in
theorem B_isPGroup : IsPGroup 2 ↥H.B := by
  have hT2 : IsPGroup 2 ↥(T.subgroupOf (centralizer ({x} : Set G))) :=
    H.sylowT.isPGroup.comap_subtype
  exact hT2.of_surjective ((Back.actHom H.KN).subgroupMap _)
    ((Back.actHom H.KN).subgroupMap_surjective _)

include H in
theorem B_inf_inn [Finite G] :
    H.B ⊓ innAut (kBar K) = ((T ⊓ K).subgroupOf (centralizer ({x} : Set G))).map
      (Back.actHom H.KN) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC := H.T_le_C
  have hPC := H.P_le_C
  have hSylK : IsSylowOf 2 ((T ⊓ K).subgroupOf (centralizer ({x} : Set G)))
      (K.subgroupOf (centralizer ({x} : Set G))) := by
    rw [← isSylowOf_map_subtype_iff (centralizer ({x} : Set G)),
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC,
      inf_eq_left.2 H.KC]
    exact H.sylowP
  have hSyl : IsSylowOf 2 (((T ⊓ K).subgroupOf (centralizer ({x} : Set G))).map
      (Back.actHom H.KN)) (innAut (kBar K)) := by
    have := isSylowOf_map_hom (Back.actHom H.KN) hSylK
    rwa [map_actHom_K H.KC H.KN] at this
  have hPT : (T ⊓ K).subgroupOf (centralizer ({x} : Set G)) ≤
      T.subgroupOf (centralizer ({x} : Set G)) := fun a ha =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 ha).1
  have hPB : ((T ⊓ K).subgroupOf (centralizer ({x} : Set G))).map (Back.actHom H.KN) ≤
      H.B ⊓ innAut (kBar K) := le_inf (Subgroup.map_mono hPT) hSyl.le
  exact hSyl.eq_of_le hPB inf_le_right H.B_isPGroup.to_inf_left

include H in
theorem mem_B_inf_inn [Finite G] {u : MulAut (kBar K)} :
    u ∈ H.B ⊓ innAut (kBar K) ↔ ∃ p ∈ T ⊓ K, act H.KN p = u := by
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
  have hSylK : IsSylowOf 2 ((T ⊓ K).subgroupOf (centralizer ({x} : Set G)))
      (K.subgroupOf (centralizer ({x} : Set G))) := by
    rw [← isSylowOf_map_subtype_iff (centralizer ({x} : Set G)),
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 H.P_le_C, inf_eq_left.2 H.KC]
    exact H.sylowP
  rw [H.B_inf_inn]
  have := isSylowOf_map_hom (Back.actHom H.KN) hSylK
  rwa [map_actHom_K H.KC H.KN] at this

include H in
theorem fiber_mem_Q {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) (h : act H.KN t = act H.KN t') :
    t'⁻¹ * t ∈ H.Q := by
  refine (H.mem_Q).2 ⟨T.mul_mem (T.inv_mem ht') ht, ?_⟩
  rw [act_mul H.KN (Subgroup.inv_mem _ (H.T_le_C ht')) (H.T_le_C ht), act_inv H.KN (H.T_le_C ht'), h]
  group

include H in
theorem mem_normalizer_P [Finite G] {t : G} (ht : t ∈ T) :
    t ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) :=
  P34.mem_normalizer_of_conj_le (fun a ha =>
    ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) ha.1) ht, by
      simpa using H.KN t⁻¹ (H.T_le_C (T.inv_mem ht)) a ha.2⟩)

include H in
theorem mem_PQ_iff [Finite G] {t : G} :
    t ∈ (T ⊓ K) ⊔ H.Q ↔ ∃ p ∈ T ⊓ K, ∃ q ∈ H.Q, t = p * q := by
  constructor
  · intro ht
    exact Back.exists_mul_of_mem_sup_of_commute (fun p hp q hq => H.P_comm_Q hp hq) ht
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hq)

include H in
theorem Q_le_T : H.Q ≤ T := inf_le_left

include H in
theorem PQ_le_T : (T ⊓ K) ⊔ H.Q ≤ T := sup_le inf_le_left H.Q_le_T

include H in
theorem act_Q {q : G} (hq : q ∈ H.Q) : act H.KN q = 1 := ((H.mem_Q).1 hq).2

include H in
theorem act_PQ [Finite G] {t : G} (ht : t ∈ (T ⊓ K) ⊔ H.Q) :
    act H.KN t ∈ H.B ⊓ innAut (kBar K) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := (H.mem_PQ_iff).1 ht
  rw [act_mul H.KN (H.P_le_C hp) (H.T_le_C (H.Q_le_T hq)), H.act_Q hq, mul_one]
  exact (H.mem_B_inf_inn).2 ⟨p, hp, rfl⟩

include H in
theorem mem_PQ_of_act_mem [Finite G] {t : G} (ht : t ∈ T)
    (h : act H.KN t ∈ H.B ⊓ innAut (kBar K)) : t ∈ (T ⊓ K) ⊔ H.Q := by
  obtain ⟨p, hp, hpt⟩ := (H.mem_B_inf_inn).1 h
  have hq := H.fiber_mem_Q ht hp.1 hpt.symm
  have : t = p * (p⁻¹ * t) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hq)

include H in
theorem act_f_comm_Pbar [Finite G] {a : MulAut (kBar K)} (ha : a ∈ H.B ⊓ innAut (kBar K)) :
    act H.KN f * a = a * act H.KN f := by
  obtain ⟨p, hp, rfl⟩ := (H.mem_B_inf_inn).1 ha
  have hfC : f ∈ centralizer ({x} : Set G) := H.T_le_C H.f_mem
  rw [← act_mul H.KN hfC (H.P_le_C hp), ← act_mul H.KN (H.P_le_C hp) hfC, H.f_cent p hp]

include H in
theorem mem_PQf_iff [Finite G] {t : G} (ht : t ∈ T) :
    t ∈ ((T ⊓ K) ⊔ H.Q) ⊔ zpowers f ↔
      act H.KN t ∈ (H.B ⊓ innAut (kBar K)) ⊔ zpowers (act H.KN f) := by
  have hfC : f ∈ centralizer ({x} : Set G) := H.T_le_C H.f_mem
  have hαα : act H.KN f * act H.KN f = 1 := by
    rw [← act_mul H.KN hfC hfC, H.f_sq, act_one]
  constructor
  · intro h
    let S : Subgroup (MulAut (kBar K)) := (H.B ⊓ innAut (kBar K)) ⊔ zpowers (act H.KN f)
    let U : Subgroup G := (S.comap (Back.actHom H.KN)).map (centralizer ({x} : Set G)).subtype
    have hle : ((T ⊓ K) ⊔ H.Q) ⊔ zpowers f ≤ U := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro p hp
        refine ⟨⟨p, H.P_le_C hp⟩, ?_, rfl⟩
        show Back.actHom H.KN ⟨p, H.P_le_C hp⟩ ∈ S
        rw [← act_of_mem H.KN (H.P_le_C hp)]
        exact Subgroup.mem_sup_left ((H.mem_B_inf_inn).2 ⟨p, hp, rfl⟩)
      · intro q hq
        refine ⟨⟨q, H.T_le_C (H.Q_le_T hq)⟩, ?_, rfl⟩
        show Back.actHom H.KN ⟨q, H.T_le_C (H.Q_le_T hq)⟩ ∈ S
        rw [← act_of_mem H.KN (H.T_le_C (H.Q_le_T hq)), H.act_Q hq]
        exact S.one_mem
      · rw [zpowers_le]
        refine ⟨⟨f, hfC⟩, ?_, rfl⟩
        show Back.actHom H.KN ⟨f, hfC⟩ ∈ S
        rw [← act_of_mem H.KN hfC]
        exact Subgroup.mem_sup_right (mem_zpowers _)
    obtain ⟨m, hm, rfl⟩ := hle h
    show act H.KN (m : G) ∈ S
    rw [act_of_mem H.KN m.2]
    exact hm
  · intro h
    have hcomm : ∀ a ∈ H.B ⊓ innAut (kBar K), ∀ b ∈ zpowers (act H.KN f), a * b = b * a := by
      intro a ha b hb
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (show Commute a (act H.KN f) from (H.act_f_comm_Pbar ha).symm) j).eq
    obtain ⟨a, ha, b, hb, hab⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm h
    obtain ⟨p, hp, hpa⟩ := (H.mem_B_inf_inn).1 ha
    rcases mem_zpowers_of_mul_self hαα hb with rfl | rfl
    ·
      rw [mul_one] at hab
      have hq := H.fiber_mem_Q ht hp.1 (by rw [hpa, hab])
      have : t = p * (p⁻¹ * t) := by group
      rw [this]
      exact Subgroup.mem_sup_left (Subgroup.mul_mem _ (Subgroup.mem_sup_left hp)
        (Subgroup.mem_sup_right hq))
    ·
      have hpfT : p * f ∈ T := T.mul_mem hp.1 H.f_mem
      have hq := H.fiber_mem_Q ht hpfT (by
        rw [act_mul H.KN (H.P_le_C hp) hfC, hpa, hab])
      have : t = (p * f) * ((p * f)⁻¹ * t) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
        (Subgroup.mem_sup_left hp)) (Subgroup.mem_sup_right (mem_zpowers f)))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hq))

end Real34

end CFSG.GH74.GLS.C3.Layer1.P34Real
