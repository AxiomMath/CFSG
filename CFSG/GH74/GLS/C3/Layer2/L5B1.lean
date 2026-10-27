module

public import CFSG.GH74.GLS.C3.Layer2.L5B0
public import CFSG.GH74.GLS.C3.Layer2.L5A3
public import CFSG.GH74.GLS.C3.Layer2.L5T33

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

@[expose] def Case47
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : Prop :=
  ∀ V ∈ FamQ (c.lift Rm) Q, V = Q ∨ V = T ⊓ K

theorem a_sq_mem (h : IsAConfig 5 x K T Q S a) : a * a ∈ T := by
  have := h.a_mem.2.2.2
  rwa [pow_two] at this

theorem P_ne_Q
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : T ⊓ K ≠ Q := by
  intro heq
  have h1 := P_inf_Q h c
  rw [heq, inf_idem] at h1
  have := h.card_Q
  rw [h1, Subgroup.card_bot] at this
  omega

theorem cj_a_Q
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) :
    cj a Q = T ⊓ K := by
  have hV : cj a Q ∈ FamQ (c.lift Rm) Q := ⟨a, a_mem_N h c, rfl⟩
  rcases hc _ hV with h1 | h1
  · exfalso
    obtain ⟨q, hq, hqa⟩ := a_not_NQ h c
    apply hqa
    have : a * q * a⁻¹ ∈ cj a Q := mem_cj_self hq
    rwa [h1] at this
  · exact h1

theorem cj_a_P
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) :
    cj a (T ⊓ K) = Q := by
  have hn : a * a ∈ normalizer (Q : Set G) := h.C_le_normalizer_Q (h.T_le_C (a_sq_mem h))
  calc cj a (T ⊓ K) = cj a (cj a Q) := by rw [cj_a_Q hc]
    _ = cj (a * a) Q := (cj_mul a a Q).symm
    _ = Q := cj_eq_of_normalizes hn

theorem T_le_normalizer_P (h : IsAConfig 5 x K T Q S a) :
    T ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  intro t ht
  have key : ∀ t ∈ T, ∀ y ∈ T ⊓ K, t * y * t⁻¹ ∈ T ⊓ K := by
    intro t ht y hy
    refine ⟨T.mul_mem (T.mul_mem ht hy.1) (T.inv_mem ht), ?_⟩
    exact h.normalInC t (h.T_le_C ht) y hy.2
  refine mem_normalizer_iff.2 (fun y => ⟨key t ht y, fun hy => ?_⟩)
  have h1 := key t⁻¹ (T.inv_mem ht) _ hy
  have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem T_le_normalizer_Q (h : IsAConfig 5 x K T Q S a) :
    T ≤ normalizer (Q : Set G) := fun _ ht => h.C_le_normalizer_Q (h.T_le_C ht)

@[expose] def Msub (T : Subgroup G) (a : G) (haN : a ∈ normalizer (T : Set G)) (haa : a * a ∈ T) :
    Subgroup G where
  carrier := {g | g ∈ T ∨ ∃ t ∈ T, g = a * t}
  one_mem' := Or.inl T.one_mem
  mul_mem' := by
    have hinv : ∀ t ∈ T, a⁻¹ * t * a ∈ T := fun t ht => by
      have := (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem haN) t).1 ht
      simpa using this
    rintro g g' (hg | ⟨t, ht, rfl⟩) (hg' | ⟨t', ht', rfl⟩)
    · exact Or.inl (T.mul_mem hg hg')
    · exact Or.inr ⟨a⁻¹ * g * a * t', T.mul_mem (hinv g hg) ht', by group⟩
    · exact Or.inr ⟨t * g', T.mul_mem ht hg', by group⟩
    · refine Or.inl ?_
      have : a * t * (a * t') = (a * a) * (a⁻¹ * t * a) * t' := by group
      rw [this]
      exact T.mul_mem (T.mul_mem haa (hinv t ht)) ht'
  inv_mem' := by
    have hinv : ∀ t ∈ T, a⁻¹ * t * a ∈ T := fun t ht => by
      have := (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem haN) t).1 ht
      simpa using this
    rintro g (hg | ⟨t, ht, rfl⟩)
    · exact Or.inl (T.inv_mem hg)
    · refine Or.inr ⟨(a⁻¹ * t⁻¹ * a) * (a * a)⁻¹,
        T.mul_mem (hinv t⁻¹ (T.inv_mem ht)) (T.inv_mem haa), ?_⟩
      group

abbrev Mh (h : IsAConfig 5 x K T Q S a) : Subgroup G :=
  Msub T a h.a_mem.2.1 (a_sq_mem h)

theorem mem_Mh {h : IsAConfig 5 x K T Q S a} {g : G} :
    g ∈ Mh h ↔ g ∈ T ∨ ∃ t ∈ T, g = a * t := Iff.rfl

theorem T_le_Mh (h : IsAConfig 5 x K T Q S a) : T ≤ Mh h := fun _ ht => Or.inl ht

theorem a_mem_Mh (h : IsAConfig 5 x K T Q S a) : a ∈ Mh h := Or.inr ⟨1, T.one_mem, by simp⟩

theorem Mh_le_S (h : IsAConfig 5 x K T Q S a) : Mh h ≤ S := by
  rintro g (hg | ⟨t, ht, rfl⟩)
  · exact h.T_lt_S.le hg
  · exact S.mul_mem h.a_mem.1 (h.T_lt_S.le ht)

theorem Mh_pgroup (h : IsAConfig 5 x K T Q S a) : IsPGroup 2 ↥(Mh h) := by
  have hSp : IsPGroup 2 ↥S := (isSylowOf_iff.1 h.sylowS).2.1
  exact hSp.to_le (Mh_le_S h)

theorem a_inv_conj_mem (h : IsAConfig 5 x K T Q S a) {t : G} (ht : t ∈ T) : a⁻¹ * t * a ∈ T := by
  have := (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem h.a_mem.2.1) t).1 ht
  simpa using this

theorem relIndex_T_Mh (h : IsAConfig 5 x K T Q S a) : T.relIndex (Mh h) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨a, a_mem_Mh h, ?_⟩
  intro g hg
  rcases hg with hg | ⟨t, ht, rfl⟩
  · exact Or.inr ⟨hg, fun hga => h.a_mem.2.2.1 ((Subgroup.mul_mem_cancel_left T hg).1 hga)⟩
  · refine Or.inl ⟨?_, fun hgT => h.a_mem.2.2.1 ?_⟩
    · have : a * t * a = (a * a) * (a⁻¹ * t * a) := by group
      rw [this]
      exact T.mul_mem (a_sq_mem h) (a_inv_conj_mem h ht)
    · have : a = (a * t) * t⁻¹ := by group
      rw [this]
      exact T.mul_mem hgT (T.inv_mem ht)

theorem card_Mh
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) : Nat.card (Mh h) = 64 := by
  have h1 := Subgroup.card_mul_index (T.subgroupOf (Mh h))
  have h2 : Nat.card ↥(T.subgroupOf (Mh h)) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (T_le_Mh h)).toEquiv
  have h3 : (T.subgroupOf (Mh h)).index = 2 := relIndex_T_Mh h
  rw [h2, h3, card_T_five h c] at h1
  omega

theorem Mh_le_N
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) :
    Mh h ≤ normalizer ((c.lift Rm : Subgroup G) : Set G) := by
  rintro g (hg | ⟨t, ht, rfl⟩)
  · exact (T_sylow_NQ h c).le hg |>.1
  · exact mul_mem (a_mem_N h c) ((T_sylow_NQ h c).le ht).1

theorem card_H_eq
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) :
    Nat.card ↥(normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)) =
      32 * T.relIndex (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)) := by
  have hTH := (T_sylow_NQ h c).le
  have h1 := Subgroup.card_mul_index (T.subgroupOf (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓
    normalizer (Q : Set G)))
  have h2 : Nat.card ↥(T.subgroupOf (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓
      normalizer (Q : Set G))) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  rw [h2, card_T_five h c] at h1
  exact h1.symm

theorem card_fam_two
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) :
    Nat.card (FamQ (c.lift Rm) Q) = 2 := by
  have heq : FamQ (c.lift Rm) Q = {Q, T ⊓ K} := by
    ext V
    constructor
    · intro hV
      rcases hc V hV with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · exact Q_mem_fam
      · rw [← cj_a_Q hc]
        exact ⟨a, a_mem_N h c, rfl⟩
  rw [heq, Nat.card_coe_set_eq, Set.ncard_pair (P_ne_Q h c).symm]

theorem M_sylow_N
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) :
    IsSylowOf 2 (Mh h) (normalizer ((c.lift Rm : Subgroup G) : Set G)) := by
  rw [isSylowOf_iff]
  refine ⟨Mh_le_N h c, Mh_pgroup h, ?_⟩
  have hmul := fam_card_mul (c.lift Rm) Q
  rw [card_fam_two hc, card_H_eq h c] at hmul
  have h1 := Subgroup.card_mul_index ((Mh h).subgroupOf (normalizer ((c.lift Rm : Subgroup G) : Set G)))
  have h2 : Nat.card ↥((Mh h).subgroupOf (normalizer ((c.lift Rm : Subgroup G) : Set G))) =
      Nat.card (Mh h) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Mh_le_N h c)).toEquiv
  rw [h2, card_Mh h c] at h1
  obtain ⟨-, -, hodd⟩ := isSylowOf_iff.1 (T_sylow_NQ h c)
  have h3 : ((Mh h).subgroupOf (normalizer ((c.lift Rm : Subgroup G) : Set G))).index =
      T.relIndex (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)) := by
    have : 64 * ((Mh h).subgroupOf (normalizer ((c.lift Rm : Subgroup G) : Set G))).index =
        64 * T.relIndex (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)) := by
      rw [h1, ← hmul]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have h4 : (Mh h).relIndex (normalizer ((c.lift Rm : Subgroup G) : Set G)) =
      T.relIndex (normalizer ((c.lift Rm : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)) := h3
  rw [h4]
  exact hodd

theorem card_le_two_mul_card_of_coset {R R₀ : Subgroup G}
    (h : ∀ r ∈ R, ∀ s ∈ R, r ∉ R₀ → s ∉ R₀ → r⁻¹ * s ∈ R₀) :
    Nat.card R ≤ 2 * Nat.card R₀ := by
  classical
  by_cases hex : ∃ r₀ ∈ R, r₀ ∉ R₀
  · obtain ⟨r₀, hr₀R, hr₀⟩ := hex
    let f : R → R₀ ⊕ R₀ := fun r =>
      if hr : (r : G) ∈ R₀ then Sum.inl ⟨r, hr⟩ else Sum.inr ⟨r₀⁻¹ * r, h r₀ hr₀R r r.2 hr₀ hr⟩
    have hf : Function.Injective f := by
      intro u v huv
      by_cases hu : (u : G) ∈ R₀ <;> by_cases hv : (v : G) ∈ R₀ <;>
        simp only [f, hu, hv, dite_true, dite_false, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq,
          Subtype.mk.injEq] at huv
      · exact Subtype.ext huv
      · exact Subtype.ext (mul_left_cancel huv)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_sum, ← two_mul] at this
  · push Not at hex
    have hle : R ≤ R₀ := hex
    have := Subgroup.card_le_of_le hle
    omega

theorem R_prod_G
    {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) {r : G} (hr : r ∈ c.lift Rm) :
    ∃ p ∈ T ⊓ K, ∃ q ∈ Q, r = p * q := by
  have hrC := Coord5.lift_mem_cent hr
  have hmem : c.co ⟨r, hrC⟩ ∈ Rm := by
    rw [← Coord5.rco_of_mem c hrC]
    exact Coord5.rco_mem c hr
  obtain ⟨p, hp, q, hq, hpq⟩ := Rm_prod _ hmem
  obtain ⟨p', hp'⟩ := c.co_surj (Pm_le_Fgrp hp)
  obtain ⟨q', hq'⟩ := c.co_surj (Qm_le_Fgrp hq)
  have h1 : (⟨r, hrC⟩ : ↥(centralizer ({x} : Set G))) = p' * q' := by
    apply c.co_inj
    rw [c.co_mul, hp', hq']
    exact hpq
  refine ⟨p', (SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) (p' : G)).2 ⟨p'.2, by rw [hp']; exact hp⟩,
    q', (SetLike.ext_iff.1 (Coord5.Q_eq_lift (c := c)) (q' : G)).2 ⟨q'.2, by rw [hq']; exact hq⟩,
    congrArg Subtype.val h1⟩

theorem relIndex_R_T
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) :
    (c.lift Rm).relIndex T = 2 := by
  have h1 := Subgroup.card_mul_index ((c.lift Rm).subgroupOf T)
  have h2 : Nat.card ↥((c.lift Rm).subgroupOf T) = Nat.card (c.lift Rm) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Coord5.Rg_le_T (c := c))).toEquiv
  rw [h2, Coord5.card_lift_Rm, card_T_five h c] at h1
  have : ((c.lift Rm).subgroupOf T).index = 2 := by omega
  exact this

theorem PQ_comm_G (h : IsAConfig 5 x K T Q S a) (c : Coord5 h) :
    ∀ p ∈ T ⊓ K, ∀ q ∈ Q, p * q = q * p := by
  intro p hp q hq
  exact Coord5.lift_comm (c := c) (M := Rm) (fun a ha b hb => Rm_comm a ha b hb)
    (P_le_R h c hp) (Q_le_R h c hq)

attribute [-instance] CFSG.GorensteinWalter.instDecidableEqPermFinOfNatNat_certificates in
theorem card_R_cent_le
    {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) {t : G} (ht : t ∈ T)
    (htR : t ∉ c.lift Rm) : Nat.card ↥(c.lift Rm ⊓ centralizer ({t} : Set G)) ≤ 4 := by
  have htC := h.T_le_C ht
  have ht5 : c.co ⟨t, htC⟩ ∈ T5 := (c.hιT ⟨t, htC⟩).1 ht
  have ht5R : c.co ⟨t, htC⟩ ∉ Rm := fun hm => htR ⟨htC, hm⟩
  have hrt : c.rco t = c.co ⟨t, htC⟩ := Coord5.rco_of_mem c htC
  have heq : c.lift Rm ⊓ centralizer ({t} : Set G) =
      c.lift (Rm ⊓ centralizer ({c.co ⟨t, htC⟩} : Set (Amb 5))) := by
    ext g
    constructor
    · rintro ⟨hgR, hgc⟩
      have hgC := Coord5.lift_mem_cent hgR
      rw [Coord5.mem_lift_rco c]
      refine ⟨hgC, Coord5.rco_mem c hgR, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [← hrt, ← Coord5.rco_mul c hgC htC, ← Coord5.rco_mul c htC hgC]
      exact congrArg c.rco (mem_centralizer_singleton_iff.1 hgc)
    · intro hg
      rw [Coord5.mem_lift_rco c] at hg
      obtain ⟨hgC, hgm, hgc⟩ := hg
      refine ⟨(Coord5.mem_lift_rco c).2 ⟨hgC, hgm⟩, ?_⟩
      refine mem_centralizer_singleton_iff.2 ?_
      refine Coord5.rco_inj c (mul_mem hgC htC) (mul_mem htC hgC) ?_
      rw [Coord5.rco_mul c hgC htC, Coord5.rco_mul c htC hgC, hrt]
      exact mem_centralizer_singleton_iff.1 hgc
  rw [heq, Coord5.card_lift (inf_le_left.trans Rm_le_Fgrp)]
  have hnd : (Rml.filter (fun s => decide (s * c.co ⟨t, htC⟩ = c.co ⟨t, htC⟩ * s))).Nodup :=
    Rml_nodup.filter _
  have hlen := natCard_eq_length (Rm ⊓ centralizer ({c.co ⟨t, htC⟩} : Set (Amb 5)))
    (Rml.filter (fun s => decide (s * c.co ⟨t, htC⟩ = c.co ⟨t, htC⟩ * s))) hnd (fun p => by
      simp only [Subgroup.mem_inf, List.mem_filter, mem_Rm, decide_eq_true_eq,
        Subgroup.mem_centralizer_singleton_iff])
  rw [hlen]
  exact T5_cent_R_le ht5 ht5R

theorem exists_cent_P
    {h : IsAConfig 5 x K T Q S a} (c : Coord5 h) {t : G} (ht : t ∈ T)
    (htR : t ∉ c.lift Rm) : ∃ p ∈ T ⊓ K, p ≠ 1 ∧ t * p = p * t := by
  have htC := h.T_le_C ht
  have ht5 : c.co ⟨t, htC⟩ ∈ T5 := (c.hιT ⟨t, htC⟩).1 ht
  have ht5R : c.co ⟨t, htC⟩ ∉ Rm := fun hm => htR ⟨htC, hm⟩
  obtain ⟨p', hp', hp'1, hp't⟩ := T5_cent_P_ne ht5 ht5R
  obtain ⟨p, hp⟩ := c.co_surj (Pm_le_Fgrp hp')
  have hpP : (p : G) ∈ T ⊓ K := (SetLike.ext_iff.1 (Coord5.P_eq_lift (c := c)) (p : G)).2
    ⟨p.2, by rw [hp]; exact hp'⟩
  refine ⟨p, hpP, ?_, ?_⟩
  · intro h1
    apply hp'1
    rw [← hp]
    have : p = 1 := Subtype.ext h1
    rw [this, c.co_one]
  · have h2 : (⟨t, htC⟩ : ↥(centralizer ({x} : Set G))) * p = p * ⟨t, htC⟩ := by
      apply c.co_inj
      rw [c.co_mul, c.co_mul, hp]
      exact hp't.symm
    exact congrArg Subtype.val h2

theorem cj_aT_P
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {t : G}
    (ht : t ∈ T) : cj (a * t) (T ⊓ K) = Q := by
  rw [cj_mul, cj_eq_of_normalizes (T_le_normalizer_P h ht), cj_a_P hc]

theorem cj_aT_Q
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {t : G}
    (ht : t ∈ T) : cj (a * t) Q = T ⊓ K := by
  rw [cj_mul, cj_eq_of_normalizes (T_le_normalizer_Q h ht), cj_a_Q hc]

theorem card_R_cent_aT_le
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {t : G}
    (ht : t ∈ T) : Nat.card ↥(c.lift Rm ⊓ centralizer ({a * t} : Set G)) ≤ 4 := by
  set e := a * t with he
  have hPe : ∀ p ∈ T ⊓ K, e * p * e⁻¹ ∈ Q := fun p hp => by
    rw [← cj_aT_P hc ht]
    exact mem_cj_self hp
  have hQe : ∀ q ∈ Q, e * q * e⁻¹ ∈ T ⊓ K := fun q hq => by
    rw [← cj_aT_Q hc ht]
    exact mem_cj_self hq
  have hsub : ((c.lift Rm ⊓ centralizer ({e} : Set G) : Subgroup G) : Set G) ⊆
      (fun p => p * (e * p * e⁻¹)) '' ((T ⊓ K : Subgroup G) : Set G) := by
    intro r hr
    obtain ⟨hrR, hrc⟩ := hr
    obtain ⟨p, hp, q, hq, rfl⟩ := R_prod_G c hrR
    refine ⟨p, hp, ?_⟩
    have hcomm : p * q * e = e * (p * q) := mem_centralizer_singleton_iff.1 hrc
    have hp₁ : e * q * e⁻¹ ∈ T ⊓ K := hQe q hq
    have hq₁ : e * p * e⁻¹ ∈ Q := hPe p hp
    have h1 : (e * p * e⁻¹) * (e * q * e⁻¹) = p * q := by
      calc (e * p * e⁻¹) * (e * q * e⁻¹) = e * (p * q) * e⁻¹ := by group
        _ = (p * q * e) * e⁻¹ := by rw [← hcomm]
        _ = p * q := by group
    have h2 : (e * q * e⁻¹) * (e * p * e⁻¹) = p * q := by
      rw [← h1]
      exact PQ_comm_G h c _ hp₁ _ hq₁
    have h3 : p⁻¹ * (e * q * e⁻¹) = q * (e * p * e⁻¹)⁻¹ := by
      have : p⁻¹ * ((e * q * e⁻¹) * (e * p * e⁻¹)) * (e * p * e⁻¹)⁻¹ =
          p⁻¹ * (p * q) * (e * p * e⁻¹)⁻¹ := by rw [h2]
      calc p⁻¹ * (e * q * e⁻¹) = p⁻¹ * ((e * q * e⁻¹) * (e * p * e⁻¹)) * (e * p * e⁻¹)⁻¹ := by group
        _ = p⁻¹ * (p * q) * (e * p * e⁻¹)⁻¹ := this
        _ = q * (e * p * e⁻¹)⁻¹ := by group
    have hP' : p⁻¹ * (e * q * e⁻¹) ∈ T ⊓ K := (T ⊓ K).mul_mem ((T ⊓ K).inv_mem hp) hp₁
    have hQ' : q * (e * p * e⁻¹)⁻¹ ∈ Q := Q.mul_mem hq (Q.inv_mem hq₁)
    have h4 : p⁻¹ * (e * q * e⁻¹) ∈ (T ⊓ K) ⊓ Q := ⟨hP', h3 ▸ hQ'⟩
    rw [P_inf_Q h c] at h4
    have h5 : p⁻¹ * (e * q * e⁻¹) = 1 := Subgroup.mem_bot.1 h4
    have h6 : q = e * p * e⁻¹ := by
      have h7 : q * (e * p * e⁻¹)⁻¹ = 1 := by rw [← h3]; exact h5
      calc q = (q * (e * p * e⁻¹)⁻¹) * (e * p * e⁻¹) := by group
        _ = e * p * e⁻¹ := by rw [h7, one_mul]
    show p * (e * p * e⁻¹) = p * q
    rw [h6]
  have hfin : ((T ⊓ K : Subgroup G) : Set G).Finite := Set.toFinite _
  calc Nat.card ↥(c.lift Rm ⊓ centralizer ({e} : Set G))
      = ((c.lift Rm ⊓ centralizer ({e} : Set G) : Subgroup G) : Set G).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ((fun p => p * (e * p * e⁻¹)) '' ((T ⊓ K : Subgroup G) : Set G)).ncard :=
        Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ ((T ⊓ K : Subgroup G) : Set G).ncard := Set.ncard_image_le hfin
    _ = Nat.card ↥(T ⊓ K) := (Nat.card_coe_set_eq _).symm
    _ = 4 := card_P_five h c

theorem aT_cent_P
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {t : G}
    (ht : t ∈ T) {p : G} (hp : p ∈ T ⊓ K) (hcp : (a * t) * p * (a * t)⁻¹ = p) : p = 1 := by
  have hpQ : p ∈ Q := by
    have : (a * t) * p * (a * t)⁻¹ ∈ cj (a * t) (T ⊓ K) := mem_cj_self hp
    rw [hcp, cj_aT_P hc ht] at this
    exact this
  have h1 : p ∈ (T ⊓ K) ⊓ Q := ⟨hp, hpQ⟩
  rw [P_inf_Q h c] at h1
  exact Subgroup.mem_bot.1 h1

theorem E_eq_R
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) {E : Subgroup G}
    (hEM : E ≤ Mh h) (hE16 : Nat.card E = 16) (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) :
    E = c.lift Rm := by
  have hRle : c.lift Rm ≤ T := Coord5.Rg_le_T (c := c)
  have hRT := relIndex_R_T h c
  have hR16 : Nat.card (c.lift Rm) = 16 := Coord5.card_lift_Rm (c := c)
  by_cases hET : E ≤ T
  · by_contra hne
    have hnotle : ¬ E ≤ c.lift Rm := fun hle =>
      hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hE16, hR16]))
    obtain ⟨e, heE, heR⟩ : ∃ e ∈ E, e ∉ c.lift Rm := by
      by_contra hcon
      push Not at hcon
      exact hnotle hcon
    have h8 : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ c.lift Rm) := by
      refine card_le_two_mul_card_of_coset (fun r hr s hs hr' hs' => ?_)
      have hrR : r ∉ c.lift Rm := fun hh => hr' ⟨hr, hh⟩
      have hsR : s ∉ c.lift Rm := fun hh => hs' ⟨hs, hh⟩
      exact ⟨E.mul_mem (E.inv_mem hr) hs,
        inv_mul_mem_of_relIndex_two hRT (hET hr) (hET hs) hrR hsR⟩
    have hle : E ⊓ c.lift Rm ≤ c.lift Rm ⊓ centralizer ({e} : Set G) := fun g hg =>
      ⟨hg.2, mem_centralizer_singleton_iff.2 (hEc g hg.1 e heE)⟩
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_R_cent_le c (hET heE) heR
    omega
  · exfalso
    obtain ⟨e', he'E, he'T⟩ : ∃ e' ∈ E, e' ∉ T := by
      by_contra hcon
      push Not at hcon
      exact hET hcon
    obtain ⟨t', ht', rfl⟩ : ∃ t' ∈ T, e' = a * t' := by
      rcases hEM he'E with hh | ⟨t, ht, hh⟩
      · exact absurd hh he'T
      · exact ⟨t, ht, hh⟩
    have h8 : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ T) := by
      refine card_le_two_mul_card_of_coset (fun r hr s hs hr' hs' => ?_)
      have hrT : r ∉ T := fun hh => hr' ⟨hr, hh⟩
      have hsT : s ∉ T := fun hh => hs' ⟨hs, hh⟩
      refine ⟨E.mul_mem (E.inv_mem hr) hs, ?_⟩
      rcases hEM hr with h1 | ⟨t₁, ht₁, h1⟩
      · exact absurd h1 hrT
      rcases hEM hs with h2 | ⟨t₂, ht₂, h2⟩
      · exact absurd h2 hsT
      rw [h1, h2]
      have : (a * t₁)⁻¹ * (a * t₂) = t₁⁻¹ * t₂ := by group
      rw [this]
      exact T.mul_mem (T.inv_mem ht₁) ht₂
    have hER_le : E ⊓ c.lift Rm ≤ c.lift Rm ⊓ centralizer ({a * t'} : Set G) := fun g hg =>
      ⟨hg.2, mem_centralizer_singleton_iff.2 (hEc g hg.1 _ he'E)⟩
    have hER4 : Nat.card ↥(E ⊓ c.lift Rm) ≤ 4 :=
      (Subgroup.card_le_of_le hER_le).trans (card_R_cent_aT_le hc ht')
    obtain ⟨e, ⟨heE, heT⟩, heR⟩ : ∃ e ∈ E ⊓ T, e ∉ c.lift Rm := by
      by_contra hcon
      push Not at hcon
      have hle : E ⊓ T ≤ E ⊓ c.lift Rm := fun g hg => ⟨hg.1, hcon g hg⟩
      have := Subgroup.card_le_of_le hle
      omega
    have h4 : Nat.card ↥(E ⊓ T) ≤ 2 * Nat.card ↥(E ⊓ c.lift Rm) := by
      refine card_le_two_mul_card_of_coset (fun r hr s hs hr' hs' => ?_)
      have hrR : r ∉ c.lift Rm := fun hh => hr' ⟨hr.1, hh⟩
      have hsR : s ∉ c.lift Rm := fun hh => hs' ⟨hs.1, hh⟩
      exact ⟨E.mul_mem (E.inv_mem hr.1) hs.1,
        inv_mul_mem_of_relIndex_two hRT hr.2 hs.2 hrR hsR⟩
    have hle2 : E ⊓ c.lift Rm ≤ c.lift Rm ⊓ centralizer ({e} : Set G) := fun g hg =>
      ⟨hg.2, mem_centralizer_singleton_iff.2 (hEc g hg.1 e heE)⟩
    have hcent4 := card_R_cent_le c heT heR
    have heq : E ⊓ c.lift Rm = c.lift Rm ⊓ centralizer ({e} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle2 (by omega)
    obtain ⟨p, hpP, hp1, hep⟩ := exists_cent_P c heT heR
    have hpRC : p ∈ c.lift Rm ⊓ centralizer ({e} : Set G) :=
      ⟨P_le_R h c hpP, mem_centralizer_singleton_iff.2 hep.symm⟩
    rw [← heq] at hpRC
    have hpE : p ∈ E := hpRC.1
    have hcomm := hEc _ he'E p hpE
    have hfix : (a * t') * p * (a * t')⁻¹ = p := by rw [hcomm]; group
    exact hp1 (aT_cent_P hc ht' hpP hfix)

theorem R_char_M
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) :
    ∀ g ∈ normalizer ((Mh h : Subgroup G) : Set G),
      g ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_cj_le
  have hRM : c.lift Rm ≤ Mh h := (Coord5.Rg_le_T (c := c)).trans (T_le_Mh h)
  have hEM : cj g (c.lift Rm) ≤ Mh h := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := mem_cj.1 hy
    exact (mem_normalizer_iff.1 hg r).1 (hRM hr)
  have hE := E_eq_R hc hEM (by rw [card_cj]; exact Coord5.card_lift_Rm (c := c))
    (fun e he e' he' => by
      obtain ⟨r, hr, rfl⟩ := mem_cj.1 he
      obtain ⟨r', hr', rfl⟩ := mem_cj.1 he'
      have := Coord5.lift_comm (c := c) (M := Rm) (fun a ha b hb => Rm_comm a ha b hb) hr hr'
      calc g * r * g⁻¹ * (g * r' * g⁻¹) = g * (r * r') * g⁻¹ := by group
        _ = g * (r' * r) * g⁻¹ := by rw [this]
        _ = g * r' * g⁻¹ * (g * r * g⁻¹) := by group)
  exact hE.le

theorem S_eq_Mh
    {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} (hc : Case47 h c) : S = Mh h := by
  by_contra hne
  have hle := Mh_le_S h
  have hSp : IsPGroup 2 ↥S := (isSylowOf_iff.1 h.sylowS).2.1
  have : Group.IsNilpotent ↥S := hSp.isNilpotent
  have hH : (Mh h).subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm
    · intro g hg
      have : (⟨g, hg⟩ : ↥S) ∈ (Mh h).subgroupOf S := by rw [htop]; trivial
      exact this
    · exact hle
  obtain ⟨s, hsn, hsH⟩ := IsConcreteLE.exists_of_lt
    ((Group.normalizerCondition_of_isNilpotent (G := ↥S)) _ hH)
  have hsM : (s : G) ∈ normalizer ((Mh h : Subgroup G) : Set G) := by
    refine mem_normalizer_iff.2 (fun g => ?_)
    by_cases hgS : g ∈ S
    · exact mem_normalizer_iff.1 hsn ⟨g, hgS⟩
    · constructor
      · intro hg
        exact absurd (hle hg) hgS
      · intro hg
        exfalso
        apply hgS
        have h1 : (s : G) * g * (s : G)⁻¹ ∈ S := hle hg
        have : g = (s : G)⁻¹ * ((s : G) * g * (s : G)⁻¹) * (s : G) := by group
        rw [this]
        exact S.mul_mem (S.mul_mem (S.inv_mem s.2) h1) s.2
  have hsN := R_char_M hc (s : G) hsM
  have hUN : Mh h ⊔ zpowers (s : G) ≤ normalizer ((c.lift Rm : Subgroup G) : Set G) :=
    sup_le (Mh_le_N h c) (zpowers_le.2 hsN)
  have hUS : Mh h ⊔ zpowers (s : G) ≤ S := sup_le hle (zpowers_le.2 s.2)
  have hUp : IsPGroup 2 ↥(Mh h ⊔ zpowers (s : G)) := hSp.to_le hUS
  have hUM := eq_of_isSylowOf_le (M_sylow_N hc) hUN hUp le_sup_left
  apply hsH
  show (s : G) ∈ Mh h
  rw [← hUM]
  exact mem_sup_right (mem_zpowers _)

end CFSG.GH74.GLS.C3.Layer2.L5
