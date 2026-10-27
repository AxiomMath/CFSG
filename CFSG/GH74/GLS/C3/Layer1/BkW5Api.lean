module

public import CFSG.GH74.GLS.C3.Layer1.BkW5Coord
public import CFSG.GH74.GLS.C3.Layer2.L5C8

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.W5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
open scoped commutatorElement
open CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfigW 5 x K T Q S a}

namespace Coord

open Classical in
noncomputable def rco (c : Coord h) (g : G) : Amb 5 :=
  if hg : g ∈ centralizer ({x} : Set G) then ((c.co ⟨g, hg⟩ : Fgrp 5) : Amb 5) else 1

theorem rco_of_mem (c : Coord h) {g : G} (hg : g ∈ centralizer ({x} : Set G)) :
    c.rco g = ((c.co ⟨g, hg⟩ : Fgrp 5) : Amb 5) := by
  simp [rco, hg]

theorem rco_of_not_mem (c : Coord h) {g : G} (hg : g ∉ centralizer ({x} : Set G)) : c.rco g = 1 := by
  simp [rco, hg]

theorem rco_mul (c : Coord h) {g g' : G} (hg : g ∈ centralizer ({x} : Set G))
    (hg' : g' ∈ centralizer ({x} : Set G)) : c.rco (g * g') = c.rco g * c.rco g' := by
  rw [rco_of_mem c (mul_mem hg hg'), rco_of_mem c hg, rco_of_mem c hg']
  have := c.co.map_mul ⟨g, hg⟩ ⟨g', hg'⟩
  exact congrArg (fun z : ↥(Fgrp 5) => (z : Amb 5)) this

theorem rco_inv (c : Coord h) {g : G} (hg : g ∈ centralizer ({x} : Set G)) : c.rco g⁻¹ = (c.rco g)⁻¹ := by
  rw [rco_of_mem c (inv_mem hg), rco_of_mem c hg]
  have := c.co.map_inv ⟨g, hg⟩
  exact congrArg (fun z : ↥(Fgrp 5) => (z : Amb 5)) this

theorem rco_one (c : Coord h) : c.rco 1 = 1 := by
  rw [rco_of_mem c (one_mem _)]
  have := c.co.map_one
  exact congrArg (fun z : ↥(Fgrp 5) => (z : Amb 5)) this

theorem rco_inj (c : Coord h) {g g' : G} (hg : g ∈ T) (hg' : g' ∈ T) (hgg : c.rco g = c.rco g') : g = g' := by
  have hgC := h.T_le_C hg
  have hg'C := h.T_le_C hg'
  rw [rco_of_mem c hgC, rco_of_mem c hg'C] at hgg
  have h1 : c.co ⟨g, hgC⟩ = c.co ⟨g', hg'C⟩ := Subtype.ext hgg
  have h2 : (⟨g', hg'C⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨g, hgC⟩ ∈ Wc x := by
    rw [← c.co_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have h3 : g'⁻¹ * g ∈ T ⊓ pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
    ⟨T.mul_mem (T.inv_mem hg') hg, mem_Wc.1 h2⟩
  rw [T_inf_W h, Subgroup.mem_bot] at h3
  exact (inv_mul_eq_one.1 h3).symm

@[expose] noncomputable def lift (c : Coord h) (M : Subgroup (Amb 5)) : Subgroup G where
  carrier := {g | g ∈ T ∧ c.rco g ∈ M}
  one_mem' := ⟨T.one_mem, by rw [rco_one]; exact M.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨T.mul_mem ha hb, by
      rw [rco_mul c (h.T_le_C ha) (h.T_le_C hb)]; exact M.mul_mem ha' hb'⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨T.inv_mem ha, by rw [rco_inv c (h.T_le_C ha)]; exact M.inv_mem ha'⟩

theorem mem_lift_rco (c : Coord h) {M : Subgroup (Amb 5)} {g : G} : g ∈ c.lift M ↔ g ∈ T ∧ c.rco g ∈ M := Iff.rfl

theorem lift_mem_cent {c : Coord h} {M : Subgroup (Amb 5)} {g : G} (hg : g ∈ c.lift M) :
    g ∈ centralizer ({x} : Set G) := h.T_le_C hg.1

theorem rco_mem (c : Coord h) {M : Subgroup (Amb 5)} {g : G} (hg : g ∈ c.lift M) : c.rco g ∈ M := hg.2

theorem lift_mono {c : Coord h} {M₁ M₂ : Subgroup (Amb 5)} (hM : M₁ ≤ M₂) : c.lift M₁ ≤ c.lift M₂ :=
  fun _ ⟨hg, hm⟩ => ⟨hg, hM hm⟩

theorem rco_mem_T5 (c : Coord h) {t : G} (ht : t ∈ T) : c.rco t ∈ T5 := by
  rw [rco_of_mem c (h.T_le_C ht)]
  exact c.hιT _ ht

theorem rco_T_mul (c : Coord h) {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) : c.rco (t * t') = c.rco t * c.rco t' :=
  rco_mul c (h.T_le_C ht) (h.T_le_C ht')

theorem rco_T_inv (c : Coord h) {t : G} (ht : t ∈ T) : c.rco t⁻¹ = (c.rco t)⁻¹ := rco_inv c (h.T_le_C ht)

theorem rco_T_inj (c : Coord h) {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) (hh : c.rco t = c.rco t') : t = t' :=
  rco_inj c ht ht' hh

theorem exists_T_rco (c : Coord h) {m : Amb 5} (hm : m ∈ T5) :
    ∃ t ∈ T, c.rco t = m := by
  set Tco : Subgroup (Amb 5) := ((T.subgroupOf (centralizer ({x} : Set G))).map c.co).map
    (Fgrp 5).subtype with hTco
  have hle : Tco ≤ T5 := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have := c.hιT t (Subgroup.mem_subgroupOf.1 ht)
    exact this
  have hcard : Nat.card ↥Tco = 32 := by
    rw [hTco, Subgroup.card_map_of_injective (Fgrp 5).subtype_injective, ← card_T h]
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.T_le_C).toEquiv]
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun t : ↥(T.subgroupOf (centralizer ({x} : Set G))) =>
      (⟨c.co t, Subgroup.mem_map_of_mem _ t.2⟩ :
        ↥((T.subgroupOf (centralizer ({x} : Set G))).map c.co))) ⟨fun t₁ t₂ hq => ?_, ?_⟩
    · have h1 := congrArg (fun z : ↥((T.subgroupOf (centralizer ({x} : Set G))).map c.co) =>
        ((z : Fgrp 5) : Amb 5)) hq
      have h2 : c.rco (t₁ : G) = c.rco (t₂ : G) := by
        rw [rco_of_mem c t₁.1.2, rco_of_mem c t₂.1.2]
        exact h1
      exact Subtype.ext (Subtype.ext (rco_T_inj c (Subgroup.mem_subgroupOf.1 t₁.2)
        (Subgroup.mem_subgroupOf.1 t₂.2) h2))
    · rintro ⟨z, hz⟩
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz
      exact ⟨⟨u, hu⟩, rfl⟩
  have heq : Tco = T5 := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_T5])
  have hm' : m ∈ Tco := heq ▸ hm
  obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hm'
  exact ⟨(t : G), Subgroup.mem_subgroupOf.1 ht, by rw [rco_of_mem c t.2]; rfl⟩

theorem exists_lift_rco (c : Coord h) {M : Subgroup (Amb 5)} (hM : M ≤ T5) {m : Amb 5}
    (hm : m ∈ M) : ∃ g ∈ c.lift M, c.rco g = m := by
  obtain ⟨t, ht, htm⟩ := exists_T_rco (c := c) (hM hm)
  exact ⟨t, ⟨ht, htm ▸ hm⟩, htm⟩

theorem Q_eq_lift {c : Coord h} : Q = c.lift Qm := by
  ext g
  constructor
  · intro hg
    have hgT : g ∈ T := h.Q_le_T hg
    have hgC := h.T_le_C hgT
    refine ⟨hgT, ?_⟩
    have h1 : ((c.co ⟨g, hgC⟩ : Fgrp 5) : Amb 5).1 = 1 := (c.hιQ ⟨g, hgC⟩).2 (h.Q_le_CxK hg)
    rw [rco_of_mem c hgC]
    exact (Qm_coord (c.hιT _ hgT)).1 h1
  · rintro ⟨hgT, hm⟩
    have hgC := h.T_le_C hgT
    have h1 : ((c.co ⟨g, hgC⟩ : Fgrp 5) : Amb 5) ∈ Qm := by rw [← rco_of_mem c hgC]; exact hm
    have h2 : ((c.co ⟨g, hgC⟩ : Fgrp 5) : Amb 5).1 = 1 :=
      (Qm_coord (c.hιT _ hgT)).2 h1
    have h3 : g ∈ CxK x K := (c.hιQ ⟨g, hgC⟩).1 h2
    rw [h.hQ]
    exact ⟨hgT, h3⟩

theorem K_mem_Km {c : Coord h} {k : G} (hk : k ∈ K) :
    c.rco k ∈ Km := by
  rw [rco_of_mem c (h.K_le_C hk)]
  exact co_K_mem_Km h c.co c.co_surj c.co_ker c.hιQ hk

theorem P_eq_lift {c : Coord h} :
    T ⊓ K = c.lift Pm := by
  ext g
  constructor
  · rintro ⟨hgT, hgK⟩
    refine ⟨hgT, ?_⟩
    have : c.rco g ∈ T5 ⊓ Km := ⟨rco_mem_T5 c hgT, K_mem_Km (c := c) hgK⟩
    rwa [T5_inf_Km] at this
  · rintro ⟨hgT, hm⟩
    refine ⟨hgT, ?_⟩
    have hgC := h.T_le_C hgT
    have hmKm : c.rco g ∈ Km := by
      have : c.rco g ∈ T5 ⊓ Km := by rw [T5_inf_Km]; exact hm
      exact this.2
    exact mem_K_of_co_Km h c.co c.co_surj c.co_ker c.hιQ (c := ⟨g, hgC⟩) hgT (by
      rw [← rco_of_mem c hgC]; exact hmKm)

theorem x_co {c : Coord h} : c.rco x = f1 := by
  have hxC : x ∈ centralizer ({x} : Set G) := self_mem_centralizer_singleton
  rw [rco_of_mem c hxC]
  exact c.hι1

theorem card_lift {c : Coord h} {M : Subgroup (Amb 5)} (hM : M ≤ T5) :
    Nat.card (c.lift M) = Nat.card M := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun g : ↥(c.lift M) => (⟨c.rco g, rco_mem c g.2⟩ : ↥M)) ⟨fun g₁ g₂ hg => ?_, ?_⟩
  · exact Subtype.ext (rco_T_inj c g₁.2.1 g₂.2.1 (congrArg Subtype.val hg))
  · rintro ⟨m, hm⟩
    obtain ⟨g, hg, hgm⟩ := exists_lift_rco (c := c) hM hm
    exact ⟨⟨g, hg⟩, Subtype.ext hgm⟩

theorem card_lift_Pm {c : Coord h} :
    Nat.card (c.lift Pm) = 4 := by
  rw [card_lift (c := c) Pm_le_T5, card_Pm]

theorem card_lift_Rm {c : Coord h} :
    Nat.card (c.lift Rm) = 16 := by
  rw [card_lift (c := c) Rm_le_T5, card_Rm]

theorem lift_sq {c : Coord h} {M : Subgroup (Amb 5)} (hM : ∀ p ∈ M, p * p = 1) {g : G} (hg : g ∈ c.lift M) :
    g * g = 1 := by
  refine rco_T_inj c (T.mul_mem hg.1 hg.1) T.one_mem ?_
  rw [rco_T_mul c hg.1 hg.1, hM _ hg.2, rco_one]

theorem lift_comm {c : Coord h} {M : Subgroup (Amb 5)} (hM : ∀ p ∈ M, ∀ q ∈ M, p * q = q * p) {g g' : G}
    (hg : g ∈ c.lift M) (hg' : g' ∈ c.lift M) : g * g' = g' * g := by
  refine rco_T_inj c (T.mul_mem hg.1 hg'.1) (T.mul_mem hg'.1 hg.1) ?_
  rw [rco_T_mul c hg.1 hg'.1, rco_T_mul c hg'.1 hg.1, hM _ hg.2 _ hg'.2]

theorem Rg_le_T {c : Coord h} : c.lift Rm ≤ T := fun _ hg => hg.1

theorem Rg_norm_T {c : Coord h} {t r : G} (ht : t ∈ T) (hr : r ∈ c.lift Rm) :
    t * r * t⁻¹ ∈ c.lift Rm := by
  refine ⟨T.mul_mem (T.mul_mem ht hr.1) (T.inv_mem ht), ?_⟩
  rw [rco_T_mul c (T.mul_mem ht hr.1) (T.inv_mem ht), rco_T_mul c ht hr.1, rco_T_inv c ht]
  exact T5_norm_Rm (rco_mem_T5 c ht) hr.2

theorem R_eq_lift {c : Coord h} :
    (T ⊓ K) ⊔ Q = c.lift Rm := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact (P_eq_lift (c := c)).le.trans (lift_mono Pm_le_Rm)
    · exact (Q_eq_lift (c := c)).le.trans (lift_mono Qm_le_Rm)
  · rintro g ⟨hgT, hmem⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := Rm_prod _ hmem
    obtain ⟨p', hp', hpp'⟩ := exists_lift_rco (c := c) Pm_le_T5 hp
    obtain ⟨q', hq', hqq'⟩ := exists_lift_rco (c := c) Qm_le_T5 hq
    have hgpq : g = p' * q' := by
      refine rco_T_inj c hgT (T.mul_mem hp'.1 hq'.1) ?_
      rw [rco_T_mul c hp'.1 hq'.1, hpp', hqq']
      exact hpq
    rw [hgpq]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · exact (SetLike.ext_iff.1 (P_eq_lift (c := c)) p').2 hp'
    · exact (SetLike.ext_iff.1 (Q_eq_lift (c := c)) q').2 hq'

theorem K_inf_W_le_WK (h : IsAConfigW 5 x K T Q S a) :
    K ⊓ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤ pPrimeCoreOf 2 K := by
  refine le_pPrimeCoreOf_of_normal inf_le_left (fun g hg y hy => ⟨K.mul_mem (K.mul_mem hg hy.1)
    (K.inv_mem hg), W_norm (h.K_le_C hg) hy.2⟩) ?_
  exact Odd.of_dvd_nat (W_odd x) (Subgroup.card_dvd_of_le inf_le_right)

theorem exists_wC (c : Coord h) :
    ∃ w : ↥(centralizer ({x} : Set G)), (w : G) ∈ K ∧
      c.co w = ⟨wm, Km_le_Fgrp wm_mem_Km⟩ ∧
      (w : G) ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) ∧
      (∀ q ∈ Q, (w : G) * q = q * (w : G)) ∧ Odd (orderOf (w : G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRel, hRcard⟩ := Bk.aconfigW_five_R h
  have hR2 : IsPGroup 2 ↥((T ⊓ K) ⊔ Q) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hRN := Bk.aconfigW_five_R_le_normalizer_W h
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left h.Q_le_T
  obtain ⟨k, hkK, hk⟩ := co_K_onto h c.co c.co_surj c.co_ker c.hιQ (m := wm) wm_mem_Km
  have hkC : (k : G) ∈ centralizer ({x} : Set G) := k.2
  have hrk : c.rco (k : G) = wm := by rw [rco_of_mem c hkC]; exact hk
  have hP₀ : ∀ p ∈ T ⊓ K, ∃ p' ∈ T ⊓ K, ∃ w' ∈ pPrimeCoreOf 2 K,
      (k : G) * p * (k : G)⁻¹ = p' * w' := by
    intro p hp
    have hpC := h.T_le_C hp.1
    have hpP : c.rco p ∈ Pm := by
      have := (SetLike.ext_iff.1 (P_eq_lift (c := c)) p).1 hp
      exact this.2
    have hconj : c.rco ((k : G) * p * (k : G)⁻¹) = wm * c.rco p * wm⁻¹ := by
      rw [rco_mul c (mul_mem hkC hpC) (inv_mem hkC), rco_mul c hkC hpC, rco_inv c hkC, hrk]
    have hPm : c.rco ((k : G) * p * (k : G)⁻¹) ∈ Pm := by rw [hconj]; exact wm_norm_P _ hpP
    obtain ⟨p', hp'lift, hp'⟩ := exists_lift_rco (c := c) Pm_le_T5 hPm
    have hp'P : p' ∈ T ⊓ K := (SetLike.ext_iff.1 (P_eq_lift (c := c)) p').2 hp'lift
    refine ⟨p', hp'P, p'⁻¹ * ((k : G) * p * (k : G)⁻¹), ?_, by group⟩
    have hmemK : p'⁻¹ * ((k : G) * p * (k : G)⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem hp'P.2) (K.mul_mem (K.mul_mem hkK hp.2) (K.inv_mem hkK))
    have hmemC : p'⁻¹ * ((k : G) * p * (k : G)⁻¹) ∈ centralizer ({x} : Set G) := h.K_le_C hmemK
    have hco1 : c.rco (p'⁻¹ * ((k : G) * p * (k : G)⁻¹)) = 1 := by
      rw [rco_mul c (inv_mem (h.T_le_C hp'P.1)) (mul_mem (mul_mem hkC hpC) (inv_mem hkC)),
        rco_inv c (h.T_le_C hp'P.1), hp', inv_mul_cancel]
    have hW : (⟨p'⁻¹ * ((k : G) * p * (k : G)⁻¹), hmemC⟩ : ↥(centralizer ({x} : Set G))) ∈ Wc x := by
      rw [← c.co_ker]
      apply Subtype.ext
      rw [← rco_of_mem c hmemC, hco1]
      rfl
    exact K_inf_W_le_WK h ⟨hmemK, mem_Wc.1 hW⟩
  have hkN : (k : G) ∈ normalizer ((((T ⊓ K) ⊔ Q) ⊔ pPrimeCoreOf 2 K : Subgroup G) : Set G) :=
    Bk.mem_normalizer_of_conj_le (Bk.aconfigW_five_K_normalizes_sup h hkK hP₀)
  obtain ⟨w₀, hw₀, hnorm⟩ := Bk.frattini_odd hR2 hRN (TwoThin.card_pPrimeCoreOf_odd K) hkN
  have hw₀K : w₀ ∈ K := (Setup91.mem_pPrimeCoreOf_iff.1 hw₀).1
  have hw₀C : w₀ ∈ centralizer ({x} : Set G) := h.K_le_C hw₀K
  have hwK : w₀ * (k : G) ∈ K := K.mul_mem hw₀K hkK
  have hwC : w₀ * (k : G) ∈ centralizer ({x} : Set G) := h.K_le_C hwK
  have hw₀W : (⟨w₀, hw₀C⟩ : ↥(centralizer ({x} : Set G))) ∈ Wc x :=
    mem_Wc.2 (WK_le_W h hw₀)
  have hcow : c.co ⟨w₀ * (k : G), hwC⟩ = ⟨wm, Km_le_Fgrp wm_mem_Km⟩ := by
    have e : (⟨w₀ * (k : G), hwC⟩ : ↥(centralizer ({x} : Set G))) = ⟨w₀, hw₀C⟩ * k := rfl
    rw [e, map_mul, (c.co_ker _).2 hw₀W, one_mul]
    exact Subtype.ext hk
  refine ⟨⟨w₀ * (k : G), hwC⟩, hwK, hcow, hnorm, ?_, ?_⟩
  ·
    intro q hq
    have hqR : q ∈ (T ⊓ K) ⊔ Q := Subgroup.mem_sup_right hq
    have hwq1 : (w₀ * (k : G)) * q * (w₀ * (k : G))⁻¹ ∈ (T ⊓ K) ⊔ Q :=
      (Subgroup.mem_normalizer_iff.1 hnorm q).1 hqR
    have hNxK : w₀ * (k : G) ∈ NxK x K := ⟨hwC, Subgroup.le_normalizer hwK⟩
    have hwq2 : (w₀ * (k : G)) * q * (w₀ * (k : G))⁻¹ ∈ CxK x K :=
      (Subgroup.mem_normalizer_iff.1 (NxK_le_normalizer_CxK x K hNxK) q).1 (h.Q_le_CxK hq)
    have hwq : (w₀ * (k : G)) * q * (w₀ * (k : G))⁻¹ ∈ Q := by
      rw [h.hQ]
      exact ⟨hRT hwq1, hwq2⟩
    have hcomm : ⁅w₀ * (k : G), q⁆ ∈ pPrimeCoreOf 2 K := (h.Q_le_CxK hq).2.2.2 _ hwK
    have hcommQ : ⁅w₀ * (k : G), q⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hwq (Q.inv_mem hq)
    have h1 : ⁅w₀ * (k : G), q⁆ ∈ Q ⊓ pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
      ⟨hcommQ, WK_le_W h hcomm⟩
    rw [Q_inf_W h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  ·
    have hw3 : (w₀ * (k : G)) ^ 3 ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
      have hw3C : (w₀ * (k : G)) ^ 3 ∈ centralizer ({x} : Set G) := Subgroup.pow_mem _ hwC 3
      have e : (⟨(w₀ * (k : G)) ^ 3, hw3C⟩ : ↥(centralizer ({x} : Set G))) =
          (⟨w₀ * (k : G), hwC⟩ : ↥(centralizer ({x} : Set G))) ^ 3 := rfl
      have h1 : c.co (⟨(w₀ * (k : G)) ^ 3, hw3C⟩ : ↥(centralizer ({x} : Set G))) = 1 := by
        rw [e, map_pow, hcow]
        apply Subtype.ext
        show wm ^ 3 = 1
        have := wm_cube
        simpa [pow_succ, mul_assoc] using this
      exact mem_Wc.1 ((c.co_ker _).1 h1)
    have h1 : orderOf ((w₀ * (k : G)) ^ 3) ∣ Nat.card ↥(pPrimeCoreOf 2 (centralizer ({x} : Set G))) :=
      Subgroup.orderOf_dvd_natCard _ hw3
    have hodd3 : Odd (orderOf ((w₀ * (k : G)) ^ 3)) := Odd.of_dvd_nat (W_odd x) h1
    have h2 : orderOf (w₀ * (k : G)) ∣ 3 * orderOf ((w₀ * (k : G)) ^ 3) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    exact Odd.of_dvd_nat (Odd.mul (by decide) hodd3) h2

noncomputable def wC (c : Coord h) :
    ↥(centralizer ({x} : Set G)) := (exists_wC c).choose

theorem co_wC {c : Coord h} :
    ((c.co c.wC : Fgrp 5) : Amb 5) = wm := congrArg Subtype.val (exists_wC c).choose_spec.2.1

theorem wG_norm_R' {c : Coord h} :
    (c.wC : G) ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) :=
  (exists_wC c).choose_spec.2.2.1

theorem wG_cent_Q' {c : Coord h} :
    ∀ q ∈ Q, (c.wC : G) * q = q * (c.wC : G) := (exists_wC c).choose_spec.2.2.2.1

theorem w_mem_N {c : Coord h} :
    (c.wC : G) ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) := by
  rw [← R_eq_lift (c := c)]
  exact wG_norm_R' (c := c)

theorem rco_conj_w (c : Coord h) {g : G}
    (hg : g ∈ centralizer ({x} : Set G)) :
    c.rco ((c.wC : G) * g * (c.wC : G)⁻¹) = wm * c.rco g * wm⁻¹ := by
  have hw : (c.wC : G) ∈ centralizer ({x} : Set G) := c.wC.2
  rw [rco_mul c (mul_mem hw hg) (inv_mem hw), rco_mul c hw hg, rco_inv c hw, rco_of_mem c hw,
    co_wC (c := c)]

section Lift

variable (c : Coord h)

noncomputable def liftEl
    (i : Fin 16) : G :=
  (exists_lift_rco c Rm_le_T5 (el16_mem i)).choose

theorem liftEl_mem
    (i : Fin 16) : c.liftEl i ∈ c.lift Rm :=
  (exists_lift_rco c Rm_le_T5 (el16_mem i)).choose_spec.1

theorem rco_liftEl
    (i : Fin 16) : c.rco (c.liftEl i) = el16 i :=
  (exists_lift_rco c Rm_le_T5 (el16_mem i)).choose_spec.2

theorem liftEl_mem_C
    (i : Fin 16) : c.liftEl i ∈ centralizer ({x} : Set G) :=
  lift_mem_cent (c.liftEl_mem i)

theorem liftEl_mem_T
    (i : Fin 16) : c.liftEl i ∈ T :=
  (c.liftEl_mem i).1

theorem exists_liftEl
    {g : G} (hg : g ∈ c.lift Rm) : g = c.liftEl (idx16 (c.rco g)) := by
  have hr : c.rco g ∈ Rm := rco_mem c hg
  refine rco_inj c hg.1 (c.liftEl_mem_T _) ?_
  rw [c.rco_liftEl, el16_idx16 hr]

theorem liftEl_inj
    {i j : Fin 16} (hij : c.liftEl i = c.liftEl j) : i = j := by
  have := congrArg c.rco hij
  rw [c.rco_liftEl, c.rco_liftEl] at this
  have h2 := congrArg idx16 this
  rwa [idx16_el16, idx16_el16] at h2

theorem liftEl_xor
    (i j : Fin 16) : c.liftEl (xor16 i j) = c.liftEl i * c.liftEl j := by
  refine rco_inj c (c.liftEl_mem_T _) (T.mul_mem (c.liftEl_mem_T _) (c.liftEl_mem_T _)) ?_
  rw [rco_T_mul c (c.liftEl_mem_T _) (c.liftEl_mem_T _), c.rco_liftEl, c.rco_liftEl,
    c.rco_liftEl, el16_xor]

theorem liftEl_zero :
    c.liftEl 0 = 1 := by
  refine rco_inj c (c.liftEl_mem_T _) T.one_mem ?_
  rw [c.rco_liftEl, el16_zero, rco_one]

theorem liftEl_sq
    (i : Fin 16) : c.liftEl i * c.liftEl i = 1 := by
  rw [← c.liftEl_xor]
  have : xor16 i i = 0 := Fin.ext (by simp [xor16])
  rw [this, c.liftEl_zero]

noncomputable def rhoFun
    (n : G) (i : Fin 16) : Fin 16 :=
  idx16 (c.rco (n * c.liftEl i * n⁻¹))

variable {c}

theorem rhoFun_spec
    {n : G} (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G)) (i : Fin 16) :
    c.liftEl (c.rhoFun n i) = n * c.liftEl i * n⁻¹ := by
  have hr : n * c.liftEl i * n⁻¹ ∈ c.lift Rm := (mem_normalizer_iff.1 hn _).1 (c.liftEl_mem i)
  exact (exists_liftEl c hr).symm

theorem rhoFun_mul
    {n n' : G} (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G))
    (hn' : n' ∈ normalizer ((c.lift Rm : Subgroup G) : Set G)) (i : Fin 16) :
    c.rhoFun (n * n') i = c.rhoFun n (c.rhoFun n' i) := by
  apply liftEl_inj c
  rw [rhoFun_spec (mul_mem hn hn'), rhoFun_spec hn, rhoFun_spec hn']
  group

theorem rhoFun_one
    (i : Fin 16) : c.rhoFun 1 i = i := by
  apply liftEl_inj c
  rw [rhoFun_spec (one_mem _)]
  group

theorem rhoFun_xor
    {n : G} (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G))
    (i j : Fin 16) : c.rhoFun n (xor16 i j) = xor16 (c.rhoFun n i) (c.rhoFun n j) := by
  apply liftEl_inj c
  rw [rhoFun_spec hn, liftEl_xor, liftEl_xor, rhoFun_spec hn, rhoFun_spec hn]
  group

variable (c)

@[expose] noncomputable def rhoPerm
    (n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G))) : Perm (Fin 16) where
  toFun := c.rhoFun (n : G)
  invFun := c.rhoFun ((n : G)⁻¹)
  left_inv := fun i => by
    rw [← rhoFun_mul (inv_mem n.2) n.2, inv_mul_cancel, rhoFun_one]
  right_inv := fun i => by
    rw [← rhoFun_mul n.2 (inv_mem n.2), mul_inv_cancel, rhoFun_one]

@[expose] noncomputable def rhoG :
    ↥(normalizer ((c.lift Rm : Subgroup G) : Set G)) →* Perm (Fin 16) where
  toFun := c.rhoPerm
  map_one' := Equiv.ext fun i => rhoFun_one i
  map_mul' n n' := Equiv.ext fun i => by
    simp only [Equiv.Perm.mul_apply]
    exact rhoFun_mul n.2 n'.2 i

theorem rhoG_apply
    (n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G))) (i : Fin 16) :
    c.rhoG n i = c.rhoFun (n : G) i := rfl

theorem rhoG_spec
    (n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G))) (i : Fin 16) :
    c.liftEl (c.rhoG n i) = (n : G) * c.liftEl i * (n : G)⁻¹ :=
  rhoFun_spec n.2 i

theorem rhoG_xor
    (n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G))) (i j : Fin 16) :
    c.rhoG n (xor16 i j) = xor16 (c.rhoG n i) (c.rhoG n j) :=
  rhoFun_xor n.2 i j

theorem T_le_N :
    T ≤ normalizer ((c.lift Rm : Subgroup G) : Set G) := fun t ht =>
  (mem_normalizer_iff).2 fun r => ⟨fun hr => Rg_norm_T (c := c) ht hr, fun hr => by
    have := Rg_norm_T (c := c) (T.inv_mem ht) hr
    simpa [mul_assoc] using this⟩

theorem rhoG_T
    {t : G} (ht : t ∈ T) (i : Fin 16) :
    c.rhoG ⟨t, T_le_N c ht⟩ i = actF (c.rco t) i := by
  rw [rhoG_apply, rhoFun, actF]
  congr 1
  rw [rco_T_mul c (T.mul_mem ht (c.liftEl_mem_T i)) (T.inv_mem ht),
    rco_T_mul c ht (c.liftEl_mem_T i), rco_T_inv c ht, c.rco_liftEl]

theorem rhoG_wC
    (i : Fin 16) : c.rhoG ⟨(c.wC : G), w_mem_N (c := c)⟩ i = wHat i := by
  rw [rhoG_apply, rhoFun, ← actF_wm]
  unfold actF
  congr 1
  rw [rco_conj_w c (c.liftEl_mem_C i), c.rco_liftEl]

theorem R_le_N :
    c.lift Rm ≤ normalizer ((c.lift Rm : Subgroup G) : Set G) :=
  Subgroup.le_normalizer

theorem rhoG_R
    {r : G} (hr : r ∈ c.lift Rm) (i : Fin 16) :
    c.rhoG ⟨r, R_le_N c hr⟩ i = i := by
  apply liftEl_inj c
  rw [rhoG_spec]
  have hcomm : r * c.liftEl i = c.liftEl i * r :=
    lift_comm (c := c) (M := Rm) (fun p hp q hq => Rm_comm p hp q hq) hr (c.liftEl_mem i)
  rw [hcomm]
  group

end Lift

end Coord

end CFSG.GH74.GLS.C3.Layer1.Bk.W5
