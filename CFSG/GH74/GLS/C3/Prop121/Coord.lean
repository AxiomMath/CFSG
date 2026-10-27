module

public import CFSG.GH74.GLS.C3.Prop121.Interfaces
public import CFSG.GH74.GLS.C3.Layer2.LocalIso
public import CFSG.GH74.GLS.C3.Layer2.LocalRank

public section

namespace CFSG.GH74.GLS.C3.Prop121

namespace Coord

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem conj_mem_inv [Finite G] {Q : Subgroup G} {m : G} (hm : ∀ r ∈ Q, m * r * m⁻¹ ∈ Q) :
    ∀ r ∈ Q, m⁻¹ * r * m ∈ Q := by
  intro r hr
  let f : Q → Q := fun s => ⟨m * s * m⁻¹, hm s s.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : m * (a : G) * m⁻¹ = m * (b : G) * m⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h1)
  obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.1 hf ⟨r, hr⟩
  have h1 : m * (b : G) * m⁻¹ = r := congrArg Subtype.val hb
  have : m⁻¹ * r * m = b := by rw [← h1]; group
  rw [this]; exact b.2

theorem conj_le_of_two [Finite G] {Q : Subgroup G} (hQ : Nat.card Q = 4) {x z g : G}
    (hx : x ∈ Q) (hz : z ∈ Q) (hx1 : x ≠ 1) (hz1 : z ≠ 1) (hxz : x ≠ z)
    (hxg : g⁻¹ * x * g ∈ Q) (hzg : z = g * x * g⁻¹) : ∀ r ∈ Q, g * r * g⁻¹ ∈ Q := by
  set Q' : Subgroup G := Q.map (MulAut.conj g).toMonoidHom with hQ'
  have hQ'card : Nat.card Q' = 4 := by
    rw [hQ', Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hQ
  have hxQ' : x ∈ Q' := ⟨g⁻¹ * x * g, hxg, by simp [MulAut.conj_apply]; group⟩
  have hzQ' : z ∈ Q' := ⟨x, hx, by simp [MulAut.conj_apply, hzg]⟩
  have hD3 : 3 ≤ Nat.card ↥(Q ⊓ Q') := by
    have hsub : ({1, x, z} : Set G) ⊆ ((Q ⊓ Q' : Subgroup G) : Set G) := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact one_mem _
      · exact ⟨hx, hxQ'⟩
      · exact ⟨hz, hzQ'⟩
    have h3 : ({1, x, z} : Set G).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨1, x, z, hx1.symm, hz1.symm, hxz, rfl⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h3] at this
    rwa [← Nat.card_coe_set_eq] at this
  have hDdvd : Nat.card ↥(Q ⊓ Q') ∣ 4 := hQ ▸ Subgroup.card_dvd_of_le inf_le_left
  have hD4 : Nat.card ↥(Q ⊓ Q') = 4 := by
    have hle : Nat.card ↥(Q ⊓ Q') ≤ 4 := Nat.le_of_dvd (by norm_num) hDdvd
    rcases Nat.lt_or_ge (Nat.card ↥(Q ⊓ Q')) 4 with hlt | hge
    · have h3 : Nat.card ↥(Q ⊓ Q') = 3 := by omega
      rw [h3] at hDdvd
      omega
    · omega
  have hDeq : Q ⊓ Q' = Q' := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
  intro r hr
  have : g * r * g⁻¹ ∈ Q' := ⟨r, hr, by simp [MulAut.conj_apply]⟩
  rw [← hDeq] at this
  exact this.1

theorem comm_mul_comm {k₁ k₂ q₁ q₂ : G} (h12 : q₁ * k₂ = k₂ * q₁) (h21 : q₂ * k₁ = k₁ * q₂)
    (hqq : q₁ * q₂ = q₂ * q₁) : ⁅k₁ * q₁, k₂ * q₂⁆ = ⁅k₁, k₂⁆ := by
  have c21 : Commute q₂ k₁ := h21
  simp only [commutatorElement_def, mul_inv_rev]
  calc k₁ * q₁ * (k₂ * q₂) * (q₁⁻¹ * k₁⁻¹) * (q₂⁻¹ * k₂⁻¹)
      = k₁ * (q₁ * k₂) * q₂ * (q₁⁻¹ * k₁⁻¹) * (q₂⁻¹ * k₂⁻¹) := by group
    _ = k₁ * (k₂ * q₁) * q₂ * (q₁⁻¹ * k₁⁻¹) * (q₂⁻¹ * k₂⁻¹) := by rw [h12]
    _ = k₁ * k₂ * (q₁ * q₂) * (q₁⁻¹ * k₁⁻¹) * (q₂⁻¹ * k₂⁻¹) := by group
    _ = k₁ * k₂ * ((q₁ * q₂) * q₁⁻¹) * k₁⁻¹ * (q₂⁻¹ * k₂⁻¹) := by group
    _ = k₁ * k₂ * q₂ * k₁⁻¹ * (q₂⁻¹ * k₂⁻¹) := by
        rw [hqq]; group
    _ = k₁ * k₂ * (q₂ * k₁⁻¹) * (q₂⁻¹ * k₂⁻¹) := by group
    _ = k₁ * k₂ * (k₁⁻¹ * q₂) * (q₂⁻¹ * k₂⁻¹) := by rw [c21.inv_right.eq]
    _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by group

theorem commutator_eq_top_of_equiv {K : Type*} [Group K] {n : ℕ} (hn : 5 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) : commutator K = ⊤ := by
  have h1 := map_commutator_eq K e.toMonoidHom
  have h2 : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 e.surjective
  rw [h2] at h1
  have h3 : ⁅(⊤ : Subgroup (alternatingGroup (Fin n))), ⊤⁆ = ⊤ :=
    commutator_alternatingGroup_eq_top (by simpa using hn)
  rw [h3] at h1
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [h1, Subgroup.map_top, h2]

theorem le_commutator_of_equiv {K : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥K ≃* alternatingGroup (Fin n)) : K ≤ ⁅K, K⁆ := by
  have h := commutator_eq_top_of_equiv hn e
  have h2 := Subgroup.map_subtype_commutator K
  rw [h, Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2.le

end Generic

section Coordinates

variable {C : Type*} [Group C] {n : ℕ}

private def coordFst (ι : C ≃* Fgrp n) : C →* Perm (Fin n) :=
  (MonoidHom.fst _ _).comp ((Fgrp n).subtype.comp ι.toMonoidHom)

private def coordSnd (ι : C ≃* Fgrp n) : C →* Perm (Fin 4) :=
  (MonoidHom.snd _ _).comp ((Fgrp n).subtype.comp ι.toMonoidHom)

private theorem coordFst_apply (ι : C ≃* Fgrp n) (c : C) :
    coordFst ι c = ((ι c : Fgrp n) : Amb n).1 := rfl

private theorem coordSnd_apply (ι : C ≃* Fgrp n) (c : C) :
    coordSnd ι c = ((ι c : Fgrp n) : Amb n).2 := rfl

theorem V4_comm : ∀ a b : Perm (Fin 4), a * x4 = x4 * a → Perm.sign a = 1 → b * x4 = x4 * b →
    Perm.sign b = 1 → a * b = b * a := by decide

theorem sign_of_mem_K (hn : 5 ≤ n) {K : Subgroup C} (eK : K ≃* alternatingGroup (Fin n))
    (ι : C ≃* Fgrp n) {k : C} (hk : k ∈ K) : Perm.sign ((ι k : Fgrp n) : Amb n).1 = 1 := by
  let χ : alternatingGroup (Fin n) →* ℤˣ :=
    (Perm.sign.comp (coordFst ι)).comp (K.subtype.comp eK.symm.toMonoidHom)
  have hle : commutator (alternatingGroup (Fin n)) ≤ χ.ker :=
    Abelianization.commutator_subset_ker χ
  rw [commutator_alternatingGroup_eq_top (by simpa using hn)] at hle
  have h1 : χ (eK ⟨k, hk⟩) = 1 := MonoidHom.mem_ker.mp (hle (Subgroup.mem_top _))
  simpa [χ, coordFst_apply] using h1

theorem snd_of_mem_K (hn : 5 ≤ n) {K : Subgroup C} (eK : K ≃* alternatingGroup (Fin n))
    (ι : C ≃* Fgrp n) {k : C} (hk : k ∈ K) : ((ι k : Fgrp n) : Amb n).2 = 1 := by
  let V : Subgroup (Perm (Fin 4)) := centralizer {x4} ⊓ alternatingGroup (Fin 4)
  have : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (V4_comm a b
    (mem_centralizer_singleton_iff.1 a.2.1) (mem_alternatingGroup.1 a.2.2)
    (mem_centralizer_singleton_iff.1 b.2.1) (mem_alternatingGroup.1 b.2.2))⟩⟩
  have hmem : ∀ k ∈ K, coordSnd ι k ∈ V := by
    intro k hk
    refine ⟨mem_centralizer_singleton_iff.2 (ι k).2.1, mem_alternatingGroup.2 ?_⟩
    rw [coordSnd_apply, ← (ι k).2.2]
    exact sign_of_mem_K hn eK ι hk
  let f : alternatingGroup (Fin n) →* V :=
    ((coordSnd ι).comp (K.subtype.comp eK.symm.toMonoidHom)).codRestrict V
      (fun a => hmem _ (eK.symm a).2)
  have hle : commutator (alternatingGroup (Fin n)) ≤ f.ker :=
    Abelianization.commutator_subset_ker f
  rw [commutator_alternatingGroup_eq_top (by simpa using hn)] at hle
  have h1 : f (eK ⟨k, hk⟩) = 1 := MonoidHom.mem_ker.mp (hle (Subgroup.mem_top _))
  have h2 := congrArg Subtype.val h1
  simpa [f, coordSnd_apply] using h2

theorem exists_mem_K_of_sign (hn : 5 ≤ n) {K Q : Subgroup C} (eK : K ≃* alternatingGroup (Fin n))
    (ι : C ≃* Fgrp n) (hQ : ∀ c, ((ι c : Fgrp n) : Amb n).1 = 1 ↔ c ∈ Q)
    (hKQ : ∀ k ∈ K, k ∈ Q → k = 1) {σ : Perm (Fin n)} (hσ : Perm.sign σ = 1) :
    ∃ k ∈ K, ((ι k : Fgrp n) : Amb n).1 = σ := by
  have hinj : Function.Injective ((coordFst ι).comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have : (k : C) ∈ Q := (hQ k).1 hk
    exact Subtype.ext (hKQ k k.2 this)
  have hle : ((coordFst ι).comp K.subtype).range ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨k, rfl⟩
    exact mem_alternatingGroup.mpr (sign_of_mem_K hn eK ι k.2)
  have hcard : Nat.card (alternatingGroup (Fin n)) ≤
      Nat.card ((coordFst ι).comp K.subtype).range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr eK.toEquiv]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hσ' : σ ∈ alternatingGroup (Fin n) := mem_alternatingGroup.mpr hσ
  rw [← heq] at hσ'
  obtain ⟨k, hk⟩ := hσ'
  exact ⟨k, k.2, hk⟩

theorem mem_K_iff (hn : 5 ≤ n) {K Q : Subgroup C} (eK : K ≃* alternatingGroup (Fin n))
    (ι : C ≃* Fgrp n) (hQ : ∀ c, ((ι c : Fgrp n) : Amb n).1 = 1 ↔ c ∈ Q)
    (hKQ : ∀ k ∈ K, k ∈ Q → k = 1) (c : C) :
    c ∈ K ↔ Perm.sign ((ι c : Fgrp n) : Amb n).1 = 1 ∧ ((ι c : Fgrp n) : Amb n).2 = 1 := by
  refine ⟨fun hc => ⟨sign_of_mem_K hn eK ι hc, snd_of_mem_K hn eK ι hc⟩, fun ⟨h1, h2⟩ => ?_⟩
  obtain ⟨k, hk, hkc⟩ := exists_mem_K_of_sign hn eK ι hQ hKQ h1
  have h3 : ι k = ι c := Subtype.ext (Prod.ext hkc (by rw [snd_of_mem_K hn eK ι hk, h2]))
  rw [← ι.injective h3]
  exact hk

theorem mem_KQ_iff (hn : 5 ≤ n) {K Q : Subgroup C} (eK : K ≃* alternatingGroup (Fin n))
    (ι : C ≃* Fgrp n) (hQ : ∀ c, ((ι c : Fgrp n) : Amb n).1 = 1 ↔ c ∈ Q)
    (hKQ : ∀ k ∈ K, k ∈ Q → k = 1) (c : C) :
    (∃ k ∈ K, ∃ q ∈ Q, c = k * q) ↔ Perm.sign ((ι c : Fgrp n) : Amb n).1 = 1 := by
  constructor
  · rintro ⟨k, hk, q, hq, rfl⟩
    have h1 := sign_of_mem_K hn eK ι hk
    have h2 : ((ι q : Fgrp n) : Amb n).1 = 1 := (hQ q).2 hq
    have : ((ι (k * q) : Fgrp n) : Amb n).1 =
        ((ι k : Fgrp n) : Amb n).1 * ((ι q : Fgrp n) : Amb n).1 := by
      rw [map_mul]; rfl
    rw [this, h2, mul_one]
    exact h1
  · intro hs
    obtain ⟨k, hk, hkc⟩ := exists_mem_K_of_sign hn eK ι hQ hKQ hs
    refine ⟨k, hk, k⁻¹ * c, ?_, by simp⟩
    rw [← hQ]
    have : ((ι (k⁻¹ * c) : Fgrp n) : Amb n).1 =
        (((ι k : Fgrp n) : Amb n).1)⁻¹ * ((ι c : Fgrp n) : Amb n).1 := by
      rw [map_mul, map_inv]; rfl
    rw [this, hkc, inv_mul_cancel]

end Coordinates

section Pattern

variable {G : Type} [Group G] {n : ℕ} {x : G} {Q : Subgroup G}

theorem mem_Hgrp_iff {w g : Amb n} : g ∈ Hgrp n w ↔ g ∈ Fgrp n ∧ g * w = w * g := by
  unfold Hgrp
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem conj_comm_iff (a c g : G) :
    g * c * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * c * g⁻¹) ↔ c * a = a * c := by
  have e1 : g * c * g⁻¹ * (g * a * g⁻¹) = g * (c * a) * g⁻¹ := by group
  have e2 : g * a * g⁻¹ * (g * c * g⁻¹) = g * (a * c) * g⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro h
    exact mul_left_cancel (mul_right_cancel h)
  · intro h; rw [h]

theorem card_conj_pair (a b g : G) :
    Nat.card ↥(centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) =
      Nat.card ↥(centralizer ({g * a * g⁻¹} : Set G) ⊓ centralizer ({g * b * g⁻¹} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun c => ?_)
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact and_congr (conj_comm_iff a c g).symm (conj_comm_iff b c g).symm

theorem card_cent_pair (ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n)) {z : G}
    (hz : z ∈ centralizer ({x} : Set G)) :
    Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G)) =
      Nat.card ↥(Hgrp n ((ι ⟨z, hz⟩ : Fgrp n) : Amb n)) := by
  have key : ∀ a : ↥(centralizer ({x} : Set G)), (a : G) ∈ centralizer ({z} : Set G) ↔
      ((ι a : Fgrp n) : Amb n) ∈ Hgrp n ((ι ⟨z, hz⟩ : Fgrp n) : Amb n) := by
    intro a
    rw [mem_Hgrp_iff, mem_centralizer_singleton_iff]
    refine ⟨fun ha => ⟨(ι a).2, ?_⟩, fun ha => ?_⟩
    · have h1 : a * ⟨z, hz⟩ = ⟨z, hz⟩ * a := Subtype.ext ha
      have h2 := congrArg ι h1
      rw [map_mul, map_mul] at h2
      exact congrArg Subtype.val h2
    · have h1 : ι (a * ⟨z, hz⟩) = ι (⟨z, hz⟩ * a) := by
        rw [map_mul, map_mul]; exact Subtype.ext ha.2
      exact congrArg Subtype.val (ι.injective h1)
  refine Nat.card_congr
    { toFun := fun a => ⟨((ι ⟨a.1, a.2.1⟩ : Fgrp n) : Amb n), (key ⟨a.1, a.2.1⟩).1 a.2.2⟩
      invFun := fun g =>
        ⟨((ι.symm ⟨g.1, (mem_Hgrp_iff.1 g.2).1⟩ : ↥(centralizer ({x} : Set G))) : G),
          (ι.symm ⟨g.1, (mem_Hgrp_iff.1 g.2).1⟩).2,
          (key _).2 (by simp)⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }

theorem card_cent_x (ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n)) :
    Nat.card ↥(centralizer ({x} : Set G)) = 4 * n.factorial := by
  rw [Nat.card_congr ι.toEquiv, card_Fgrp]

structure CoordData (n : ℕ) (x : G) (Q : Subgroup G)
    (ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n)) : Prop where
  x_sq : x ^ 2 = 1
  x_ne : x ≠ 1
  x_mem : x ∈ Q
  Q_card : Nat.card Q = 4
  Q_sq : ∀ q ∈ Q, q ^ 2 = 1
  Q_comm : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q
  Q_le_C : Q ≤ centralizer ({x} : Set G)
  Q_normal : ∀ c ∈ centralizer ({x} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q
  ι_x : ((ι (xC x) : Fgrp n) : Amb n) = x0 n
  ι_Q : ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp n) : Amb n).1 = 1 ↔ (c : G) ∈ Q)

variable {ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n)}

theorem card_cent_q (hC : CoordData n x Q ι) (hF : FnFacts n) {q : G} (hq : q ∈ Q) (hq1 : q ≠ 1)
    (hqx : q ≠ x) :
    Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({q} : Set G)) = 2 * n.factorial := by
  have hqC : q ∈ centralizer ({x} : Set G) := hC.Q_le_C hq
  rw [card_cent_pair ι hqC]
  refine hF.card_C_q _ (ι ⟨q, hqC⟩).2 ((hC.ι_Q ⟨q, hqC⟩).2 hq) ?_ ?_
  · intro h1
    apply hq1
    have h2 : ι ⟨q, hqC⟩ = 1 := Subtype.ext h1
    have h3 : (⟨q, hqC⟩ : ↥(centralizer ({x} : Set G))) = 1 :=
      ι.injective (h2.trans (map_one ι).symm)
    exact congrArg Subtype.val h3
  · intro h1
    apply hqx
    have h2 : ι ⟨q, hqC⟩ = ι (xC x) := Subtype.ext (h1.trans hC.ι_x.symm)
    exact congrArg Subtype.val (ι.injective h2)

theorem isConj_x_of_mem_Q (hC : CoordData n x Q ι) (hF : FnFacts n)
    (hP : PatternFacts G n) {q : G} (hq : q ∈ Q) (hq1 : q ≠ 1) (hqx : q ≠ x) : IsConj x q := by
  obtain ⟨hP1, hP2⟩ := hP
  have hordq : orderOf q = 2 := orderOf_eq_prime (hC.Q_sq q hq) hq1
  have hordx : orderOf x = 2 := orderOf_eq_prime hC.x_sq hC.x_ne
  have hdvd : 2 * n.factorial ∣ Nat.card ↥(centralizer ({q} : Set G)) := by
    have := Subgroup.card_dvd_of_le
      (inf_le_right : centralizer ({x} : Set G) ⊓ centralizer ({q} : Set G) ≤
        centralizer ({q} : Set G))
    rwa [card_cent_q hC hF hq hq1 hqx] at this
  have hq4 : Nat.card ↥(centralizer ({q} : Set G)) = 4 * n.factorial := by
    rcases hP1 q hordq with h | h
    · exact h
    · exact absurd (h ▸ hdvd) hF.not_dvd
  exact hP2 x q hordx hordq (card_cent_x ι) hq4

theorem conj_normalizes [Finite G] (hC : CoordData n x Q ι) (hF : FnFacts n) {g : G}
    (hg : g⁻¹ * x * g ∈ Q) : ∀ r ∈ Q, g * r * g⁻¹ ∈ Q := by
  by_cases hzx : g * x * g⁻¹ = x
  · have hgC : g ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [hzx]
    exact hC.Q_normal g hgC
  · have hxe : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    have hqx : g⁻¹ * x * g ≠ x := by
      intro hqx
      apply hzx
      calc g * x * g⁻¹ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hqx]
        _ = x := by group
    have hq1 : g⁻¹ * x * g ≠ 1 := by
      intro hq1
      apply hC.x_ne
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := hxe
        _ = 1 := by rw [hq1]; group
    have hcardq := card_cent_q hC hF hg hq1 hqx
    have hz : g * x * g⁻¹ ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hxq : x * (g⁻¹ * x * g) = (g⁻¹ * x * g) * x := hC.Q_comm x hC.x_mem _ hg
      calc g * x * g⁻¹ * x = g * x * g⁻¹ * (g * (g⁻¹ * x * g) * g⁻¹) := congrArg _ hxe
        _ = g * (x * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * x) * g⁻¹ := by rw [hxq]
        _ = x * (g * x * g⁻¹) := by group
    have hcardz : Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({g * x * g⁻¹} : Set G)) =
        2 * n.factorial := by
      have h1 := card_conj_pair x (g * x * g⁻¹) g⁻¹
      have e1 : g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g := by rw [inv_inv]
      have e2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      have h2 : centralizer ({g⁻¹ * x * g} : Set G) ⊓ centralizer ({x} : Set G) =
          centralizer ({x} : Set G) ⊓ centralizer ({g⁻¹ * x * g} : Set G) := inf_comm _ _
      rw [h1, e1, e2, h2]
      exact hcardq
    have hww : ((ι ⟨g * x * g⁻¹, hz⟩ : Fgrp n) : Amb n) *
        ((ι ⟨g * x * g⁻¹, hz⟩ : Fgrp n) : Amb n) = 1 := by
      have h1 : (⟨g * x * g⁻¹, hz⟩ : ↥(centralizer ({x} : Set G))) * ⟨g * x * g⁻¹, hz⟩ = 1 := by
        apply Subtype.ext
        show g * x * g⁻¹ * (g * x * g⁻¹) = 1
        have : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        rw [this, ← sq, hC.x_sq]; group
      have h2 := congrArg ι h1
      rw [map_mul, map_one] at h2
      exact congrArg Subtype.val h2
    obtain ⟨hw1, -, -⟩ := hF.card_C_inv _ (ι ⟨g * x * g⁻¹, hz⟩).2 hww
      (by rw [← card_cent_pair ι hz]; exact hcardz)
    have hzQ : g * x * g⁻¹ ∈ Q := (hC.ι_Q ⟨g * x * g⁻¹, hz⟩).1 hw1
    have hz1 : g * x * g⁻¹ ≠ 1 := by
      intro h1
      apply hC.x_ne
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, h1]; group
    exact conj_le_of_two hC.Q_card hC.x_mem hzQ hC.x_ne hz1 (fun h => hzx h.symm) hg rfl

theorem transitive_of_coord [Finite G] (hC : CoordData n x Q ι) (hF : FnFacts n)
    (hP : PatternFacts G n) :
    ∀ q ∈ Q, q ≠ 1 → ∃ m : G, (∀ r ∈ Q, m * r * m⁻¹ ∈ Q) ∧ m * x * m⁻¹ = q := by
  intro q hq hq1
  by_cases hqx : q = x
  · exact ⟨1, fun r hr => by simpa using hr, by simp [hqx]⟩
  · obtain ⟨m, hm⟩ := isConj_iff.1 (isConj_x_of_mem_Q hC hF hP hq hq1 hqx)
    refine ⟨m, ?_, hm⟩
    have h1 := conj_normalizes hC hF (g := m⁻¹) (by rw [inv_inv, hm]; exact hq)
    intro r hr
    have h2 := conj_mem_inv (m := m⁻¹) (Q := Q) (fun s hs => by simpa using h1 s hs) r hr
    simpa using h2

end Pattern

section U0

variable {G : Type} [Group G] {n : ℕ} {x : G} {K Q : Subgroup G}

theorem exists_involution_odd (hn : 2 ≤ n) :
    ∃ w q : Fgrp n, w * w = 1 ∧ Perm.sign (w : Amb n).1 = -1 ∧ (q : Amb n).1 = 1 ∧
      w * q ≠ q * w := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hw : ((swap a b, swap 0 1) : Amb n) ∈ Fgrp n := by
    refine ⟨?_, ?_⟩
    · show swap (0 : Fin 4) 1 * x4 = x4 * swap 0 1
      decide
    · show Perm.sign (swap a b) = Perm.sign (swap (0 : Fin 4) 1)
      rw [sign_swap hab, sign_swap (by decide)]
  have hq : ((1, swap 0 2 * swap 1 3) : Amb n) ∈ Fgrp n := by
    refine ⟨?_, ?_⟩
    · show swap (0 : Fin 4) 2 * swap 1 3 * x4 = x4 * (swap 0 2 * swap 1 3)
      decide
    · show Perm.sign (1 : Perm (Fin n)) = Perm.sign (swap (0 : Fin 4) 2 * swap 1 3)
      rw [map_one, map_mul, sign_swap (by decide), sign_swap (by decide)]; rfl
  refine ⟨⟨_, hw⟩, ⟨_, hq⟩, ?_, ?_, rfl, ?_⟩
  · exact Subtype.ext (Prod.ext (swap_mul_self _ _) (swap_mul_self _ _))
  · show Perm.sign (swap a b) = -1
    exact sign_swap hab
  · intro h
    have := congrArg (fun p : Fgrp n => (p : Amb n).2) h
    exact (by decide : swap (0 : Fin 4) 1 * (swap 0 2 * swap 1 3) ≠
      (swap 0 2 * swap 1 3) * swap 0 1) this

theorem exists_u0_of_coord (hn : 2 ≤ n) (ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n))
    (hQ : ∀ c, ((ι c : Fgrp n) : Amb n).1 = 1 ↔ (c : G) ∈ Q)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, ∀ c : ↥(centralizer ({x} : Set G)), (c : G) = k * q →
      Perm.sign ((ι c : Fgrp n) : Amb n).1 = 1)
    (hKnorm : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hQnorm : ∀ c ∈ centralizer ({x} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) :
    ∃ u : G, u ^ 2 = 1 ∧ u * x = x * u ∧ (∀ k ∈ K, u * k * u⁻¹ ∈ K) ∧
      (∀ k ∈ K, ∀ q ∈ Q, u ≠ k * q) ∧ (∃ q ∈ Q, u * q ≠ q * u) ∧
      (∀ r ∈ Q, u * r * u⁻¹ ∈ Q) := by
  obtain ⟨w, q0, hw2, hws, hq1, hwq⟩ := exists_involution_odd hn
  let u : ↥(centralizer ({x} : Set G)) := ι.symm w
  let q : ↥(centralizer ({x} : Set G)) := ι.symm q0
  have hu : ι u = w := ι.apply_symm_apply w
  have hq : ι q = q0 := ι.apply_symm_apply q0
  refine ⟨u, ?_, ?_, ?_, ?_, ⟨q, ?_, ?_⟩, ?_⟩
  · have h1 : u * u = 1 := ι.injective (by rw [map_mul, hu, hw2, map_one])
    rw [sq]
    exact congrArg Subtype.val h1
  · exact mem_centralizer_singleton_iff.1 u.2
  · intro k hk
    exact hKnorm u u.2 k hk
  · intro k hk r hr hur
    have := hKQ k hk r hr u hur
    rw [hu, hws] at this
    exact absurd this (by decide)
  · exact (hQ q).1 (by rw [hq]; exact hq1)
  · intro hcomm
    apply hwq
    have h1 : u * q = q * u := Subtype.ext hcomm
    have := congrArg ι h1
    rw [map_mul, map_mul, hu, hq] at this
    exact this
  · intro r hr
    exact hQnorm u u.2 r hr

end U0

section KNorm

variable {G : Type} [Group G] {K Q : Subgroup G} {n : ℕ}

theorem K_norm_of [Finite G] (hn : 5 ≤ n) (eK : ↥K ≃* alternatingGroup (Fin n))
    (hcomm : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k) (hQcomm : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q)
    (hCQ : ∀ c : G, (∀ q ∈ Q, c * q = q * c) → ∃ k ∈ K, ∃ q ∈ Q, c = k * q) :
    ∀ m : G, (∀ r ∈ Q, m * r * m⁻¹ ∈ Q) → ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
  intro m hm
  have hm' := conj_mem_inv hm
  have hKK : K ≤ ⁅K, K⁆ := le_commutator_of_equiv hn eK
  have hcent : ∀ k ∈ K, ∃ k' ∈ K, ∃ q' ∈ Q, m * k * m⁻¹ = k' * q' := by
    intro k hk
    apply hCQ
    intro r hr
    have h1 := hcomm k hk (m⁻¹ * r * m) (hm' r hr)
    calc m * k * m⁻¹ * r = m * (k * (m⁻¹ * r * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * r * m) * k) * m⁻¹ := by rw [h1]
      _ = r * (m * k * m⁻¹) := by group
  have hle : ⁅K, K⁆ ≤ K.comap (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨k₁, hk₁, q₁, hq₁, e₁⟩ := hcent a ha
    obtain ⟨k₂, hk₂, q₂, hq₂, e₂⟩ := hcent b hb
    show m * ⁅a, b⁆ * m⁻¹ ∈ K
    have h1 : m * ⁅a, b⁆ * m⁻¹ = ⁅k₁ * q₁, k₂ * q₂⁆ := by
      rw [← e₁, ← e₂]
      simp only [commutatorElement_def]
      group
    rw [h1, comm_mul_comm (hcomm k₂ hk₂ q₁ hq₁).symm (hcomm k₁ hk₁ q₂ hq₂).symm
      (hQcomm q₁ hq₁ q₂ hq₂)]
    exact Subgroup.commutator_le_self K (Subgroup.commutator_mem_commutator hk₁ hk₂)
  intro k hk
  exact hle (hKK hk)

end KNorm

end Coord

section Config

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem exists_coord (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) :
    ∃ ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n), ((ι (xC x) : Fgrp n) : Amb n) = x0 n ∧
      ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp n) : Amb n).1 = 1 ↔ (c : G) ∈ Q) := by
  have hn5 : 5 ≤ n := by omega
  have hnt : ∃ t ∈ T, ∃ q ∈ Q, t * q ≠ q * t := by
    rcases hn with rfl | hn67
    · obtain ⟨y, hyT, -, -, q, hq, hyq⟩ := h.fiveCase rfl
      exact ⟨y, hyT, q, hq, hyq⟩
    · exact h.exists_noncomm hn67 hG4
  exact h.exists_equiv_Fgrp hn5 hnt

theorem coordData_of_config (h : IsAConfig n x K T Q S a)
    {ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n)}
    (hι1 : ((ι (xC x) : Fgrp n) : Amb n) = x0 n)
    (hι2 : ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp n) : Amb n).1 = 1 ↔ (c : G) ∈ Q)) :
    Coord.CoordData n x Q ι :=
  { x_sq := h.x_sq, x_ne := h.x_ne_one, x_mem := h.x_mem_Q, Q_card := h.card_Q,
    Q_sq := fun _ hq => h.Q_sq hq, Q_comm := fun _ hq _ hr => h.Q_comm hq hr,
    Q_le_C := h.Q_le_T.trans h.T_le_C, Q_normal := h.Q_normal, ι_x := hι1, ι_Q := hι2 }

private theorem K_inf_Q_sub (hn5 : 5 ≤ n) (h : IsAConfig n x K T Q S a) :
    ∀ k ∈ K.subgroupOf (centralizer ({x} : Set G)),
      k ∈ Q.subgroupOf (centralizer ({x} : Set G)) → k = 1 := by
  intro k hk hkQ
  have h1 : (k : G) ∈ K ⊓ Q := ⟨Subgroup.mem_subgroupOf.1 hk, Subgroup.mem_subgroupOf.1 hkQ⟩
  rw [h.K_inf_Q hn5, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem K_iff (hn : n = 5 ∨ n = 6 ∨ n = 7) (h : IsAConfig n x K T Q S a)
    {ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n)}
    (hι2 : ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp n) : Amb n).1 = 1 ↔ (c : G) ∈ Q))
    (c : ↥(centralizer ({x} : Set G))) :
    (c : G) ∈ K ↔
      Perm.sign ((ι c : Fgrp n) : Amb n).1 = 1 ∧ ((ι c : Fgrp n) : Amb n).2 = 1 := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨e⟩ := h.K_equiv_alt
  have := Coord.mem_K_iff hn5 (K := K.subgroupOf (centralizer ({x} : Set G)))
    (Q := Q.subgroupOf (centralizer ({x} : Set G)))
    ((Subgroup.subgroupOfEquivOfLe h.K_le_C).trans e) ι
    (fun c => (hι2 c).trans Subgroup.mem_subgroupOf.symm) (K_inf_Q_sub hn5 h) c
  rwa [Subgroup.mem_subgroupOf] at this

theorem KQ_iff (hn : n = 5 ∨ n = 6 ∨ n = 7) (h : IsAConfig n x K T Q S a)
    {ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n)}
    (hι2 : ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp n) : Amb n).1 = 1 ↔ (c : G) ∈ Q))
    (c : ↥(centralizer ({x} : Set G))) :
    (∃ k ∈ K, ∃ q ∈ Q, (c : G) = k * q) ↔ Perm.sign ((ι c : Fgrp n) : Amb n).1 = 1 := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨e⟩ := h.K_equiv_alt
  rw [← Coord.mem_KQ_iff hn5 (K := K.subgroupOf (centralizer ({x} : Set G)))
    (Q := Q.subgroupOf (centralizer ({x} : Set G)))
    ((Subgroup.subgroupOfEquivOfLe h.K_le_C).trans e) ι
    (fun c => (hι2 c).trans Subgroup.mem_subgroupOf.symm) (K_inf_Q_sub hn5 h) c]
  constructor
  · rintro ⟨k, hk, q, hq, hc⟩
    exact ⟨⟨k, h.K_le_C hk⟩, Subgroup.mem_subgroupOf.2 hk,
      ⟨q, (h.Q_le_T.trans h.T_le_C) hq⟩, Subgroup.mem_subgroupOf.2 hq, Subtype.ext hc⟩
  · rintro ⟨k, hk, q, hq, hc⟩
    exact ⟨k, Subgroup.mem_subgroupOf.1 hk, q, Subgroup.mem_subgroupOf.1 hq,
      congrArg Subtype.val hc⟩

theorem centralizer_Q_eq (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) (hF : FnFacts n) :
    ∀ c : G, (∀ q ∈ Q, c * q = q * c) → ∃ k ∈ K, ∃ q ∈ Q, c = k * q := by
  obtain ⟨ι, -, hι2⟩ := exists_coord hn hG4 h
  intro c hc
  have hcC : c ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 (hc x h.x_mem_Q)
  have hsign : Perm.sign ((ι ⟨c, hcC⟩ : Fgrp n) : Amb n).1 = 1 := by
    rw [← hF.centralizes_iff _ (ι ⟨c, hcC⟩).2]
    intro q' hq' hq'1
    obtain ⟨q'', hq''⟩ : ∃ q'' : ↥(centralizer ({x} : Set G)), ι q'' = ⟨q', hq'⟩ :=
      ι.surjective _
    have hq''Q : (q'' : G) ∈ Q := (hι2 q'').1 (by rw [hq'']; exact hq'1)
    have h1 : (⟨c, hcC⟩ : ↥(centralizer ({x} : Set G))) * q'' = q'' * ⟨c, hcC⟩ :=
      Subtype.ext (hc q'' hq''Q)
    have h2 := congrArg ι h1
    rw [map_mul, map_mul, hq''] at h2
    exact congrArg Subtype.val h2
  exact (KQ_iff hn h hι2 ⟨c, hcC⟩).2 hsign

theorem transitive (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) (hF : FnFacts n) (hP : PatternFacts G n) :
    ∀ q ∈ Q, q ≠ 1 → ∃ m : G, (∀ r ∈ Q, m * r * m⁻¹ ∈ Q) ∧ m * x * m⁻¹ = q := by
  obtain ⟨ι, hι1, hι2⟩ := exists_coord hn hG4 h
  exact Coord.transitive_of_coord (coordData_of_config h hι1 hι2) hF hP

theorem exists_u0 (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) :
    ∃ u : G, u ^ 2 = 1 ∧ u * x = x * u ∧ (∀ k ∈ K, u * k * u⁻¹ ∈ K) ∧
      (∀ k ∈ K, ∀ q ∈ Q, u ≠ k * q) ∧ (∃ q ∈ Q, u * q ≠ q * u) ∧
      (∀ r ∈ Q, u * r * u⁻¹ ∈ Q) := by
  obtain ⟨ι, -, hι2⟩ := exists_coord hn hG4 h
  exact Coord.exists_u0_of_coord (by omega) ι hι2
    (fun k hk q hq c hc => (KQ_iff hn h hι2 c).1 ⟨k, hk, q, hq, hc⟩) h.normalInC h.Q_normal

theorem K_norm (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) (hF : FnFacts n) :
    ∀ m : G, (∀ r ∈ Q, m * r * m⁻¹ ∈ Q) → ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
  obtain ⟨e⟩ := h.K_equiv_alt
  exact Coord.K_norm_of (by omega) e (fun k hk q hq => ((h.mem_Q_iff q).1 hq).2 k hk)
    (fun q hq r hr => h.Q_comm hq hr) (centralizer_Q_eq hn hG4 h hF)

end Config

end CFSG.GH74.GLS.C3.Prop121
