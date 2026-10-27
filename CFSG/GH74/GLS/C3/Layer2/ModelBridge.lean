module

public import CFSG.GH74.GLS.C3.Layer2.Assembly
public import CFSG.GH74.GLS.C3.Layer2.FinModel
public import CFSG.GH74.GLS.C3.Layer2.LocalBasic

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

structure Coord [NeZero n] (_h : IsAConfig n x K T Q S a) where
  ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n)
  ι_x : ((ι (xC x) : Fgrp n) : Amb n) = x0 n
  ι_Q : ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp n) : Amb n).1 = 1 ↔ (c : G) ∈ Q)
  ι_T : ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ T ↔ ((ι c : Fgrp n) : Amb n) ∈ T0 n

theorem IsAConfig.a_conj_x_ne (h : IsAConfig n x K T Q S a) : a * x * a⁻¹ ≠ x := by
  intro hax
  have haC : a ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.2 (calc a * x = (a * x * a⁻¹) * a := by group
      _ = x * a := by rw [hax])
  have hSle : T ⊔ zpowers a ≤ S := sup_le h.T_lt_S.le (zpowers_le.2 h.a_mem.1)
  have hp : IsPGroup 2 ↥(T ⊔ zpowers a) := IsPGroup.to_le h.sylowS.isPGroup hSle
  have hsup : T ⊔ zpowers a ≤ centralizer ({x} : Set G) :=
    sup_le h.T_le_C (zpowers_le.2 haC)
  have heq := h.sylowT.eq_of_le le_sup_left hsup hp
  have hmem : a ∈ T ⊔ zpowers a := (le_sup_right : zpowers a ≤ T ⊔ zpowers a) (mem_zpowers a)
  rw [heq] at hmem
  exact h.a_mem.2.2.1 hmem

theorem IsAConfig.conj_x_comm (h : IsAConfig n x K T Q S a) {t : G} (ht : t ∈ T) :
    t * (a * x * a⁻¹) = (a * x * a⁻¹) * t := by
  have ht' : a⁻¹ * t * a ∈ T := by
    have := (mem_normalizer_iff.1 (inv_mem h.a_mem.2.1) t).1 ht
    simpa using this
  have h1 : (a⁻¹ * t * a) * x = x * (a⁻¹ * t * a) :=
    mem_centralizer_singleton_iff.1 (h.T_le_C ht')
  calc t * (a * x * a⁻¹) = a * ((a⁻¹ * t * a) * x) * a⁻¹ := by group
    _ = a * (x * (a⁻¹ * t * a)) * a⁻¹ := by rw [h1]
    _ = (a * x * a⁻¹) * t := by group

theorem IsAConfig.conj_x_mem (h : IsAConfig n x K T Q S a) : a * x * a⁻¹ ∈ T :=
  (mem_normalizer_iff.1 h.a_mem.2.1 x).1 h.x_mem_T

theorem IsAConfig.inv_conj_x (h : IsAConfig n x K T Q S a) : a⁻¹ * x * a = a * x * a⁻¹ := by
  have h1 : a ^ 2 * x = x * a ^ 2 := mem_centralizer_singleton_iff.1 (h.T_le_C h.a_mem.2.2.2)
  have h2 : a ^ 2 * x * (a ^ 2)⁻¹ = x := by rw [h1]; group
  calc a⁻¹ * x * a = a⁻¹ * (a ^ 2 * x * (a ^ 2)⁻¹) * a := by rw [h2]
    _ = a * x * a⁻¹ := by group

namespace IsAConfig

theorem factorization_C (h : IsAConfig n x K T Q S a) (hT : Nat.card T = 64) :
    (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 = 6 := by
  have h1 := h.sylowT.card_eq
  rw [hT, show (64 : ℕ) = 2 ^ 6 by norm_num] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

theorem sup_le_centralizer_v (h : IsAConfig n x K T Q S a) :
    T ⊔ zpowers a ≤ centralizer ({x * (a * x * a⁻¹)} : Set G) := by
  refine sup_le (fun t ht => ?_) (zpowers_le.2 ?_)
  · rw [mem_centralizer_singleton_iff]
    have h1 : t * x = x * t := mem_centralizer_singleton_iff.1 (h.T_le_C ht)
    have h2 := h.conj_x_comm ht
    calc t * (x * (a * x * a⁻¹)) = (t * x) * (a * x * a⁻¹) := (mul_assoc t x _).symm
      _ = x * (t * (a * x * a⁻¹)) := by rw [h1, mul_assoc]
      _ = x * ((a * x * a⁻¹) * t) := by rw [h2]
      _ = x * (a * x * a⁻¹) * t := (mul_assoc x _ t).symm
  · rw [mem_centralizer_singleton_iff]
    have h3 : a * (a * x * a⁻¹) * a⁻¹ = x := by
      have := h.inv_conj_x
      calc a * (a * x * a⁻¹) * a⁻¹ = a * (a⁻¹ * x * a) * a⁻¹ := by rw [this]
        _ = x := by group
    have h4 : x * (a * x * a⁻¹) = (a * x * a⁻¹) * x := h.conj_x_comm h.x_mem_T
    calc a * (x * (a * x * a⁻¹)) = (a * x * a⁻¹) * (a * (a * x * a⁻¹) * a⁻¹) * a := by group
      _ = (a * x * a⁻¹) * x * a := by rw [h3]
      _ = x * (a * x * a⁻¹) * a := by rw [← h4]

theorem two_pow_seven_dvd (h : IsAConfig n x K T Q S a) (hT : Nat.card T = 64) :
    2 ^ 7 ∣ Nat.card ↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) := by
  have hSle : T ⊔ zpowers a ≤ S := sup_le h.T_lt_S.le (zpowers_le.2 h.a_mem.1)
  have hp : IsPGroup 2 ↥(T ⊔ zpowers a) := IsPGroup.to_le h.sylowS.isPGroup hSle
  have haS1 : a ∈ T ⊔ zpowers a := (le_sup_right : zpowers a ≤ T ⊔ zpowers a) (mem_zpowers a)
  have hlt : T < T ⊔ zpowers a := lt_of_le_of_ne le_sup_left (fun heq => by
    rw [← heq] at haS1
    exact h.a_mem.2.2.1 haS1)
  have hcard := Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk, hT] at hcard
  have hk7 : 7 ≤ k := by
    by_contra hk7
    have : 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (pow_dvd_pow 2 hk7).trans (hk ▸ Subgroup.card_dvd_of_le h.sup_le_centralizer_v)

theorem not_isConj_x_v (h : IsAConfig n x K T Q S a) (hT : Nat.card T = 64) :
    ¬ IsConj x (x * (a * x * a⁻¹)) := by
  intro hc
  obtain ⟨e⟩ := nonempty_centralizer_equiv_of_isConj hc
  have hcard := Nat.card_congr e.toEquiv
  have h7 := h.two_pow_seven_dvd hT
  rw [← hcard] at h7
  have hne : Nat.card ↥(centralizer ({x} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 h7
  rw [h.factorization_C hT] at this
  omega

end IsAConfig

section ConjAut

variable {G : Type} [Group G] {T : Subgroup G} {a : G}

@[expose] def conjAutT (haN : a ∈ normalizer (T : Set G)) : ↥T ≃* ↥T where
  toFun t := ⟨a * t * a⁻¹, (mem_normalizer_iff.1 haN t).1 t.2⟩
  invFun t := ⟨a⁻¹ * t * a, by simpa using (mem_normalizer_iff.1 (inv_mem haN) t).1 t.2⟩
  left_inv t := Subtype.ext (by simp [mul_assoc])
  right_inv t := Subtype.ext (by simp [mul_assoc])
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

end ConjAut

namespace Coord

variable [NeZero n] {h : IsAConfig n x K T Q S a} (c : Coord h)

@[expose] noncomputable def tau : ↥T ≃* ↥(T0 n) where
  toFun t := ⟨((c.ι ⟨(t : G), h.T_le_C t.2⟩ : Fgrp n) : Amb n), (c.ι_T _).1 t.2⟩
  invFun y := ⟨((c.ι.symm ⟨(y : Amb n), T0_le_Fgrp n y.2⟩ : ↥(centralizer ({x} : Set G))) : G),
    (c.ι_T _).2 (by simp)⟩
  left_inv t := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by
    show ((c.ι ⟨((s * t : ↥T) : G), _⟩ : Fgrp n) : Amb n) =
      ((c.ι ⟨(s : G), _⟩ : Fgrp n) : Amb n) * ((c.ι ⟨(t : G), _⟩ : Fgrp n) : Amb n)
    rw [← Subgroup.coe_mul, ← map_mul]
    rfl)

theorem tau_apply (t : ↥T) :
    ((c.tau t : ↥(T0 n)) : Amb n) = ((c.ι ⟨(t : G), h.T_le_C t.2⟩ : Fgrp n) : Amb n) := rfl

@[expose] noncomputable def alpha : ↥(T0 n) ≃* ↥(T0 n) :=
  c.tau.symm.trans ((conjAutT h.a_mem.2.1).trans c.tau)

@[expose] noncomputable def uElt : ↥(T0 n) := c.tau ⟨a ^ 2, h.a_mem.2.2.2⟩

theorem alpha_tau (t : ↥T) : c.alpha (c.tau t) = c.tau (conjAutT h.a_mem.2.1 t) := by
  simp [alpha]

theorem tau_xT : c.tau ⟨x, h.x_mem_T⟩ = x0T n := Subtype.ext (by rw [tau_apply]; exact c.ι_x)

theorem alpha_x0T_ne : c.alpha (x0T n) ≠ x0T n := by
  intro hax
  rw [← c.tau_xT, alpha_tau] at hax
  have := c.tau.injective hax
  exact h.a_conj_x_ne (congrArg Subtype.val this)

theorem alpha_uElt : c.alpha c.uElt = c.uElt := by
  unfold uElt
  rw [alpha_tau]
  congr 1
  apply Subtype.ext
  show a * a ^ 2 * a⁻¹ = a ^ 2
  group

theorem alpha_alpha (t : ↥(T0 n)) : c.alpha (c.alpha t) = c.uElt * t * c.uElt⁻¹ := by
  obtain ⟨t', rfl⟩ := c.tau.surjective t
  unfold uElt
  rw [alpha_tau, alpha_tau, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show a * (a * t' * a⁻¹) * a⁻¹ = a ^ 2 * t' * (a ^ 2)⁻¹
  rw [sq, mul_inv_rev]
  group

@[expose] def XSet : Set ↥(T0 n) := {t | IsConj ((c.tau.symm t : ↥T) : G) x}

@[expose] def VSet : Set ↥(T0 n) := {t | IsConj ((c.tau.symm t : ↥T) : G) (x * (a * x * a⁻¹))}

theorem x0T_mem_XSet : x0T n ∈ c.XSet := by
  show IsConj ((c.tau.symm (x0T n) : ↥T) : G) x
  rw [← c.tau_xT, MulEquiv.symm_apply_apply]

theorem x0T_mul_alpha : x0T n * c.alpha (x0T n) =
    c.tau (⟨x, h.x_mem_T⟩ * conjAutT h.a_mem.2.1 ⟨x, h.x_mem_T⟩) := by
  have h1 : c.alpha (x0T n) = c.tau (conjAutT h.a_mem.2.1 ⟨x, h.x_mem_T⟩) := by
    rw [← c.tau_xT, alpha_tau]
  rw [h1, map_mul, c.tau_xT]

theorem x0T_mul_alpha_mem_VSet : x0T n * c.alpha (x0T n) ∈ c.VSet := by
  show IsConj ((c.tau.symm (x0T n * c.alpha (x0T n)) : ↥T) : G) (x * (a * x * a⁻¹))
  rw [x0T_mul_alpha, MulEquiv.symm_apply_apply]
  exact IsConj.refl _

theorem isConj_of_model (s t : ↥(T0 n))
    (hst : (∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = c.alpha s) :
    IsConj ((c.tau.symm s : ↥T) : G) ((c.tau.symm t : ↥T) : G) := by
  rcases hst with ⟨g, hg, hgst⟩ | rfl
  · set y : ↥(centralizer ({x} : Set G)) := c.ι.symm ⟨g, hg⟩ with hy
    set s' : ↥(centralizer ({x} : Set G)) :=
      ⟨((c.tau.symm s : ↥T) : G), h.T_le_C (c.tau.symm s).2⟩ with hs'
    have hs'ι : ((c.ι s' : Fgrp n) : Amb n) = (s : Amb n) := by
      have := c.tau_apply (c.tau.symm s)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    have hι : ((c.ι (y * s' * y⁻¹) : Fgrp n) : Amb n) = (t : Amb n) := by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hs'ι,
        hy, MulEquiv.apply_symm_apply]
      exact hgst
    have hmem : ((y * s' * y⁻¹ : ↥(centralizer ({x} : Set G))) : G) ∈ T :=
      (c.ι_T _).2 (by rw [hι]; exact t.2)
    have htau : c.tau ⟨((y * s' * y⁻¹ : ↥(centralizer ({x} : Set G))) : G), hmem⟩ = t :=
      Subtype.ext (by rw [tau_apply]; exact hι)
    have hsymm : c.tau.symm t = ⟨((y * s' * y⁻¹ : ↥(centralizer ({x} : Set G))) : G), hmem⟩ := by
      rw [← htau, MulEquiv.symm_apply_apply]
    refine isConj_iff.2 ⟨(y : G), ?_⟩
    rw [hsymm]
    rfl
  · have : c.tau.symm (c.alpha s) = conjAutT h.a_mem.2.1 (c.tau.symm s) := by simp [alpha]
    rw [this]
    exact isConj_iff.2 ⟨a, rfl⟩

end Coord

theorem IsAConfig.conj_mem_D (h : IsAConfig n x K T Q S a) {d : G}
    (hd : d ∈ centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G)) :
    a * d * a⁻¹ ∈ centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G) := by
  obtain ⟨hd1, hd2⟩ := hd
  have hd1' : d * x = x * d := mem_centralizer_singleton_iff.1 hd1
  have hd2' : d * (a * x * a⁻¹) = (a * x * a⁻¹) * d := mem_centralizer_singleton_iff.1 hd2
  have h3 : a * (a * x * a⁻¹) * a⁻¹ = x := by
    have := h.inv_conj_x
    calc a * (a * x * a⁻¹) * a⁻¹ = a * (a⁻¹ * x * a) * a⁻¹ := by rw [this]
      _ = x := by group
  refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
  · calc a * d * a⁻¹ * x = a * d * a⁻¹ * (a * (a * x * a⁻¹) * a⁻¹) := by rw [h3]
      _ = a * (d * (a * x * a⁻¹)) * a⁻¹ := by group
      _ = a * ((a * x * a⁻¹) * d) * a⁻¹ := by rw [hd2']
      _ = (a * (a * x * a⁻¹) * a⁻¹) * (a * d * a⁻¹) := by group
      _ = x * (a * d * a⁻¹) := by rw [h3]
  · calc a * d * a⁻¹ * (a * x * a⁻¹) = a * (d * x) * a⁻¹ := by group
      _ = a * (x * d) * a⁻¹ := by rw [hd1']
      _ = a * x * a⁻¹ * (a * d * a⁻¹) := by group

@[expose] def IsAConfig.thetaHom (h : IsAConfig n x K T Q S a) :
    ↥(centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G)) →*
      ↥(centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G)) where
  toFun d := ⟨a * (d : G) * a⁻¹, h.conj_mem_D d.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

theorem IsAConfig.thetaHom_injective (h : IsAConfig n x K T Q S a) :
    Function.Injective h.thetaHom := by
  intro s t hst
  have := congrArg Subtype.val hst
  simp only [IsAConfig.thetaHom, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj,
    mul_right_inj] at this
  exact Subtype.ext this

@[expose] noncomputable def IsAConfig.thetaEquiv (h : IsAConfig n x K T Q S a) :
    ↥(centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G)) ≃*
      ↥(centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G)) :=
  MulEquiv.ofBijective h.thetaHom (Finite.injective_iff_bijective.1 h.thetaHom_injective)

namespace Coord

variable [NeZero n] {h : IsAConfig n x K T Q S a} (c : Coord h)

theorem iota_x'_eq : ((c.ι ⟨a * x * a⁻¹, h.T_le_C h.conj_x_mem⟩ : Fgrp n) : Amb n) =
    ((c.alpha (x0T n) : ↥(T0 n)) : Amb n) := by
  rw [← c.tau_xT, alpha_tau, tau_apply]
  rfl

theorem iota_comm
    (d : ↥(centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G))) :
    ((c.ι ⟨(d : G), (mem_inf.1 d.2).1⟩ : Fgrp n) : Amb n) *
        ((c.alpha (x0T n) : ↥(T0 n)) : Amb n) =
      ((c.alpha (x0T n) : ↥(T0 n)) : Amb n) *
        ((c.ι ⟨(d : G), (mem_inf.1 d.2).1⟩ : Fgrp n) : Amb n) := by
  rw [← c.iota_x'_eq]
  have h1 : (⟨(d : G), (mem_inf.1 d.2).1⟩ : ↥(centralizer ({x} : Set G))) *
      ⟨a * x * a⁻¹, h.T_le_C h.conj_x_mem⟩ =
      ⟨a * x * a⁻¹, h.T_le_C h.conj_x_mem⟩ * ⟨(d : G), (mem_inf.1 d.2).1⟩ :=
    Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 d.2).2)
  have h2 : ((c.ι ((⟨(d : G), (mem_inf.1 d.2).1⟩ : ↥(centralizer ({x} : Set G))) *
        ⟨a * x * a⁻¹, h.T_le_C h.conj_x_mem⟩) : Fgrp n) : Amb n) =
      ((c.ι (⟨a * x * a⁻¹, h.T_le_C h.conj_x_mem⟩ *
        (⟨(d : G), (mem_inf.1 d.2).1⟩ : ↥(centralizer ({x} : Set G)))) : Fgrp n) : Amb n) := by
    rw [h1]
  rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul] at h2
  exact h2

@[expose] noncomputable def iotaH :
    ↥(centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G)) →*
      ↥(Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n)) where
  toFun d := ⟨((c.ι ⟨(d : G), (mem_inf.1 d.2).1⟩ : Fgrp n) : Amb n), (c.ι _).2,
    mem_centralizer_singleton_iff.2 (c.iota_comm d)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by
    show ((c.ι ⟨((s * t : _) : G), _⟩ : Fgrp n) : Amb n) =
      ((c.ι ⟨(s : G), _⟩ : Fgrp n) : Amb n) * ((c.ι ⟨(t : G), _⟩ : Fgrp n) : Amb n)
    rw [← Subgroup.coe_mul, ← map_mul]
    rfl)

theorem iotaH_injective : Function.Injective c.iotaH := by
  intro s t hst
  have h0 := congrArg Subtype.val hst
  have h1 := c.ι.injective (Subtype.ext h0)
  have h2 := congrArg Subtype.val h1
  exact Subtype.ext h2

theorem iotaH_surjective : Function.Surjective c.iotaH := by
  intro y
  have hyF : (y : Amb n) ∈ Fgrp n := y.2.1
  have hcomm : c.ι.symm ⟨(y : Amb n), hyF⟩ * ⟨a * x * a⁻¹, h.T_le_C h.conj_x_mem⟩ =
      ⟨a * x * a⁻¹, h.T_le_C h.conj_x_mem⟩ * c.ι.symm ⟨(y : Amb n), hyF⟩ := by
    apply c.ι.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, c.iota_x'_eq,
      MulEquiv.apply_symm_apply]
    exact mem_centralizer_singleton_iff.1 y.2.2
  have hD : ((c.ι.symm ⟨(y : Amb n), hyF⟩ : ↥(centralizer ({x} : Set G))) : G) ∈
      centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G) :=
    ⟨(c.ι.symm ⟨(y : Amb n), hyF⟩).2, mem_centralizer_singleton_iff.2 (congrArg Subtype.val hcomm)⟩
  refine ⟨⟨((c.ι.symm ⟨(y : Amb n), hyF⟩ : ↥(centralizer ({x} : Set G))) : G), hD⟩,
    Subtype.ext ?_⟩
  show ((c.ι (c.ι.symm ⟨(y : Amb n), hyF⟩) : Fgrp n) : Amb n) = (y : Amb n)
  rw [MulEquiv.apply_symm_apply]

@[expose] noncomputable def iotaHEquiv :
    ↥(centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G)) ≃*
      ↥(Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n)) :=
  MulEquiv.ofBijective c.iotaH ⟨c.iotaH_injective, c.iotaH_surjective⟩

@[expose] noncomputable def betaEquiv :
    ↥(Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n)) ≃*
      ↥(Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n)) :=
  c.iotaHEquiv.symm.trans (h.thetaEquiv.trans c.iotaHEquiv)

theorem betaEquiv_apply (t : ↥(T0 n))
    (ht : (t : Amb n) ∈ Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n)) :
    ((c.betaEquiv ⟨(t : Amb n), ht⟩ : ↥(Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n))) : Amb n) =
      ((c.alpha t : ↥(T0 n)) : Amb n) := by
  obtain ⟨t', rfl⟩ := c.tau.surjective t
  have hDmem : ((t' : ↥T) : G) ∈
      centralizer ({x} : Set G) ⊓ centralizer ({a * x * a⁻¹} : Set G) :=
    ⟨h.T_le_C t'.2, mem_centralizer_singleton_iff.2 (h.conj_x_comm t'.2)⟩
  have h1 : c.iotaHEquiv ⟨((t' : ↥T) : G), hDmem⟩ = ⟨((c.tau t' : ↥(T0 n)) : Amb n), ht⟩ :=
    Subtype.ext (c.tau_apply t').symm
  rw [betaEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply,
    alpha_tau, tau_apply]
  rfl

theorem hext : ∃ β : ↥(Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n)) ≃*
      ↥(Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n)),
    ∀ (t : ↥(T0 n)) (ht : (t : Amb n) ∈ Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n)),
      ((β ⟨(t : Amb n), ht⟩ : ↥(Hgrp n ((c.alpha (x0T n) : ↥(T0 n)) : Amb n))) : Amb n) =
        ((c.alpha t : ↥(T0 n)) : Amb n) :=
  ⟨c.betaEquiv, c.betaEquiv_apply⟩

include c in
theorem card_T (hn : n = 6 ∨ n = 7) : Nat.card T = 64 :=
  (Nat.card_congr c.tau.toEquiv).trans (card_T0 n hn)

theorem disjoint_XV (hn : n = 6 ∨ n = 7) : Disjoint c.XSet c.VSet :=
  Set.disjoint_left.2 fun _ htX htV =>
    h.not_isConj_x_v (c.card_T hn) ((htX : IsConj _ x).symm.trans htV)

theorem hQ_model (hn : n = 6 ∨ n = 7)
    (hW2 : ∀ q ∈ Q, q ≠ 1 → (Nat.card ↥(centralizer ({q} : Set G))).factorization 2 ≤
      (Nat.card ↥(centralizer ({x} : Set G))).factorization 2) :
    ∀ q : ↥(T0 n), (q : Amb n).1 = 1 → q ≠ 1 → q ∉ c.VSet := by
  intro q hq1 hqne hqV
  have hT : Nat.card T = 64 := c.card_T hn
  have hιq' : ((c.ι ⟨((c.tau.symm q : ↥T) : G), h.T_le_C (c.tau.symm q).2⟩ : Fgrp n) : Amb n) =
      (q : Amb n) := by
    have := c.tau_apply (c.tau.symm q)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hq'Q : ((c.tau.symm q : ↥T) : G) ∈ Q :=
    (c.ι_Q ⟨((c.tau.symm q : ↥T) : G), h.T_le_C (c.tau.symm q).2⟩).1 (by rw [hιq']; exact hq1)
  have hq'ne : ((c.tau.symm q : ↥T) : G) ≠ 1 := by
    intro h1
    apply hqne
    have h2 : c.tau.symm q = 1 := Subtype.ext h1
    rw [← MulEquiv.apply_symm_apply c.tau q, h2, map_one]
  obtain ⟨e⟩ := nonempty_centralizer_equiv_of_isConj hqV
  have hcard := Nat.card_congr e.toEquiv
  have h7 := h.two_pow_seven_dvd hT
  rw [← hcard] at h7
  have hne : Nat.card ↥(centralizer ({((c.tau.symm q : ↥T) : G)} : Set G)) ≠ 0 :=
    Nat.card_pos.ne'
  have h7' := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 h7
  have h6 := hW2 _ hq'Q hq'ne
  rw [h.factorization_C hT] at h6
  omega

theorem modelIso
    (hn : n = 6 ∨ n = 7)
    (hW2 : ∀ q ∈ Q, q ≠ 1 → (Nat.card ↥(centralizer ({q} : Set G))).factorization 2 ≤
      (Nat.card ↥(centralizer ({x} : Set G))).factorization 2) :
    ModelIso n c.alpha c.uElt c.XSet c.VSet :=
  fin_main n hn c.alpha c.uElt c.XSet c.VSet c.alpha_x0T_ne c.alpha_uElt c.alpha_alpha
    (fun _ => c.hext) c.x0T_mem_XSet c.x0T_mul_alpha_mem_VSet (c.disjoint_XV hn)
    (fun s t _ hst hs => (c.isConj_of_model s t hst).symm.trans hs)
    (fun s t _ hst hs => (c.isConj_of_model s t hst).symm.trans hs) (c.hQ_model hn hW2)

end Coord

end CFSG.GH74.GLS
