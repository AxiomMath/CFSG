module

public import CFSG.CGT.Stroth77.Types
public import CFSG.CGT.Stroth77.TypesMore
public import CFSG.CGT.Stroth77.Types13x
public import CFSG.CGT.Stroth77.Types21x
public import CFSG.CGT.Stroth77.Types22x
public import CFSG.CGT.Stroth77.Types32x
public import CFSG.CGT.Stroth77.Types321

public section

namespace CFSG.CGT.Stroth77

open Matrix

inductive StrothTypeIndex : Type where
  | t100 (m : ℕ)
  | t101 (s : ℕ)
  | t110 (t : ℕ)
  | t111 (t : ℕ)
  | t120 (m : ℕ) (hm : 3 ≤ m)
  | t121 (m : ℕ) (hm : 3 ≤ m)
  | t130 (m : ℕ) (hm : 3 ≤ m)
  | t131 (m : ℕ) (hm : 3 ≤ m)
  | t200 (m : ℕ)
  | t201 (m : ℕ)
  | t210 (m : ℕ) (hm : 2 ≤ m)
  | t211 (m : ℕ) (hm : 2 ≤ m)
  | t220 (s : ℕ) (hs : 1 ≤ s)
  | t221 (s : ℕ) (hs : 1 ≤ s)
  | t230 (s : ℕ) (hs : 1 ≤ s)
  | t231 (s : ℕ) (hs : 1 ≤ s)
  | t300 (n : ℕ)
  | t310 (m : ℕ) (hm : 2 ≤ m)
  | t320 (m : ℕ) (hm : 3 ≤ m)
  | t330 (m : ℕ) (hm : 3 ≤ m)
  | t321
  | t331

namespace StrothTypeIndex

@[expose] def param : StrothTypeIndex → ℕ
  | t100 m => m
  | t101 s => s
  | t110 t => t
  | t111 t => t
  | t120 m _ => m
  | t121 m _ => m
  | t130 m _ => m
  | t131 m _ => m
  | t200 m => m
  | t201 m => m
  | t210 m _ => m
  | t211 m _ => m
  | t220 s _ => s
  | t221 s _ => s
  | t230 s _ => s
  | t231 s _ => s
  | t300 n => n
  | t310 m _ => m
  | t320 m _ => m
  | t330 m _ => m
  | t321 => 3
  | t331 => 3

@[expose] def k : StrothTypeIndex → Fin 3 → ℕ
  | t100 m => Type100.k m
  | t101 s => Type101.k s
  | t110 t => Type110.k t
  | t111 t => Type111.k t
  | t120 m _ => Type120.k m
  | t121 m _ => Type121.k m
  | t130 m _ => Type130.k m
  | t131 m _ => Type131.k m
  | t200 m => Type200.k m
  | t201 m => Type201.k m
  | t210 m _ => Type210.k m
  | t211 m _ => Type211.k m
  | t220 s _ => Type220.k s
  | t221 s _ => Type221.k s
  | t230 s _ => Type230.k s
  | t231 s _ => Type231.k s
  | t300 n => Type300.k n
  | t310 m _ => Type310.k m
  | t320 m _ => Type320.k m
  | t330 m _ => Type330.k m
  | t321 => Type321.k
  | t331 => Type331.k

@[expose] def action : (τ : StrothTypeIndex) → SigmaFourAction τ.k
  | t100 m => Type100.action m
  | t101 s => Type101.action s
  | t110 t => Type110.action t
  | t111 t => Type111.action t
  | t120 m hm => Type120.actionPaper m (by omega)
  | t121 m hm => Type121.actionPaper m (by omega)
  | t130 m hm => Type130.actionPaper m (by omega)
  | t131 m hm => Type131.actionPaper m (by omega)
  | t200 m => Type200.action m
  | t201 m => Type201.action m
  | t210 m hm => Type210.action m hm
  | t211 m hm => Type211.action m hm
  | t220 s _ => Type220.actionPaper s
  | t221 s _ => Type221.actionPaper s
  | t230 s _ => Type230.actionPaper s
  | t231 s _ => Type231.actionPaper s
  | t300 n => Type300.action n
  | t310 m hm => Type310.action m hm
  | t320 m hm => Type320.actionPaper m hm
  | t330 m hm => Type330.actionPaper m hm
  | t321 => Type321.action
  | t331 => Type331.action

@[expose] def m (τ : StrothTypeIndex) : ℕ := τ.k 0

@[expose] def n (τ : StrothTypeIndex) : ℕ := τ.k 1

theorem k_two (τ : StrothTypeIndex) : τ.k 2 = τ.n := by
  cases τ <;> rfl

theorem k_eq (τ : StrothTypeIndex) : τ.k = ![τ.m, τ.n, τ.n] := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact τ.k_two

end StrothTypeIndex

theorem natCard_torus (k : Fin 3 → ℕ) : Nat.card (Torus k) = 2 ^ (k 0 + k 1 + k 2) := by
  rw [Nat.card_pi]
  simp only [Nat.card_zmod]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_three]

theorem addOrderOf_gen (k : Fin 3 → ℕ) (j : Fin 3) :
    addOrderOf (gen k j) = 2 ^ k j := by
  apply Nat.dvd_antisymm
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    funext i
    by_cases h : i = j
    · subst h
      simp only [gen, Pi.smul_apply, Pi.single_eq_same, Nat.smul_one_eq_cast, ZMod.natCast_self,
        Pi.zero_apply]
    · rw [Pi.smul_apply, gen, Pi.single_eq_of_ne h, nsmul_zero, Pi.zero_apply]
  · have h1 : addOrderOf (gen k j) • (1 : ZMod (2 ^ k j)) = 0 := by
      have h0 := congrFun (addOrderOf_nsmul_eq_zero (gen k j)) j
      simpa [gen] using h0
    have := (addOrderOf_dvd_iff_nsmul_eq_zero (x := (1 : ZMod (2 ^ k j)))).mpr h1
    simpa using this

theorem addOrderOf_c (k : Fin 3 → ℕ) : addOrderOf (Torus.c : Torus k) = 2 ^ k 0 :=
  addOrderOf_gen k 0

theorem addOrderOf_a (k : Fin 3 → ℕ) : addOrderOf (Torus.a : Torus k) = 2 ^ k 1 :=
  addOrderOf_gen k 1

theorem addOrderOf_b (k : Fin 3 → ℕ) : addOrderOf (Torus.b : Torus k) = 2 ^ k 2 :=
  addOrderOf_gen k 2

@[expose] def conjBy {S : Type*} [Group S] {B : Subgroup S} {g : S}
    (hg : g ∈ Subgroup.normalizer B) (x : B) : B :=
  ⟨g⁻¹ * (x : S) * g, (Subgroup.mem_normalizer_iff''.mp hg (x : S)).mp x.2⟩

section Group

variable {S : Type*} [Group S]

structure StrothTypeData (B : Subgroup S) (τ : StrothTypeIndex) where
  e : Additive B ≃+ Torus τ.k
  uv : S
  t : S
  u : S
  ρ : S
  uv_sq : uv * uv = 1
  t_sq : t * t = 1
  uv_comm_t : uv * t = t * uv
  rho_cube : ρ * ρ * ρ = 1
  u_sq : u * u = 1
  u_rho : u * ρ * u * ρ = 1
  uv_rho : uv * ρ = ρ * t
  t_rho : t * ρ = ρ * uv * t
  uv_comm_u : uv * u = u * uv
  t_u : t * u = u * uv * t
  uv_mem : uv ∈ Subgroup.normalizer B
  t_mem : t ∈ Subgroup.normalizer B
  u_mem : u ∈ Subgroup.normalizer B
  ρ_mem : ρ ∈ Subgroup.normalizer B
  uv_conj : ∀ x : B,
    e (Additive.ofMul (conjBy uv_mem x)) = τ.action.φuv (e (Additive.ofMul x))
  t_conj : ∀ x : B,
    e (Additive.ofMul (conjBy t_mem x)) = τ.action.φt (e (Additive.ofMul x))
  u_conj : ∀ x : B,
    e (Additive.ofMul (conjBy u_mem x)) = τ.action.φu (e (Additive.ofMul x))
  ρ_conj : ∀ x : B,
    e (Additive.ofMul (conjBy ρ_mem x)) = τ.action.φρ (e (Additive.ofMul x))

@[expose] def HasStrothType (B : Subgroup S) (τ : StrothTypeIndex) : Prop :=
  Nonempty (StrothTypeData B τ)

namespace StrothTypeData

variable {B : Subgroup S} {τ : StrothTypeIndex}

@[expose] def c (D : StrothTypeData B τ) : B := Additive.toMul (D.e.symm Torus.c)

@[expose] def a (D : StrothTypeData B τ) : B := Additive.toMul (D.e.symm Torus.a)

@[expose] def b (D : StrothTypeData B τ) : B := Additive.toMul (D.e.symm Torus.b)

theorem card (D : StrothTypeData B τ) :
    Nat.card B = 2 ^ (τ.k 0 + τ.k 1 + τ.k 2) := by
  calc Nat.card B = Nat.card (Additive B) := Nat.card_congr Additive.ofMul
    _ = Nat.card (Torus τ.k) := Nat.card_congr D.e.toEquiv
    _ = 2 ^ (τ.k 0 + τ.k 1 + τ.k 2) := natCard_torus τ.k

theorem card_eq (D : StrothTypeData B τ) :
    Nat.card B = 2 ^ (τ.m + τ.n + τ.n) := by
  have h : τ.k 0 + τ.k 1 + τ.k 2 = τ.m + τ.n + τ.n := by
    rw [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k_two, StrothTypeIndex.n]
  rw [D.card, h]

theorem orderOf_c (D : StrothTypeData B τ) : orderOf D.c = 2 ^ τ.m := by
  rw [c, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq, addOrderOf_c]
  rfl

theorem orderOf_a (D : StrothTypeData B τ) : orderOf D.a = 2 ^ τ.n := by
  rw [a, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq, addOrderOf_a]
  rfl

theorem orderOf_b (D : StrothTypeData B τ) : orderOf D.b = 2 ^ τ.n := by
  rw [b, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq, addOrderOf_b,
    StrothTypeIndex.k_two]

theorem generator_orders (D : StrothTypeData B τ) :
    orderOf D.c = 2 ^ τ.m ∧ orderOf D.a = 2 ^ τ.n ∧ orderOf D.b = 2 ^ τ.n :=
  ⟨D.orderOf_c, D.orderOf_a, D.orderOf_b⟩

theorem orderOf_uv_dvd_two (D : StrothTypeData B τ) : orderOf D.uv ∣ 2 := by
  rw [orderOf_dvd_iff_pow_eq_one, pow_two]
  exact D.uv_sq

theorem orderOf_t_dvd_two (D : StrothTypeData B τ) : orderOf D.t ∣ 2 := by
  rw [orderOf_dvd_iff_pow_eq_one, pow_two]
  exact D.t_sq

theorem orderOf_u_dvd_two (D : StrothTypeData B τ) : orderOf D.u ∣ 2 := by
  rw [orderOf_dvd_iff_pow_eq_one, pow_two]
  exact D.u_sq

theorem orderOf_ρ_dvd_three (D : StrothTypeData B τ) : orderOf D.ρ ∣ 3 := by
  rw [orderOf_dvd_iff_pow_eq_one, pow_three, ← mul_assoc]
  exact D.rho_cube

theorem conj_apply (D : StrothTypeData B τ) {g : S} (hg : g ∈ Subgroup.normalizer B)
    {φ : Torus τ.k →+ Torus τ.k}
    (hconj : ∀ x : B, D.e (Additive.ofMul (conjBy hg x)) = φ (D.e (Additive.ofMul x)))
    (y : Torus τ.k) :
    D.e (Additive.ofMul (conjBy hg (Additive.toMul (D.e.symm y)))) = φ y := by
  rw [hconj, ofMul_toMul, AddEquiv.apply_symm_apply]

theorem t100_uv_c {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.uv_mem D.c)) =
      (-3 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-2 : ℤ) • Torus.b := by
  have h := (D.conj_apply D.uv_mem D.uv_conj Torus.c).trans (Type100.uv_c m)
  exact h

theorem t100_uv_a {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.uv_mem D.a)) =
      (2 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (2 : ℤ) • Torus.b := by
  have h := (D.conj_apply D.uv_mem D.uv_conj Torus.a).trans (Type100.uv_a m)
  exact h

theorem t100_uv_b {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.uv_mem D.b)) =
      (2 : ℤ) • Torus.c + (2 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  have h := (D.conj_apply D.uv_mem D.uv_conj Torus.b).trans (Type100.uv_b m)
  exact h

theorem t100_t_c {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.t_mem D.c)) =
      (1 : ℤ) • Torus.c + (2 : ℤ) • Torus.a := by
  have h := (D.conj_apply D.t_mem D.t_conj Torus.c).trans (Type100.t_c m)
  exact h

theorem t100_t_a {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.t_mem D.a)) = (-1 : ℤ) • Torus.a := by
  have h := (D.conj_apply D.t_mem D.t_conj Torus.a).trans (Type100.t_a m)
  exact h

theorem t100_t_b {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.t_mem D.b)) =
      (-2 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  have h := (D.conj_apply D.t_mem D.t_conj Torus.b).trans (Type100.t_b m)
  exact h

theorem t100_u_c {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.u_mem D.c)) = (1 : ℤ) • Torus.c := by
  have h := (D.conj_apply D.u_mem D.u_conj Torus.c).trans (Type100.u_c m)
  exact h

theorem t100_u_a {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.u_mem D.a)) = (1 : ℤ) • Torus.b := by
  have h := (D.conj_apply D.u_mem D.u_conj Torus.a).trans (Type100.u_a m)
  exact h

theorem t100_u_b {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.u_mem D.b)) = (1 : ℤ) • Torus.a := by
  have h := (D.conj_apply D.u_mem D.u_conj Torus.b).trans (Type100.u_b m)
  exact h

theorem t100_rho_c {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.ρ_mem D.c)) = (1 : ℤ) • Torus.c := by
  have h := (D.conj_apply D.ρ_mem D.ρ_conj Torus.c).trans (Type100.rho_c m)
  exact h

theorem t100_rho_a {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.ρ_mem D.a)) = (1 : ℤ) • Torus.b := by
  have h := (D.conj_apply D.ρ_mem D.ρ_conj Torus.a).trans (Type100.rho_a m)
  exact h

theorem t100_rho_b {m : ℕ} (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.e (Additive.ofMul (conjBy D.ρ_mem D.b)) =
      (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  have h := (D.conj_apply D.ρ_mem D.ρ_conj Torus.b).trans (Type100.rho_b m)
  exact h

end StrothTypeData

namespace HasStrothType

variable {B : Subgroup S} {τ : StrothTypeIndex}

@[expose] noncomputable def data (h : HasStrothType B τ) : StrothTypeData B τ :=
  Classical.choice h

@[expose] noncomputable def e (h : HasStrothType B τ) : Additive B ≃+ Torus τ.k := h.data.e

@[expose] noncomputable def uv (h : HasStrothType B τ) : S := h.data.uv

@[expose] noncomputable def t (h : HasStrothType B τ) : S := h.data.t

@[expose] noncomputable def u (h : HasStrothType B τ) : S := h.data.u

@[expose] noncomputable def ρ (h : HasStrothType B τ) : S := h.data.ρ

theorem uv_sq (h : HasStrothType B τ) : h.uv * h.uv = 1 := h.data.uv_sq

theorem t_sq (h : HasStrothType B τ) : h.t * h.t = 1 := h.data.t_sq

theorem uv_comm_t (h : HasStrothType B τ) : h.uv * h.t = h.t * h.uv := h.data.uv_comm_t

theorem rho_cube (h : HasStrothType B τ) : h.ρ * h.ρ * h.ρ = 1 := h.data.rho_cube

theorem u_sq (h : HasStrothType B τ) : h.u * h.u = 1 := h.data.u_sq

theorem u_rho (h : HasStrothType B τ) : h.u * h.ρ * h.u * h.ρ = 1 := h.data.u_rho

theorem uv_rho (h : HasStrothType B τ) : h.uv * h.ρ = h.ρ * h.t := h.data.uv_rho

theorem t_rho (h : HasStrothType B τ) : h.t * h.ρ = h.ρ * h.uv * h.t := h.data.t_rho

theorem uv_comm_u (h : HasStrothType B τ) : h.uv * h.u = h.u * h.uv := h.data.uv_comm_u

theorem t_u (h : HasStrothType B τ) : h.t * h.u = h.u * h.uv * h.t := h.data.t_u

theorem uv_mem (h : HasStrothType B τ) : h.uv ∈ Subgroup.normalizer B := h.data.uv_mem

theorem t_mem (h : HasStrothType B τ) : h.t ∈ Subgroup.normalizer B := h.data.t_mem

theorem u_mem (h : HasStrothType B τ) : h.u ∈ Subgroup.normalizer B := h.data.u_mem

theorem ρ_mem (h : HasStrothType B τ) : h.ρ ∈ Subgroup.normalizer B := h.data.ρ_mem

theorem uv_conj (h : HasStrothType B τ) :
    ∀ x : B, h.e (Additive.ofMul (conjBy h.uv_mem x)) =
      τ.action.φuv (h.e (Additive.ofMul x)) := h.data.uv_conj

theorem t_conj (h : HasStrothType B τ) :
    ∀ x : B, h.e (Additive.ofMul (conjBy h.t_mem x)) =
      τ.action.φt (h.e (Additive.ofMul x)) := h.data.t_conj

theorem u_conj (h : HasStrothType B τ) :
    ∀ x : B, h.e (Additive.ofMul (conjBy h.u_mem x)) =
      τ.action.φu (h.e (Additive.ofMul x)) := h.data.u_conj

theorem ρ_conj (h : HasStrothType B τ) :
    ∀ x : B, h.e (Additive.ofMul (conjBy h.ρ_mem x)) =
      τ.action.φρ (h.e (Additive.ofMul x)) := h.data.ρ_conj

@[expose] noncomputable def c (h : HasStrothType B τ) : B := h.data.c

@[expose] noncomputable def a (h : HasStrothType B τ) : B := h.data.a

@[expose] noncomputable def b (h : HasStrothType B τ) : B := h.data.b

theorem card (h : HasStrothType B τ) :
    Nat.card B = 2 ^ (τ.k 0 + τ.k 1 + τ.k 2) :=
  h.data.card

theorem card_eq (h : HasStrothType B τ) : Nat.card B = 2 ^ (τ.m + τ.n + τ.n) :=
  h.data.card_eq

theorem generator_orders (h : HasStrothType B τ) :
    orderOf h.c = 2 ^ τ.m ∧ orderOf h.a = 2 ^ τ.n ∧ orderOf h.b = 2 ^ τ.n :=
  h.data.generator_orders

theorem orderOf_uv_dvd_two (h : HasStrothType B τ) : orderOf h.uv ∣ 2 :=
  h.data.orderOf_uv_dvd_two

theorem orderOf_t_dvd_two (h : HasStrothType B τ) : orderOf h.t ∣ 2 :=
  h.data.orderOf_t_dvd_two

theorem orderOf_u_dvd_two (h : HasStrothType B τ) : orderOf h.u ∣ 2 :=
  h.data.orderOf_u_dvd_two

theorem orderOf_ρ_dvd_three (h : HasStrothType B τ) : orderOf h.ρ ∣ 3 :=
  h.data.orderOf_ρ_dvd_three

end HasStrothType

end Group

end CFSG.CGT.Stroth77
