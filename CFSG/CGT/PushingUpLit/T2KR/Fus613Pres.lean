module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613Model
public import Mathlib.GroupTheory.NoncommPiCoprod

public section

namespace CFSG.CGT.PushingUpLit.T2KR.Model613

open DihedralGroup
open scoped commutatorElement

structure Struct613Rel {G : Type} [Group G] (g₀ g₁ g₂ g₃ ξ ρ u β : G) : Prop where
  sq₀ : g₀ * g₀ = 1
  sq₁ : g₁ * g₁ = 1
  sq₂ : g₂ * g₂ = 1
  sq₃ : g₃ * g₃ = 1
  c₀₁ : g₀ * g₁ = g₁ * g₀
  c₀₂ : g₀ * g₂ = g₂ * g₀
  c₀₃ : g₀ * g₃ = g₃ * g₀
  c₁₂ : g₁ * g₂ = g₂ * g₁
  c₁₃ : g₁ * g₃ = g₃ * g₁
  c₂₃ : g₂ * g₃ = g₃ * g₂
  xi_sq : ξ * ξ = 1
  xi₀ : ξ * g₀ = g₀ * ξ
  xi₁ : ξ * g₁ = g₁ * ξ
  xi₂ : ξ * g₂ = g₂ * ξ
  xi₃ : ξ * g₃ = g₃ * ξ
  rho_sq : ρ * ρ = 1
  u_sq : u * u = 1
  beta_sq : β * β = 1
  rho_u : ρ * u = u * ρ
  rho_beta : ρ * β = β * ρ
  beta_u : β * u * β⁻¹ = ρ * u
  rho₀ : ρ * g₀ * ρ⁻¹ = g₀
  rho₁ : ρ * g₁ * ρ⁻¹ = g₁
  rho₂ : ρ * g₂ * ρ⁻¹ = g₂ * g₀
  rho₃ : ρ * g₃ * ρ⁻¹ = g₃ * g₁
  rho_xi : ρ * ξ * ρ⁻¹ = ξ
  u₀ : u * g₀ * u⁻¹ = g₀
  u₁ : u * g₁ * u⁻¹ = g₁
  u₂ : u * g₂ * u⁻¹ = g₂ * g₁
  u₃ : u * g₃ * u⁻¹ = g₃ * g₀ * g₁
  u_xi : u * ξ * u⁻¹ = ξ * g₀
  beta₀ : β * g₀ * β⁻¹ = g₀
  beta₁ : β * g₁ * β⁻¹ = g₀ * g₁
  beta₂ : β * g₂ * β⁻¹ = g₂
  beta₃ : β * g₃ * β⁻¹ = g₂ * g₃
  beta_xi : β * ξ * β⁻¹ = ξ

@[expose] def S613 {G : Type} [Group G] (g₀ g₁ g₂ g₃ ξ ρ u β : G) : Subgroup G :=
  Subgroup.closure ({g₀, g₁, g₂, g₃, ξ, ρ, u, β} : Set G)

namespace Struct613Rel

variable {G : Type} [Group G] {g₀ g₁ g₂ g₃ ξ ρ u β : G}
  (hR : Struct613Rel g₀ g₁ g₂ g₃ ξ ρ u β)

theorem inv_eq_self {x : G} (h : x * x = 1) : x⁻¹ = x := inv_eq_of_mul_eq_one_right h

include hR

theorem a_sq : (u * β) * (u * β) = ρ := by
  have h1 : β * u * β = ρ * u := by
    have := hR.beta_u
    rwa [inv_eq_self hR.beta_sq] at this
  calc (u * β) * (u * β) = u * (β * u * β) := by group
    _ = u * (ρ * u) := by rw [h1]
    _ = (u * ρ) * u := by group
    _ = (ρ * u) * u := by rw [hR.rho_u]
    _ = ρ * (u * u) := by group
    _ = ρ := by rw [hR.u_sq, mul_one]

theorem a_pow_four : (u * β) ^ 4 = 1 := by
  have h : (u * β) ^ 4 = (u * β) ^ 2 * (u * β) ^ 2 := by rw [← pow_add]
  rw [h, sq, hR.a_sq, hR.rho_sq]

theorem u_conj_a : u * (u * β) * u⁻¹ = (u * β)⁻¹ := by
  have h1 : u⁻¹ = u := inv_eq_self hR.u_sq
  have h2 : β⁻¹ = β := inv_eq_self hR.beta_sq
  rw [mul_inv_rev, h1, h2]
  calc u * (u * β) * u = (u * u) * β * u := by group
    _ = β * u := by rw [hR.u_sq, one_mul]

end Struct613Rel

def Apow {G : Type} [Group G] (a : G) (k : ZMod 4) : G := a ^ k.val

section Apow

variable {G : Type} [Group G] {a : G} (ha : a ^ 4 = 1)
include ha

theorem pow_mod_four (n : ℕ) : a ^ (n % 4) = a ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, ha, one_pow, one_mul]

theorem Apow_add (i j : ZMod 4) : Apow a (i + j) = Apow a i * Apow a j := by
  unfold Apow
  rw [ZMod.val_add, pow_mod_four ha, pow_add]

omit ha in
theorem Apow_zero : Apow a 0 = 1 := by simp [Apow]

theorem Apow_neg (i : ZMod 4) : Apow a (-i) = (Apow a i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← Apow_add ha, neg_add_cancel, Apow_zero]

theorem conj_Apow {u : G} (hu : u * a * u⁻¹ = a⁻¹) (i : ZMod 4) :
    u * Apow a i * u⁻¹ = Apow a (-i) := by
  unfold Apow
  have h1 : u * a ^ i.val * u⁻¹ = (u * a * u⁻¹) ^ i.val := by
    have := map_pow (MulAut.conj u) a i.val
    simp
  rw [h1, hu, inv_pow]
  have := Apow_neg ha i
  unfold Apow at this
  exact this.symm

end Apow


namespace Struct613Rel

variable {G : Type} [Group G] {g₀ g₁ g₂ g₃ ξ ρ u β : G}
  (hR : Struct613Rel g₀ g₁ g₂ g₃ ξ ρ u β)

def f2 : DihedralGroup 4 →* G where
  toFun d := match d with
    | DihedralGroup.r i => Apow (u * β) i
    | DihedralGroup.sr i => u * Apow (u * β) i
  map_one' := by
    show Apow (u * β) 0 = 1
    exact Apow_zero
  map_mul' := by
    have ha4 := hR.a_pow_four
    have hcomm : ∀ i : ZMod 4, Apow (u * β) i * u = u * Apow (u * β) (-i) := by
      intro i
      have h2 := conj_Apow ha4 hR.u_conj_a (-i)
      rw [neg_neg] at h2
      rw [← h2]
      group
    rintro (i | i) (j | j)
    · show Apow (u * β) (i + j) = Apow (u * β) i * Apow (u * β) j
      exact Apow_add ha4 i j
    · show u * Apow (u * β) (j - i) = Apow (u * β) i * (u * Apow (u * β) j)
      rw [← mul_assoc, hcomm i, mul_assoc, ← Apow_add ha4]
      congr 2
      ring
    · show u * Apow (u * β) (i + j) = u * Apow (u * β) i * Apow (u * β) j
      rw [Apow_add ha4, mul_assoc]
    · show Apow (u * β) (j - i) = u * Apow (u * β) i * (u * Apow (u * β) j)
      calc Apow (u * β) (j - i) = (u * u) * (Apow (u * β) (-i) * Apow (u * β) j) := by
            rw [hR.u_sq, one_mul, ← Apow_add ha4]
            congr 1
            ring
        _ = u * (u * Apow (u * β) (-i)) * Apow (u * β) j := by group
        _ = u * (Apow (u * β) i * u) * Apow (u * β) j := by rw [hcomm i]
        _ = u * Apow (u * β) i * (u * Apow (u * β) j) := by group

theorem f2_sr0 : hR.f2 (DihedralGroup.sr 0) = u := by
  show u * Apow (u * β) 0 = u
  rw [Apow_zero, mul_one]

theorem f2_sr1 : hR.f2 (DihedralGroup.sr 1) = β := by
  show u * Apow (u * β) 1 = β
  have : Apow (u * β) 1 = u * β := by
    have h1 : (1 : ZMod 4).val = 1 := rfl
    rw [Apow, h1, pow_one]
  rw [this, ← mul_assoc, hR.u_sq, one_mul]

theorem f2_r2 : hR.f2 (DihedralGroup.r 2) = ρ := by
  show Apow (u * β) 2 = ρ
  have : Apow (u * β) 2 = (u * β) * (u * β) := by
    have h2 : (2 : ZMod 4).val = 2 := rfl
    rw [Apow, h2, pow_two]
  rw [this, hR.a_sq]


theorem pow_mod_two {x : G} (hx : x * x = 1) (n : ℕ) : x ^ (n % 2) = x ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, pow_two, hx, one_pow, one_mul]

end Struct613Rel

def invHom {G : Type} [Group G] (x : G) (hx : x * x = 1) : Multiplicative (ZMod 2) →* G where
  toFun a := x ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [Struct613Rel.pow_mod_two hx, pow_add]

namespace Struct613Rel

variable {G : Type} [Group G] {g₀ g₁ g₂ g₃ ξ ρ u β : G}
  (hR : Struct613Rel g₀ g₁ g₂ g₃ ξ ρ u β)
include hR

def gen (g₀ g₁ g₂ g₃ ξ : G) : Fin 5 → G
  | 0 => g₀
  | 1 => g₁
  | 2 => g₂
  | 3 => g₃
  | 4 => ξ

theorem gen_sq (i : Fin 5) : gen g₀ g₁ g₂ g₃ ξ i * gen g₀ g₁ g₂ g₃ ξ i = 1 := by
  fin_cases i
  · exact hR.sq₀
  · exact hR.sq₁
  · exact hR.sq₂
  · exact hR.sq₃
  · exact hR.xi_sq

theorem gen_comm (i j : Fin 5) :
    gen g₀ g₁ g₂ g₃ ξ i * gen g₀ g₁ g₂ g₃ ξ j = gen g₀ g₁ g₂ g₃ ξ j * gen g₀ g₁ g₂ g₃ ξ i := by
  fin_cases i <;> fin_cases j <;> first
    | rfl | exact hR.c₀₁ | exact hR.c₀₁.symm | exact hR.c₀₂ | exact hR.c₀₂.symm
    | exact hR.c₀₃ | exact hR.c₀₃.symm | exact hR.c₁₂ | exact hR.c₁₂.symm
    | exact hR.c₁₃ | exact hR.c₁₃.symm | exact hR.c₂₃ | exact hR.c₂₃.symm
    | exact hR.xi₀ | exact hR.xi₀.symm | exact hR.xi₁ | exact hR.xi₁.symm
    | exact hR.xi₂ | exact hR.xi₂.symm | exact hR.xi₃ | exact hR.xi₃.symm

theorem f1_comm : Pairwise fun i j : Fin 5 => ∀ x y : Multiplicative (ZMod 2),
    Commute (invHom (gen g₀ g₁ g₂ g₃ ξ i) (hR.gen_sq i) x)
      (invHom (gen g₀ g₁ g₂ g₃ ξ j) (hR.gen_sq j) y) := by
  intro i j _ x y
  show Commute (gen g₀ g₁ g₂ g₃ ξ i ^ _) (gen g₀ g₁ g₂ g₃ ξ j ^ _)
  exact Commute.pow_pow (hR.gen_comm i j) _ _

def f1 : (Fin 5 → Multiplicative (ZMod 2)) →* G :=
  MonoidHom.noncommPiCoprod (fun i => invHom (gen g₀ g₁ g₂ g₃ ξ i) (hR.gen_sq i)) hR.f1_comm

theorem f1_single (i : Fin 5) :
    hR.f1 (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 2))) = gen g₀ g₁ g₂ g₃ ξ i := by
  have h := MonoidHom.noncommPiCoprod_mulSingle
    (ϕ := fun i => invHom (gen g₀ g₁ g₂ g₃ ξ i) (hR.gen_sq i)) (hcomm := hR.f1_comm) i
    (Multiplicative.ofAdd (1 : ZMod 2))
  refine h.trans ?_
  show gen g₀ g₁ g₂ g₃ ξ i ^ (1 : ZMod 2).val = _
  rw [ZMod.val_one, pow_one]


end Struct613Rel

theorem closure_sg : Subgroup.closure (Set.range sg) = ⊤ := by
  rw [eq_top_iff]
  intro q _
  have hq : q = ∏ i, Pi.mulSingle i (q i) := (Finset.univ_prod_mulSingle q).symm
  rw [hq]
  refine Subgroup.prod_mem _ fun i _ => ?_
  have h2 : q i = 1 ∨ q i = Multiplicative.ofAdd (1 : ZMod 2) := by
    generalize q i = a
    revert a
    decide
  rcases h2 with h | h
  · rw [h]; simp
  · rw [h]; exact Subgroup.subset_closure ⟨i, rfl⟩

theorem closure_sr : ∀ d : DihedralGroup 4,
    d ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) := by
  have hs0 : sr 0 ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) :=
    Subgroup.subset_closure (by simp)
  have hs1 : sr 1 ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) :=
    Subgroup.subset_closure (by simp)
  have hr1 : r 1 ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) := by
    have : (r 1 : DihedralGroup 4) = sr 0 * sr 1 := by decide
    rw [this]; exact Subgroup.mul_mem _ hs0 hs1
  have hr2 : r 2 ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) := by
    have : (r 2 : DihedralGroup 4) = r 1 * r 1 := by decide
    rw [this]; exact Subgroup.mul_mem _ hr1 hr1
  have hr3 : r 3 ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) := by
    have : (r 3 : DihedralGroup 4) = r 2 * r 1 := by decide
    rw [this]; exact Subgroup.mul_mem _ hr2 hr1
  have hs2 : sr 2 ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) := by
    have : (sr 2 : DihedralGroup 4) = sr 1 * r 1 := by decide
    rw [this]; exact Subgroup.mul_mem _ hs1 hr1
  have hs3 : sr 3 ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) := by
    have : (sr 3 : DihedralGroup 4) = sr 1 * r 2 := by decide
    rw [this]; exact Subgroup.mul_mem _ hs1 hr2
  have h0 : r 0 ∈ Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) := by
    have : (r 0 : DihedralGroup 4) = 1 := by decide
    rw [this]; exact Subgroup.one_mem _
  rintro (i | i)
  · fin_cases i
    · exact h0
    · exact hr1
    · exact hr2
    · exact hr3
  · fin_cases i
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3

namespace Struct613Rel

variable {G : Type} [Group G] {g₀ g₁ g₂ g₃ ξ ρ u β : G}
  (hR : Struct613Rel g₀ g₁ g₂ g₃ ξ ρ u β)
include hR

def Compat (d : DihedralGroup 4) : Prop :=
  ∀ q : N0, hR.f1 (phi0 d q) = hR.f2 d * hR.f1 q * (hR.f2 d)⁻¹

theorem compat_one : hR.Compat 1 := by
  intro q
  simp

theorem compat_mul {d d' : DihedralGroup 4} (hd : hR.Compat d) (hd' : hR.Compat d') :
    hR.Compat (d * d') := by
  intro q
  have : phi0 (d * d') q = phi0 d (phi0 d' q) := by rw [map_mul]; rfl
  rw [this, hd, hd', map_mul]
  group

theorem compat_inv {d : DihedralGroup 4} (hd : hR.Compat d) : hR.Compat d⁻¹ := by
  intro q
  have h1 := hd (phi0 d⁻¹ q)
  have h2 : phi0 d (phi0 d⁻¹ q) = q := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [h2] at h1
  rw [map_inv hR.f2 d, h1]
  group

theorem compat_gen (d : DihedralGroup 4)
    (h : ∀ i : Fin 5, hR.f1 (phi0 d (sg i)) = hR.f2 d * hR.f1 (sg i) * (hR.f2 d)⁻¹) :
    hR.Compat d := by
  have : hR.f1.comp (phi0 d).toMonoidHom = (MulAut.conj (hR.f2 d)).toMonoidHom.comp hR.f1 := by
    refine MonoidHom.eq_of_eqOn_dense closure_sg ?_
    rintro _ ⟨i, rfl⟩
    exact h i
  intro q
  exact DFunLike.congr_fun this q


theorem f1_sg (i : Fin 5) : hR.f1 (sg i) = gen g₀ g₁ g₂ g₃ ξ i := hR.f1_single i

theorem compat_sr0 : hR.Compat (sr 0) := by
  apply hR.compat_gen
  have h2 := hR.f2_sr0
  intro i
  fin_cases i
  · show hR.f1 (phi0 (sr 0) (sg 0)) = _
    rw [phi_u0, h2, hR.f1_sg, hR.f1_sg]
    exact (hR.u₀).symm
  · show hR.f1 (phi0 (sr 0) (sg 1)) = _
    rw [phi_u1, h2, hR.f1_sg, hR.f1_sg]
    exact (hR.u₁).symm
  · show hR.f1 (phi0 (sr 0) (sg 2)) = _
    rw [phi_u2, h2, map_mul, hR.f1_sg, hR.f1_sg, hR.f1_sg]
    show g₁ * g₂ = u * g₂ * u⁻¹
    rw [hR.u₂]
    exact hR.c₁₂
  · show hR.f1 (phi0 (sr 0) (sg 3)) = _
    rw [phi_u3, h2, map_mul, map_mul, hR.f1_sg, hR.f1_sg, hR.f1_sg, hR.f1_sg]
    show g₀ * g₁ * g₃ = u * g₃ * u⁻¹
    rw [hR.u₃]
    calc g₀ * g₁ * g₃ = g₀ * (g₁ * g₃) := by group
      _ = g₀ * (g₃ * g₁) := by rw [hR.c₁₃]
      _ = (g₀ * g₃) * g₁ := by group
      _ = (g₃ * g₀) * g₁ := by rw [hR.c₀₃]
  · show hR.f1 (phi0 (sr 0) (sg 4)) = _
    rw [phi_u4, h2, map_mul, hR.f1_sg, hR.f1_sg, hR.f1_sg]
    show g₀ * ξ = u * ξ * u⁻¹
    rw [hR.u_xi]
    exact hR.xi₀.symm

theorem compat_sr1 : hR.Compat (sr 1) := by
  apply hR.compat_gen
  have h2 := hR.f2_sr1
  intro i
  fin_cases i
  · show hR.f1 (phi0 (sr 1) (sg 0)) = _
    rw [phi_b0, h2, hR.f1_sg, hR.f1_sg]
    exact (hR.beta₀).symm
  · show hR.f1 (phi0 (sr 1) (sg 1)) = _
    rw [phi_b1, h2, map_mul, hR.f1_sg, hR.f1_sg, hR.f1_sg]
    exact (hR.beta₁).symm
  · show hR.f1 (phi0 (sr 1) (sg 2)) = _
    rw [phi_b2, h2, hR.f1_sg, hR.f1_sg]
    exact (hR.beta₂).symm
  · show hR.f1 (phi0 (sr 1) (sg 3)) = _
    rw [phi_b3, h2, map_mul, hR.f1_sg, hR.f1_sg, hR.f1_sg]
    exact (hR.beta₃).symm
  · show hR.f1 (phi0 (sr 1) (sg 4)) = _
    rw [phi_b4, h2, hR.f1_sg, hR.f1_sg]
    exact (hR.beta_xi).symm

theorem compat_all (d : DihedralGroup 4) : hR.Compat d := by
  let K : Subgroup (DihedralGroup 4) :=
    { carrier := {d | hR.Compat d}
      mul_mem' := fun ha hb => hR.compat_mul ha hb
      one_mem' := hR.compat_one
      inv_mem' := fun ha => hR.compat_inv ha }
  have hle : Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4)) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hR.compat_sr0
    · exact hR.compat_sr1
  exact hle (closure_sr d)


def Phi : T0 →* G :=
  SemidirectProduct.lift hR.f1 hR.f2 fun d => MonoidHom.ext fun q => hR.compat_all d q

theorem Phi_inl (q : N0) : hR.Phi (SemidirectProduct.inl q) = hR.f1 q :=
  SemidirectProduct.lift_inl _ _ _ _

theorem Phi_inr (d : DihedralGroup 4) : hR.Phi (SemidirectProduct.inr d) = hR.f2 d :=
  SemidirectProduct.lift_inr _ _ _ _

theorem Phi_e (i : Fin 5) : hR.Phi (e i) = gen g₀ g₁ g₂ g₃ ξ i := by
  show hR.Phi (SemidirectProduct.inl (sg i)) = _
  rw [hR.Phi_inl, hR.f1_sg]

theorem Phi_e0 : hR.Phi (e 0) = g₀ := hR.Phi_e 0

theorem Phi_dd (d : DihedralGroup 4) : hR.Phi (dd d) = hR.f2 d := hR.Phi_inr d

omit hR in
theorem gen_mem (i : Fin 5) :
    gen g₀ g₁ g₂ g₃ ξ i ∈ S613 g₀ g₁ g₂ g₃ ξ ρ u β := by
  apply Subgroup.subset_closure
  fin_cases i <;> simp [gen]

theorem range_Phi : hR.Phi.range = S613 g₀ g₁ g₂ g₃ ξ ρ u β := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    have ht : t = SemidirectProduct.inl t.left * SemidirectProduct.inr t.right := by
      rw [← SemidirectProduct.mk_eq_inl_mul_inr]
    rw [ht, map_mul, hR.Phi_inl, hR.Phi_inr]
    refine Subgroup.mul_mem _ ?_ ?_
    · have h1 : hR.f1 t.left ∈ Subgroup.map hR.f1 ⊤ := ⟨t.left, trivial, rfl⟩
      rw [← closure_sg, MonoidHom.map_closure] at h1
      refine (Subgroup.closure_le _).2 ?_ h1
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [hR.f1_sg]
      exact gen_mem i
    · have h1 : hR.f2 t.right ∈ Subgroup.map hR.f2
          (Subgroup.closure ({sr 0, sr 1} : Set (DihedralGroup 4))) :=
        ⟨t.right, closure_sr _, rfl⟩
      rw [MonoidHom.map_closure, Set.image_pair, hR.f2_sr0, hR.f2_sr1] at h1
      refine (Subgroup.closure_le _).2 ?_ h1
      rintro _ (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  · rw [S613, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨e 0, hR.Phi_e 0⟩
    · exact ⟨e 1, hR.Phi_e 1⟩
    · exact ⟨e 2, hR.Phi_e 2⟩
    · exact ⟨e 3, hR.Phi_e 3⟩
    · exact ⟨e 4, hR.Phi_e 4⟩
    · exact ⟨dd (r 2), by rw [hR.Phi_dd, hR.f2_r2]⟩
    · exact ⟨dd (sr 0), by rw [hR.Phi_dd, hR.f2_sr0]⟩
    · exact ⟨dd (sr 1), by rw [hR.Phi_dd, hR.f2_sr1]⟩

theorem inf_centralizer_eq (hinj : Function.Injective hR.Phi) (s : T0) :
    S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({hR.Phi s} : Set G) =
      Subgroup.map hR.Phi (Subgroup.centralizer ({s} : Set T0)) := by
  ext x
  rw [Subgroup.mem_inf, ← hR.range_Phi, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    refine ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply hinj
    rw [map_mul, map_mul]
    exact hy
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, ← map_mul, hy]


theorem f1_mem_of_four (q : N0) (hq : q 4 = 1) :
    hR.f1 q ∈ Subgroup.closure ({g₀, g₁, g₂, g₃} : Set G) := by
  have hq' : q = ∏ i, Pi.mulSingle i (q i) := (Finset.univ_prod_mulSingle q).symm
  have : q ∈ Subgroup.comap hR.f1 (Subgroup.closure ({g₀, g₁, g₂, g₃} : Set G)) := by
    rw [hq']
    refine Subgroup.prod_mem _ fun i _ => ?_
    by_cases hi : i = 4
    · subst hi
      rw [hq]
      simp
    · have h2 : q i = 1 ∨ q i = Multiplicative.ofAdd (1 : ZMod 2) := by
        generalize q i = a
        revert a
        decide
      rcases h2 with h | h
      · rw [h]; simp
      · rw [h]
        show hR.f1 (sg i) ∈ Subgroup.closure ({g₀, g₁, g₂, g₃} : Set G)
        rw [hR.f1_sg]
        apply Subgroup.subset_closure
        fin_cases i
        · simp [gen]
        · simp [gen]
        · simp [gen]
        · simp [gen]
        · exact absurd rfl hi
  exact this

theorem Phi_mem_N00 {t : T0} (ht : t ∈ N00) :
    hR.Phi t ∈ Subgroup.closure ({g₀, g₁, g₂, g₃, ρ, u} : Set G) := by
  obtain ⟨h4, hd⟩ := mem_N00.1 ht
  have hle : Subgroup.closure ({g₀, g₁, g₂, g₃} : Set G) ≤
      Subgroup.closure ({g₀, g₁, g₂, g₃, ρ, u} : Set G) :=
    Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have hρ : ρ ∈ Subgroup.closure ({g₀, g₁, g₂, g₃, ρ, u} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hu : u ∈ Subgroup.closure ({g₀, g₁, g₂, g₃, ρ, u} : Set G) :=
    Subgroup.subset_closure (by simp)
  have ht' : t = SemidirectProduct.inl t.left * SemidirectProduct.inr t.right := by
    rw [← SemidirectProduct.mk_eq_inl_mul_inr]
  rw [ht', map_mul, hR.Phi_inl, hR.Phi_inr]
  refine Subgroup.mul_mem _ (hle (hR.f1_mem_of_four _ h4)) ?_
  have hr0 : hR.f2 (r 0) = 1 := by
    show Apow (u * β) 0 = 1
    exact Apow_zero
  have hsr2 : hR.f2 (sr 2) = u * ρ := by
    show u * Apow (u * β) 2 = u * ρ
    have : Apow (u * β) 2 = ρ := hR.f2_r2
    rw [this]
  rcases hd with h | h | h | h
  · rw [h, hr0]; exact Subgroup.one_mem _
  · rw [h, hR.f2_r2]; exact hρ
  · rw [h, hR.f2_sr0]; exact hu
  · rw [h, hsr2]; exact Subgroup.mul_mem _ hu hρ


theorem part_Z (hinj : Function.Injective hR.Phi) :
    g₀ ≠ 1 ∧ ∀ t ∈ S613 g₀ g₁ g₂ g₃ ξ ρ u β, t * g₀ = g₀ * t := by
  have h0 : hR.Phi (e 0) = g₀ := hR.Phi_e 0
  refine ⟨fun h => e0_ne_one (hinj ?_), ?_⟩
  · exact h0.trans (h.trans (map_one hR.Phi).symm)
  · intro t ht
    rw [← hR.range_Phi] at ht
    obtain ⟨s, rfl⟩ := ht
    calc hR.Phi s * g₀ = hR.Phi s * hR.Phi (e 0) := by rw [h0]
      _ = hR.Phi (s * e 0) := (map_mul _ _ _).symm
      _ = hR.Phi (e 0 * s) := by rw [e0_central]
      _ = hR.Phi (e 0) * hR.Phi s := map_mul _ _ _
      _ = g₀ * hR.Phi s := by rw [h0]

theorem part_A (hinj : Function.Injective hR.Phi) :
    ∀ t ∈ S613 g₀ g₁ g₂ g₃ ξ ρ u β, t * t = 1 → t ≠ 1 → t ≠ g₀ →
      t ∈ ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({t} : Set G),
        S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({t} : Set G)⁆ →
      ∀ w ∈ ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({t} : Set G),
        S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({t} : Set G)⁆,
        w = 1 ∨ w = t ∨ w = g₀ ∨ w = t * g₀ := by
  intro t ht hs2 hs1 hsz hC w hw
  have h0 : hR.Phi (e 0) = g₀ := hR.Phi_e 0
  rw [← hR.range_Phi] at ht
  obtain ⟨s, rfl⟩ := ht
  rw [hR.inf_centralizer_eq hinj, ← Subgroup.map_commutator,
    Subgroup.mem_map_iff_mem hinj] at hC
  rw [hR.inf_centralizer_eq hinj, ← Subgroup.map_commutator] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  have hs2' : s * s = 1 := hinj (by rw [map_mul, hs2, map_one])
  have := T0_A s hs2' (fun h => hs1 (by rw [h, map_one])) (fun h => hsz (by rw [h, h0])) hC w' hw'
  rcases this with h | h | h | h
  · left; rw [h, map_one]
  · right; left; rw [h]
  · right; right; left; rw [h, h0]
  · right; right; right; rw [h, map_mul, h0]

theorem part_B (hinj : Function.Injective hR.Phi) :
    g₀ ∈ ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({ξ * ρ} : Set G),
      S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({ξ * ρ} : Set G)⁆ ∧
    ∃ w ∈ ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({ξ * ρ} : Set G),
      S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({ξ * ρ} : Set G)⁆, w ≠ 1 ∧ w ≠ g₀ := by
  have h0 : hR.Phi (e 0) = g₀ := hR.Phi_e 0
  have hxr : hR.Phi (e 4 * dd (r 2)) = ξ * ρ := by
    rw [map_mul, hR.Phi_e 4, hR.Phi_dd, hR.f2_r2]
    rfl
  rw [← hxr, hR.inf_centralizer_eq hinj, ← Subgroup.map_commutator]
  obtain ⟨hB1, w, hw, hw1, hw0⟩ := T0_B
  refine ⟨?_, hR.Phi w, Subgroup.mem_map_of_mem _ hw, ?_, ?_⟩
  · have := Subgroup.mem_map_of_mem hR.Phi hB1
    rwa [h0] at this
  · intro h; exact hw1 (hinj (by rw [h, map_one]))
  · intro h; exact hw0 (hinj (by rw [h, h0]))

theorem part_L :
    ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β, S613 g₀ g₁ g₂ g₃ ξ ρ u β⁆ ≤
      Subgroup.closure ({g₀, g₁, g₂, g₃, ρ, u} : Set G) := by
  rw [← hR.range_Phi, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  rintro _ ⟨t, ht, rfl⟩
  exact hR.Phi_mem_N00 (comm_top_le_N00 ht)

end Struct613Rel

end CFSG.CGT.PushingUpLit.T2KR.Model613
