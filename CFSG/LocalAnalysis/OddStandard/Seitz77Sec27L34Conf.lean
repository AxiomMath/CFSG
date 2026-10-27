module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34Orbit
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34GL
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.OddStandard.Seitz77

open Matrix Subgroup

structure L34Conf (G S : Type) [Group G] [Finite G] [Group S] [Finite S] where
  ρ : G →* GL (Fin 8) (ZMod 2)
  π : G →* S
  Xh : Subgroup G
  ρ_inj : Function.Injective ρ
  π_surj : Function.Surjective π
  perf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤
  odd : Odd (Nat.card π.ker)
  S_simple : IsSimpleGroup S
  S_card : Nat.card S = 20160
  inv2 : ∀ x y : S, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → ∃ g : S, g * x * g⁻¹ = y
  inv3 : ∀ x y : S, orderOf x = 3 → orderOf y = 3 → ∃ g : S, g * x * g⁻¹ = y
  X_simple : IsSimpleGroup Xh
  X_card : Nat.card Xh = 60
  X_ker : ∀ x ∈ Xh, π x = 1 → x = 1
  dims : ∀ U : Submodule (ZMod 2) V8, (∀ g : G, ∀ w ∈ U, glPermHom (ρ g) w ∈ U) →
    Module.finrank (ZMod 2) U = 0 ∨ Module.finrank (ZMod 2) U = 4 ∨
      Module.finrank (ZMod 2) U = 8
  fpf : ∀ x ∈ Xh, orderOf x = 3 → ∀ w : V8, glPermHom (ρ x) w = w → w = 0

variable {G S : Type} [Group G] [Finite G] [Group S] [Finite S]

theorem L34Conf.exists_order_three (c : L34Conf G S) : ∃ x ∈ c.Xh, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := c.Xh) 3 (by
    rw [c.X_card]
    norm_num)
  exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

set_option backward.isDefEq.respectTransparency false in
theorem L34Conf.not_dim_four (c : L34Conf G S) (U : Submodule (ZMod 2) V8)
    (hU : ∀ g : G, ∀ w ∈ U, glPermHom (c.ρ g) w ∈ U) (h4 : Module.finrank (ZMod 2) U = 4) :
    False := by
  have hmv : ∀ (g : G) (w : V8), glPermHom (c.ρ g) w =
      (Matrix.mulVecLin (c.ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2))) w := fun g w => rfl
  let b := Module.finBasisOfFinrankEq (ZMod 2) U h4
  let fg : G → (U →ₗ[ZMod 2] U) := fun g =>
    (Matrix.mulVecLin (c.ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2))).restrict
      (fun w hw => hU g w hw)
  have hfg_apply : ∀ (g : G) (w : U), ((fg g w : U) : V8) = glPermHom (c.ρ g) w := fun g w => rfl
  have hfg_one : fg 1 = LinearMap.id := by
    ext w
    simp [hfg_apply, map_one]
  have hfg_mul : ∀ g h, fg (g * h) = (fg g).comp (fg h) := by
    intro g h
    ext w
    simp [hfg_apply, map_mul]
  let ψ₀ : G →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    { toFun := fun g => LinearMap.toMatrix b b (fg g)
      map_one' := by rw [hfg_one, LinearMap.toMatrix_id]
      map_mul' := fun g h => by rw [hfg_mul, LinearMap.toMatrix_comp b b b] }
  let ψ : G →* GL (Fin 4) (ZMod 2) := ψ₀.toHomUnits
  have hψ1 : ∀ g, ψ g = 1 → ∀ w ∈ U, glPermHom (c.ρ g) w = w := by
    intro g hg w hw
    have h1 : ψ₀ g = 1 := by
      have := congrArg Units.val hg
      simpa [ψ] using this
    have h2 : fg g = LinearMap.id := by
      apply (LinearMap.toMatrix b b).injective
      rw [LinearMap.toMatrix_id]
      exact h1
    have := congrArg (fun f => ((f ⟨w, hw⟩ : U) : V8)) h2
    simpa [hfg_apply] using this
  have hXψ : ∀ x ∈ c.Xh, ψ x = 1 → x = 1 := by
    have hn : (ψ.ker.subgroupOf c.Xh).Normal := inferInstance
    rcases c.X_simple.eq_bot_or_eq_top_of_normal (ψ.ker.subgroupOf c.Xh) with hbot | htop
    · intro x hx hψx
      have : (⟨x, hx⟩ : c.Xh) ∈ ψ.ker.subgroupOf c.Xh := by
        rw [Subgroup.mem_subgroupOf]
        exact hψx
      rw [hbot, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      obtain ⟨x, hx, hx3⟩ := c.exists_order_three
      have hψx : ψ x = 1 := by
        have : (⟨x, hx⟩ : c.Xh) ∈ ψ.ker.subgroupOf c.Xh := htop ▸ Subgroup.mem_top _
        rw [Subgroup.mem_subgroupOf] at this
        exact this
      have hne : U ≠ ⊥ := by
        intro hbot
        rw [hbot, finrank_bot] at h4
        omega
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact hw0 (c.fpf x hx hx3 w (hψ1 x hψx w hw))
  exact no_gl4_quotient c.π c.π_surj c.S_simple c.S_card c.inv2 c.odd ψ c.Xh
    (by rw [c.X_card]; exact ⟨30, rfl⟩) hXψ

set_option backward.isDefEq.respectTransparency false in
theorem L34Conf.irreducible (c : L34Conf G S) (U : Submodule (ZMod 2) V8)
    (hU : ∀ g : G, ∀ w ∈ U, glPermHom (c.ρ g) w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  rcases c.dims U hU with h | h | h
  · exact Or.inl (Submodule.finrank_eq_zero.1 h)
  · exact (c.not_dim_four U hU h).elim
  · right
    apply Submodule.eq_top_of_finrank_eq
    rw [h, Module.finrank_fin_fun]

set_option backward.isDefEq.respectTransparency false in
theorem L34Conf.fix_eq_zero (c : L34Conf G S) (Q : Subgroup G) [Q.Normal] (hQ : Q ≠ ⊥)
    (v : V8) (hv : ∀ q ∈ Q, glPermHom (c.ρ q) v = v) : v = 0 := by
  let U : Submodule (ZMod 2) V8 :=
    { carrier := {w | ∀ q ∈ Q, glPermHom (c.ρ q) w = w}
      add_mem' := fun {a b} ha hb q hq => by
        rw [glPermHom_add, ha q hq, hb q hq]
      zero_mem' := fun q _ => glPermHom_zero _
      smul_mem' := fun r {w} hw q hq => by
        simp only [glPermHom_apply] at hw ⊢
        rw [Matrix.mulVec_smul, hw q hq] }
  have hU : ∀ g : G, ∀ w ∈ U, glPermHom (c.ρ g) w ∈ U := by
    intro g w hw q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := Normal.conj_mem ‹Q.Normal› q hq g⁻¹
      simpa using this
    have h1 := hw (g⁻¹ * q * g) hq'
    have h2 : glPermHom (c.ρ q) (glPermHom (c.ρ g) w) =
        glPermHom (c.ρ g) (glPermHom (c.ρ (g⁻¹ * q * g)) w) := by
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, ← map_mul,
        ← map_mul]
      congr 2
      group
    rw [h2, h1]
  rcases c.irreducible U hU with h | h
  · have : v ∈ U := fun q hq => hv q hq
    rw [h, Submodule.mem_bot] at this
    exact this
  · exfalso
    apply hQ
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    apply c.ρ_inj
    rw [map_one]
    apply eq_one_of_forall_glPerm_eq
    intro w
    have : w ∈ U := h ▸ Submodule.mem_top
    exact this q hq

end CFSG.OddStandard.Seitz77
