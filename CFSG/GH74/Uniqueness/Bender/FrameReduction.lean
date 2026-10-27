module

public import CFSG.GH74.Uniqueness.Bender.FrameDefs
public import CFSG.LinearAlgebra.OddSolvableUnitary.LowDegreeScalar
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.Uniqueness.Bender.Frame

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {E : Type} [Field E]

section LinearAlgebra

open Module

theorem pow_three_eq_trace_smul_sub (M : Matrix (Fin 3) (Fin 3) E) :
    M ^ 3 = M.trace • M ^ 2 - M.adjugate.trace • M + M.det • (1 : Matrix (Fin 3) (Fin 3) E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three,
      Matrix.adjugate_fin_three, Matrix.det_fin_three] <;> ring

theorem eq_zero_of_eq_mul_of_ne_one {μ a : E} (hμ : μ ≠ 1) (h : a = μ * a) : a = 0 := by
  have : (μ - 1) * a = 0 := by rw [sub_mul, ← h, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hμ)

theorem pow_three_eq_one_of_mul_eq_smul {x y : GL (Fin 3) E} {μ : E} (hμ : μ ≠ 1)
    (hxy : (x : Matrix (Fin 3) (Fin 3) E) * y = μ • ((y : Matrix (Fin 3) (Fin 3) E) * x))
    (hdet : (y : Matrix (Fin 3) (Fin 3) E).det = 1) : (y : Matrix (Fin 3) (Fin 3) E) ^ 3 = 1 := by
  set X := (x : Matrix (Fin 3) (Fin 3) E) with hX
  set Y := (y : Matrix (Fin 3) (Fin 3) E) with hY
  set X' := ((x⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) with hX'
  set Y' := ((y⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) with hY'
  have hXX' : X * X' = 1 := by rw [hX, hX', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hYY' : Y * Y' = 1 := by rw [hY, hY', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hY'Y : Y' * Y = 1 := by rw [hY, hY', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr : Y.trace = 0 := by
    have h1 : X * Y * X' = μ • Y := by rw [hxy, smul_mul_assoc, mul_assoc, hXX', mul_one]
    have h2 := Matrix.trace_units_conj x Y
    rw [← hX, ← hX', h1, Matrix.trace_smul, smul_eq_mul] at h2
    exact eq_zero_of_eq_mul_of_ne_one hμ h2.symm
  have htr' : Y'.trace = 0 := by
    have h1 : Y' * X = μ • (X * Y') := by
      calc Y' * X = Y' * (X * Y) * Y' := by rw [mul_assoc, mul_assoc, hYY', mul_one]
        _ = μ • (X * Y') := by
          rw [hxy, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hY'Y, one_mul]
    have h2 : Y' = μ • (X * Y' * X') := by
      calc Y' = Y' * X * X' := by rw [mul_assoc, hXX', mul_one]
        _ = μ • (X * Y' * X') := by rw [h1, smul_mul_assoc]
    have h3 := Matrix.trace_units_conj x Y'
    rw [← hX, ← hX'] at h3
    have h4 : Y'.trace = μ * Y'.trace := by
      conv_lhs => rw [h2]
      rw [Matrix.trace_smul, smul_eq_mul, h3]
    exact eq_zero_of_eq_mul_of_ne_one hμ h4
  have hadj : Y.adjugate = Y' := by
    rw [hY', Matrix.coe_units_inv, Matrix.inv_def, ← hY, hdet, Ring.inverse_one, one_smul]
  rw [pow_three_eq_trace_smul_sub, htr, hadj, htr', hdet, zero_smul, zero_smul, sub_zero,
    zero_add, one_smul]

theorem isScalarMat_of_commute {x y g : GL (Fin 3) E} {μ : E} (hμ : IsPrimitiveRoot μ 3)
    (hxy : (x : Matrix (Fin 3) (Fin 3) E) * y = μ • ((y : Matrix (Fin 3) (Fin 3) E) * x))
    (hy3 : (y : Matrix (Fin 3) (Fin 3) E) ^ 3 = 1)
    (hgx : g * x = x * g) (hgy : g * y = y * g) : IsScalarMat g := by
  set b : Module.End E (Fin 3 → E) := Matrix.toLinAlgEquiv' (y : Matrix (Fin 3) (Fin 3) E)
    with hbdef
  set c : Module.End E (Fin 3 → E) := Matrix.toLinAlgEquiv' (x : Matrix (Fin 3) (Fin 3) E)
    with hcdef
  set m : Module.End E (Fin 3 → E) := Matrix.toLinAlgEquiv' (g : Matrix (Fin 3) (Fin 3) E)
    with hmdef
  have hb : b ^ 3 = 1 := by rw [hbdef, ← map_pow, hy3, map_one]
  have hc : Function.Injective c := by
    intro u v huv
    have h := congrArg
      (Matrix.toLinAlgEquiv' ((x⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) huv
    rwa [hcdef, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, map_one] at h
  have hcb : c * b = μ • (b * c) := by rw [hcdef, hbdef, ← map_mul, ← map_mul, hxy, map_smul]
  have hmb : m * b = b * m := by
    rw [hmdef, hbdef, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hgy]
  have hmc : m * c = c * m := by
    rw [hmdef, hcdef, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hgx]
  have h3 := CFSG.OddSolvableUnitary.finrank_eq_mul_finrank_eigenspace_one
    (by norm_num : 0 < 3) hμ hb hc hcb
  rw [Module.finrank_fin_fun] at h3
  have h1 : finrank E (b.eigenspace 1) = 1 := by omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := b.eigenspace 1) (by
    intro h
    rw [h, finrank_bot] at h1
    exact zero_ne_one h1)
  have hmv : m v ∈ b.eigenspace 1 := by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [one_smul] at hv ⊢
    rw [← Module.End.mul_apply, ← hmb, Module.End.mul_apply, hv]
  obtain ⟨l, hl⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : b.eigenspace 1)
    (fun h => hv0 (congrArg Subtype.val h))).1 h1 ⟨m v, hmv⟩
  have hlv : m v = l • v := (congrArg Subtype.val hl).symm
  set U := m.eigenspace l with hUdef
  have hbU : ∀ u ∈ U, b u ∈ U := by
    intro u hu
    rw [hUdef, Module.End.mem_eigenspace_iff] at hu ⊢
    rw [← Module.End.mul_apply, hmb, Module.End.mul_apply, hu, map_smul]
  have hcU : ∀ u ∈ U, c u ∈ U := by
    intro u hu
    rw [hUdef, Module.End.mem_eigenspace_iff] at hu ⊢
    rw [← Module.End.mul_apply, hmc, Module.End.mul_apply, hu, map_smul]
  have hU3 := CFSG.OddSolvableUnitary.finrank_eq_mul_finrank_inf_eigenspace_one
    (by norm_num : 0 < 3) hμ hb hc hcb hbU hcU
  have hvU : v ∈ U := by rw [hUdef, Module.End.mem_eigenspace_iff]; exact hlv
  have hpos : 0 < finrank E (U ⊓ b.eigenspace 1 : Submodule E (Fin 3 → E)) :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨v, Submodule.mem_inf.2 ⟨hvU, hv⟩⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have hUtop : U = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le U
    rw [Module.finrank_fin_fun] at this ⊢
    omega
  refine ⟨l, Matrix.toLinAlgEquiv'.injective ?_⟩
  rw [map_smul, map_one, ← hmdef]
  refine LinearMap.ext fun w => ?_
  have hw : w ∈ U := hUtop ▸ Submodule.mem_top
  rw [hUdef, Module.End.mem_eigenspace_iff] at hw
  rw [hw]
  rfl

end LinearAlgebra

section GroupTheory

open Subgroup
open scoped Pointwise commutatorElement

theorem commutatorElement_mul_left_of_forall_commute {G : Type*} [Group G] {g h x : G}
    (hc : ∀ k : G, ⁅h, x⁆ * k = k * ⁅h, x⁆) : ⁅g * h, x⁆ = ⁅g, x⁆ * ⁅h, x⁆ := by
  calc ⁅g * h, x⁆ = g * ⁅h, x⁆ * (x * g⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    _ = ⁅h, x⁆ * ⁅g, x⁆ := by rw [← hc g, commutatorElement_def g x]; group
    _ = ⁅g, x⁆ * ⁅h, x⁆ := hc _

theorem exists_abelian_of_commutator_isScalarMat {C : Subgroup (GL (Fin 3) E)} [Finite C]
    (hdet : ∀ c ∈ C, (c : Matrix (Fin 3) (Fin 3) E).det = 1) (hodd : Odd (Nat.card C))
    (τ : C →* C) (hτ2 : ∀ g, τ (τ g) = g)
    (hτs : ∀ g : C, IsScalarMat (g : GL (Fin 3) E) → τ g = g)
    {N : Subgroup C} [N.Normal] (hNτ : ∀ g ∈ N, τ g ∈ N) (hNc : ¬ IsMulCommutative N)
    (hNN : ∀ g ∈ ⁅N, N⁆, IsScalarMat (g : GL (Fin 3) E)) :
    ∃ B : Subgroup C, B.Normal ∧ (∀ g ∈ B, τ g ∈ B) ∧ IsMulCommutative B ∧
      ∃ g ∈ B, ¬ IsScalarMat (g : GL (Fin 3) E) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hscomm : ∀ z g : C, IsScalarMat (z : GL (Fin 3) E) → z * g = g * z := by
    rintro z g ⟨ν, hν⟩
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hν, smul_mul_assoc, one_mul, mul_smul_comm,
      mul_one]
  have hcube : ∀ z : C, IsScalarMat (z : GL (Fin 3) E) → z ^ 3 = 1 := by
    rintro z ⟨ν, hν⟩
    have h := hdet z z.2
    rw [hν, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hν, smul_pow, one_pow, h, one_smul,
      Subgroup.coe_one, Units.val_one]
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x := by
    by_contra! h
    exact hNc ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩
  set s := ⁅x, y⁆ with hsdef
  have hsN : s ∈ N := by
    rw [hsdef, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  obtain ⟨μ, hμ⟩ := hNN s (commutator_mem_commutator hx hy)
  have hs1 : s ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hμ3 : μ ^ 3 = 1 := by
    have h := hdet s s.2
    rwa [hμ, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    apply hs1
    apply Subtype.ext
    apply Units.ext
    rw [hμ, one_smul]
    rfl
  have hμp : IsPrimitiveRoot μ 3 := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hμ3 hμ1)
  have hrel : ((x : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) * (y : GL (Fin 3) E) =
      μ • (((y : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) * (x : GL (Fin 3) E)) := by
    have h : x * y = s * (y * x) := by rw [hsdef, commutatorElement_def]; group
    have h' := congrArg (fun g : C => ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) h
    simp only [Subgroup.coe_mul, Units.val_mul] at h'
    rw [h', hμ, smul_mul_assoc, one_mul]
  have hy3 := pow_three_eq_one_of_mul_eq_smul hμ1 hrel (hdet y y.2)
  have hcs : ∀ g : C, g * x = x * g → g * y = y * g → IsScalarMat (g : GL (Fin 3) E) :=
    fun g hgx hgy => isScalarMat_of_commute hμp hrel hy3 (congrArg Subtype.val hgx)
      (congrArg Subtype.val hgy)
  set Z := zpowers s with hZdef
  have hZ1 : ∀ g : C, IsScalarMat (g : GL (Fin 3) E) → g ∈ Z := by
    rintro g ⟨ν, hν⟩
    have h := hdet g g.2
    rw [hν, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
    obtain ⟨i, -, hi⟩ := hμp.eq_pow_of_pow_eq_one h
    refine Subgroup.mem_zpowers_iff.2 ⟨(i : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hμ, smul_pow, one_pow, hi, hν]
  have hZ2 : ∀ g ∈ Z, IsScalarMat (g : GL (Fin 3) E) := by
    intro g hg
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hg)
    refine ⟨μ ^ n, ?_⟩
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hμ, smul_pow, one_pow]
  have hZ3 : Nat.card Z = 3 := by
    rw [hZdef, Nat.card_zpowers]
    exact orderOf_eq_prime (hcube s ⟨μ, hμ⟩) hs1
  have hZN : Z ≤ N := (zpowers_le).2 hsN
  have hZc : ∀ z ∈ Z, ∀ g : C, z * g = g * z := fun z hz g => hscomm z g (hZ2 z hz)
  have hZn : Z.Normal := ⟨fun z hz g => by rw [← hZc z hz g, mul_inv_cancel_right]; exact hz⟩
  have hcZ : ∀ g ∈ N, ∀ h ∈ N, ⁅g, h⁆ ∈ Z :=
    fun g hg h hh => hZ1 _ (hNN _ (commutator_mem_commutator hg hh))
  let ψ : N →* Z × Z :=
    { toFun := fun g => (⟨⁅(g : C), x⁆, hcZ g g.2 x hx⟩, ⟨⁅(g : C), y⁆, hcZ g g.2 y hy⟩)
      map_one' := Prod.ext (Subtype.ext (commutatorElement_one_left x))
        (Subtype.ext (commutatorElement_one_left y))
      map_mul' := fun g h => Prod.ext
        (Subtype.ext
          (commutatorElement_mul_left_of_forall_commute fun k => hZc _ (hcZ h h.2 x hx) k))
        (Subtype.ext
          (commutatorElement_mul_left_of_forall_commute fun k => hZc _ (hcZ h h.2 y hy) k)) }
  have hker : ψ.ker = Z.subgroupOf N := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ⁅(g : C), x⁆ = 1 := congrArg Subtype.val (congrArg Prod.fst h)
      have h2 : ⁅(g : C), y⁆ = 1 := congrArg Subtype.val (congrArg Prod.snd h)
      exact hZ1 _ (hcs _ (commutatorElement_eq_one_iff_mul_comm.1 h1)
        (commutatorElement_eq_one_iff_mul_comm.1 h2))
    · intro h
      exact Prod.ext (Subtype.ext (commutatorElement_eq_one_iff_mul_comm.2 (hZc _ h x)))
        (Subtype.ext (commutatorElement_eq_one_iff_mul_comm.2 (hZc _ h y)))
  have hψx : ψ ⟨x, hx⟩ = (1, ⟨s, mem_zpowers s⟩) :=
    Prod.ext (Subtype.ext (commutatorElement_self x)) rfl
  have hψy : ψ ⟨y, hy⟩ = (⟨s, mem_zpowers s⟩⁻¹, 1) :=
    Prod.ext (Subtype.ext (commutatorElement_inv x y).symm)
      (Subtype.ext (commutatorElement_self y))
  have hψs : Function.Surjective ψ := by
    rintro ⟨a, b⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    refine ⟨(⟨y, hy⟩ : N) ^ (-i) * (⟨x, hx⟩ : N) ^ j, ?_⟩
    rw [map_mul, map_zpow, map_zpow, hψx, hψy]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp [← hi]
    · simp [← hj]
  have hN27 : Nat.card N = 27 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv, Nat.card_prod,
      hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv, hZ3]
  have hcent : ∀ g ∈ N, g ∉ Z → Nat.card (N ⊓ centralizer ({g} : Set C) : Subgroup C) = 9 := by
    intro g hgN hgZ
    set Cg := N ⊓ centralizer ({g} : Set C) with hCg
    have hCgN : Cg ≤ N := inf_le_left
    have hZCg : Z ≤ Cg := fun z hz =>
      ⟨hZN hz, Subgroup.mem_centralizer_singleton_iff.2 (hZc z hz g)⟩
    have hgCg : g ∈ Cg := ⟨hgN, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    have hdvd : Nat.card Cg ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hN27]
      exact Subgroup.card_dvd_of_le hCgN
    obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hne3 : Nat.card Cg ≠ 3 := fun h =>
      hgZ ((Subgroup.eq_of_le_of_card_ge hZCg (by rw [h, hZ3])) ▸ hgCg)
    have hge3 : 3 ≤ Nat.card Cg := by
      have h := Subgroup.card_le_of_le hZCg
      rwa [hZ3] at h
    have hne27 : Nat.card Cg ≠ 27 := by
      intro h
      have hCgeq : Cg = N := Subgroup.eq_of_le_of_card_ge hCgN (by rw [h, hN27])
      have hxC : x ∈ Cg := hCgeq ▸ hx
      have hyC : y ∈ Cg := hCgeq ▸ hy
      exact hgZ (hZ1 _ (hcs _ (Subgroup.mem_centralizer_singleton_iff.1 hxC.2).symm
        (Subgroup.mem_centralizer_singleton_iff.1 hyC.2).symm))
    rw [hcard] at hne3 hge3 hne27 ⊢
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · norm_num at hge3
    · exact absurd (pow_one 3) hne3
    · norm_num
    · exact absurd (by norm_num) hne27
  have hτcomm : ∀ g ∈ N, g * τ g = τ g * g := by
    intro g hg
    set w := ⁅g, τ g⁆ with hw
    have hwZ : w ∈ Z := hcZ g hg (τ g) (hNτ g hg)
    have hw1 : τ w = w := hτs w (hZ2 w hwZ)
    have hw2 : τ w = w⁻¹ := by rw [hw, map_commutatorElement, hτ2, commutatorElement_inv]
    have hw3 : w ^ 3 = 1 := hcube w (hZ2 w hwZ)
    have hww : w * w = 1 := by
      calc w * w = w * τ w := by rw [hw1]
        _ = 1 := by rw [hw2, mul_inv_cancel]
    have hw0 : w = 1 := by
      calc w = w ^ 3 * (w * w)⁻¹ := by group
        _ = 1 := by rw [hw3, hww, inv_one, mul_one]
    exact commutatorElement_eq_one_iff_mul_comm.1 hw0
  have hS := CFSG.OddSolvableUnitary.ncard_setOf_card_eq_nine hZN hN27 hZ3
    (fun z hz g _ => hZc z hz g) hNc
  have : Finite (ConjAct C) := Finite.of_equiv C ConjAct.toConjAct.toEquiv
  have hoddC : Odd (Nat.card (ConjAct C)) := by
    rwa [Nat.card_congr (ConjAct.toConjAct (G := C)).toEquiv.symm]
  obtain ⟨B, ⟨-, hBN, hB9⟩, hBfix⟩ :=
    CFSG.OddSolvableUnitary.exists_fixed_of_card_eq_four hoddC _ hS
      fun c B hB => CFSG.OddSolvableUnitary.smul_mem_setOf_card_eq_nine c hB
  have hBn : B.Normal := ⟨fun g hg c => by
    have h := smul_mem_pointwise_smul g (ConjAct.toConjAct c) B hg
    rwa [hBfix, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at h⟩
  have hBc : IsMulCommutative B :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hB9]; norm_num)
  have hBτ : ∀ g ∈ B, τ g ∈ B := by
    intro g hg
    by_cases hgZ : g ∈ Z
    · rw [hτs g (hZ2 g hgZ)]
      exact hg
    · have hBC : B ≤ N ⊓ centralizer ({g} : Set C) := fun b hb =>
        ⟨hBN hb, Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (hBc.is_comm.comm ⟨b, hb⟩ ⟨g, hg⟩))⟩
      have hBeq := Subgroup.eq_of_le_of_card_ge hBC (by rw [hcent g (hBN hg) hgZ, hB9])
      rw [hBeq]
      exact ⟨hNτ g (hBN hg), Subgroup.mem_centralizer_singleton_iff.2 (hτcomm g (hBN hg)).symm⟩
  obtain ⟨g, hgB, hgZ⟩ : ∃ g ∈ B, g ∉ Z := by
    by_contra! h
    have h' := Subgroup.card_le_of_le (show B ≤ Z from h)
    rw [hB9, hZ3] at h'
    norm_num at h'
  exact ⟨B, hBn, hBτ, hBc, g, hgB, fun hgs => hgZ (hZ1 g hgs)⟩

theorem exists_abelian_normal_nonscalar (hU : UnitaryFieldData 2 f E)
    {C : Subgroup (GL (Fin 3) E)} {t : GL (Fin 3) E}
    (hdet : ∀ c ∈ C, (c : Matrix (Fin 3) (Fin 3) E).det = 1) (hodd : Odd (Nat.card C))
    (ht2 : t * t = 1) (hnorm : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (hns : ∃ c ∈ C, ¬ IsScalarMat c) :
    ∃ A : Subgroup (GL (Fin 3) E), A ≤ C ∧ (∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) ∧
      (∀ a ∈ A, t * a * t⁻¹ ∈ A) ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∃ a ∈ A, ¬ IsScalarMat a := by
  classical
  have : Finite E := hU.finite
  let τ : C →* C :=
    { toFun := fun g => ⟨t * g * t⁻¹, hnorm g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hτ : ∀ g : C, (τ g : GL (Fin 3) E) = t * g * t⁻¹ := fun g => rfl
  have hτ2 : ∀ g, τ (τ g) = g := fun g => Subtype.ext (by
    rw [hτ, hτ]
    have h : t * (t * (g : GL (Fin 3) E) * t⁻¹) * t⁻¹ = (t * t) * g * (t * t)⁻¹ := by group
    rw [h, ht2, one_mul, inv_one, mul_one])
  have hτs : ∀ g : C, IsScalarMat (g : GL (Fin 3) E) → τ g = g := by
    rintro g ⟨ν, hν⟩
    apply Subtype.ext
    rw [hτ]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hν, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  suffices h : ∃ B : Subgroup C, B.Normal ∧ (∀ g ∈ B, τ g ∈ B) ∧ IsMulCommutative B ∧
      ∃ g ∈ B, ¬ IsScalarMat (g : GL (Fin 3) E) by
    obtain ⟨B, hBn, hBτ, hBc, g, hgB, hg⟩ := h
    refine ⟨B.map C.subtype, Subgroup.map_subtype_le B, ?_, ?_, ?_, ⟨g, ⟨g, hgB, rfl⟩, hg⟩⟩
    · rintro c hc _ ⟨b, hb, rfl⟩
      refine ⟨⟨c, hc⟩ * b * ⟨c, hc⟩⁻¹, hBn.conj_mem b hb _, ?_⟩
      simp only [map_mul, map_inv, Subgroup.coe_subtype]
    · rintro _ ⟨b, hb, rfl⟩
      exact ⟨τ b, hBτ b hb, hτ b⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg (fun z : B => ((z : C) : GL (Fin 3) E)) (hBc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨k, hk⟩ := (Group.isSolvable_def C).1 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hex : ∃ n, ∀ g ∈ derivedSeries C n, IsScalarMat (g : GL (Fin 3) E) :=
    ⟨k, fun g hg => by
      rw [hk, Subgroup.mem_bot] at hg
      exact ⟨1, by rw [hg, one_smul]; rfl⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := by
    refine ⟨Nat.find hex - 1, ?_⟩
    have hn0 : Nat.find hex ≠ 0 := by
      intro h0
      have h := Nat.find_spec hex
      rw [h0, derivedSeries_zero] at h
      obtain ⟨c, hc, hcs⟩ := hns
      exact hcs (h ⟨c, hc⟩ (Subgroup.mem_top _))
    omega
  have hNs : ¬ ∀ g ∈ derivedSeries C m, IsScalarMat (g : GL (Fin 3) E) :=
    Nat.find_min hex (by omega)
  have hNN : ∀ g ∈ ⁅derivedSeries C m, derivedSeries C m⁆, IsScalarMat (g : GL (Fin 3) E) := by
    rw [← derivedSeries_succ, ← hm]
    exact Nat.find_spec hex
  have hNτ : ∀ g ∈ derivedSeries C m, τ g ∈ derivedSeries C m :=
    fun g hg => map_derivedSeries_le_derivedSeries τ m ⟨g, hg, rfl⟩
  push Not at hNs
  by_cases hNc : IsMulCommutative (derivedSeries C m)
  · exact ⟨_, derivedSeries_normal C m, hNτ, hNc, hNs⟩
  · exact exists_abelian_of_commutator_isScalarMat hdet hodd τ hτ2 hτs hNτ hNc hNN

end GroupTheory

end CFSG.GH74.Uniqueness.Bender.Frame
