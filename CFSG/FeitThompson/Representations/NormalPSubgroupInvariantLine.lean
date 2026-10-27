module

public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RepresentationTheory.Invariants

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix MulAction

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def glFixedSubmodule (R : Subgroup (GL n k)) : Submodule k (n → k) :=
  (Representation.ofDistribMulAction k R (n → k)).invariants

theorem mem_glFixedSubmodule {R : Subgroup (GL n k)} {v : n → k} :
    v ∈ glFixedSubmodule R ↔ ∀ x ∈ R, (x : Matrix n n k) *ᵥ v = v := by
  simp only [glFixedSubmodule, Representation.mem_invariants, Subtype.forall]
  rfl

theorem mem_glFixedSubmodule_iff_smul {R : Subgroup (GL n k)} {v : n → k} :
    v ∈ glFixedSubmodule R ↔ ∀ x ∈ R, x • v = v := mem_glFixedSubmodule

theorem coe_glFixedSubmodule (R : Subgroup (GL n k)) :
    (glFixedSubmodule R : Set (n → k)) = fixedPoints R (n → k) := by
  ext v
  simp only [SetLike.mem_coe, mem_glFixedSubmodule, mem_fixedPoints, Subtype.forall]
  rfl

theorem natCard_glFixedSubmodule (R : Subgroup (GL n k)) :
    Nat.card (glFixedSubmodule R) = Nat.card (fixedPoints R (n → k)) :=
  Nat.card_congr (Set.equivOfEq (coe_glFixedSubmodule R))

@[simp]
theorem glFixedSubmodule_bot : glFixedSubmodule (⊥ : Subgroup (GL n k)) = ⊤ := by
  ext v
  simp only [mem_glFixedSubmodule, Submodule.mem_top, iff_true]
  intro x hx
  rw [Subgroup.mem_bot] at hx
  subst hx
  simp

theorem glFixedSubmodule_le_of_le {R S : Subgroup (GL n k)} (h : R ≤ S) :
    glFixedSubmodule S ≤ glFixedSubmodule R := fun _ hv =>
  mem_glFixedSubmodule.2 fun x hx => mem_glFixedSubmodule.1 hv x (h hx)

variable {p a : ℕ}

theorem glFixedSubmodule_ne_bot [Finite k] [Fact p.Prime] [Nonempty n]
    (hk : p ∣ Nat.card k) {R : Subgroup (GL n k)} (hR : Nat.card R = p ^ a) :
    glFixedSubmodule R ≠ ⊥ := by
  have hp : p.Prime := Fact.out
  have := Fintype.ofFinite k
  have hX : p ∣ Nat.card (n → k) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ← Nat.card_eq_fintype_card (α := k)]
    exact dvd_pow hk Fintype.card_ne_zero
  have hd := dvd_natCard_sub_natCard_fixedPoints (p := p) (P := R) (X := (n → k)) hR
  have hle := natCard_fixedPoints_le (P := R) (X := (n → k))
  have hfix : p ∣ Nat.card (glFixedSubmodule R) := by
    rw [natCard_glFixedSubmodule]
    exact (Nat.dvd_sub_iff_right hle hX).mp hd
  have h1 : 1 < Nat.card (glFixedSubmodule R) :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hfix)
  exact Submodule.nontrivial_iff_ne_bot.mp (Finite.one_lt_card_iff_nontrivial.mp h1)

theorem glFixedSubmodule_ne_bot_of_charP [Finite k] [Fact p.Prime] [CharP k p] [Nonempty n]
    {R : Subgroup (GL n k)} (hR : Nat.card R = p ^ a) : glFixedSubmodule R ≠ ⊥ := by
  have := Fintype.ofFinite k
  obtain ⟨m, -, hm⟩ := FiniteField.card k p
  exact glFixedSubmodule_ne_bot
    (by rw [Nat.card_eq_fintype_card, hm]; exact dvd_pow_self p m.ne_zero) hR

theorem glFixedSubmodule_ne_top {R : Subgroup (GL n k)} (hR : R ≠ ⊥) :
    glFixedSubmodule R ≠ ⊤ := by
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hR
  obtain ⟨x, hx⟩ := hR
  intro htop
  have hall : ∀ w : n → k, ∀ y ∈ R, (y : Matrix n n k) *ᵥ w = w := fun w =>
    mem_glFixedSubmodule.mp (htop ▸ (Submodule.mem_top : w ∈ (⊤ : Submodule k (n → k))))
  refine hx ?_
  have h1 : ((x : GL n k) : Matrix n n k) = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [hall v x x.2, Matrix.one_mulVec]
  ext i j
  simpa using congrFun (congrFun h1 i) j

theorem smul_mem_glFixedSubmodule {G R : Subgroup (GL n k)} (hRG : R ≤ G)
    (hnorm : (R.subgroupOf G).Normal) {g : GL n k} (hg : g ∈ G) {v : n → k}
    (hv : v ∈ glFixedSubmodule R) : g • v ∈ glFixedSubmodule R := by
  rw [mem_glFixedSubmodule_iff_smul] at hv ⊢
  intro x hx
  have hconj : g⁻¹ * x * g ∈ R := by
    have := (Subgroup.normal_subgroupOf_iff hRG).mp hnorm x g⁻¹ hx (inv_mem hg)
    simpa using this
  calc x • (g • v) = (x * g) • v := by rw [mul_smul]
    _ = (g * (g⁻¹ * x * g)) • v := by group
    _ = g • ((g⁻¹ * x * g) • v) := by rw [mul_smul]
    _ = g • v := by rw [hv _ hconj]

theorem finrank_glFixedSubmodule_eq_one [Finite k] [Fact p.Prime] (hk : p ∣ Nat.card k)
    {R : Subgroup (GL (Fin 2) k)} (hR1 : R ≠ ⊥) (hR : Nat.card R = p ^ a) :
    Module.finrank k (glFixedSubmodule R) = 1 := by
  have hlt : Module.finrank k (glFixedSubmodule R) < Module.finrank k (Fin 2 → k) :=
    Submodule.finrank_lt (glFixedSubmodule_ne_top hR1)
  have h2 : Module.finrank k (Fin 2 → k) = 2 := by simp
  have hnt : Nontrivial (glFixedSubmodule R) :=
    Submodule.nontrivial_iff_ne_bot.mpr (glFixedSubmodule_ne_bot hk hR)
  have hpos : 0 < Module.finrank k (glFixedSubmodule R) := Module.finrank_pos
  omega

theorem finrank_glFixedSubmodule_eq_one_and_invariant {f q : ℕ} [Fact p.Prime] [CharP k p]
    (hf : 1 ≤ f) (hq : q = p ^ f) (hcard : Nat.card k = q)
    {G R : Subgroup (GL (Fin 2) k)} (hRG : R ≤ G) (hnorm : (R.subgroupOf G).Normal)
    (hR1 : R ≠ ⊥) (hR : Nat.card R = p ^ a) :
    Module.finrank k (glFixedSubmodule R) = 1 ∧
      ∀ g ∈ G, ∀ v ∈ glFixedSubmodule R, g • v ∈ glFixedSubmodule R := by
  have hp : p.Prime := Fact.out
  have hk : p ∣ Nat.card k := by
    rw [hcard, hq]
    exact dvd_pow_self p (by omega)
  have : Finite k :=
    Nat.finite_of_card_ne_zero (by rw [hcard, hq]; exact pow_ne_zero _ hp.pos.ne')
  exact ⟨finrank_glFixedSubmodule_eq_one hk hR1 hR,
    fun _ hg _ hv => smul_mem_glFixedSubmodule hRG hnorm hg hv⟩

theorem glFixedSubmodule_mem_invtSubmodule {G R : Subgroup (GL n k)} (hRG : R ≤ G)
    (hnorm : (R.subgroupOf G).Normal) :
    glFixedSubmodule R ∈ (Representation.ofDistribMulAction k G (n → k)).invtSubmodule := by
  rw [Representation.mem_invtSubmodule]
  intro g
  rw [Module.End.mem_invtSubmodule]
  intro v hv
  rw [Submodule.mem_comap, Representation.ofDistribMulAction_apply_apply]
  exact smul_mem_glFixedSubmodule hRG hnorm g.2 hv

end CFSG.FeitThompson
