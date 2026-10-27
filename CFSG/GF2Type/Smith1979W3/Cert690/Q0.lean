module

public import CFSG.GF2Type.Smith1979W3.Cert690.Statements
public import CFSG.LargeExtraspecial.S9FiveB
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseExtraspecial

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62
open QuadraticMap
open scoped commutatorElement

@[simp] theorem mul_a (x y : Q0) : (x * y).a = x.a + y.a + beta0 x.v y.v := rfl

@[simp] theorem mul_v (x y : Q0) : (x * y).v = x.v + y.v := rfl

@[simp] theorem inv_a (x : Q0) : x⁻¹.a = x.a + beta0 x.v x.v := rfl

@[simp] theorem inv_v (x : Q0) : x⁻¹.v = x.v := rfl

@[simp] theorem one_a : (1 : Q0).a = 0 := rfl

@[simp] theorem one_v : (1 : Q0).v = 0 := rfl

theorem q0_mul_self (x : Q0) : x * x = ⟨beta0 x.v x.v, 0⟩ := by
  ext <;> simp [CharTwo.add_self_eq_zero]

theorem beta0_self (v : V₀) : beta0 v v = qPlus v := by
  simp only [beta0, qPlus_apply]
  ring

theorem polar_qPlus_eq_beta0_add (v w : V₀) :
    beta0 v w + beta0 w v = polar qPlus v w := by
  rw [polar_qPlus]
  simp only [beta0]
  ring

@[expose] def Q0Z : Subgroup Q0 where
  carrier := {x | x.v = 0}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    change x.v + y.v = 0
    rw [show x.v = 0 from hx, show y.v = 0 from hy, add_zero]
  inv_mem' := by
    intro x hx
    simpa using hx

@[simp] theorem mem_Q0Z_iff {x : Q0} : x ∈ Q0Z ↔ x.v = 0 := Iff.rfl

theorem exists_not_mem_Q0Z : ∃ x : Q0, x ∉ Q0Z := by
  refine ⟨⟨0, fun _ => 1⟩, ?_⟩
  intro h
  have h0 : (1 : ZMod 2) = 0 := by simpa using congrFun h 0
  exact one_ne_zero h0

theorem mem_Q0Z_of_forall_mul_comm {x : Q0} (hx : ∀ y : Q0, x * y = y * x) : x ∈ Q0Z := by
  by_contra hx0
  have hxne : x.v ≠ 0 := fun h => hx0 (mem_Q0Z_iff.mpr h)
  obtain ⟨w, hw⟩ : ∃ w : V₀, polar qPlus x.v w ≠ 0 := by
    by_contra h
    push Not at h
    exact hxne (polar_qPlus_nondeg x.v h)
  have h := congrArg Q0.a (hx ⟨0, w⟩)
  simp only [mul_a, zero_add, add_zero] at h
  have hb : beta0 x.v w = beta0 w x.v := add_left_cancel h
  have hp : polar qPlus x.v w = 0 := by
    rw [← polar_qPlus_eq_beta0_add, hb, CharTwo.add_self_eq_zero]
  exact hw hp

theorem center_le_Q0Z : Subgroup.center Q0 ≤ Q0Z := fun x hx =>
  mem_Q0Z_of_forall_mul_comm fun y => (Subgroup.mem_center_iff.mp hx y).symm

theorem Q0Z_le_center : Q0Z ≤ Subgroup.center Q0 := by
  intro x hx
  rw [mem_Q0Z_iff] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Q0.ext
  · simp only [mul_a, hx, beta0, Pi.zero_apply, zero_mul, mul_zero, add_zero]
    ring
  · simp only [mul_v, hx, add_zero, zero_add]

theorem center_eq_Q0Z : Subgroup.center Q0 = Q0Z :=
  le_antisymm center_le_Q0Z Q0Z_le_center

theorem commutator_mem_Q0Z (x y : Q0) : ⁅x, y⁆ ∈ Q0Z := by
  change (⁅x, y⁆).v = 0
  simp only [commutatorElement_def, mul_v, inv_v]
  calc x.v + y.v + x.v + y.v = (x.v + x.v) + (y.v + y.v) := by abel
    _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

theorem sq_mem_Q0Z (x : Q0) : x ^ 2 ∈ Q0Z := by
  rw [pow_two]
  change (x * x).v = 0
  simp only [mul_v]
  exact CharTwo.add_self_eq_zero x.v

def Q0ZEquiv : Q0Z ≃ ZMod 2 where
  toFun x := x.1.a
  invFun a := ⟨⟨a, 0⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Q0.ext
    · rfl
    · exact x.2.symm
  right_inv a := rfl

theorem card_Q0Z : Nat.card Q0Z = 2 := by
  rw [Nat.card_congr Q0ZEquiv, Nat.card_zmod]

def Q0ProdEquiv : Q0 ≃ ZMod 2 × V₀ where
  toFun x := (x.a, x.v)
  invFun p := ⟨p.1, p.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by cases p; rfl

theorem card_Q0 : Nat.card Q0 = 128 := by
  calc
    Nat.card Q0 = Nat.card (ZMod 2 × V₀) := Nat.card_congr Q0ProdEquiv
    _ = Nat.card (ZMod 2) * Nat.card V₀ := Nat.card_prod _ _
    _ = 2 * 2 ^ 6 := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    _ = 128 := by norm_num

theorem isPGroup_Q0 : IsPGroup 2 Q0 :=
  IsPGroup.of_card (n := 7) (by rw [card_Q0]; norm_num)

theorem isExtraspecialPGroup_Q0 : IsExtraspecialPGroup 2 Q0 :=
  CFSG.LargeExtraspecial.S9.isExtraspecialPGroup_of_center isPGroup_Q0 card_Q0Z Q0Z_le_center
    commutator_mem_Q0Z sq_mem_Q0Z (fun _ hx => mem_Q0Z_of_forall_mul_comm hx)
    exists_not_mem_Q0Z

noncomputable instance : Module (ZMod 2) (Additive (Abelianization Q0)) :=
  CFSG.GroupTheory.extraspecialQuotientModule isExtraspecialPGroup_Q0

@[expose] def q0Hom : Q0 →* Multiplicative V₀ where
  toFun x := Multiplicative.ofAdd x.v
  map_one' := rfl
  map_mul' x y := rfl

@[simp] theorem q0Hom_apply (x : Q0) : q0Hom x = Multiplicative.ofAdd x.v := rfl

theorem q0Hom_ker : q0Hom.ker = commutator Q0 := by
  rw [isExtraspecialPGroup_Q0.2.1, center_eq_Q0Z]
  ext x
  rw [MonoidHom.mem_ker, mem_Q0Z_iff]
  constructor
  · intro h
    have h' : Multiplicative.ofAdd x.v = (1 : Multiplicative V₀) := by
      simpa only [q0Hom_apply] using h
    simpa using Multiplicative.ofAdd.injective h'
  · intro h
    rw [q0Hom_apply, h]
    rfl

@[expose] noncomputable def q0Equiv : Additive (Abelianization Q0) ≃ₗ[ZMod 2] V₀ :=
  CFSG.ComponentClassification.BMCase.abelianizationEquiv q0Hom
    (fun w => ⟨⟨0, Multiplicative.toAdd w⟩, rfl⟩) q0Hom_ker

theorem q0Equiv_of (x : Q0) :
    q0Equiv (Additive.ofMul (Abelianization.of x)) = x.v :=
  rfl

theorem qPlus_q0Equiv (u : Additive (Abelianization Q0)) :
    CFSG.LargeExtraspecial.O62.qPlus (q0Equiv u) =
      CFSG.RankThree.Literature.FSmith.extraspecialQuadForm isExtraspecialPGroup_Q0 u := by
  obtain ⟨x, rfl⟩ := CFSG.RankThree.Literature.FSmith.exists_ofMul_of u
  rw [q0Equiv_of, CFSG.RankThree.Literature.FSmith.extraspecialQuadForm_apply]
  have hsq : x ^ 2 = (⟨beta0 x.v x.v, (0 : V₀)⟩ : Q0) := by
    rw [pow_two, q0_mul_self]
  by_cases h : x ^ 2 = 1
  · rw [if_pos h]
    have hb : beta0 x.v x.v = 0 := by
      have h' := congrArg Q0.a (hsq.symm.trans h)
      simpa using h'
    rw [← beta0_self, hb]
  · rw [if_neg h]
    have hb : beta0 x.v x.v ≠ 0 := by
      intro hb0
      apply h
      rw [hsq, hb0]
      rfl
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (beta0 x.v x.v) with h0 | h1
    · exact absurd h0 hb
    · rw [← beta0_self, h1]

end CFSG.GF2Type.Smith1979W3.Cert690

end
