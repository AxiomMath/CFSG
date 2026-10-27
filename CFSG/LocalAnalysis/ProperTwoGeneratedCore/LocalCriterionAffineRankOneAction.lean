module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Complement

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne

open scoped IsMulCommutative Pointwise

universe u v

variable {F : Type u} [Group F] {Λ : Type v} [MulAction F Λ]

theorem normal_subgroup_pretransitive
    [MulAction.IsPretransitive F Λ] [FaithfulSMul F Λ] [Nontrivial Λ]
    (a : Λ) (hmax : IsCoatom (MulAction.stabilizer F a))
    (N : Subgroup F) [N.Normal] (hne : N ≠ ⊥) :
    MulAction.IsPretransitive N Λ := by
  let : MulAction.IsPreprimitive F Λ :=
    (MulAction.isCoatom_stabilizer_iff_preprimitive F a).mp hmax
  apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N)
  intro hfixed
  apply hne
  apply le_antisymm _ bot_le
  intro n hn
  apply Subgroup.mem_bot.mpr
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Λ)
  intro x
  have hx : x ∈ MulAction.fixedPoints N Λ := by
    rw [hfixed]
    exact Set.mem_univ x
  have hnx := MulAction.mem_fixedPoints.mp hx ⟨n, hn⟩
  change n • x = x at hnx
  simpa only [one_smul] using hnx

theorem stabilizer_centralizer_eq_bot
    [FaithfulSMul F Λ] (N : Subgroup F) [MulAction.IsPretransitive N Λ]
    (a : Λ) :
    MulAction.stabilizer F a ⊓ Subgroup.centralizer (N : Set F) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Λ)
  intro b
  simp only [one_smul]
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N a b
  have hcomm : (n : F) * x = x * n :=
    Subgroup.mem_centralizer_iff.mp hx.2 n n.property
  calc
    x • b = x • ((n : F) • a) := by rw [← hn]; rfl
    _ = ((n : F) * x) • a := by rw [← mul_smul, ← hcomm]
    _ = (n : F) • a := by
      rw [mul_smul, MulAction.mem_stabilizer_iff.mp hx.1]
    _ = b := hn

theorem abelian_pretransitive_regular
    [FaithfulSMul F Λ] (N : Subgroup F) [IsMulCommutative N]
    [MulAction.IsPretransitive N Λ] :
    ∀ a b : Λ, ∃! n : N, n • a = b := by
  intro a b
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N a b
  refine ⟨n, hn, ?_⟩
  intro n' hn'
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Λ)
  intro c
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq N a c
  calc
    n' • c = n' • (q • a) := by rw [hq]
    _ = q • (n' • a) := by rw [← mul_smul, mul_comm n' q, mul_smul]
    _ = q • (n • a) := by rw [hn', hn]
    _ = n • c := by rw [← mul_smul, mul_comm q n, mul_smul, hq]

theorem abelian_normal_primitive_complement
    [MulAction.IsPretransitive F Λ] [FaithfulSMul F Λ] [Nontrivial Λ]
    (a : Λ) (hmax : IsCoatom (MulAction.stabilizer F a))
    (N : Subgroup F) [N.Normal] [IsMulCommutative N] (hne : N ≠ ⊥) :
    N.IsComplement' (MulAction.stabilizer F a) ∧
      N ⊔ MulAction.stabilizer F a = ⊤ ∧
      N ⊓ MulAction.stabilizer F a = ⊥ ∧
      MulAction.stabilizer F a ⊓ Subgroup.centralizer (N : Set F) = ⊥ ∧
      ∀ x y : Λ, ∃! n : N, n • x = y := by
  let : MulAction.IsPretransitive N Λ := normal_subgroup_pretransitive a hmax N hne
  have hc := stabilizer_centralizer_eq_bot N a
  have hNcentral : N ≤ Subgroup.centralizer (N : Set F) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hinf : N ⊓ MulAction.stabilizer F a = ⊥ := by
    apply le_antisymm _ bot_le
    intro n hn
    exact hc ▸ (show n ∈ MulAction.stabilizer F a ⊓
      Subgroup.centralizer (N : Set F) from ⟨hn.2, hNcentral hn.1⟩)
  have hprod : (N : Set F) * (MulAction.stabilizer F a : Set F) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N a (g • a)
    have hh : (n : F)⁻¹ * g ∈ MulAction.stabilizer F a := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← hn]
      exact inv_smul_smul (n : F) a
    exact Set.mem_mul.mpr ⟨n, n.property, (n : F)⁻¹ * g, hh, by simp⟩
  have hcompl : N.IsComplement' (MulAction.stabilizer F a) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (disjoint_iff.mpr hinf) hprod
  exact ⟨hcompl, hcompl.isCompl.sup_eq_top, hinf, hc,
    abelian_pretransitive_regular N⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne
