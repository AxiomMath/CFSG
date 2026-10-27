module

public import CFSG.Quasithin.Background.G2UAdjoint
public import CFSG.LieType.Chevalley.BorelCoreCenter

public section

namespace CFSG.AGLEmbedding.KFactProofs.G2Q

open CFSG.Quasithin.G2U CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


theorem xUnit_not_comm {K : Type} [Field K] :
    (xUnit .G2 K (ix 0) 1 * xUnit .G2 K (ix 1) 1 : ModGL .G2 K) ≠
      xUnit .G2 K (ix 1) 1 * xUnit .G2 K (ix 0) 1 := by
  intro h
  have h1 := congrArg (fun g : ModGL .G2 K =>
    endEquiv (RingEquiv.refl K) (g : Module.End K (RootModule .G2 K))) h
  simp only [Units.val_mul, map_mul, coe_xUnit, endEquiv_xOp] at h1
  have key : ∀ i : Fin Tag.G2.rank,
      XMat K i ((RingEquiv.refl K) 1) = (XMat ℤ i 1).map (Int.castRingHom K) := by
    intro i
    rw [map_XMat]
    simp
  have h2 : ((XMat ℤ (ix 0) 1 * XMat ℤ (ix 1) 1).map (Int.castRingHom K)) =
      ((XMat ℤ (ix 1) 1 * XMat ℤ (ix 0) 1).map (Int.castRingHom K)) := by
    rw [Matrix.map_mul, Matrix.map_mul, ← key, ← key]
    exact h1
  have h3 := congrFun (congrFun h2 0) 5
  simp only [Matrix.map_apply] at h3
  have h4 : ((XMat ℤ (ix 0) 1 * XMat ℤ (ix 1) 1) 0 5 : ℤ) -
      (XMat ℤ (ix 1) 1 * XMat ℤ (ix 0) 1) 0 5 = 1 := by decide +kernel
  have h5 := congrArg (Int.castRingHom K) h4
  rw [map_sub, h3, sub_self, map_one] at h5
  exact zero_ne_one h5

theorem xUnit_pow_three {K : Type} [Field K] [CharP K 3] (i : Fin Tag.G2.rank) :
    (xUnit .G2 K i 1 : ModGL .G2 K) ^ 3 = 1 := by
  have h : (xUnit .G2 K i 1 : ModGL .G2 K) ^ 3 = xUnit .G2 K i (1 + 1 + 1) := by
    rw [xUnit_add, xUnit_add, pow_succ, pow_two]
  rw [h]
  have : (1 + 1 + 1 : K) = 0 := by
    have h3 : (1 + 1 + 1 : K) = ((3 : ℕ) : K) := by norm_num
    rw [h3]
    exact CharP.cast_eq_zero K 3
  rw [this, xUnit_zero]

theorem exists_pair_char_three {K : Type} [Field K] [Finite K] [CharP K 3] :
    ∃ x y : adjointGroup .G2 K, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set (adjointGroup .G2 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : adjointGroup .G2 K := ⟨xUnit .G2 K (ix 0) 1, xUnit_mem_adjointGroup _ _⟩
  let y : adjointGroup .G2 K := ⟨xUnit .G2 K (ix 1) 1, xUnit_mem_adjointGroup _ _⟩
  refine ⟨x, y, Subtype.ext (xUnit_pow_three _), Subtype.ext (xUnit_pow_three _), ?_, ?_⟩
  · intro h
    exact xUnit_not_comm (congrArg Subtype.val h)
  · have hU : IsPGroup 3 ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)) :=
      ((positive_root_triangularity.{0, 0} .G2).2 K 3).2.1.comap_subtype
    refine hU.to_le ((Subgroup.closure_le _).2 ?_)
    rintro _ (rfl | rfl)
    · exact xUnit_mem_posUnipotent _ _
    · exact xUnit_mem_posUnipotent _ _

end CFSG.AGLEmbedding.KFactProofs.G2Q
