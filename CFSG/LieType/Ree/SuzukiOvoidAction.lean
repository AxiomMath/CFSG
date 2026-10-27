module

public import CFSG.LieType.Ree.SuzukiBruhatNormalForm
public import CFSG.LieType.Ree.SuzukiOvoidUnipotent
public import CFSG.LieType.Ree.SuzukiScalarKernel
public import CFSG.Blueprint.SuzukiDeterminants

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix
open scoped LinearAlgebra.Projectivization

variable {a : ℕ} {K : Type} [Field K]

theorem mem_suzukiOmega_iff {x : ℙ K (Fin 4 → K)} :
    x ∈ suzukiOmega a K ↔ x = suzukiInfty K ∨ ∃ u v : K, suzukiLine a K u v = x := by
  constructor
  · rintro (⟨⟨u, v⟩, rfl⟩ | rfl)
    · exact Or.inr ⟨u, v, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨u, v, rfl⟩)
    · exact suzukiInfty_mem_suzukiOmega a K
    · exact suzukiLine_mem_suzukiOmega a K u v

theorem suzukiSElt_smul_mem
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (c d : K)
    {x : ℙ K (Fin 4 → K)} (hx : x ∈ suzukiOmega a K) :
    suzukiSElt a K c d • x ∈ suzukiOmega a K := by
  rcases mem_suzukiOmega_iff.1 hx with rfl | ⟨u, v, rfl⟩
  · rw [suzukiSElt_smul_suzukiInfty]
    exact suzukiInfty_mem_suzukiOmega a K
  · rw [suzukiSElt_smul_suzukiLine hK]
    exact suzukiLine_mem_suzukiOmega a K _ _

theorem suzukiDElt_smul_mem
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ)
    {x : ℙ K (Fin 4 → K)} (hx : x ∈ suzukiOmega a K) :
    suzukiDElt a K l • x ∈ suzukiOmega a K := by
  rcases mem_suzukiOmega_iff.1 hx with rfl | ⟨u, v, rfl⟩
  · rw [(suzuki_ovoid_torus_action a hK l 0 0).1]
    exact suzukiInfty_mem_suzukiOmega a K
  · rw [(suzuki_ovoid_torus_action a hK l u v).2]
    exact suzukiLine_mem_suzukiOmega a K _ _

theorem suzukiWElt_smul_mem
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : ℙ K (Fin 4 → K)} (hx : x ∈ suzukiOmega a K) : suzukiWElt a K • x ∈ suzukiOmega a K := by
  obtain ⟨h1, h2, h3⟩ := suzuki_ovoid_weyl_action a hK
  rcases mem_suzukiOmega_iff.1 hx with rfl | ⟨u, v, rfl⟩
  · rw [h1]
    exact suzukiLine_mem_suzukiOmega a K _ _
  · by_cases huv : (u, v) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
      rw [h2]
      exact suzukiInfty_mem_suzukiOmega a K
    · rw [h3 u v huv]
      exact suzukiLine_mem_suzukiOmega a K _ _

theorem suzuki_smul_mem_suzukiOmega
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (g : suzukiGroup a K) {x : ℙ K (Fin 4 → K)} (hx : x ∈ suzukiOmega a K) :
    g • x ∈ suzukiOmega a K := by
  rcases (suzuki_bruhat_normal_form hK g).1 with ⟨u, v, l, rfl⟩ | ⟨u, v, l, c, d, rfl⟩
  · rw [mul_smul]
    exact suzukiSElt_smul_mem hK u v (suzukiDElt_smul_mem hK l hx)
  · rw [mul_smul, mul_smul, mul_smul]
    exact suzukiSElt_smul_mem hK u v (suzukiDElt_smul_mem hK l
      (suzukiWElt_smul_mem hK (suzukiSElt_smul_mem hK c d hx)))

@[expose] noncomputable def suzukiOmegaSub
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    SubMulAction (suzukiGroup a K) (ℙ K (Fin 4 → K)) where
  carrier := suzukiOmega a K
  smul_mem' g _ hx := suzuki_smul_mem_suzukiOmega hK g hx

theorem suzukiB_le_stabilizer
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiB a K ≤ MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K) := by
  refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨⟨c, d⟩, rfl⟩
    exact suzukiSElt_smul_suzukiInfty c d
  · rintro _ ⟨l, rfl⟩
    exact (suzuki_ovoid_torus_action a hK l 0 0).1

theorem suzuki_ovoid_stabilizer
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K) = suzukiB a K ∧
    MulAction.stabilizer (suzukiGroup a K)
      (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) = suzukiB a K := by
  have h : MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K) = suzukiB a K := by
    refine le_antisymm (fun g hg => ?_) (suzukiB_le_stabilizer hK)
    rw [MulAction.mem_stabilizer_iff] at hg
    rcases (suzuki_bruhat_normal_form hK g).1 with ⟨u, v, l, rfl⟩ | ⟨u, v, l, c, d, rfl⟩
    · exact (mem_suzukiB_iff hK).2 ⟨u, v, l, rfl⟩
    · exfalso
      rw [mul_smul, mul_smul, mul_smul, suzukiSElt_smul_suzukiInfty,
        (suzuki_ovoid_weyl_action a hK).1, (suzuki_ovoid_torus_action a hK l 0 0).2,
        suzukiSElt_smul_suzukiLine hK] at hg
      exact suzukiLine_ne_suzukiInfty _ _ hg
  refine ⟨h, ?_⟩
  ext g
  rw [MulAction.mem_stabilizer_iff, ← h, MulAction.mem_stabilizer_iff]
  exact ⟨fun hg => by simpa [SubMulAction.val_smul] using congrArg Subtype.val hg,
    fun hg => Subtype.ext (by rw [SubMulAction.val_smul]; exact hg)⟩

theorem exists_smul_eq_suzukiInfty
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : ℙ K (Fin 4 → K)} (hx : x ∈ suzukiOmega a K) :
    ∃ g : suzukiGroup a K, g • x = suzukiInfty K := by
  rcases mem_suzukiOmega_iff.1 hx with rfl | ⟨u, v, rfl⟩
  · exact ⟨1, one_smul _ _⟩
  · obtain ⟨g, hg, -⟩ := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1 _
      (mem_suzukiOmega_diff_iff.2 ⟨u, v, rfl⟩) _ (mem_suzukiOmega_diff_iff.2 ⟨0, 0, rfl⟩)
    exact ⟨suzukiWElt a K * g, by rw [mul_smul, hg, (suzuki_ovoid_weyl_action a hK).2.1]⟩

theorem exists_smul_eq_pair
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : ℙ K (Fin 4 → K)} (hx : x ∈ suzukiOmega a K) (hy : y ∈ suzukiOmega a K)
    (hxy : x ≠ y) : ∃ g : suzukiGroup a K, g • x = suzukiInfty K ∧ g • y = suzukiLine a K 0 0 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_suzukiInfty hK hx
  have hgy : g • y ∈ suzukiOmega a K \ {suzukiInfty K} :=
    ⟨suzuki_smul_mem_suzukiOmega hK g hy, fun h => hxy (smul_left_cancel g (hg.trans h.symm))⟩
  obtain ⟨⟨u, hu⟩, hu', -⟩ := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1 _ hgy _
    (mem_suzukiOmega_diff_iff.2 ⟨0, 0, rfl⟩)
  refine ⟨u * g, ?_, by rw [mul_smul]; exact hu'⟩
  rw [mul_smul, hg]
  exact suzukiB_le_stabilizer hK (suzukiU_le_suzukiB a K hu)

theorem suzuki_ovoid_double_transitivity
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ g : suzukiGroup a K, ∀ x ∈ suzukiOmega a K, g • x ∈ suzukiOmega a K) ∧
    (∀ x ∈ suzukiOmega a K, ∀ y ∈ suzukiOmega a K, ∀ x' ∈ suzukiOmega a K,
      ∀ y' ∈ suzukiOmega a K, x ≠ y → x' ≠ y' →
        ∃ g : suzukiGroup a K, g • x = x' ∧ g • y = y') ∧
    MulAction.IsMultiplyPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) 2 ∧
    Nonempty (suzukiOmegaSub hK) ∧
    MulAction.IsPreprimitive (suzukiGroup a K) (suzukiOmegaSub hK) := by
  have h2 : ∀ x ∈ suzukiOmega a K, ∀ y ∈ suzukiOmega a K, ∀ x' ∈ suzukiOmega a K,
      ∀ y' ∈ suzukiOmega a K, x ≠ y → x' ≠ y' →
        ∃ g : suzukiGroup a K, g • x = x' ∧ g • y = y' := by
    intro x hx y hy x' hx' y' hy' hxy hxy'
    obtain ⟨g, hg1, hg2⟩ := exists_smul_eq_pair hK hx hy hxy
    obtain ⟨h, hh1, hh2⟩ := exists_smul_eq_pair hK hx' hy' hxy'
    refine ⟨h⁻¹ * g, ?_, ?_⟩
    · rw [mul_smul, hg1, ← hh1, inv_smul_smul]
    · rw [mul_smul, hg2, ← hh2, inv_smul_smul]
  have hmult : MulAction.IsMultiplyPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro x y x' y' hxy hxy'
    obtain ⟨g, h1, h2'⟩ := h2 x x.2 y y.2 x' x'.2 y' y'.2 (fun h => hxy (Subtype.ext h))
      (fun h => hxy' (Subtype.ext h))
    exact ⟨g, Subtype.ext (by rw [SubMulAction.val_smul, h1]),
      Subtype.ext (by rw [SubMulAction.val_smul, h2'])⟩
  exact ⟨fun g x hx => suzuki_smul_mem_suzukiOmega hK g hx, h2, hmult,
    ⟨⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩⟩,
    MulAction.isPreprimitive_of_is_two_pretransitive hmult⟩

theorem det_suzukiGroup (g : suzukiGroup a K) :
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  have hle : suzukiGroup a K ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (⟨u, v, hx⟩ | ⟨l, hx⟩ | hx) <;> rw [SetLike.mem_coe, MonoidHom.mem_ker] <;>
      refine Units.ext ?_ <;> rw [Matrix.GeneralLinearGroup.val_det_apply, hx, Units.val_one]
    · exact det_suzukiS a u v
    · exact det_suzukiD a l
    · exact det_suzukiW_eq_one
  have h := MonoidHom.mem_ker.1 (hle g.2)
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]

theorem suzuki_ovoid_faithful
    (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ g : suzukiGroup a K, (∀ x ∈ suzukiOmega a K, g • x = x) → g = 1) ∧
    FaithfulSMul (suzukiGroup a K) (suzukiOmegaSub hK) := by
  have hker : ∀ g : suzukiGroup a K, (∀ x ∈ suzukiOmega a K, g • x = x) → g = 1 := by
    intro g hg
    obtain ⟨h2, -⟩ := suzuki_frob_data a hK
    obtain ⟨c, hc⟩ := suzuki_ovoid_scalar_kernel ha hK (g : GL (Fin 4) K) fun x hx => hg x hx
    have hdet := det_suzukiGroup g
    rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    have hc1 : c = 1 := by
      have : (c - 1) ^ 4 = 0 := by
        linear_combination hdet + (-2 * c ^ 3 + 3 * c ^ 2 - 2 * c + 1) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    refine Subtype.ext (Units.ext ?_)
    rw [hc, hc1, Subgroup.coe_one, Units.val_one, Matrix.scalar_apply, Matrix.diagonal_one]
  refine ⟨hker, ⟨fun {g₁ g₂} h => ?_⟩⟩
  rw [← mul_inv_eq_one]
  refine hker _ fun x hx => ?_
  have hy : g₂⁻¹ • x ∈ suzukiOmega a K := suzuki_smul_mem_suzukiOmega hK _ hx
  have h1 := congrArg Subtype.val (h ⟨g₂⁻¹ • x, hy⟩)
  rw [SubMulAction.val_smul, SubMulAction.val_smul] at h1
  rw [mul_smul, h1, smul_inv_smul]

end CFSG.LieType.Ree
