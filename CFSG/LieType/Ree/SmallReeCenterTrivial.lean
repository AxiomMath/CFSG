module

public import CFSG.LieType.Ree.ReeBorelCoreCenter
public import CFSG.LieType.Ree.SmallReeTorusAction

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}

theorem center_reeGamma_G2_eq_bot
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Subgroup.center (G2.reeGamma K a) = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbij, -⟩ := small_Ree_field_power_identities a K hK
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzH : (z : ModGL G2.tag K) ∈ G2.reeFixedTorus K a :=
    mem_reeFixedTorus_of_mem_normalCore (center_le_normalCore_reeFixedBorel hz)
  obtain ⟨s, hs⟩ := exists_smallReeTorusElt_eq hzH
  have hu : (smallReeCoord a K 1 0 0 : ModGL G2.tag K) ∈ G2.reeGamma K a :=
    (Subgroup.mem_inf.1 ((bijOn_smallReeCoord hK).1
      (Set.mem_univ ((1 : K), (0 : K), (0 : K))))).2
  have hcomm : smallReeTorusElt a K s * smallReeCoord a K 1 0 0 =
      smallReeCoord a K 1 0 0 * smallReeTorusElt a K s := by
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨_, hu⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hs] at h
    exact h.symm
  have h2 : smallReeTorusElt a K s * smallReeCoord a K 1 0 0 * (smallReeTorusElt a K s)⁻¹ =
      smallReeCoord a K 1 0 0 := by
    rw [hcomm, mul_inv_cancel_right]
  have key := h2.symm.trans (smallReeTorusElt_conj_smallReeCoord hK s 1 0 0)
  rw [smallReeCoord_eq_smallReeP, smallReeCoord_eq_smallReeP] at key
  obtain ⟨e0, -⟩ := smallReeP_injective key
  rw [mul_one] at e0
  have hs1 : s ^ (2 * 3 ^ a - 1) = (1 : Kˣ) ^ (2 * 3 ^ a - 1) := by
    rw [one_pow]
    exact Units.ext e0.symm
  have hs' : s = 1 := hbij.1 hs1
  subst hs'
  refine Subtype.ext ?_
  rw [← hs, smallReeTorusElt_one]
  rfl

end ReeTag

theorem small_Ree_fixed_group_center_trivial
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Subgroup.center (ReeTag.G2.reeGamma K a) = ⊥ ∧
    (MulAction.toPermHom (ReeTag.G2.reeGamma K a) (ReeTag.G2.reeGamma K a ⧸
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a))).ker = ⊥ ∧
    FaithfulSMul (ReeTag.G2.reeGamma K a) (ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) := by
  have hZ := ReeTag.center_reeGamma_G2_eq_bot (a := a) hK
  have hker := (ReeTag.ree_Borel_core_center ReeTag.G2 a K hK).2
  rw [hZ] at hker
  refine ⟨hZ, hker, ⟨fun {g₁ g₂} h => ?_⟩⟩
  have hmem : g₁⁻¹ * g₂ ∈ (MulAction.toPermHom (ReeTag.G2.reeGamma K a)
      (ReeTag.G2.reeGamma K a ⧸ (ReeTag.G2.reeFixedBorel K a).subgroupOf
        (ReeTag.G2.reeGamma K a))).ker := by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun x => ?_
    change (g₁⁻¹ * g₂) • x = x
    rw [mul_smul, ← h x, inv_smul_smul]
  rw [hker, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.1 hmem

end CFSG.LieType.Ree
