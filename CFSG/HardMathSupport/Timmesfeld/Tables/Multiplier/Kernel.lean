module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Kernel116TDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Open (GriessAllModelsStatement)

theorem kernel11_6U_conj (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    {J : Type} [Group J] [Finite J] (hq : CFSG.Open.IsQuasisimple J)
    (hK : CFSG.Open.IsKGroup J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hU : ∃ U : Subgroup J, U ≤ Subgroup.center J ∧ CFSG.Open.IsElemAbelian p U ∧
      Nat.card U = p ^ 2) :
    ∀ φ : MulAut J, IsPGroup p (Subgroup.zpowers φ) → ∃ x : J, φ = MulAut.conj x := by
  obtain ⟨U, hUZ, hUab, hUc⟩ := hU
  have h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.center J) :=
    CFSG.SectionRank.le_pRank hp.one_lt hUZ hUab hUc
  obtain ⟨rfl, -, -, h8⟩ := identify_of_two_le_pRank_center hGA hSpM hq hK hp hp2 h2
  have : Group.IsPerfect J := ⟨hq.1⟩
  intro φ hφ
  have hN : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (J ⧸ Subgroup.center J)) := by
    rw [h8]
    norm_num
  obtain ⟨x, hx⟩ := isInner_of_pElement hp hφ hN
  exact ⟨x, hx.symm⟩

theorem kernel11_6T_of_tables (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers) :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.Kernel11_6T :=
  fun _ _ _ hq hK _ hp hp2 hU => kernel11_6U_conj hGA hSpM hq hK hp hp2 hU

theorem kernel11_6U_fixes_center (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    {J : Type} [Group J] [Finite J] (hq : CFSG.Open.IsQuasisimple J)
    (hK : CFSG.Open.IsKGroup J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hU : ∃ U : Subgroup J, U ≤ Subgroup.center J ∧ CFSG.Open.IsElemAbelian p U ∧
      Nat.card U = p ^ 2) :
    ∀ φ : MulAut J, IsPGroup p (Subgroup.zpowers φ) →
      ∀ z ∈ Subgroup.center J, φ z = z := by
  intro φ hφ z hz
  obtain ⟨x, rfl⟩ := kernel11_6U_conj hGA hSpM hq hK hp hp2 hU φ hφ
  change x * z * x⁻¹ = z
  rw [Subgroup.mem_center_iff.mp hz x, mul_inv_cancel_right]
