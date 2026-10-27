module

public import CFSG.ClassicalInvolution.Q3.AE.Group
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG.ClassicalInvolution.Q3.AE Wr

theorem card_wr_five : Nat.card (Wr 5) = 3840 := by
  have e : Wr 5 ≃ (Fin 5 → ZMod 2) × Equiv.Perm (Fin 5) :=
    { toFun := fun a => (a.vec, a.perm)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_perm, Nat.card_zmod, Nat.card_fin]
  decide

theorem card_AEQ_five_le : Nat.card (AEQ 5) ≤ 3840 := by
  rw [← card_wr_five]
  exact Nat.card_le_card_of_surjective (mkQ 5) (QuotientGroup.mk'_surjective _)

theorem card_evenVec_zero : Nat.card {v : Fin 6 → ZMod 2 // ∑ i, v i = 0 ∧ v 5 = 0} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem five_thousand_le_card_ae6 : 5760 ≤ Nat.card ((aeSub 6).map (mkQ 6)) := by
  classical
  let S : Type := {v : Fin 6 → ZMod 2 // ∑ i, v i = 0 ∧ v 5 = 0}
  have hS : Nat.card S = 16 := card_evenVec_zero
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hmem : ∀ p : S × alternatingGroup (Fin 6),
      (⟨p.1.1, p.2.1⟩ : Wr 6) ∈ aeSub 6 := by
    intro p
    refine ⟨?_, Equiv.Perm.mem_alternatingGroup.mp p.2.2⟩
    exact p.1.2.1
  let F : S × alternatingGroup (Fin 6) → ↥((aeSub 6).map (mkQ 6)) := fun p =>
    ⟨mkQ 6 ⟨p.1.1, p.2.1⟩, Subgroup.mem_map_of_mem _ (hmem p)⟩
  have hF : Function.Injective F := by
    intro p p' h
    have h1 : mkQ 6 ⟨p.1.1, p.2.1⟩ = mkQ 6 ⟨p'.1.1, p'.2.1⟩ := congrArg Subtype.val h
    rcases mkQ_eq_iff.mp h1 with h2 | h2
    · have h3 : (⟨p.1.1, p.2.1⟩ : Wr 6) = ⟨p'.1.1, p'.2.1⟩ := inv_mul_eq_one.mp h2
      have hv : p.1.1 = p'.1.1 := congrArg Wr.vec h3
      have hp : p.2.1 = p'.2.1 := congrArg Wr.perm h3
      exact Prod.ext (Subtype.ext hv) (Subtype.ext hp)
    · exfalso
      have h3 : (⟨p'.1.1, p'.2.1⟩ : Wr 6) = ⟨p.1.1, p.2.1⟩ * allOnes 6 := by
        rw [← h2, mul_inv_cancel_left]
      have h4 := congrFun (congrArg Wr.vec h3) 5
      rw [mul_vec] at h4
      have e1 : (allOnes 6).vec ((⟨p.1.1, p.2.1⟩ : Wr 6).perm.symm 5) = 1 := rfl
      have e2 : (⟨p.1.1, p.2.1⟩ : Wr 6).vec 5 = 0 := p.1.2.2
      have e3 : (⟨p'.1.1, p'.2.1⟩ : Wr 6).vec 5 = 0 := p'.1.2.2
      rw [e1, e2, e3] at h4
      exact absurd h4 (by decide)
  have h5 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, hS, hA] at h5
  omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
