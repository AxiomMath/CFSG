module

public import CFSG.CharacterTheory.Semidihedral.Local.CentralizerOddCoreAction
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.GroupTheory

open SemidirectProduct

universe u

variable {G P : Type*} [Group G] [Group P]

@[expose] def actionPCore (p : ℕ) (ρ : G →* MulAut P) : Subgroup G :=
  (CFSG.pCore p (G ⧸ ρ.ker)).comap (QuotientGroup.mk' ρ.ker)

@[expose] def actionCommutator (ρ : G →* MulAut P) (u : P) (x : G) : P ⋊[ρ] G :=
  (inl u)⁻¹ * (inr x)⁻¹ * inl u * inr x

@[expose] def IsPStableAction (p : ℕ) (ρ : G →* MulAut P) : Prop :=
  ∀ x : G, (∀ u : P, (actionCommutator ρ u x)⁻¹ * (inr x)⁻¹ * actionCommutator ρ u x * inr x = 1) →
    x ∈ actionPCore p ρ

theorem inr_inv_mul_inl_mul_inr (ρ : G →* MulAut P) (u : P) (x : G) :
    ((inr x)⁻¹ * inl u * inr x : P ⋊[ρ] G) = inl (ρ x⁻¹ u) := by
  rw [inl_aut, ← map_inv, inv_inv]

theorem actionCommutator_eq (ρ : G →* MulAut P) (u : P) (x : G) :
    actionCommutator ρ u x = inl (u⁻¹ * ρ x⁻¹ u) := by
  rw [actionCommutator, mul_assoc, mul_assoc, ← mul_assoc (inr x)⁻¹,
    inr_inv_mul_inl_mul_inr, ← map_inv, ← map_mul]

theorem double_commutator_eq_one_iff (ρ : G →* MulAut P) (u : P) (x : G) :
    (actionCommutator ρ u x)⁻¹ * (inr x)⁻¹ * actionCommutator ρ u x * inr x = 1 ↔
      ρ x⁻¹ (u⁻¹ * ρ x⁻¹ u) = u⁻¹ * ρ x⁻¹ u := by
  rw [actionCommutator_eq, mul_assoc, mul_assoc, ← mul_assoc (inr x)⁻¹,
    inr_inv_mul_inl_mul_inr, ← map_inv, ← map_mul, ← map_one (inl : P →* P ⋊[ρ] G),
    inl_injective.eq_iff, inv_mul_eq_one, eq_comm]

theorem pow_apply_of_fixes (α : MulAut P) (hα : ∀ u : P, α (u⁻¹ * α u) = u⁻¹ * α u) (u : P)
    (k : ℕ) : (α ^ k) u = u * (u⁻¹ * α u) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hα, pow_succ', ← mul_assoc,
      mul_inv_cancel_left]

theorem pow_card_mem_ker [Finite P] (ρ : G →* MulAut P) (x : G)
    (hx : ∀ u : P, (actionCommutator ρ u x)⁻¹ * (inr x)⁻¹ * actionCommutator ρ u x * inr x = 1) :
    x ^ Nat.card P ∈ ρ.ker := by
  have hfix : ∀ u : P, ρ x⁻¹ (u⁻¹ * ρ x⁻¹ u) = u⁻¹ * ρ x⁻¹ u := fun u =>
    (double_commutator_eq_one_iff ρ u x).mp (hx u)
  have hpow : ρ x⁻¹ ^ Nat.card P = 1 := by
    ext u
    rw [pow_apply_of_fixes _ hfix, pow_card_eq_one', mul_one, MulAut.one_apply]
  rw [MonoidHom.mem_ker, ← inv_inj, ← map_inv, inv_one, ← inv_pow, map_pow]
  exact hpow

theorem normal_sylow_acting_groups_have_stable_subgroup_actions {G : Type*} [Group G]
    [Finite G] (p : ℕ) [Fact p.Prime] (A : Sylow p G) (hA : (A : Subgroup G).Normal)
    (H : Subgroup G) (P : Type u) [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : H →* MulAut P) : IsPStableAction p ρ := by
  intro x hx
  obtain ⟨e, he⟩ := (IsPGroup.iff_card.mp hP)
  have hxe : QuotientGroup.mk' ρ.ker x ^ p ^ e = 1 := by
    rw [← map_pow, ← he]
    exact (QuotientGroup.eq_one_iff _).mpr (pow_card_mem_ker ρ x hx)
  have : (A : Subgroup G).Normal := hA
  let Q : Subgroup (H ⧸ ρ.ker) := ((A : Subgroup G).subgroupOf H).map (QuotientGroup.mk' ρ.ker)
  have hQnormal : Q.Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective ρ.ker)
  have hQp : IsPGroup p Q :=
    (A.isPGroup'.comap_subtype (K := H)).map (QuotientGroup.mk' ρ.ker) |>.of_equiv (by rfl)
  have hQindex : ¬ p ∣ Q.index := by
    intro hdvd
    have h1 : Q.index ∣ ((A : Subgroup G).subgroupOf H).index :=
      Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective ρ.ker)
    have h2 : ((A : Subgroup G).subgroupOf H).index ∣ (A : Subgroup G).index :=
      Subgroup.relIndex_dvd_index_of_normal _ _
    exact A.not_dvd_index ((hdvd.trans h1).trans h2)
  have hxQ : QuotientGroup.mk' ρ.ker x ∈ Q :=
    CFSG.Semidihedral.Local.mem_of_pow_eq_one_of_index Q hQindex hxe
  exact (le_sSup ⟨hQnormal, hQp⟩ : Q ≤ CFSG.pCore p (H ⧸ ρ.ker)) hxQ

end CFSG.GroupTheory
