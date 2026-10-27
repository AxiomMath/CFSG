module

public import CFSG.LieType.ChevTwo.OppCl.FormsSplitBasic

public section

namespace CFSG.LieType.ChevTwo.OppCl.FS

open CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V] [Finite V]

theorem exists_avg (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (Rh : Subgroup (Equiv.Perm V))
    (hs : Rh ≤ semilinGroup F V) (hR : IsPGroup p Rh) (s : V →ₗ[F] V) :
    ∃ (T : Finset (Equiv.Perm V)) (s' : V →ₗ[F] V),
      (∀ r, r ∈ T ↔ r ∈ Rh) ∧ (∀ v, s' v = ∑ r ∈ T, r (s (r⁻¹ v))) ∧
        ((T.card : ℕ) : F) = 1 ∧ ∀ r ∈ Rh, ∀ v, r (s' v) = s' (r v) := by
  classical
  set T : Finset (Equiv.Perm V) := (Set.toFinite (Rh : Set (Equiv.Perm V))).toFinset with hTdef
  have hT : ∀ r, r ∈ T ↔ r ∈ Rh := fun r => by
    simp [hTdef]
  have hrr : ∀ (r : Equiv.Perm V) (x : V), r (r⁻¹ x) = x := fun r x => r.apply_symm_apply x
  have hrr' : ∀ (r : Equiv.Perm V) (x : V), r⁻¹ (r x) = x := fun r x => r.symm_apply_apply x
  have hadd : ∀ r ∈ Rh, ∀ u v : V, r (u + v) = r u + r v := fun r hr u v => (hs hr).1 u v
  have hinvadd : ∀ r ∈ Rh, ∀ u v : V, r⁻¹ (u + v) = r⁻¹ u + r⁻¹ v := fun r hr u v =>
    (hs (inv_mem hr)).1 u v
  have hsmul : ∀ r ∈ Rh, ∀ (c : F) (v : V), r (s (r⁻¹ (c • v))) = c • r (s (r⁻¹ v)) := by
    intro r hr c v
    obtain ⟨σ, hσ⟩ := (hs hr).2
    have h1 : r⁻¹ (c • v) = σ.symm c • r⁻¹ v := by
      apply r.injective
      rw [hrr, hσ, RingEquiv.apply_symm_apply, hrr]
    rw [h1, map_smul, hσ, RingEquiv.apply_symm_apply]
  let f : V → V := fun v => ∑ r ∈ T, r (s (r⁻¹ v))
  have hf_add : ∀ u v, f (u + v) = f u + f v := by
    intro u v
    simp only [f]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := (hT r).1 hr
    rw [hinvadd r hr', map_add, hadd r hr']
  have hf_smul : ∀ (c : F) v, f (c • v) = c • f v := by
    intro c v
    simp only [f]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun r hr => hsmul r ((hT r).1 hr) c v
  refine ⟨T, ⟨⟨f, hf_add⟩, hf_smul⟩, hT, fun v => rfl, ?_, ?_⟩
  · have hcard : T.card = Nat.card Rh :=
      (Nat.card_eq_card_finite_toFinset (Set.toFinite (Rh : Set (Equiv.Perm V)))).symm
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    have hodd : Odd (p ^ n) := ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
    rw [hcard, hn]
    exact natCast_eq_one_of_odd_of_two_eq_zero hodd CharTwo.two_eq_zero
  · intro r₀ hr₀ v
    show r₀ (f v) = f (r₀ v)
    simp only [f]
    rw [semilin_sum (hs hr₀)]
    refine Finset.sum_equiv (Equiv.mulLeft r₀) (fun r => ?_) (fun r hr => ?_)
    · simp only [Equiv.coe_mulLeft, hT]
      exact ⟨fun h => mul_mem hr₀ h, fun h => by simpa using mul_mem (inv_mem hr₀) h⟩
    · simp only [Equiv.coe_mulLeft, mul_inv_rev, Equiv.Perm.mul_apply, hrr']

end CFSG.LieType.ChevTwo.OppCl.FS
