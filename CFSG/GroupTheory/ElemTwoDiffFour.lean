module

public import Mathlib.GroupTheory.Index

import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GroupTheory

theorem card_closure_range_apply_mul_inv_eq_four {V : Type*} [Group V] [Finite V]
    (hcomm : ∀ x y : V, x * y = y * x) (hexp : ∀ x : V, x * x = 1)
    {τ σ : MulAut V} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hστ : σ * τ * σ⁻¹ = τ⁻¹)
    {D : Subgroup V} (hD : D.index ≤ 2) (hσD : ∀ d ∈ D, σ d = d) :
    Nat.card (Subgroup.closure (Set.range fun v : V => τ v * v⁻¹)) = 4 := by
  obtain ⟨δ, hδ⟩ : ∃ δ : V →* V, ∀ v, δ v = τ v * v⁻¹ :=
    ⟨MonoidHom.mk' (fun v => τ v * v⁻¹) fun x y => by
      rw [map_mul, mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc (τ y),
        hcomm (τ y * y⁻¹) x⁻¹], fun _ => rfl⟩
  have hcl : (Set.range fun v : V => τ v * v⁻¹) = δ.range := by
    rw [MonoidHom.coe_range]
    exact congrArg Set.range (funext fun v => (hδ v).symm)
  rw [hcl, Subgroup.closure_eq]
  have hfix : ∀ v, τ (τ v) = v → τ v = v := fun v hv => by
    have h3 := DFunLike.congr_fun hτ3 v
    rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply, hv, MulAut.one_apply] at h3
  have hστ' : ∀ w, σ (τ w) = τ⁻¹ (σ w) := fun w => by
    simpa only [MulAut.mul_apply] using DFunLike.congr_fun (mul_inv_eq_iff_eq_mul.mp hστ) w
  have hle : Nat.card δ.range ≤ 4 := by
    have hker : D ⊓ D.comap τ.toMonoidHom ≤ δ.ker := fun d hd => by
      obtain ⟨hd1, hd2⟩ := Subgroup.mem_inf.mp hd
      have h := hστ' d
      rw [hσD d hd1, hσD (τ d) hd2] at h
      rw [MonoidHom.mem_ker, hδ, mul_inv_eq_one]
      exact hfix d (by rw [h, MulAut.apply_inv_self])
    calc Nat.card δ.range = δ.ker.index := (Subgroup.index_ker δ).symm
      _ ≤ (D ⊓ D.comap τ.toMonoidHom).index := Subgroup.index_antitone hker
      _ ≤ D.index * (D.comap τ.toMonoidHom).index := Subgroup.index_inf_le
      _ = D.index * D.index := by
        rw [D.index_comap_of_surjective (f := τ.toMonoidHom) τ.surjective]
      _ ≤ 2 * 2 := Nat.mul_le_mul hD hD
  obtain ⟨v, hv⟩ : ∃ v, τ v ≠ v := not_forall.mp fun h => hτ1 (MulEquiv.ext h)
  have hu : δ v ≠ 1 := by rwa [hδ, ne_eq, mul_inv_eq_one]
  have hτu : τ (δ v) = δ (τ v) := by rw [hδ, hδ, map_mul, map_inv]
  have h2 : 2 ∣ Nat.card δ.range := by
    have h := δ.range.orderOf_dvd_natCard (δ.mem_range.mpr ⟨v, rfl⟩)
    rwa [orderOf_eq_prime (p := 2) (by rw [pow_two, hexp]) hu] at h
  have hne2 : Nat.card δ.range ≠ 2 := by
    intro hcard
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : δ.range)).mp hcard
    have e1 := hy ⟨δ v, δ.mem_range.mpr ⟨v, rfl⟩⟩ fun h => hu (congrArg Subtype.val h)
    have e2 := hy ⟨δ (τ v), δ.mem_range.mpr ⟨τ v, rfl⟩⟩ fun h =>
      hu (τ.map_eq_one_iff.mp (hτu.trans (congrArg Subtype.val h)))
    have hτδ : τ (δ v) = δ v := hτu.trans (congrArg Subtype.val (e2.trans e1.symm))
    have hτv : τ v = δ v * v := by rw [hδ, inv_mul_cancel_right]
    refine hv (hfix v ?_)
    calc τ (τ v) = τ (δ v * v) := by rw [← hτv]
      _ = δ v * (δ v * v) := by rw [map_mul, hτδ, hτv]
      _ = v := by rw [← mul_assoc, hexp, one_mul]
  have := Nat.card_pos (α := δ.range)
  omega

end CFSG.GroupTheory
