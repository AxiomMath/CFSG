module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

theorem exists_apply_mul_eq {V : Type} [CommGroup V] [Finite V] (hsq : ∀ v : V, v * v = 1)
    (α : MulAut V) (hα : α * α = 1)
    (hcard : Nat.card V = Nat.card {v : V // α v = v} ^ 2) {c : V} (hc : α c = c) :
    ∃ v : V, α v * v = c := by
  classical
  have hαα : ∀ v : V, α (α v) = v := by
    intro v
    have := congrArg (fun m : MulAut V => m v) hα
    simpa using this
  have hinv : ∀ a : V, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  let δ : V →* V := MonoidHom.mk' (fun v => α v * v) (by
    intro a b
    simp only [map_mul]
    ac_rfl)
  have hδ : ∀ v, δ v = α v * v := fun v => rfl
  let Fix : Subgroup V := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id V)
  have hFix : ∀ v, v ∈ Fix ↔ α v = v := fun v => Iff.rfl
  have hker : δ.ker ≤ Fix := by
    intro w hw
    rw [MonoidHom.mem_ker, hδ] at hw
    rw [hFix]
    exact (eq_inv_of_mul_eq_one_left hw).trans (hinv w)
  have hFix_le_ker : Fix ≤ δ.ker := by
    intro w hw
    rw [MonoidHom.mem_ker, hδ, (hFix w).mp hw]
    exact hsq w
  have hrange : δ.range ≤ Fix := by
    rintro _ ⟨w, rfl⟩
    rw [hFix, hδ]
    simp only [map_mul, hαα]
    exact mul_comm _ _
  have hFixcard : Nat.card Fix = Nat.card {v : V // α v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hFix)
  have hV2 : Nat.card V = Nat.card Fix ^ 2 := by
    rw [hcard, ← hFixcard]
  have hker_eq : δ.ker = Fix := le_antisymm hker hFix_le_ker
  have hprod : Nat.card Fix * Nat.card δ.range = Nat.card Fix ^ 2 := by
    have h1 : Nat.card δ.ker * Nat.card δ.range = Nat.card V :=
      Subgroup.card_ker_mul_card_range δ
    rw [hker_eq] at h1
    rw [h1, hV2]
  have hFixpos : 0 < Nat.card Fix := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
  have hcardRange : Nat.card δ.range = Nat.card Fix := by
    refine Nat.eq_of_mul_eq_mul_left hFixpos ?_
    rw [hprod, pow_two]
  have hrange_eq : δ.range = Fix :=
    Subgroup.eq_of_le_of_card_ge hrange (le_of_eq hcardRange.symm)
  have hcRange : c ∈ δ.range := by
    rw [hrange_eq]
    exact (hFix c).mpr hc
  rw [MonoidHom.mem_range] at hcRange
  obtain ⟨v, hv⟩ := hcRange
  exact ⟨v, by rw [← hδ v]; exact hv⟩

end C10

end CFSG.OddStandard.SmallF3.Omega
