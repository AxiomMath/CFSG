module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup

theorem normal_fpf_involution {X : Type*} [Group X] {S : Subgroup X} [S.Normal] [Finite S]
    {v : X} (hv : v * v = 1) (hC : ∀ s ∈ S, v * s = s * v → s = 1) :
    (∀ s ∈ S, v * s * v⁻¹ = s⁻¹) ∧ (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) ∧
      Odd (Nat.card S) := by
  let φ : S →* S :=
    { toFun := fun s => ⟨v * (s : X) * v⁻¹,
        (inferInstance : S.Normal).conj_mem (s : X) s.2 v⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        simp only [Subgroup.coe_mul, Subtype.coe_mk]
        group }
  have hφ : MonoidHom.FixedPointFree φ := by
    intro s hs
    apply Subtype.ext
    have hval : v * (s : X) * v⁻¹ = (s : X) := by
      simpa [φ] using congrArg (fun t : S => (t : X)) hs
    exact hC (s : X) s.2 (mul_inv_eq_iff_eq_mul.mp hval)
  have h2 : Function.Involutive φ := by
    intro s
    ext
    calc v * (v * (s : X) * v⁻¹) * v⁻¹
        = (v * v) * (s : X) * (v⁻¹ * v⁻¹) := by group
      _ = (s : X) := by rw [hv, ← mul_inv_rev, hv]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have h := congrArg (fun t : S => (t : X)) (congrFun (hφ.coe_eq_inv_of_involutive h2) ⟨s, hs⟩)
    simpa [φ] using h
  · intro a ha b hb
    exact Subtype.ext_iff.mp (hφ.commute_all_of_involutive h2 ⟨a, ha⟩ ⟨b, hb⟩)
  · exact hφ.odd_card_of_involutive h2

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
