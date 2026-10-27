module

public import CFSG.GH74.KGroups.M11
public import CFSG.ClassicalInvolution.Q3.Closing

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Blueprint

theorem m11_outer_trivial (hM : Q3.M11Facts) :
    ∀ φ : MulAut ↥NativeSporadic.M11, ∃ g, φ = MulAut.conj g := by
  obtain ⟨hsimple, hcard⟩ := hM
  have hX : NativeSporadic.IsSporadic NativeSporadic.M11 .M11 := ⟨MulEquiv.refl _⟩
  have hnab : ∃ a b : ↥NativeSporadic.M11, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : Std.Commutative (α := ↥NativeSporadic.M11) (· * ·) := ⟨fun a b => hcon a b⟩
    have : IsMulCommutative ↥NativeSporadic.M11 := ⟨hcomm⟩
    have hp := IsSimpleGroup.prime_card (α := ↥NativeSporadic.M11)
    rw [hcard] at hp
    norm_num at hp
  have hcen : Subgroup.center ↥NativeSporadic.M11 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥NativeSporadic.M11) with
      h' | h'
    · exact h'
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top b) a)
  have hinj : Function.Injective
      (MulAut.conj : ↥NativeSporadic.M11 →* MulAut ↥NativeSporadic.M11) := by
    intro g g' e
    have hc : g'⁻¹ * g ∈ Subgroup.center ↥NativeSporadic.M11 :=
      Subgroup.mem_center_iff.2 fun x => by
      have h1 := congrArg (fun α : MulAut ↥NativeSporadic.M11 => α x) e
      simp only [MulAut.conj_apply] at h1
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [← h1]
        _ = g'⁻¹ * g * x := by group
    rw [hcen, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  have : Finite (MulAut ↥NativeSporadic.M11) := GH74.KGroups.M11.finite_mulAut hX
  have hle : Nat.card (MulAut ↥NativeSporadic.M11) ≤ Nat.card ↥NativeSporadic.M11 := by
    rw [GH74.KGroups.M11.card_mulAut hX, hcard]
  have hsurj := (hinj.bijective_of_nat_card_le hle).2
  intro φ
  obtain ⟨g, hg⟩ := hsurj φ
  exact ⟨g, hg.symm⟩

end CFSG.ClassicalInvolution.Q3.Q3T6
