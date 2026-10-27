module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace Subgroup

variable {Y : Type*} [Group Y]

theorem conjNormal_injective_of_centralizer_eq_bot {N : Subgroup Y} [N.Normal]
    (hC : centralizer (N : Set Y) = ⊥) :
    Function.Injective (MulAut.conjNormal : Y →* MulAut N) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ centralizer (N : Set Y) := by
    intro n hn
    have h := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : Y)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    have hgn : g * n = n * g := by
      simpa [mul_assoc] using congrArg (fun x : Y => x * g) h
    exact hgn.symm
  simpa [hC] using hmem

theorem conjNormal_injective_of_centralizer_le {N : Subgroup Y} [N.Normal]
    (hC : centralizer (N : Set Y) ≤ N) (hZ : center N = ⊥) :
    Function.Injective (MulAut.conjNormal : Y →* MulAut N) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ n : N, MulAut.conjNormal g n = n := by
    intro n
    have := congrArg (fun f : MulAut N => f n) hg
    simpa using this
  have hcomm : ∀ n : N, (n : Y) * g = g * n := by
    intro n
    have hval : g * (n : Y) * g⁻¹ = (n : Y) := by
      simpa [MulAut.conjNormal_apply] using congrArg Subtype.val (hfix n)
    have hgn : g * (n : Y) = (n : Y) * g := by
      simpa [mul_assoc] using congrArg (fun x : Y => x * g) hval
    exact hgn.symm
  have hmem : g ∈ centralizer (N : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact hcomm ⟨n, hn⟩
  have hgN : g ∈ N := hC hmem
  have hcenter : (⟨g, hgN⟩ : N) ∈ center N := by
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    exact hcomm n
  have hone : (⟨g, hgN⟩ : N) = 1 := by
    have := hcenter
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  simpa using congrArg Subtype.val hone

theorem card_le_card_mulAut_of_centralizer_le [Finite Y] {N : Subgroup Y} [N.Normal]
    (hC : centralizer (N : Set Y) ≤ N) (hZ : center N = ⊥) :
    Nat.card Y ≤ Nat.card (MulAut N) := by
  haveI : Finite N := Subtype.finite
  haveI : Finite (MulAut N) :=
    Finite.of_injective (fun f : MulAut N => (f : N → N)) DFunLike.coe_injective
  exact Nat.card_le_card_of_injective (MulAut.conjNormal : Y →* MulAut N)
    (conjNormal_injective_of_centralizer_le hC hZ)

end Subgroup
