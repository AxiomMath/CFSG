module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private def base4Tau : Sym 4 := Equiv.swap 0 1 * Equiv.swap 2 3

private def base4Rho : Sym 4 where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def base4S : Sym 4 := Equiv.swap 0 1

private def base4F : DihedralGroup 4 → Sym 4
  | .r i => base4Rho ^ i.val
  | .sr i => base4S * base4Rho ^ i.val

private theorem base4Tau_cycleType : base4Tau.cycleType = {2, 2} := by
  unfold base4Tau
  exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

private theorem base4F_mul : ∀ x y : DihedralGroup 4,
    base4F (x * y) = base4F x * base4F y := by
  decide +kernel

private def base4Hom : DihedralGroup 4 →* Sym 4 where
  toFun := base4F
  map_one' := by decide +kernel
  map_mul' := base4F_mul

private theorem base4F_inj : Function.Injective base4F := by
  decide +kernel

private theorem base4F_comm : ∀ x : DihedralGroup 4,
    base4Tau * base4F x = base4F x * base4Tau := by
  decide +kernel

theorem symCent_base_four {τ : Sym 4} (hτ : τ.cycleType = {2, 2}) :
    Nonempty (↥(Subgroup.centralizer ({τ} : Set (Sym 4))) ≃* DihedralGroup 4) := by
  obtain ⟨e1⟩ := symCent_mulEquiv_of_isConj (g := τ) (h := base4Tau)
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hτ.trans base4Tau_cycleType.symm))
  have hcard : Nat.card (DihedralGroup 4) =
      Nat.card ↥(Subgroup.centralizer ({base4Tau} : Set (Sym 4))) := by
    rw [DihedralGroup.nat_card, Equiv.Perm.nat_card_centralizer base4Tau, base4Tau_cycleType]
    decide +kernel
  obtain ⟨e2⟩ := symCent_mulEquiv_of_injective base4Hom base4F_inj
    (fun x => by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact base4F_comm x)
    hcard
  exact ⟨e1.trans e2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
