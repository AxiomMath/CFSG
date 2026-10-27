module

public import CFSG.Sporadic.SmallOddCore.Co3Classes
public import CFSG.RankThree.PartTwo.Census.Sporadic.Centralizer

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.SmallOddCore (ctuc_co3_complete_inner_involution_classes)
open CFSG.RankThree.PartTwo.Census

section Certified


theorem card_centralizer_co3_involution {u : NativeSporadic.Co3} (hu : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.Co3)) = 2903040 ∨
      Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.Co3)) = 190080 := by
  have hcard : Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.Co3)) =
      Nat.card ↥(co3P ⊓ Subgroup.centralizer
        ({((co3PermEquiv u : co3P) : Equiv.Perm (Fin 276))} : Set (Equiv.Perm (Fin 276)))) := by
    rw [@card_centralizer_mulEquiv NativeSporadic.Co3 co3P Units.instGroup (Subgroup.toGroup _)
      co3PermEquiv u, card_centralizer_subgroup]
  have hv2 : orderOf ((co3PermEquiv u : co3P) : Equiv.Perm (Fin 276)) = 2 := by
    rw [Subgroup.orderOf_coe, @MulEquiv.orderOf_eq NativeSporadic.Co3 Units.instMonoid co3P _
      co3PermEquiv u, hu]
  obtain ⟨-, -, -, hcl, -, -⟩ := ctuc_co3_complete_inner_involution_classes
  have hconj : ∀ g ∈ co3P, ∀ x : Equiv.Perm (Fin 276),
      Nat.card ↥(co3P ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set (Equiv.Perm (Fin 276)))) =
        Nat.card ↥(co3P ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 276)))) :=
    fun g hg x => card_inf_centralizer_conj co3P
      (fun m hm => co3P.mul_mem (co3P.mul_mem hg hm) (co3P.inv_mem hg))
      (fun m hm => co3P.mul_mem (co3P.mul_mem (co3P.inv_mem hg) hm) hg) x
  by_cases hz : ∃ g ∈ co3P, ((co3PermEquiv u : co3P) : Equiv.Perm (Fin 276)) = g * co3Z * g⁻¹
  · left
    obtain ⟨g, hg, hvg⟩ := hz
    rw [hvg, hconj g hg, ← co3M_eq_centralizer] at hcard
    rw [hcard]
    exact card_co3M
  · right
    have ht : ∃ g ∈ co3P,
        ((co3PermEquiv u : co3P) : Equiv.Perm (Fin 276)) = g * co3Tt * g⁻¹ := by
      by_contra hn
      exact hz ((hcl _ (co3PermEquiv u).2 hv2).2 hn)
    obtain ⟨g, hg, hvg⟩ := ht
    rw [hvg, hconj g hg, ← co3M1_eq_centralizer] at hcard
    rw [hcard]
    exact card_co3M1

theorem card_centralizer_of_isSporadic_co3 {G : Type} [Group G] (hG : IsSporadic G .Co3) {t : G}
    (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) = 2903040 ∨
      Nat.card (Subgroup.centralizer ({t} : Set G)) = 190080 := by
  obtain ⟨e⟩ := hG
  have hcard := @card_centralizer_mulEquiv G NativeSporadic.Co3 _ Units.instGroup e t
  rw [hcard]
  exact card_centralizer_co3_involution (by
    rw [@MulEquiv.orderOf_eq G _ NativeSporadic.Co3 Units.instMonoid e t, ht])

end Certified

end CFSG.EvenSporadicStandard.M12Std
