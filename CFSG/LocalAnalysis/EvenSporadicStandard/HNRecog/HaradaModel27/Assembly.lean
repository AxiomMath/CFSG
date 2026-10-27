module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Hmod
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA
  CFSG.EvenSporadicStandard.HNRecog.Harada.S25

theorem haradaInterfaceAll_of_P
    (hiso : ∀ {H : Type} [Group H] {E : Subgroup H}, TwoHS.IsF5Centralizer H E →
      ∃ Ψ : H ≃* ↥P1408, ∀ x : H, x ∈ E ↔ ((Ψ x : ↥P1408) : Equiv.Perm (Fin 1408)) ∈ blocks1408)
    (hcard : ∀ {H : Type} [Group H] {E : Subgroup H}, TwoHS.IsF5Centralizer H E →
      Nat.card ↥P1408 = 177408000)
    (hP : ∀ {Ep : Subgroup ↥P1408}, Nat.card ↥P1408 = 177408000 →
      TwoHS.IsF5Centralizer ↥P1408 Ep →
      (∀ x : ↥P1408, x ∈ Ep ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) →
      ∃ (a z b z₁ : ↥P1408) (S T T' W0 : Subgroup ↥P1408) (ι : Elem2 6 →* ↥P1408) (zv : V6)
        (R0 F : Subgroup ↥P1408), HaradaFactsAll ↥P1408 Ep a z b z₁ S T T' W0 ι zv R0 F) :
    HaradaInterfaceAll := fun H _ E h => by
  obtain ⟨Ψ, hΨ⟩ := hiso h
  have hF : TwoHS.IsF5Centralizer ↥P1408 (E.map (Ψ : H →* ↥P1408)) :=
    Section3.isF5Centralizer_map' Ψ h
  have hE : ∀ x : ↥P1408, x ∈ E.map (Ψ : H →* ↥P1408) ↔
      (x : Equiv.Perm (Fin 1408)) ∈ blocks1408 := fun x => by
    refine (Subgroup.mem_map_equiv (f := Ψ)).trans ?_
    rw [hΨ, MulEquiv.apply_symm_apply]
  have hE' : (E.map (Ψ : H →* ↥P1408)).map (Ψ.symm : ↥P1408 →* H) = E := by
    ext x
    refine (Subgroup.mem_map_equiv (f := Ψ.symm)).trans ?_
    refine (Subgroup.mem_map_equiv (f := Ψ)).trans ?_
    simp
  obtain ⟨a, z, b, z₁, S, T, T', W0, ι, zv, R0, F, hFP⟩ := hP (hcard h) hF hE
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, HaradaFactsAll.of_mulEquiv Ψ.symm hE' hFP⟩

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel27
