module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem card_quotient_oddCore_dvd [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y) :
    Nat.card (X ⧸ oddCore X) ∣ Nat.card (Y ⧸ oddCore Y) := by
  let ψ : ↥X →* ↥Y := Subgroup.inclusion hXY
  let φ : ↥X →* ↥Y ⧸ oddCore ↥Y := (QuotientGroup.mk' (oddCore ↥Y)).comp ψ
  have hψinj : Function.Injective ψ := Subgroup.inclusion_injective hXY
  have hker : φ.ker = (oddCore ↥Y).comap ψ := by
    change ((QuotientGroup.mk' (oddCore ↥Y)).comp ψ).ker = (oddCore ↥Y).comap ψ
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hKodd : Odd (Nat.card φ.ker) := by
    rw [hker]
    exact (odd_card_oddCore' ↥Y).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective (oddCore ↥Y) ψ hψinj)
  have hKle : φ.ker ≤ oddCore ↥X := by
    show φ.ker ≤ sSup {N : Subgroup ↥X | N.Normal ∧ Odd (Nat.card N)}
    exact le_sSup ⟨inferInstance, hKodd⟩
  have h1 : Nat.card (↥X ⧸ oddCore ↥X) ∣ Nat.card (↥X ⧸ φ.ker) := by
    have h := Subgroup.card_quotient_dvd_card ((oddCore ↥X).map (QuotientGroup.mk' φ.ker))
    rw [← Nat.card_congr
      (QuotientGroup.quotientQuotientEquivQuotient φ.ker (oddCore ↥X) hKle).toEquiv]
    exact h
  have h2 : Nat.card (↥X ⧸ φ.ker) ∣ Nat.card (↥Y ⧸ oddCore ↥Y) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card φ.range
  exact h1.trans h2

theorem smallF3OmegaQuotient_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : SmallF3OmegaQuotient Q) : SmallF3OmegaQuotient Q' := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl (LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (LieModel.of_mulEquiv e h)))))

theorem isTwoU43_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : IsTwoU43 Q) : IsTwoU43 Q' := by
  obtain ⟨hcard, hLie⟩ := h
  have hmap : (center Q).map e.toMonoidHom = center Q' := Subgroup.map_center_eq e
  have hcard' : Nat.card (center Q') = 2 := by
    rw [← hmap,
      Subgroup.card_map_of_injective (K := center Q) (f := e.toMonoidHom) e.injective, hcard]
  refine ⟨hcard', ?_⟩
  exact LieModel.of_mulEquiv (QuotientGroup.congr (center Q) (center Q') e hmap) hLie

end CFSG.OddStandard.SmallF3.Omega
