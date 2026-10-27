module

public import CFSG.LieType.BorelTits.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Unitary
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.LieType.BorelTits.OrthogonalEven

public section

namespace CFSG.LieType.BorelTits

open CFSG.Assembly.LowTwoRank

theorem charP_of_natCard_eq {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (h : Nat.card K = p ^ f) : CharP K p := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, h])

theorem holds_of_statedClassicalModel_of_even {G : Type} [Group G] {t : StatedLieTag}
    {n p f : ℕ}
    (hplus : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n →
      Holds (StatedProj (StatedOmega (StatedQuadPlus n K))) 2)
    (hminus : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      Holds (StatedProj (StatedOmega (StatedQuadMinus n K b c))) 2)
    (h : StatedClassicalModel G t n p f) : Holds G p := by
  obtain ⟨⟨hp, -, hadm⟩, hmodel⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  cases t with
  | PSL =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
    have := charP_of_natCard_eq hK
    exact (holds_statedProj_statedSL n K p).of_mulEquiv e.symm
  | PSU =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
    have : CharP K p := charP_of_natCard_eq (f := f * 2) (by rw [hK, pow_mul])
    exact (holds_statedProj_statedSU hK n).of_mulEquiv e.symm
  | PSp =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
    have := charP_of_natCard_eq hK
    exact (holds_statedProj_statedSp n K p).of_mulEquiv e.symm
  | POmegaOdd =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
    have := charP_of_natCard_eq hK
    exact (holds_statedProj_statedOmega_quadOdd n K p hadm.2 (by omega)).of_mulEquiv e.symm
  | POmegaPlus =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
    have := charP_of_natCard_eq hK
    rcases eq_or_ne p 2 with rfl | hp2
    · exact (hplus K hadm).of_mulEquiv e.symm
    · exact (holds_statedProj_statedOmega_quadPlus n K p hp2 (by omega)).of_mulEquiv e.symm
  | POmegaMinus =>
    obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hmodel
    have := charP_of_natCard_eq hK
    rcases eq_or_ne p 2 with rfl | hp2
    · exact (hminus K hadm b c hirr).of_mulEquiv e.symm
    · exact (holds_statedProj_statedOmega_quadMinus n K p hp2 (by omega) b c hirr).of_mulEquiv
        e.symm
  | _ => exact hmodel.elim

theorem holds_of_statedClassicalModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) : Holds G p :=
  holds_of_statedClassicalModel_of_even
    (fun K _ _ _ hn => holds_statedProj_statedOmega_quadPlus_two n K (by omega))
    (fun K _ _ _ hn b c hirr => holds_statedProj_statedOmega_quadMinus_two n K (by omega) b c hirr)
    h

end CFSG.LieType.BorelTits
