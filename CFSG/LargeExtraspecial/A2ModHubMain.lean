module

public import CFSG.LargeExtraspecial.A2ModHubFrame
public import CFSG.LargeExtraspecial.A2ModARS
public import CFSG.LargeExtraspecial.A2ModCfgTA
public import CFSG.LargeExtraspecial.A2ModCfgTD
public import CFSG.LargeExtraspecial.A2ModCfgE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}


theorem hub_any [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ) :
    (∃ m, 3 ≤ m ∧ LieModel X .PSL m 2 1) ∨ (∃ m, 4 ≤ m ∧ LieModel X .POmegaPlus m 2 1) ∨
      (∃ n, 3 ≤ n ∧ LieModel X .PSp n 2 1) ∨ (∃ n, 4 ≤ n ∧ LieModel X .POmegaMinus n 2 1) ∨
      Nat.card X ≤ 12096 := by
  have h := hD.arsHyp
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have h2 := hD.card_eq_two
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hDc := hD.conj_mem
  have hf1 : ∀ {f : ℕ} {E : Subgroup X}, E ∈ rootSet D → Nat.card E = 2 ^ f → f = 1 :=
    fun hE hc => Nat.pow_right_injective le_rfl ((hc.symm.trans (h2 _ hE)).trans (pow_one 2).symm)
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, A, B, hX, hgen⟩ |
      ⟨m, hm, A, B, hX, hgen⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨-, ⟨F⟩⟩ |
      ⟨-, hm⟩ | hm
  · rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨f, -, hcard, hL⟩ := hX.lieModel_A_two hR hiso hZ hgen
      obtain rfl := hf1 (hX.memA 0) (hcard _ (hX.memA 0))
      exact Or.inl ⟨3, le_rfl, hL⟩
    · obtain ⟨f, -, hcard, hL⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
      exact Or.inl ⟨m + 1, by omega, hL⟩
  · obtain ⟨f, -, hcard, hL⟩ := hX.lieModel_D hR hiso hZ hm hgen
    obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
    exact Or.inr (Or.inl ⟨m, hm, hL⟩)
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · rcases frame_cases F hD hA with hC | hB | hle
    · exact Or.inr (Or.inr (Or.inl hC))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hB)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hle)))
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [Ord.card_of_lieModel_PSU33 hm]; norm_num))))

theorem exceptional_false [Finite X] {τ : StatedLieTag}
    (hτ : τ ∈ ({.F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    (hX : LieModel X τ 0 2 1) (hD : RootClass X D) (hA : A2Action D Q ρ) : False := by
  have hlt := Ord.twelve_thousand_lt_card_of_lieModel_exceptional hτ hX
  rcases hub_any hD hA with ⟨m, -, h⟩ | ⟨m, -, h⟩ | ⟨n, -, h⟩ | ⟨n, -, h⟩ | hle
  · exact Ord.lieModel_PSL_false_of_exceptional hτ h hX
  · exact Ord.lieModel_POmega_false_of_exceptional hτ (Or.inl h) hX
  · exact Ord.lieModel_PSp_false_of_exceptional hτ h hX
  · exact Ord.lieModel_POmega_false_of_exceptional hτ (Or.inr h) hX
  · omega

theorem irreducible_classify [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : 10 ≤ finrank (ZMod 2) V) :
    (∃ k, 5 ≤ k ∧ finrank (ZMod 2) V = 2 * k ∧
        (LieModel X .POmegaPlus k 2 1 ∨ LieModel X .POmegaMinus k 2 1)) ∨
      Nat.card X ≤ 12096 := by
  have h := hD.arsHyp
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have h2 := hD.card_eq_two
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hDc := hD.conj_mem
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, hX⟩ | ⟨m, hm, hX⟩ | hX | hX | hX |
      ⟨-, ⟨F⟩⟩ | ⟨-, hm⟩ | hm
  · exact absurd hV (not_le.mpr (typeA_finrank_lt hR hiso hRD hDc hA hm hX hirr))
  · rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | hm5
    · have := typeD_four_finrank_le hR hiso hRD hDc hA hX hirr
      omega
    · obtain ⟨hdim, hL⟩ := typeD_irreducible hR hiso hZ hRD hDc hA hm5 hX hirr
      exact Or.inl ⟨m, hm5, hdim, Or.inl hL⟩
  · exact (typeE_false hR hiso hRD hDc hA (Or.inl rfl) hX).elim
  · exact (typeE_false hR hiso hRD hDc hA (Or.inr (Or.inl rfl)) hX).elim
  · exact (typeE_false hR hiso hRD hDc hA (Or.inr (Or.inr rfl)) hX).elim
  · rcases frame_cases_irr F hD hA hirr hV with ⟨n, hn, hdim, hL⟩ | hle
    · exact Or.inl ⟨n, hn, hdim, Or.inr hL⟩
    · exact Or.inr hle
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · exact Or.inr (by rw [Ord.card_of_lieModel_PSU33 hm]; norm_num)

end CFSG.LargeExtraspecial.A2Mod
