module

public import CFSG.LargeExtraspecial.AS35YTHubA
public import CFSG.LargeExtraspecial.A2ModARS
public import CFSG.LargeExtraspecial.A2ModCfgE
public import CFSG.LargeExtraspecial.A2ModCfgTA
public import CFSG.LargeExtraspecial.A2ModHubFrame
public import CFSG.LargeExtraspecial.AS35YTOrd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35YT

open Module CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley A2Mod

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}


theorem fix_eq_zero_of_psl [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ) {k : ℕ}
    (hk : 5 ≤ k) (hL : LieModel X .PSL k 2 1) {v : V} (hv : v ∈ commSpaceOf ρ ⊤)
    (hfix : ∀ x, ρ x v = v) : v = 0 := by
  have h := hD.arsHyp
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have h2 := hD.card_eq_two
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hDc := hD.conj_mem
  have hf1 : ∀ {f : ℕ} {E : Subgroup X}, E ∈ rootSet D → Nat.card E = 2 ^ f → f = 1 :=
    fun hE hc => Nat.pow_right_injective le_rfl ((hc.symm.trans (h2 _ hE)).trans (pow_one 2).symm)
  have h31 : 31 ∣ Nat.card X := by
    rw [(Ord.card_of_lieModel_PSL hL).2]
    exact Ord.dvd_ordA_two (a := 5) (by norm_num) (by omega) (by norm_num)
  have hbig : 12096 < Nat.card X :=
    Ord.twelve_thousand_lt_card_of_lieModel_classical (m := k) (Or.inl ⟨by omega, hL⟩)
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, hX⟩ | ⟨m, hm, A, B, hX, hgen⟩ |
      ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨-, ⟨F⟩⟩ | ⟨-, hm⟩ | hm
  ·
    have hm4 : 4 ≤ m := by
      by_contra hlt
      obtain ⟨A, B, hX', hgen⟩ := hX
      have hLm : LieModel X .PSL (m + 1) 2 1 := by
        rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
        · obtain ⟨f, -, hcard, hL'⟩ := hX'.lieModel_A_two hR hiso hZ hgen
          obtain rfl := hf1 (hX'.memA 0) (hcard _ (hX'.memA 0))
          exact hL'
        · obtain ⟨f, -, hcard, hL'⟩ := hX'.lieModel_A hR hiso hZ hm3 hgen
          obtain rfl := hf1 (hX'.memA ⟨0, by omega⟩) (hcard _ (hX'.memA ⟨0, by omega⟩))
          exact hL'
      rw [(Ord.card_of_lieModel_PSL hLm).2] at h31
      rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl <;> revert h31 <;> decide
    obtain ⟨Ψ, hs, hΨ⟩ := typeA_exists_surjective hR hiso hRD hDc hm hX
    obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) hΨ
    obtain ⟨P, Pd, hP⟩ := exists_isPointMaps hA' (by omega : 5 ≤ m + 1)
    have hv' : v ∈ commSpaceOf (ρ.comp Ψ) ⊤ := by
      rw [← commSpaceOf_range, MonoidHom.range_eq_top.mpr hs]
      exact hv
    exact fix_eq_zero_of_isPointMaps (by omega) hP hv' fun g => hfix (Ψ g)
  ·
    obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_D hR hiso hZ hm hgen
    obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
    exact (Ord.lieModel_PSL_false_of_POmega hL (Or.inl hL')).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · rcases frame_cases F hD hA with ⟨n, -, hC⟩ | ⟨n, -, hB⟩ | hle
    · exact (lieModel_PSL_false_of_PSp hL hC).elim
    · exact (Ord.lieModel_PSL_false_of_POmega hL (Or.inr hB)).elim
    · omega
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · rw [Ord.card_of_lieModel_PSU33 hm] at hbig
    omega

end CFSG.LargeExtraspecial.AS35YT
