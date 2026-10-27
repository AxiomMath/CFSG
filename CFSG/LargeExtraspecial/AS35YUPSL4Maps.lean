module

public import CFSG.LargeExtraspecial.A2ModARS
public import CFSG.LargeExtraspecial.A2ModCfgE
public import CFSG.LargeExtraspecial.A2ModCfgTA
public import CFSG.LargeExtraspecial.AS35YTHubF
public import CFSG.LargeExtraspecial.AS35YTOrd

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.LargeExtraspecial.AS35YU

open Module CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ARS.ExclNS A2Mod AS35YT

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem exists_surjective_sl4_of_lieModel_psl4 [Finite X] (hD : RootClass X D)
    (hA : A2Action D Q ρ) (hL : LieModel X .PSL 4 2 1) :
    ∃ Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* X, Function.Surjective Ψ ∧
      Function.Injective Ψ ∧ A2Action (transvectionSet 4 (ZMod 2)) Q (ρ.comp Ψ) := by
  have h := hD.arsHyp
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have h2 := hD.card_eq_two
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hDc := hD.conj_mem
  have hf1 : ∀ {f : ℕ} {E : Subgroup X}, E ∈ rootSet D → Nat.card E = 2 ^ f → f = 1 :=
    fun hE hc => Nat.pow_right_injective le_rfl ((hc.symm.trans (h2 _ hE)).trans (pow_one 2).symm)
  have hcardX : Nat.card X = 20160 := by
    rw [(Ord.card_of_lieModel_PSL hL).2]
    decide
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, hX⟩ | ⟨m, hm, A, B, hX, hgen⟩ |
      ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨-, ⟨F⟩⟩ | ⟨-, hm⟩ | hm
  ·
    have hm3 : m = 3 := by
      obtain ⟨A, B, hX', hgen⟩ := id hX
      have hLm : LieModel X .PSL (m + 1) 2 1 := by
        rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
        · obtain ⟨f, -, hcard, hL'⟩ := hX'.lieModel_A_two hR hiso hZ hgen
          obtain rfl := hf1 (hX'.memA 0) (hcard _ (hX'.memA 0))
          exact hL'
        · obtain ⟨f, -, hcard, hL'⟩ := hX'.lieModel_A hR hiso hZ hm3 hgen
          obtain rfl := hf1 (hX'.memA ⟨0, by omega⟩) (hcard _ (hX'.memA ⟨0, by omega⟩))
          exact hL'
      have hc := (Ord.card_of_lieModel_PSL hLm).2
      rw [hcardX, Nat.add_sub_cancel] at hc
      by_contra hne
      rcases (show m = 2 ∨ 4 ≤ m by omega) with rfl | hm4
      · revert hc
        decide
      · have h31 : 31 ∣ CFSG.Open.ordA m 2 :=
          Ord.dvd_ordA_two (a := 5) (by norm_num) (by omega) (by norm_num)
        rw [← hc] at h31
        revert h31
        decide
    subst hm3
    obtain ⟨Ψ, hs, hΨ⟩ := typeA_exists_surjective hR hiso hRD hDc hm hX
    obtain ⟨hinj, hA'⟩ := hA.comp_sl (by omega) hΨ
    exact ⟨Ψ, hs, hinj, hA'⟩
  · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_D hR hiso hZ hm hgen
    obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
    exact (Ord.lieModel_PSL_false_of_POmega hL (Or.inl hL')).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · rcases frame_cases_dim F hD hA with ⟨n, -, hC, -⟩ | ⟨n, -, hB, -⟩ | hle
    · exact (lieModel_PSL_false_of_PSp hL hC).elim
    · exact (Ord.lieModel_PSL_false_of_POmega hL (Or.inr hB)).elim
    · omega
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · rw [Ord.card_of_lieModel_PSU33 hm] at hcardX
    omega

end CFSG.LargeExtraspecial.AS35YU
