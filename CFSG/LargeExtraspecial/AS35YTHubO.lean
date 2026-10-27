module

public import CFSG.LargeExtraspecial.AS35YTHubF
public import CFSG.LargeExtraspecial.A2ModARS
public import CFSG.LargeExtraspecial.A2ModCfgE
public import CFSG.LargeExtraspecial.A2ModCfgTA
public import CFSG.LargeExtraspecial.A2ModCfgTD
public import CFSG.LargeExtraspecial.AS35YTHubA
public import CFSG.LargeExtraspecial.AS35YTOrd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35YT

open Module CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley A2Mod

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem eq_of_lieModel_PSp {n k : ℕ} (h : LieModel X .PSp n 2 1) (h' : LieModel X .PSp k 2 1) :
    n = k := by
  have e := (Ord.card_of_lieModel_PSp h).2.symm.trans (Ord.card_of_lieModel_PSp h').2
  have hB := Ord.profile_BC n
  rw [e] at hB
  exact Nat.mul_self_inj.mp (hB.transfer (Ord.profile_BC k)).1


theorem dim_of_pomega [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ) {k : ℕ}
    (hL : LieModel X .POmegaPlus k 2 1 ∨ LieModel X .POmegaMinus k 2 1) :
    (5 ≤ k → finrank (ZMod 2) (commSpaceOf ρ ⊤) = 2 * k) ∧
      (k = 4 → finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 9) := by
  have h := hD.arsHyp
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have h2 := hD.card_eq_two
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hDc := hD.conj_mem
  have hf1 : ∀ {f : ℕ} {E : Subgroup X}, E ∈ rootSet D → Nat.card E = 2 ^ f → f = 1 :=
    fun hE hc => Nat.pow_right_injective le_rfl ((hc.symm.trans (h2 _ hE)).trans (pow_one 2).symm)
  have hbig : 12096 < Nat.card X := by
    rcases hL with h | h
    · exact Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inl h)))
    · exact Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inr h)))
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, A, B, hX, hgen⟩ | ⟨m, hm, hX⟩ |
      ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨-, ⟨F⟩⟩ | ⟨-, hm⟩ | hm
  ·
    exfalso
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_A_two hR hiso hZ hgen
      obtain rfl := hf1 (hX.memA 0) (hcard _ (hX.memA 0))
      exact Ord.lieModel_PSL_false_of_POmega hL' hL
    · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
      exact Ord.lieModel_PSL_false_of_POmega hL' hL
  ·
    obtain ⟨A, B, hX', hgen⟩ := id hX
    obtain ⟨f, -, hcard, hL'⟩ := hX'.lieModel_D hR hiso hZ hm hgen
    obtain rfl := hf1 (hX'.memA ⟨0, by omega⟩) (hcard _ (hX'.memA ⟨0, by omega⟩))
    obtain rfl := Ord.eq_of_lieModel_POmega (Or.inl hL') hL
    refine ⟨fun h5 => typeD_finrank_commSpaceOf_eq hR hiso hRD hDc hA h5 hX, fun h4 => ?_⟩
    subst h4
    exact typeD_four_finrank_commSpaceOf_le hR hiso hRD hDc hA hX
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · rcases frame_cases_dim F hD hA with ⟨n, -, hC, -⟩ | ⟨n, -, hB, h5, h4⟩ | hle
    · exact (Ord.lieModel_PSp_false_of_POmega hC hL).elim
    · obtain rfl := Ord.eq_of_lieModel_POmega (Or.inr hB) hL
      exact ⟨h5, h4⟩
    · omega
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · rw [Ord.card_of_lieModel_PSU33 hm] at hbig
    omega

theorem dim_of_psp [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ) {k : ℕ}
    (hL : LieModel X .PSp k 2 1) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ max (2 * k + 1) 9 ∧
      (5 ≤ k → 2 * k ≤ finrank (ZMod 2) (commSpaceOf ρ ⊤)) := by
  have h := hD.arsHyp
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have h2 := hD.card_eq_two
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hDc := hD.conj_mem
  have hf1 : ∀ {f : ℕ} {E : Subgroup X}, E ∈ rootSet D → Nat.card E = 2 ^ f → f = 1 :=
    fun hE hc => Nat.pow_right_injective le_rfl ((hc.symm.trans (h2 _ hE)).trans (pow_one 2).symm)
  have hbig : 12096 < Nat.card X :=
    Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inl hL))
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, A, B, hX, hgen⟩ |
      ⟨m, hm, A, B, hX, hgen⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨-, ⟨F⟩⟩ |
      ⟨-, hm⟩ | hm
  · exfalso
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_A_two hR hiso hZ hgen
      obtain rfl := hf1 (hX.memA 0) (hcard _ (hX.memA 0))
      exact lieModel_PSL_false_of_PSp hL' hL
    · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
      exact lieModel_PSL_false_of_PSp hL' hL
  · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_D hR hiso hZ hm hgen
    obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
    exact (Ord.lieModel_PSp_false_of_POmega hL (Or.inl hL')).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · rcases frame_cases_dim F hD hA with ⟨n, -, hC, h1, h5⟩ | ⟨n, -, hB, -⟩ | hle
    · obtain rfl := eq_of_lieModel_PSp hC hL
      exact ⟨h1, h5⟩
    · exact (Ord.lieModel_PSp_false_of_POmega hL (Or.inr hB)).elim
    · omega
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · rw [Ord.card_of_lieModel_PSU33 hm] at hbig
    omega

theorem fix_or_dim_of_psl4 [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ)
    (hL : LieModel X .PSL 4 2 1) :
    (∀ v ∈ commSpaceOf ρ ⊤, (∀ x, ρ x v = v) → v = 0) ∨
      finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 7 := by
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
    obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) hΨ
    have hrange : commSpaceOf ρ ⊤ = commSpaceOf (ρ.comp Ψ) ⊤ := by
      rw [← commSpaceOf_range, MonoidHom.range_eq_top.mpr hs]
    rcases exists_isPointMaps_or_finrank_le hA' (le_refl 4) with ⟨P, Pd, hP⟩ | hle
    · left
      intro v hv hfix
      rw [hrange] at hv
      exact fix_eq_zero_of_isPointMaps (by omega) hP hv fun g => hfix (Ψ g)
    · right
      rw [hrange]
      exact hle
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

end CFSG.LargeExtraspecial.AS35YT
