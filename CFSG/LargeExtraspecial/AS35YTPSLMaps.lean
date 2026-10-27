module

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

private theorem mem_transvectionSet_of_map_mem (hD : RootClass X D) {n : ℕ} (hn : 2 ≤ n)
    {Ψ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* X} (hb : Function.Bijective Ψ)
    (hΨ : ∀ g ∈ transvectionSet n (ZMod 2), Ψ g ∈ D)
    {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hg : Ψ g ∈ D) :
    g ∈ transvectionSet n (ZMod 2) := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by simp [Fin.ext_iff] at h
  obtain ⟨t₀, ht⟩ : ∃ t₀, t₀ ∈ transvectionSet n (ZMod 2) := ⟨_, elemTv_mem_transvectionSet h01⟩
  obtain ⟨d₀, -, hconj⟩ := hD.1.2.1
  obtain ⟨c, hc⟩ := isConj_iff.mp (((hconj _).mp (hΨ _ ht)).symm.trans ((hconj _).mp hg))
  obtain ⟨c', rfl⟩ := hb.2 c
  have hgc : g = c' * t₀ * c'⁻¹ := hb.1 (by rw [map_mul, map_mul, map_inv, hc])
  rw [hgc]
  exact conj_mem_transvectionSet c' ht


theorem exists_bijective_sl_of_lieModel_psl [Finite X] (hD : RootClass X D)
    (hA : A2Action D Q ρ) {k : ℕ} (hk : 5 ≤ k) (hL : LieModel X .PSL k 2 1) :
    ∃ (n : ℕ) (Ψ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* X), 5 ≤ n ∧
      Function.Bijective Ψ ∧ (∀ g, g ∈ transvectionSet n (ZMod 2) ↔ Ψ g ∈ D) ∧
      A2Action (transvectionSet n (ZMod 2)) Q (ρ.comp Ψ) := by
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
    obtain ⟨hinj, hA'⟩ := hA.comp_sl (by omega) hΨ
    exact ⟨m + 1, Ψ, by omega, ⟨hinj, hs⟩, fun g => ⟨hΨ g,
      mem_transvectionSet_of_map_mem hD (by omega) ⟨hinj, hs⟩ hΨ⟩, hA'⟩
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
    · exfalso
      omega
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · rw [Ord.card_of_lieModel_PSU33 hm] at hbig
    exfalso
    omega

end CFSG.LargeExtraspecial.AS35YT
