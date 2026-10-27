module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqLieEven
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2EvenOuterOmega

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)
open CFSG.SeitzReduction.RankOne



theorem a6sq_sp_fixed {X : Type} [Group X] {k : Type} [Field k] [Finite k] {r g : ℕ}
    (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r) (hg : 1 ≤ g) (Φ : X ≃* StatedSp r k)
    (hC : Nat.card X ≤ 5760) (h360 : 360 ∣ Nat.card X) : r = 2 ∧ g = 1 := by
  have hc : Nat.card X = (2 ^ g) ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, ((2 ^ g) ^ (2 * j) - 1) := by
    rw [Nat.card_congr Φ.toEquiv, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
      hk]
  rw [hc] at hC h360
  exact a6sq_sp_numeric hr hg hC h360

theorem a6sq_psl_card (hO : LieOrderFormulasInput) {S : Type} [Group S] {n : ℕ}
    (hadm : StatedLieAdmissible .PSL n 2 1) (hm : LieModel S .PSL n 2 1) (hn : n = 4 ∨ n = 5) :
    Nat.card S = 20160 ∨ Nat.card S = 9999360 := by
  obtain ⟨-, hord, -⟩ := hO S .PSL n 2 1 hadm hm
  rcases hn with rfl | rfl
  · left
    have h1 : lieOrderNumerator .PSL 4 (2 ^ 1) = 20160 := by decide
    have h2 : lieOrderDivisor .PSL 4 (2 ^ 1) = 1 := by decide
    rw [h1, h2] at hord
    omega
  · right
    have h1 : lieOrderNumerator .PSL 5 (2 ^ 1) = 9999360 := by decide
    have h2 : lieOrderDivisor .PSL 5 (2 ^ 1) = 1 := by decide
    rw [h1, h2] at hord
    omega

theorem a6sq_psu_card (hO : LieOrderFormulasInput) {S : Type} [Group S] {n : ℕ}
    (hadm : StatedLieAdmissible .PSU n 2 1) (hm : LieModel S .PSU n 2 1) (hn : n = 4 ∨ n = 5) :
    Nat.card S = 25920 ∨ Nat.card S = 13685760 := by
  obtain ⟨-, hord, -⟩ := hO S .PSU n 2 1 hadm hm
  rcases hn with rfl | rfl
  · left
    have h1 : lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 := by decide
    have h2 : lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by decide
    rw [h1, h2] at hord
    omega
  · right
    have h1 : lieOrderNumerator .PSU 5 (2 ^ 1) = 13685760 := by decide
    have h2 : lieOrderDivisor .PSU 5 (2 ^ 1) = 1 := by decide
    rw [h1, h2] at hord
    omega

theorem a6sq_even_PSL_core (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSL n 2 e) (hm : LieModel S .PSL n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)))
    (hfin : (n = 4 ∨ n = 5) → e = 1 → ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
      Nonempty (↥(fixedSubgroup σ) ≃* StatedSp 2 k) → False) : False := by
  obtain ⟨D, -, hDp, hDn, hD360, -, h360, hCf⟩ := a6sq_even_data hC hC'
  rcases psl_outer_fixed_rank hadm hm σ hσ hout with hfield | hgf | hgraph
  · obtain ⟨hadm', hm', -⟩ := hfield D hDp
    exact lieModel_two_card_ne_360 hO hadm' hm' hD360
  · obtain ⟨hadm', hm'⟩ := hgf D hDp
    exact lieModel_two_card_ne_360 hO hadm' hm' hD360
  · rcases hgraph with ⟨k, _, _, r, hk, hr1, ⟨hn3, hnr⟩, ⟨Φ⟩⟩ | hnone
    · obtain ⟨hr2, hg1⟩ := a6sq_sp_fixed hk hr1 hadm.2.1 Φ hCf h360
      subst hr2
      have hn45 : n = 4 ∨ n = 5 := by omega
      exact hfin hn45 hg1 k (by rw [hk, hg1]; norm_num) ⟨Φ⟩
    · exact hnone D hDp

theorem a6sq_even_PSL (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSL n 2 e) (hm : LieModel S .PSL n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)))
    (hS : 129600 ∣ Nat.card S) : False :=
  a6sq_even_PSL_core hO hadm hm hσ hout hC hC' fun hn45 he _ _ _ _ => by
    subst he
    rcases a6sq_psl_card hO hadm hm hn45 with h | h <;> omega

theorem a6sq_even_PSU_core (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSU n 2 e) (hm : LieModel S .PSU n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)))
    (hfin : (n = 4 ∨ n = 5) → e = 1 → ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
      Nonempty (↥(fixedSubgroup σ) ≃* StatedSp 2 k) → False) : False := by
  obtain ⟨D, -, hDp, hDn, hD360, -, h360, hCf⟩ := a6sq_even_data hC hC'
  rcases psu_outer_fixed_rank hadm hm σ hσ hout with ⟨k, _, _, r, hk, hr1, hnr, ⟨Φ⟩⟩ | hnone
  · obtain ⟨hr2, hg1⟩ := a6sq_sp_fixed hk hr1 hadm.2.1 Φ hCf h360
    subst hr2
    have hn45 : n = 4 ∨ n = 5 := by omega
    exact hfin hn45 hg1 k (by rw [hk, hg1]; norm_num) ⟨Φ⟩
  · exact hnone D hDp

theorem a6sq_even_PSU (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSU n 2 e) (hm : LieModel S .PSU n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)))
    (hS : 129600 ∣ Nat.card S) : False :=
  a6sq_even_PSU_core hO hadm hm hσ hout hC hC' fun hn45 he _ _ _ _ => by
    subst he
    rcases a6sq_psu_card hO hadm hm hn45 with h | h <;> omega

theorem a6sq_psp_card (hO : LieOrderFormulasInput) {S : Type} [Group S] {e : ℕ}
    (hadm : StatedLieAdmissible .PSp 2 2 e) (hm : LieModel S .PSp 2 2 e) (he : e = 2 ∨ e = 3) :
    Nat.card S = 979200 ∨ Nat.card S = 1056706560 := by
  obtain ⟨-, hord, -⟩ := hO S .PSp 2 2 e hadm hm
  rcases he with rfl | rfl
  · left
    have h1 : lieOrderNumerator .PSp 2 (2 ^ 2) = 979200 := by decide
    have h2 : lieOrderDivisor .PSp 2 (2 ^ 2) = 1 := by decide
    rw [h1, h2] at hord
    omega
  · right
    have h1 : lieOrderNumerator .PSp 2 (2 ^ 3) = 1056706560 := by decide
    have h2 : lieOrderDivisor .PSp 2 (2 ^ 3) = 1 := by decide
    rw [h1, h2] at hord
    omega

theorem a6sq_even_PSp_core (hO : LieOrderFormulasInput) {S : Type}
    [Group S] [Finite S] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSp n 2 e) (hm : LieModel S .PSp n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)))
    (hfin : n = 2 → (e = 2 ∨ e = 3) → ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
      Nonempty (↥(fixedSubgroup σ) ≃* StatedSp 2 k) → False) : False := by
  obtain ⟨D, -, hDp, hDn, hD360, -, h360, hCf⟩ := a6sq_even_data hC hC'
  rcases psp_outer_fixed_rank hadm hm σ hσ hout with hsp | ⟨hsimple, hadmB, hmB⟩
  · rcases hsp with ⟨k, _, _, r, hk, hr1, hrn, ⟨Φ⟩⟩ | hnone
    · have hg : 1 ≤ e / 2 := by
        by_contra h
        have h0 : e / 2 = 0 := by omega
        rw [h0, pow_zero] at hk
        have := (Finite.one_lt_card_iff_nontrivial (α := k)).2 inferInstance
        omega
      obtain ⟨hr2, hg1⟩ := a6sq_sp_fixed hk hr1 hg Φ hCf h360
      subst hr2
      subst hrn
      have he : e = 2 ∨ e = 3 := by omega
      exact hfin rfl he k (by rw [hk, hg1]; norm_num) ⟨Φ⟩
    · exact hnone D hDp
  · haveI := hsimple
    haveI := hDn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with h | h
    · rw [h] at hD360
      simp at hD360
    · have hcard : Nat.card (fixedSubgroup σ) = 360 := by
        rw [← hD360, h, Subgroup.card_top]
      exact lieModel_two_card_ne_360 hO hadmB hmB hcard

theorem a6sq_even_PSp (hO : LieOrderFormulasInput) {S : Type}
    [Group S] [Finite S] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSp n 2 e) (hm : LieModel S .PSp n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)))
    (hS : 129600 ∣ Nat.card S) : False :=
  a6sq_even_PSp_core hO hadm hm hσ hout hC hC' fun hn2 he _ _ _ _ => by
    subst hn2
    rcases a6sq_psp_card hO hadm hm he with h | h <;> omega

theorem a6sq_even_Omega_core (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S] {n e : ℕ}
    (hadm : StatedLieAdmissible t n 2 e) (hm : LieModel S t n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨D, -, hDp, hDn, hD360, -, h360, hCf⟩ := a6sq_even_data hC hC'
  have hn4 : 4 ≤ n := by rcases ht with rfl | rfl <;> exact hadm.2.2
  rcases omega_family_fixed_rank ht hadm hm σ hσ hout with hsp | hom
  · rcases hsp with ⟨k, _, _, r, hk, hr1, hrn, ⟨Φ⟩⟩ | hnone
    · obtain ⟨hr2, -⟩ := a6sq_sp_fixed hk hr1 hadm.2.1 Φ hCf h360
      omega
    · exact hnone D hDp
  · obtain ⟨t', n', f', -, hadm', hm'⟩ := hom D hDp
    exact lieModel_two_card_ne_360 hO hadm' hm' hD360

theorem a6sq_even_Omega (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S] {n e : ℕ}
    (hadm : StatedLieAdmissible t n 2 e) (hm : LieModel S t n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)))
    (hS : 129600 ∣ Nat.card S) : False :=
  a6sq_even_Omega_core hO ht hadm hm hσ hout hC hC'

end CFSG.ComponentClassification.CatFC
