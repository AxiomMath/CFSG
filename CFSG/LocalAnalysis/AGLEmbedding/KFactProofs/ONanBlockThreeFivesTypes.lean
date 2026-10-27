module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockThreeFivesGroup
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFivesParabolic
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVTypes
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo

public section

namespace CFSG.AGLEmbedding.ThreeFives

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding

theorem isPGroup_ker_quotient_pCore {X Q : Type*} [Group X] [Group Q]
    (e : X ⧸ CFSG.pCore 2 X ≃* Q) :
    IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X))).ker := by
  have := CFSG.pCore_normal (p := 2) (G := X)
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X))).ker =
      CFSG.pCore 2 X := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, ← QuotientGroup.eq_one_iff]
    rfl
  rw [hker]
  exact CFSG.pCore_isPGroup

theorem surjective_quotient_pCore {X Q : Type*} [Group X] [Group Q]
    (e : X ⧸ CFSG.pCore 2 X ≃* Q) :
    Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

section Main

variable {Y : Type*} [Group Y] [Finite Y]

theorem false_of_quotient_perm {P O : Subgroup Y} {J : Fin 3 → Subgroup Y}
    (hOP : O ≤ P) (hN : P ≤ Subgroup.normalizer (O : Set Y)) (h5 : ¬ 5 ∣ Nat.card O)
    (hsec : SectionsOrderSixty P O) (hJ : ∀ i, FiveSection P O (J i))
    (hcomm : ∀ i j, i ≠ j → ⁅J i, J j⁆ ≤ O) {n : ℕ}
    (e : ↥P ⧸ CFSG.pCore 2 ↥P ≃* Perm (Fin n)) : False := by
  have := CFSG.pCore_normal (p := 2) (G := ↥P)
  have hψ := surjective_quotient_pCore e
  have hker := isPGroup_ker_quotient_pCore e
  by_cases hn : n ≤ 4
  · exact false_of_hom_perm_small (hJ 0) hn _ hψ hker
  by_cases hn5 : n = 5
  · subst hn5
    exact false_of_hom_perm_five hOP hN h5 _ hψ hker (hJ 0) (hJ 1) (hcomm 0 1 (by decide))
  · exact false_of_hom_perm hOP hN hsec h5 (by omega) _ hψ

omit [Finite Y] in
theorem false_of_quotient_perm_prod {P O : Subgroup Y} (hOP : O ≤ P)
    (hN : P ≤ Subgroup.normalizer (O : Set Y)) (h5 : ¬ 5 ∣ Nat.card O)
    (hsec : SectionsOrderSixty P O) {r m : ℕ} (hm : 6 ≤ m)
    (e : ↥P ⧸ CFSG.pCore 2 ↥P ≃* Perm (Fin r) × Perm (Fin m)) : False := by
  have := CFSG.pCore_normal (p := 2) (G := ↥P)
  exact false_of_hom_perm_prod hOP hN hsec h5 hm _ (surjective_quotient_pCore e)

omit [Finite Y] in
theorem false_of_quotient_simple {P O J : Subgroup Y} (hOP : O ≤ P)
    (hN : P ≤ Subgroup.normalizer (O : Set Y)) (hsec : SectionsOrderSixty P O)
    {Q : Type*} [Group Q] (hQ : IsSimpleGroup Q) (h4 : 4 ∣ Nat.card Q)
    (h60 : Nat.card Q ≠ 60) (e : ↥P ⧸ CFSG.pCore 2 ↥P ≃* Q) (hJ : FiveSection P O J) :
    False := by
  have := CFSG.pCore_normal (p := 2) (G := ↥P)
  exact false_of_hom_simple hOP hN hsec hQ (exists_noncomm_of_simple hQ h4) h60 _
    (surjective_quotient_pCore e) (isPGroup_ker_quotient_pCore e) hJ

end Main

theorem kFactBlockThreeFives_of_types (hT : CitedBlockTransvectionPLType)
    (hP : KFactBlockThreeFivesParabolic) (hA7 : CitedBlockAltSevenPL)
    (h93 : Asc81bNineThree) : KFactBlockThreeFives := by
  intro G _ _ M S L hK hA hL hX hS O J hOP hN h5 hsec hJ hcomm
  have h5' : ¬ 5 ∣ Nat.card O := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 h5
  have hsec' : SectionsOrderSixty (blockPL M S L) O := hsec
  have hJ' : ∀ i, FiveSection (blockPL M S L) O (J i) := hJ
  rcases h93 G M S L hK hA hL with h1 | h2 | h3 | h4 | h5t | h6 | h7 | h8
  · exact absurd h1 hX
  · exact hP G M S L hK hA hL hX hS h2 O J hOP hN h5 hsec hJ hcomm
  · exfalso
    rcases citedBlockTransvectionPL_of_type hT G M S L hK hA hL hX hS h3 with
      ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
    · obtain ⟨hTs, h29⟩ := kFactSpTwoSimple_holds k d hk hd
      refine false_of_quotient_simple hOP hN hsec' hTs ((by norm_num : 4 ∣ 2 ^ 9).trans h29)
        (fun h => ?_) e (hJ' 0)
      rw [h] at h29
      exact absurd (Nat.le_of_dvd (by norm_num) h29) (by norm_num)
    · exact false_of_quotient_perm hOP hN h5' hsec' hJ' hcomm e
  · exfalso
    exact false_of_not_five_dvd (hJ' 0) fun h =>
      absurd (h.trans (card_blockPL_dvd_of_nineThreeFour h4)) (by norm_num)
  · exfalso
    exact false_of_not_five_dvd (hJ' 0) fun h =>
      absurd (h.trans (hA7 G M S L hK hA hL hX hS h5t)) (by norm_num)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact (false_of_quotient_perm hOP hN h5' hsec' hJ' hcomm e).elim
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact (false_of_quotient_perm hOP hN h5' hsec' hJ' hcomm e).elim
  · obtain ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2', h4', -, φ, -⟩ := h8
    have hm6 : 6 ≤ N - 2 * r := by omega
    exact (false_of_quotient_perm_prod hOP hN h5' hsec' hm6 φ).elim

end CFSG.AGLEmbedding.ThreeFives
