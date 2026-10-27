module

public import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterIb
import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterIbPerfect
import CFSG.HardMathSupport.Curtis.Proving.CommutatorCentreThreePart
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def ShortBlockCommutatorCentre : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {M L Q : Subgroup G}, IsTwoPrimeComponent M L → IsShort2 L →
    Q ≤ M → IsPGroup 3 Q → Q ≤ Subgroup.normalizer (L : Set G) →
    barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    ⁅barM M Q, barM M Q⁆ ⊓
      (barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥

@[expose] def CitedBlockAutCenterFFSL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    pCoreOf 2 M ≤ S → IsWeakSBlock M S L → NineThreeTwo M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → IbPerfectSections 3 (blockPL M S L) →
    3 ∣ Nat.card ↥(barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →
    ∀ u ∈ barM M L, u ^ 3 = 1 →
      u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
        V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        V ≤ Subgroup.normalizer (barM M (S ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ u ∈ V) →
      (∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) →
      ∀ Q : Subgroup G, Q ≤ M → IsPGroup 3 Q → Q ≤ Subgroup.normalizer (L : Set G) →
        Q ≤ Subgroup.normalizer (S : Set G) →
        barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        ⁅barM M Q, barM M Q⁆ ⊓
          (barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥

theorem citedBlockAutCenterFF_of_sl3 (hShort : ShortBlockCommutatorCentre)
    (hSL3 : CitedBlockAutCenterFFSL3) : CitedBlockAutCenterFF := by
  intro G _ _ M S L hK hA hO2 hL h93 hX hS hperf u hu hu3 huC hV hfix Q hQM hQ3 hQL hQS hQC
  have hu1 : u ≠ 1 := fun h => huC (h ▸ Subgroup.one_mem _)
  have hnine : 9 ∣ Nat.card ↥(barM M L) → ¬ 9 ∣ Nat.card (blockPL M S L) → False :=
    fun h9L h9 => h9 (nine_dvd_card_of_fix hu hu3 hu1 h9L hfix)
  rcases h93 with h1 | h2 | h3 | h4 | h5 | ⟨-, n, ⟨e⟩, ⟨eP⟩⟩ | ⟨-, n, ⟨e⟩, ⟨eP⟩⟩ |
      ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2', h4', -, φ, -⟩
  · exact absurd h1 hX
  · by_cases h3Z : 3 ∣ Nat.card ↥(barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    · exact hSL3 G M S L hK hA hO2 hL h2 hX hS hperf h3Z u hu hu3 huC hV hfix Q hQM hQ3 hQL hQS hQC
    · exact CFSG.HardMathSupport.Curtis.Proving.commutator_inf_centre_eq_bot_of_coprime hQ3
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3Z)
  · exact hShort hL.toIsTwoPrimeComponent h3.1 hQM hQ3 hQL hQC
  · exact hShort hL.toIsTwoPrimeComponent h4.1 hQM hQ3 hQL hQC
  · exact hShort hL.toIsTwoPrimeComponent h5.1 hQM hQ3 hQL hQC
  ·
    exfalso
    have : Group.IsPerfect ↥(barM M L) := Group.isPerfect_def.mpr hL.component.2.2.1
    have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      hL.component.2.2.2.toNontrivial
    have hn5 := five_le_of_isPerfect_mulEquiv_alternatingGroup e
    have h9A : 9 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
      rw [Nat.card_congr e.toEquiv]
      exact nine_dvd_card_alternatingGroup (by omega)
    exact hnine (h9A.trans (Dvd.intro _
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(barM M L))).symm))
      (not_nine_dvd_card_of_quotient_perm_ib hperf eP)
  ·
    exfalso
    have : Group.IsPerfect ↥(barM M L) := Group.isPerfect_def.mpr hL.component.2.2.1
    have : Nontrivial ↥(barM M L) := by
      have := hL.component.2.2.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
    have hn5 := five_le_of_isPerfect_mulEquiv_alternatingGroup e
    have h9L : 9 ∣ Nat.card ↥(barM M L) := by
      rw [Nat.card_congr e.toEquiv]
      exact nine_dvd_card_alternatingGroup (by omega)
    exact hnine h9L (not_nine_dvd_card_of_quotient_perm_ib hperf eP)
  ·
    exfalso
    refine false_of_surjective_perm_of_nine (n := N - 2 * r) (by omega) hperf
      ((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (QuotientGroup.mk' _))) ?_
    exact Prod.snd_surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _))

end CFSG.HardMathSupport.Curtis.Coordinator
