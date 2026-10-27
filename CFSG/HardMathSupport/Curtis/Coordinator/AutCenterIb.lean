module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterAutBound
import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterNode
import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterIbPerfect
import CFSG.HardMathSupport.Curtis.Coordinator.AutNineReduce
import CFSG.HardMathSupport.Curtis.Coordinator.ToralThreeReduce
import CFSG.HardMathSupport.Curtis.Coordinator.BlockGlue
import CFSG.HardMathSupport.Curtis.Coordinator.AutBounds
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchIb
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def CitedBlockAutCenterFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    pCoreOf 2 M ≤ S → IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → IbPerfectSections 3 (blockPL M S L) →
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

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem relIndex_le_twentySeven_of_le_sup {U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hU : U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hU3 : IsPGroup 3 U)
    (hUL : U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (h27 : ¬ 3 ^ 3 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) :
    (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 27 := by
  have h81 : ¬ 3 ^ (3 + 1) ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    fun h => h27 ((pow_dvd_pow 3 (by norm_num)).trans h)
  exact relIndex_centralizer_le_of_le_sup (k := 3) Nat.prime_three hU hUL hU3 h81

theorem relIndex_le_twentySeven_of_nineThree (hC : KFactFixCensusThree)
    (hT : CitedBlockTransvectionPLType) (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (h93 : NineThreeConclusion M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (hperf : IbPerfectSections 3 (blockPL M S L))
    {u : ↥M ⧸ CFSG.pCore 2 ↥M} (hu : u ∈ barM M L) (hu3 : u ^ 3 = 1)
    (huC : u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hV : ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
      V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      V ≤ Subgroup.normalizer (barM M (S ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ u ∈ V)
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L)
    {U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hU : U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hU3 : IsPGroup 3 U) :
    (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 27 := by
  have := barM_isPerfect hL
  have := barM_nontrivial_center_quotient hL
  have := barM_nontrivial hL
  have hu1 : u ≠ 1 := fun h => huC (h ▸ Subgroup.one_mem _)
  have hinner : ¬ 3 ∣ Nat.card (Outer ↥(barM M L)) →
      ¬ 3 ^ 3 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) →
      (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 27 :=
    fun hO h27 => relIndex_le_twentySeven_of_le_sup hU hU3 (le_sup_of_not_three_dvd hU hU3 hO) h27
  have hasix : Nat.card (Subgroup.center ↥(barM M L)) = 3 →
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) →
      (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 27 := by
    rintro hZ3 ⟨e⟩
    refine relIndex_le_twentySeven_of_le_sup hU hU3 (fun y hy => ?_) ?_
    · obtain ⟨k, hk⟩ := hU3 ⟨y, hy⟩
      exact (kFactBlockThreeASix_holds G M L hL.toIsTwoPrimeComponent hZ3 ⟨e⟩).1 y (hU hy)
        ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Nat.card_congr e.toEquiv]
      exact not_dvd_card_alternatingGroup (by norm_num)
  have hnine : 9 ∣ Nat.card ↥(barM M L) → ¬ 9 ∣ Nat.card (blockPL M S L) → False :=
    fun h9L h9 => h9 (nine_dvd_card_of_fix hu hu3 hu1 h9L hfix)
  rcases h93 with h1 | h2 | h3 | h4 | ⟨-, ⟨e⟩, -⟩ | ⟨-, n, ⟨e⟩, ⟨eP⟩⟩ | ⟨-, n, ⟨e⟩, ⟨eP⟩⟩ |
      ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2', h4', -, φ, -⟩
  · exact absurd h1 hX
  ·
    have hparab : CompParab (barM M L) (blockPL M S L) := compParab_of_nineThreeTwo hA hL hS h2
    have hperfV : ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
        V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        V ≤ Subgroup.normalizer (pCoreOf 2 (blockPL M S L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        u ∈ V := by
      obtain ⟨V, hVV, hVL, hVS, huV⟩ := hV
      refine ⟨V, hVV, hVL, ?_, huV⟩
      rw [← h2.2.2]
      exact hVS
    obtain ⟨e, he2, ⟨ι⟩⟩ := hC _ (barM M L) (blockPL M S L) hparab
      (cycPerfect_of_ib Nat.prime_three hperf) u hu hu3 huC hperfV hfix
    have h3e : ¬ 3 ∣ e := fun h3 => by
      obtain ⟨W, hWJ, hW, h9⟩ := exists_perfect_nine_dvd_of_compParab hparab he2 h3 ι
      exact hperf W hWJ hW (by simpa using h9)
    exact relIndex_centralizer_le_of_psl_three (by omega) h3e ι hU hU3
  ·
    obtain ⟨hOrth, hU4, -, -, hA8⟩ := hT G M S L hK hA hL hX hS h3
    rcases h3.2.1 with ⟨d, ⟨m, q, hq, hdm⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exfalso
      rcases hdm with hd | hd | ⟨rfl, hd⟩
      · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨e'⟩⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
        have hm4 : 4 ≤ m := by
          have h := d.2
          rw [hd] at h
          exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
        exact false_of_quotient_sp_of_nine (k := m - 1) (by omega) ⟨q', hq', hd'⟩ hperf e'
      · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨e'⟩⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
        have hm4 : 4 ≤ m := by
          have h := d.2
          rw [hd] at h
          exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
        exact false_of_quotient_sp_of_nine (k := m - 1) (by omega) ⟨q', hq', hd'⟩ hperf e'
      · obtain ⟨e6⟩ := hU4 d ⟨q, hq, hd⟩ ⟨e⟩
        exact false_of_surjective_perm_of_nine (n := 6) (by norm_num) hperf e6.toMonoidHom
          e6.surjective
    · have hn' : n = 5 ∨ n = 6 := by
        rcases hn with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · obtain ⟨e6⟩ := hA8 ⟨e⟩
          exact (false_of_surjective_perm_of_nine (n := 6) (by norm_num) hperf e6.toMonoidHom
            e6.surjective).elim
      refine hinner (not_three_dvd_card_outer_of_alt e)
        (not_dvd_card_quotient_center_of (Nat.card_congr e.toEquiv) ?_)
      rcases hn' with rfl | rfl <;> exact not_dvd_card_alternatingGroup (by omega)
  ·
    obtain ⟨-, hZ3, he, -⟩ := h4
    exact hasix hZ3 he
  ·
    exact hinner (not_three_dvd_card_outer_of_alt e)
      (not_dvd_card_quotient_center_of (Nat.card_congr e.toEquiv)
        (not_dvd_card_alternatingGroup (by omega)))
  ·
    exfalso
    have hn5 := five_le_of_isPerfect_mulEquiv_alternatingGroup e
    have h9A : 9 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
      rw [Nat.card_congr e.toEquiv]
      exact nine_dvd_card_alternatingGroup (by omega)
    exact hnine (h9A.trans (Dvd.intro _
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(barM M L))).symm))
      (not_nine_dvd_card_of_quotient_perm_ib hperf eP)
  ·
    exfalso
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

theorem citedBlockThreeAutCenterIb_of (hC : KFactFixCensusThree)
    (hT : CitedBlockTransvectionPLType) (hFF : CitedBlockAutCenterFF) :
    CitedBlockThreeAutCenterIb := by
  intro G _ _ M S L hK hA hO hL h93 hX hS hperf u hu hu3 huC hV hfix
  exact ⟨fun U hU hU3 => relIndex_le_twentySeven_of_nineThree hC hT hK hA hL h93 hX hS hperf hu hu3
    huC hV hfix hU hU3, hFF G M S L hK hA hO hL h93 hX hS hperf u hu hu3 huC hV hfix⟩

end CFSG.HardMathSupport.Curtis.Coordinator
