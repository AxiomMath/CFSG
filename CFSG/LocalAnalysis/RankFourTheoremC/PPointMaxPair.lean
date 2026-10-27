module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointInvTwo
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_dvd_mul_of_le_normalizer {A B : Subgroup G} (hBA : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ∣ Nat.card A * Nat.card B := by
  set X : Subgroup G := A ⊔ B with hX
  have hAX : A ≤ X := le_sup_left
  have hBX : B ≤ X := le_sup_right
  have hXA : X ≤ normalizer (A : Set G) := sup_le Subgroup.le_normalizer hBA
  set A' : Subgroup X := A.subgroupOf X with hA'def
  set B' : Subgroup X := B.subgroupOf X with hB'def
  have : A'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).mpr hXA
  have htop : B' ⊔ A' = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, hB'def, hA'def, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBX, inf_eq_left.mpr hAX, Subgroup.map_top,
      Subgroup.range_subtype, sup_comm]
  have h1 : A'.relIndex (B' ⊔ A') = A'.relIndex B' := Subgroup.relIndex_sup_right B' A'
  rw [htop, Subgroup.relIndex_top_right] at h1
  have hcard : Nat.card A' * A'.index = Nat.card X := Subgroup.card_mul_index A'
  have hA'card : Nat.card A' = Nat.card A := by
    rw [hA'def]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
  have hB'card : Nat.card B' = Nat.card B := by
    rw [hB'def]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  rw [← hcard, hA'card, h1, ← hB'card]
  exact Nat.mul_dvd_mul_left _ (Subgroup.relIndex_dvd_card A' B')

theorem isPGroup_sup_of_le_normalizer {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hA : IsPGroup p A) (hB : IsPGroup p B) (hBA : B ≤ normalizer (A : Set G)) :
    IsPGroup p ↥(A ⊔ B) := by
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  have hdvd := card_sup_dvd_mul_of_le_normalizer hBA
  rw [ha, hb, ← pow_add] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  exact IsPGroup.of_card hk

omit [Finite G] in
theorem le_normalizer_sup {U A B : Subgroup G} (hA : U ≤ normalizer (A : Set G))
    (hB : U ≤ normalizer (B : Set G)) : U ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro u hu
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    mem_normalizer_iff_map_conj_eq.mp (hA hu), mem_normalizer_iff_map_conj_eq.mp (hB hu)]

theorem rankTwoMaximal_of_invariantTwoMaximalWithin {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U M N T : Subgroup G} (hU : IsPGroup p U) (hUM : U ≤ M) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hNp : p.Coprime (Nat.card N))
    (hL43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ N) N → normalizer (Y : Set G) ≤ M)
    (hT : invariantTwoMaximalWithin U M T) : rankTwoMaximalInvariantTwoSubgroup U T :=
  invariantTwoMaximalWithin_global_of_normalizer_le U M T hUM hT
    (hL43 T hT.2.1 hT.1 hT.2.2.1
      (isSylowOf_inf_of_invariantTwoMaximalWithin hp hp2 hU hUM hNM hMN hNp hT))

theorem exists_maximal_escaping_pair (hchar : IsCharTwoType G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {U M N : Subgroup G} {x : G} (hU : IsElemAbelian p U)
    (hUcard : Nat.card U = p ^ 2) (hUM : U ≤ M) (hxU : x ∈ U) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hNp : p.Coprime (Nat.card N))
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hL43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ N) N → normalizer (Y : Set G) ≤ M)
    (hL45 : ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M) :
    ∃ S₁ T : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M ∧
      rankTwoMaximalInvariantTwoSubgroup U T ∧ T ≤ M ∧ invariantTwoMaximalWithin U M T ∧
      S₁ ⊓ M = S₁ ⊓ T ∧ S₁ ⊓ T ≠ ⊥ ∧
      ∀ S₁' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁' → ¬ S₁' ≤ M →
        Nat.card (S₁' ⊓ M : Subgroup G) ≤ Nat.card (S₁ ⊓ T : Subgroup G) := by
  have hUp : IsPGroup p U := elementary_isPGroup p U hU
  have hglob : ∀ T : Subgroup G, invariantTwoMaximalWithin U M T →
      rankTwoMaximalInvariantTwoSubgroup U T := fun T hT =>
    rankTwoMaximal_of_invariantTwoMaximalWithin hp hp2 hUp hUM hNM hMN hNp hL43 hT
  obtain ⟨S₁₀, hS₁₀, hS₁₀M⟩ := hL45
  have hS₁₀ne : S₁₀ ≠ ⊥ := fun h => hS₁₀M (h ▸ bot_le)
  have hS₀ne : S₁₀ ⊓ M ≠ ⊥ :=
    inf_ne_bot_of_centralizer_le hchar hp hp2 hU hUcard hS₁₀ hS₁₀ne hxU hC
  have hinv : U ≤ normalizer ((S₁₀ ⊓ M : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U S₁₀ M hS₁₀.2.1 (hUM.trans Subgroup.le_normalizer)
  obtain ⟨T₀, hST₀, hT₀⟩ := exists_invariantTwoMaximalWithin_containing U M (S₁₀ ⊓ M)
    inf_le_right hS₁₀.1.to_inf_left hinv
  have hT₀g := hglob T₀ hT₀
  obtain ⟨first, second, hfirst, hsecond, hfirstE, hsecondLe, hcard0, hmaximal⟩ :=
    exists_relative_maximal_invariant_pair U M S₁₀ T₀ hS₁₀ hT₀g hS₁₀M hT₀.1
  have hint := relative_maximal_pair_intersection_eq_overgroup_intersection U M first second hUM
    hfirst hsecond hfirstE hsecondLe hmaximal hglob
  have hne : first ⊓ second ≠ ⊥ := by
    intro hbot
    have h1 : S₁₀ ⊓ T₀ ≠ ⊥ := fun h => hS₀ne (eq_bot_iff.mpr (h ▸ le_inf inf_le_left hST₀))
    have h2 : 1 < Nat.card (S₁₀ ⊓ T₀ : Subgroup G) := (Subgroup.one_lt_card_iff_ne_bot _).mpr h1
    have h3 := hcard0
    rw [hbot, Subgroup.card_bot] at h3
    omega
  refine ⟨first, second, hfirst, hfirstE, hsecond, hsecondLe, ⟨hsecondLe, hsecond.1, hsecond.2.1,
    fun larger _ h2 hinv' hle => hsecond.2.2 larger h2 hinv' hle⟩, hint, hne, ?_⟩
  intro S₁' hS₁' hS₁'M
  have hinv' : U ≤ normalizer ((S₁' ⊓ M : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U S₁' M hS₁'.2.1 (hUM.trans Subgroup.le_normalizer)
  obtain ⟨T', hST', hT'⟩ := exists_invariantTwoMaximalWithin_containing U M (S₁' ⊓ M)
    inf_le_right hS₁'.1.to_inf_left hinv'
  exact (Subgroup.card_le_of_le (le_inf inf_le_left hST' : S₁' ⊓ M ≤ S₁' ⊓ T')).trans
    (hmaximal S₁' T' hS₁' (hglob T' hT') hS₁'M hT'.1)

theorem isSylowOf_two_glbPrimeCore_of_maximal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U M S₁ T : Subgroup G} (hU : IsPGroup p U) (hCU : centralizer (U : Set G) ≤ M)
    (hS₁ : rankTwoMaximalInvariantTwoSubgroup U S₁) (hS₁M : ¬ S₁ ≤ M)
    (hT : rankTwoMaximalInvariantTwoSubgroup U T) (hTM : T ≤ M) (hint : S₁ ⊓ M = S₁ ⊓ T)
    (hmax : ∀ S₁' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁' → ¬ S₁' ≤ M →
      Nat.card (S₁' ⊓ M : Subgroup G) ≤ Nat.card (S₁ ⊓ T : Subgroup G)) :
    IsSylowOf 2 (S₁ ⊓ T)
      (GLBPrimeCore p (normalizer ((S₁ ⊓ T : Subgroup G) : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set S : Subgroup G := S₁ ⊓ T with hSdef
  set H : Subgroup G := normalizer (S : Set G) with hH
  set O : Subgroup G := GLBPrimeCore p H with hO
  have hS2 : IsPGroup 2 S := hS₁.1.to_inf_left
  have hUS : U ≤ normalizer (S : Set G) :=
    common_normalizer_le_normalizer_inf U S₁ T hS₁.2.1 hT.2.1
  have hUH : U ≤ H := hUS
  have hUO : U ≤ normalizer (O : Set G) := hUH.trans (le_normalizer_glbPrimeCore p H)
  have hHO : H ≤ normalizer (O : Set G) := le_normalizer_glbPrimeCore p H
  have hOcop : p.Coprime (Nat.card O) := glbPrimeCore_coprime p H
  have hcop2 : ∀ A : Subgroup G, IsPGroup 2 A → p.Coprime (Nat.card A) := fun A hA => by
    obtain ⟨b, hb⟩ := hA.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hSO : S ≤ O := le_glbPrimeCore Subgroup.le_normalizer le_rfl (hcop2 S hS2)
  have hST : S < T := lt_of_le_of_ne inf_le_right fun h => by
    have hTS₁ : T ≤ S₁ := inf_eq_right.mp h
    exact hS₁M ((hT.2.2 S₁ hS₁.1 hS₁.2.1 hTS₁) ▸ hTM)
  have hSS₁ : S < S₁ := lt_of_le_of_ne inf_le_left fun h => by
    have hS₁T : S₁ ≤ T := inf_eq_left.mp h
    exact hS₁M (hS₁T.trans hTM)
  have hT₀ : S < T ⊓ H := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two T S
    hT.1 hST
  have hS₀ : S < S₁ ⊓ H := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two S₁ S
    hS₁.1 hSS₁
  have hUT₀ : U ≤ normalizer ((T ⊓ H : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U T H hT.2.1 (hUH.trans Subgroup.le_normalizer)
  have hUS₀ : U ≤ normalizer ((S₁ ⊓ H : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U S₁ H hS₁.2.1 (hUH.trans Subgroup.le_normalizer)
  have key : ∀ A : Subgroup G, IsPGroup 2 A → A ≤ H → U ≤ normalizer (A : Set G) →
      ∀ Y₀ : Subgroup G, IsSylowOf 2 Y₀ O → U ≤ normalizer (Y₀ : Set G) →
      ∃ c ∈ O ⊓ centralizer (U : Set G),
        IsSylowOf 2 (Y₀.map (MulAut.conj c).toMonoidHom) O ∧
        U ≤ normalizer ((Y₀.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) ∧
        A ≤ normalizer ((Y₀.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
    intro A hA2 hAH hUA Y₀ hY₀ hY₀U
    obtain ⟨Y₁, hY₁, hY₁U, hAY₁⟩ := exists_invariant_isSylowOf_two_normalized hp hp2 hU hUO hOcop
      (hAH.trans hHO) hA2 hUA
    obtain ⟨c, hc, hcY⟩ := exists_centralizer_conj_of_isSylowOf_two hp hU hUO hOcop hY₀ hY₁ hY₀U
      hY₁U
    exact ⟨c, hc, hcY ▸ hY₁, hcY ▸ hY₁U, hcY ▸ hAY₁⟩
  by_contra hnot
  obtain ⟨Y₀, hY₀, hY₀U, hSY₀n⟩ := exists_invariant_isSylowOf_two_normalized hp hp2 hU hUO hOcop
    (Subgroup.le_normalizer.trans hHO) hS2 hUS
  have hSY₀ : S ≤ Y₀ := by
    have hpg : IsPGroup 2 ↥(Y₀ ⊔ S) := isPGroup_sup_of_le_normalizer hY₀.isPGroup hS2 hSY₀n
    have := hY₀.eq_of_le (le_sup_left : Y₀ ≤ Y₀ ⊔ S) (sup_le hY₀.le hSO) hpg
    exact le_sup_right.trans this.le
  have hSY₀lt : S < Y₀ := lt_of_le_of_ne hSY₀ fun h => hnot (h ▸ hY₀)
  have hcardSY₀ : Nat.card S < Nat.card Y₀ := Subgroup.card_lt_of_lt hSY₀lt
  have hmaxM : ∀ (A : Subgroup G) (Z : Subgroup G), IsPGroup 2 Z → U ≤ normalizer (Z : Set G) →
      A ≤ Z → A ≤ M → S < A → Z ≤ M := by
    intro A Z hZ2 hUZ hAZ hAM hSA
    obtain ⟨S₁', hZS, hS₁'⟩ := exists_maximal_invariant_two_subgroup_containing U Z hZ2 hUZ
    by_cases h' : S₁' ≤ M
    · exact hZS.trans h'
    · exfalso
      have hlt : S < S₁' ⊓ M := lt_of_lt_of_le hSA (le_inf (hAZ.trans hZS) hAM)
      have := hmax S₁' hS₁' h'
      have := Subgroup.card_lt_of_lt hlt
      omega
  obtain ⟨c, hc, hY₁, hY₁U, hT₀Y₁⟩ := key (T ⊓ H) hT.1.to_inf_left inf_le_right hUT₀ Y₀ hY₀ hY₀U
  have hcM : c ∈ M := hCU hc.2
  have hY₀M : Y₀ ≤ M := by
    refine (conjugate_subgroup_le_iff_of_conjugator_mem Y₀ M c hcM).mp ?_
    set Y₁' : Subgroup G := Y₀.map (MulAut.conj c).toMonoidHom with hY₁'
    have hZ2 : IsPGroup 2 ↥(Y₁' ⊔ (T ⊓ H)) :=
      isPGroup_sup_of_le_normalizer hY₁.isPGroup hT.1.to_inf_left hT₀Y₁
    have hZM := hmaxM (T ⊓ H) (Y₁' ⊔ (T ⊓ H)) hZ2 (le_normalizer_sup hY₁U hUT₀) le_sup_right
      (inf_le_left.trans hTM) hT₀
    exact le_sup_left.trans hZM
  obtain ⟨c', hc', hY₂, hY₂U, hS₀Y₂⟩ := key (S₁ ⊓ H) hS₁.1.to_inf_left inf_le_right hUS₀ Y₀ hY₀
    hY₀U
  have hc'M : c' ∈ M := hCU hc'.2
  have hY₂M : Y₀.map (MulAut.conj c').toMonoidHom ≤ M :=
    (conjugate_subgroup_le_iff_of_conjugator_mem Y₀ M c' hc'M).mpr hY₀M
  have hZ2 : IsPGroup 2 ↥(Y₀.map (MulAut.conj c').toMonoidHom ⊔ (S₁ ⊓ H)) :=
    isPGroup_sup_of_le_normalizer hY₂.isPGroup hS₁.1.to_inf_left hS₀Y₂
  obtain ⟨S₁'', hZS, hS₁''⟩ := exists_maximal_invariant_two_subgroup_containing U _ hZ2
    (le_normalizer_sup hY₂U hUS₀)
  by_cases h'' : S₁'' ≤ M
  · have hS₀M : S₁ ⊓ H ≤ M := (le_sup_right.trans hZS).trans h''
    have : S₁ ⊓ H ≤ S := by
      rw [← hint]
      exact le_inf inf_le_left hS₀M
    exact hS₀.not_ge this
  · have hle : Y₀.map (MulAut.conj c').toMonoidHom ≤ S₁'' ⊓ M :=
      le_inf (le_sup_left.trans hZS) hY₂M
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj c').injective] at h1
    have h2 := hmax S₁'' hS₁'' h''
    omega

theorem exists_R₀_of_maximal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U M N S₁ T : Subgroup G}
    (hU : IsPGroup p U) (hUM : U ≤ M) (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set G))
    (hNp : p.Coprime (Nat.card N))
    (hL43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ N) N → normalizer (Y : Set G) ≤ M)
    (hS₁ : rankTwoMaximalInvariantTwoSubgroup U S₁) (hS₁M : ¬ S₁ ≤ M)
    (hT : invariantTwoMaximalWithin U M T) (hint : S₁ ⊓ M = S₁ ⊓ T)
    (hSO : IsSylowOf 2 (S₁ ⊓ T) (GLBPrimeCore p (normalizer ((S₁ ⊓ T : Subgroup G) : Set G)))) :
    ∃ R₀ : Subgroup G, R₀ ≤ N ∧ R₀ ≤ T ∧ IsPGroup 2 R₀ ∧
      R₀ ≤ normalizer ((S₁ ⊓ T : Subgroup G) : Set G) ∧ U ≤ normalizer (R₀ : Set G) ∧
      ¬ R₀ ≤ S₁ ⊓ T ∧
      ¬ R₀ ≤ GLBPrimeCore p (normalizer ((S₁ ⊓ T : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := S₁ ⊓ T with hSdef
  set R : Subgroup G := T ⊓ N with hR
  have hS2 : IsPGroup 2 S := hS₁.1.to_inf_left
  have hR2 : IsPGroup 2 R := hT.2.1.to_inf_left
  have hUN : U ≤ normalizer (N : Set G) := hUM.trans hMN
  have hUS : U ≤ normalizer (S : Set G) :=
    common_normalizer_le_normalizer_inf U S₁ T hS₁.2.1 hT.2.2.1
  have hUR : U ≤ normalizer (R : Set G) :=
    common_normalizer_le_normalizer_inf U T N hT.2.2.1 hUN
  have hSTn : S ≤ T := inf_le_right
  have hTM : T ≤ M := hT.1
  have hTR : T ≤ normalizer (R : Set G) :=
    common_normalizer_le_normalizer_inf T T N Subgroup.le_normalizer (hTM.trans hMN)
  have hSR : S ≤ normalizer (R : Set G) := hSTn.trans hTR
  have hSyl := isSylowOf_inf_of_invariantTwoMaximalWithin hp hp2 hU hUM hNM hMN hNp hT
  have hesc : ¬ normalizer (S : Set G) ≤ M :=
    relative_pair_intersection_normalizer_escapes M S₁ T hS₁.1 hS₁M hTM hint
  have hRS : ¬ R ≤ S := by
    intro hRS
    have hSN : S ⊓ N = R := le_antisymm (inf_le_inf_right N hSTn) (le_inf hRS inf_le_right)
    exact hesc (hL43 S hS2 (hSTn.trans hTM) hUS (by rw [hSN]; exact hSyl))
  have hR₀S : ¬ R ⊓ normalizer (S : Set G) ≤ S := by
    intro hR₀S
    have hSupg : IsPGroup 2 ↥(R ⊔ S) := isPGroup_sup_of_le_normalizer hR2 hS2 hSR
    rw [sup_comm] at hSupg
    have hlt : S < S ⊔ R := lt_of_le_of_ne le_sup_left fun h => hRS (h ▸ le_sup_right)
    have hgrow := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two (S ⊔ R) S hSupg
      hlt
    obtain ⟨g, hg, hgS⟩ := Set.not_subset.mp hgrow.not_ge
    have hgSR : g ∈ (↑(S ⊔ R) : Set G) := hg.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S R hSR] at hgSR
    obtain ⟨s, hs, r, hr, rfl⟩ := hgSR
    have hrN : r ∈ normalizer (S : Set G) := by
      have h1 : s⁻¹ * (s * r) ∈ normalizer (S : Set G) :=
        (normalizer (S : Set G)).mul_mem ((normalizer (S : Set G)).inv_mem
          (Subgroup.le_normalizer hs)) hg.2
      simpa using h1
    exact hgS (S.mul_mem hs (hR₀S ⟨hr, hrN⟩))
  refine ⟨R ⊓ normalizer (S : Set G), inf_le_left.trans inf_le_right,
    inf_le_left.trans inf_le_left, hR2.to_inf_left, inf_le_right,
    common_normalizer_le_normalizer_inf U R _ hUR (hUS.trans Subgroup.le_normalizer), hR₀S, ?_⟩
  intro hR₀O
  have hpg : IsPGroup 2 ↥(S ⊔ (R ⊓ normalizer (S : Set G))) :=
    isPGroup_sup_of_le_normalizer hS2 hR2.to_inf_left inf_le_right
  have := hSO.eq_of_le (le_sup_left : S ≤ S ⊔ R ⊓ normalizer (S : Set G))
    (sup_le hSO.le hR₀O) hpg
  exact hR₀S (le_sup_right.trans this.le)

end CFSG.LocalAnalysis.RankFourTheoremC
