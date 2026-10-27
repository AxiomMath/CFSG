module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddG2F4E6E8
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddE7
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlockEvenRootExclusion
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddTwistedE6Triality
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotSuzukiTits
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISmallReeBlock
public import CFSG.LieType.Ree.LargeReeInvolutionOvergroupExclusion
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.LowTwoRank

theorem exists_ringEquiv_pow_eq_one_of_frobenius {K : Type} [Field K] {q m : ℕ}
    (hK : Nat.card K = q ^ m) (hq : 0 < q) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ q) :
    ∃ σ' : K ≃+* K, σ'.toRingHom = σ ∧ σ' ^ m = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hq m).ne')
  have : Fintype K := Fintype.ofFinite K
  set σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : ∀ c, σ' c = σ c := fun _ => rfl
  have hpow : ∀ n : ℕ, ∀ c, (σ' ^ n) c = c ^ (q ^ n) := by
    intro n
    induction n with
    | zero => intro c; rw [pow_zero, pow_zero, pow_one, RingAut.one_apply]
    | succ n ih =>
      intro c
      rw [pow_succ σ' n, RingAut.mul_apply, ih, hσ', hσ, ← pow_mul, ← pow_succ']
  refine ⟨σ', RingHom.ext hσ', RingEquiv.ext fun c => ?_⟩
  rw [hpow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card, RingAut.one_apply]

theorem commuting_block_escaping_overgroup_not_exceptional {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ ExceptionalRep (L ⧸ center L) := by
  classical
  have hevenX : ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (D : RootWeightDatum k),
      ¬ Nonempty (L ⧸ center L ≃* D.group) := fun k _ _ _ D he =>
    commuting_block_even_root_model_overgroup_exclusion hq heven hJ hΔ
      ⟨L, hL, hML, hLH, k, inferInstance, inferInstance, inferInstance, D, he⟩
  rintro (⟨t, p, f, ht, hT⟩ | ⟨t, p, f, ht, hT⟩ | ⟨p, f, hT⟩)
  ·
    obtain ⟨⟨hp, hf, -⟩, hmod⟩ := hT
    have hU : ∀ τ : Tag, (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
        UntwistedChevalleyModel (L ⧸ center L) τ (p ^ f) → False := by
      rintro τ hτ ⟨K, _, _, hK, ⟨e⟩⟩
      have : CharP K p := finite_field_prime_power_characteristic hp hf hK
      have e' := e.trans (RankThree.Chevalley.adjointQuotientEquiv τ K)
      by_cases hp2 : p = 2
      · subst hp2
        exact hevenX K (.ordinary τ) ⟨e'⟩
      · have hk : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
        have hodd := commuting_block_odd_G2_F4_E6_E8_overgroup_exclusion hq heven hV hJ hΔ hL hML
          hLH
        rcases hτ with rfl | rfl | rfl | rfl | rfl
        · exact hodd _ K (Or.inl rfl) hk ⟨e'⟩
        · exact hodd _ K (Or.inr (Or.inl rfl)) hk ⟨e'⟩
        · exact hodd _ K (Or.inr (Or.inr (Or.inl rfl))) hk ⟨e'⟩
        · exact commuting_block_odd_E7_overgroup_exclusion hq heven hV hJ hΔ hL hML hLH K hk
            ⟨e'⟩
        · exact hodd _ K (Or.inr (Or.inr (Or.inr rfl))) hk ⟨e'⟩
    have hTw : ∀ t' : TwistTag, TwistedChevalleyModel (L ⧸ center L) t' (p ^ f) → False := by
      rintro t' ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩
      obtain ⟨E⟩ := RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv t' hp hf K hK σ hσ
      have e' := e.trans E
      by_cases hp2 : p = 2
      · subst hp2
        have hK' : Nat.card K = 2 ^ (f * t'.order) := by rw [hK, ← pow_mul]
        have ht0 : 0 < t'.order := by cases t' <;> decide
        have : CharP K 2 :=
          finite_field_prime_power_characteristic Nat.prime_two (Nat.mul_pos hf ht0) hK'
        obtain ⟨σ', hσσ, hσ1⟩ :=
          exists_ringEquiv_pow_eq_one_of_frobenius hK (pow_pos two_pos f) σ hσ
        subst hσσ
        exact hevenX K (.fixed t' σ' hσ1) ⟨e'⟩
      · exact commuting_block_odd_twisted_E6_triality_overgroup_exclusion hq heven hV hJ hΔ hL
          hML hLH t' p f hp (hp.odd_of_ne_two hp2) hf K hK σ hσ ⟨e'⟩
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hU .G2 (Or.inl rfl) hmod
    · exact hU .F4 (Or.inr (Or.inl rfl)) hmod
    · exact hU .E6 (Or.inr (Or.inr (Or.inl rfl))) hmod
    · exact hU .E7 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hmod
    · exact hU .E8 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hmod
    · exact hTw .E6 hmod
    · exact hTw .D4 hmod
  ·
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    ·
      obtain ⟨-, -, hp3, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier _ p f hT
      subst hp3
      obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hT
      have : CharP K ReeTag.G2.prime :=
        finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
      have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa']
      exact (ComponentClassification.OutcomeLocal.commuting_block_small_Ree_overgroup_exclusion hq
        heven hJ hΔ hL hML hLH a' K hK').1 (hiso a' K hfa' hK hw)
    ·
      obtain ⟨-, -, -, hp2, ⟨a, ha, hfa⟩, hiso⟩ := ReeTag.large_Ree_model_Schreier _ p f hT
      subst hp2
      obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hT
      have : CharP K ReeTag.F4.prime :=
        finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
      have ha' : 1 ≤ a' := by omega
      have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hfa']
      obtain ⟨θ⟩ := hiso a' K hfa' hK hw
      obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma (K := K) ha' hK'
      exact LargeReeInvolution.commuting_block_large_Ree_overgroup_exclusion hq heven hJ hΔ hL hML
        hLH a' ha' K hK' ⟨θ.trans E.symm⟩
    ·
      exact commuting_block_suzuki_tits_overgroup_exclusion hq heven hJ hΔ hL hML hLH
        (Or.inr (Sporadic.Schreier.Tits.titsModelEquiv _ p f hT))
  ·
    obtain ⟨-, a, -, K, _, _, hfa, hK, he⟩ := hT
    exact commuting_block_suzuki_tits_overgroup_exclusion hq heven hJ hΔ hL hML hLH
      (Or.inl ⟨a, K, inferInstance, inferInstance, by rw [hK, hfa], he⟩)

end CFSG.LocalAnalysis.ComponentInitial
