module

public import CFSG.LocalAnalysis.SectionRank.SignLift
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.LieType.Chevalley.G2Sign

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

theorem g2Param_quotient_injective
    {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    [CharP K p] (ι : ZMod p ≃+ K) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center (adjointGroup .G2 K))).comp
      (g2Param ι)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hv
  have hc := Holds.coprime_card_center (holds_adjointGroup_tag .G2 K p)
  have hpow : g2Param ι v ^ p = 1 := by
    rw [← map_pow]
    have : v ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [toAdd_pow, Pi.smul_apply, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, toAdd_one,
        Pi.zero_apply]
    rw [this, map_one]
  have h1 : orderOf (g2Param ι v) = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard _ hv) hc)
    (orderOf_dvd_of_pow_eq_one hpow)
  rw [orderOf_eq_one_iff] at h1
  rw [Subgroup.mem_bot]
  exact g2Param_injective ι (h1.trans (map_one _).symm)

theorem three_le_pRank_of_G2_prime_cover
    {G : Type} [Group G] [Finite G] (A : Subgroup G)
    [A.Normal] (hAZ : A ≤ Subgroup.center G) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = p) (e : G ⧸ A ≃* AdjointQuotient .G2 K) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have : CharP K p := charP_of_natCard_eq_pow (f := 1) (by rw [hK, pow_one])
  have := Fintype.ofFinite K
  let ι : ZMod p ≃+ K :=
    (ZMod.ringEquivOfPrime K hp.out (by rw [← Nat.card_eq_fintype_card, hK])).toAddEquiv
  set Z := Subgroup.center (adjointGroup .G2 K)
  let ρ : G →* AdjointQuotient .G2 K := e.toMonoidHom.comp (QuotientGroup.mk' A)
  have hρ : Function.Surjective ρ :=
    e.surjective.comp (QuotientGroup.mk'_surjective A)
  have hker : ρ.ker = A := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine three_le_pRank_of_sign_lines hp2 A hAZ ρ hρ hker ((QuotientGroup.mk' Z).comp (g2Param ι))
    (g2Param_quotient_injective ι) (QuotientGroup.mk' Z (torusElement .G2 K (0 : Fin 2) (-1)))
    (QuotientGroup.mk' Z (torusElement .G2 K (1 : Fin 2) (-1))) (fun v => ?_) (fun v => ?_)
  · have h := congrArg (QuotientGroup.mk' Z) (torusElement_conj_g2Param_zero ι v)
    rw [map_mul, map_mul, map_inv] at h
    exact h
  · have h := congrArg (QuotientGroup.mk' Z) (torusElement_conj_g2Param_one ι v)
    rw [map_mul, map_mul, map_inv] at h
    exact h

theorem g2_odd_central_cover_rank_three
    {G : Type} [Group G] [Finite G] (A : Subgroup G)
    [A.Normal] (hAZ : A ≤ Subgroup.center G) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ChevalleyExceptionalModel (G ⧸ A) .G2 p f) :
    3 ≤ CFSG.pRank p G ∧ ¬ IsStronglyQuasithin G := by
  have : Fact p.Prime := ⟨hp⟩
  have key : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
    obtain ⟨⟨-, hf, -⟩, hm⟩ := h
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
      exact three_le_pRank_of_G2_prime_cover A hAZ hp2 (by rw [hK, pow_one]) e
    · by_contra hlt
      have h3 := pRank_quotient_le_three hp2 (by omega) A hAZ
      have h6 := three_mul_le_pRank_of_G2Model hm
      omega
  refine ⟨(pRank_eq_open_pRank_top p G).symm ▸ key, fun hSQT => ?_⟩
  have := isStronglyQuasithin_iff.1 hSQT p hp hp2
  omega

theorem exceptional_odd_central_quotient_exclusion
    {G : Type} [Group G] [Finite G]
    (hSQT : IsStronglyQuasithin G) (A : Subgroup G) [A.Normal] (hAZ : A ≤ Subgroup.center G)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∀ t ∈ chevalleyExceptionalTags, ¬ ChevalleyExceptionalModel (G ⧸ A) t p f) ∧
      ¬ ReeTitsModel (G ⧸ A) .twistedG2 p f := by
  have : Fact p.Prime := ⟨hp⟩
  have hSQT' := isStronglyQuasithin_iff.1 hSQT
  have h3 := pRank_quotient_le_three hp2 (hSQT' p hp hp2) A hAZ
  refine ⟨fun t ht hmod => ?_, fun hmod => (smallRee_central_cover_rank_exclusion A hAZ hmod).2.2
    hSQT'⟩
  have hmod' := hmod
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hmod
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (g2_odd_central_cover_rank_three A hAZ hp hp2 hmod').2 hSQT
  all_goals first
    | (have := four_mul_le_pRank_of_untwistedModel (by simp) hm; omega)
    | (have := four_le_pRank_of_twistedE6Model hf hm; omega)
    | (have := four_le_pRank_of_trialityD4Model hf hm; omega)

end CFSG.SectionRank
