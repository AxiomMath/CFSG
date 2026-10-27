module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeFacts
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeFactsCenter
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeFactsUnitary

public section

namespace CFSG.ClassicalInvolution.RouteD.LieBridge

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.ModelFacts (fundamentalSubgroups_subset_longest
  fundamentalSubgroups_eq_top_PSL_two standardPairDichotomyTypes_psl standardPairDichotomyTypes_psu)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.LieType.Universal CFSG.LieType.Steinberg
open scoped commutatorElement

section Trialityd4

variable {p e : ℕ} [hp : Fact p.Prime]

theorem isPGroup_rootGroup_trialityD4 (hadm : StatedLieAdmissible .trialityD4 0 p e)
    {δ : Fin (CFSG.Blueprint.Chevalley.Tag.G2.rank) → ℤ}
    (hδ : δ ∈ (modelUniv .trialityD4 0 p e hp.out).D.roots) :
    IsPGroup p ((modelUniv .trialityD4 0 p e hp.out).D.rootGroup δ) := by
  have hf : 1 ≤ e := hadm.2.1
  have hcard : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), ← pow_mul, mul_comm]
  have hσ := TwistedD4.sigma_three_of_card
    (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e) hcard
    (fun c => iterateFrobenius_def p e c)
  exact CFSG.ClassicalInvolution.ModelFacts.isPGroup_twistedRootGroup _ hσ
    (TwistedD4.isRoot_of_mem_twistedDatum_roots _ hδ)

theorem exists_orderOf_eq_prime_trialityD4 {n : ℕ} (hadm : StatedLieAdmissible .trialityD4 n p e)
    {X : Type} [Group X] (ψ : (modelUniv .trialityD4 n p e hp.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .trialityD4 n p e hp.out).K)
    {R : Subgroup (modelUniv .trialityD4 n p e hp.out).K}
    (hR : R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e hp.out).D) :
    ∃ c ∈ Subgroup.centralizer ((R.map ψ : Subgroup X) : Set X), orderOf c = p := by
  obtain rfl : n = 0 := hadm.2.2
  have hpart : ∀ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e hp.out).D,
      ∃ R' ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e hp.out).D,
        Commutes R R' := partner_trialityD4 hadm
  obtain ⟨R', hR', hcomm⟩ := hpart R hR
  obtain ⟨g, δ, hδ, hR'eq⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.mem_roots_of_mem_fundamentalSubgroups hR'
  obtain ⟨nn, H, hct, hext⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum .trialityD4 0 p e
    hp.out trivial hadm
  have hne : (modelUniv .trialityD4 0 p e hp.out).D.rootGroup δ ≠ ⊥ := hext.ne_bot δ hδ
  obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hpg := isPGroup_rootGroup_trialityD4 hadm hδ
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hpg) u
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hu1 (orderOf_eq_one_iff.mp (by simpa using hk))
  have hpdvd : p ∣ orderOf u := by
    rw [hk]
    exact dvd_pow_self p hk0
  have hxo : orderOf (u ^ (orderOf u / p)) = p :=
    orderOf_pow_orderOf_div (by rw [hk]; exact (pow_pos hp.out.pos k).ne') hpdvd
  set v := u ^ (orderOf u / p) with hv
  set x : (modelUniv .trialityD4 0 p e hp.out).K := (v : (modelUniv .trialityD4 0 p e hp.out).K)
    with hx
  have hxU : x ∈ (modelUniv .trialityD4 0 p e hp.out).D.rootGroup δ := v.2
  set x' := g * x * g⁻¹ with hx'
  have hx'R : x' ∈ R' := by
    rw [hR'eq]
    exact ⟨x, Subgroup.mem_sup_left hxU, by simp [hx']⟩
  have hx'o : orderOf x' = p := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    rw [show (MulAut.conj g).toMonoidHom x = x' by simp [hx']] at this
    rw [this]
    have h2 : orderOf x = orderOf v := Subgroup.orderOf_coe v
    rw [h2, hxo]
  refine ⟨ψ x', ?_, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul, hcomm r hr x' hx'R]
  · have hne1 : ψ x' ≠ 1 := by
      intro h
      have hcen : x' ∈ Subgroup.center (modelUniv .trialityD4 0 p e hp.out).K :=
        hker (MonoidHom.mem_ker.mpr h)
      have h1 : x' = 1 := CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic p .trialityD4 0
        e trivial hadm (by simp) R' hR' x' hx'R fun y => by
          rw [← Subgroup.mem_center_iff.mp hcen y]
          simp
      rw [h1, orderOf_one] at hx'o
      exact hp.out.one_lt.ne hx'o
    have hpow : x' ^ p = 1 := by
      have := pow_orderOf_eq_one x'
      rwa [hx'o] at this
    exact orderOf_eq_prime (by rw [← map_pow, hpow, map_one]) hne1

end Trialityd4

section Component

variable {p f : ℕ} [Fact p.Prime]

theorem component_dichotomy' (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hOrth : FundamentalCentralizerNotSolvable p) (hK3 : CentersExponentThree p)
    (hU3 : UnitaryPairNoSplitNormalizer p) {t : StatedLieTag} {n e : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hexp : e = f ∨ (t = .trialityD4 ∧ 3 * e = f))
    {X : Type} [Group X] (ψ : (modelUniv t n p e Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K)
    {R₀ R₁ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hR₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {u₀ u₁ : X} (hu₀ : u₀ ∈ R₀.map ψ) (hu₁ : u₁ ∈ R₁.map ψ) (ho₀ : orderOf u₀ = 2)
    (ho₁ : orderOf u₁ = 2) (hc : u₀ * u₁ = u₁ * u₀) (hne : R₀.map ψ ≠ R₁.map ψ)
    (hnc : ¬ Commutes (R₀.map ψ) (R₁.map ψ))
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer ((R₀.map ψ : Subgroup X) : Set X)))
    (hnop : ∀ c ∈ Subgroup.centralizer ((R₀.map ψ : Subgroup X) : Set X), orderOf c ≠ p)
    (hγ : ∃ a ∈ R₀.map ψ, orderOf a = p ^ f - 1 ∧ conjSub a (R₁.map ψ) = R₁.map ψ) :
    e = f ∧
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField p f) W (R₀.map ψ) (R₁.map ψ) := by
  classical
  have hef : t = .PSL ∨ t = .PSU → e = f := by
    intro ht
    rcases hexp with h | ⟨h, -⟩
    · exact h
    · rcases ht with ht | ht <;> rw [ht] at h <;> exact absurd h (by decide)
  by_cases hPSL : t = .PSL ∧ n = 3
  · obtain ⟨rfl, rfl⟩ := hPSL
    obtain rfl := hef (Or.inl rfl)
    have h3 := hK3 .PSL _ (Or.inl rfl) hadm
    obtain ⟨c₀, hc₀R, hc₀u, hc₀o⟩ := exists_involution_lift ψ hker h3 hu₀ ho₀
    obtain ⟨c₁, hc₁R, hc₁u, hc₁o⟩ := exists_involution_lift ψ hker h3 hu₁ ho₁
    have hc₁sq : c₁ * c₁ = 1 := by rw [← pow_two]; exact hc₁o ▸ pow_orderOf_eq_one c₁
    have hcomm : c₀ * c₁ = c₁ * c₀ :=
      (commute_of_commute_map_of_exp_three ψ hker h3 hc₁sq (by
        rw [hc₀u, hc₁u]; exact hc)).eq
    rcases (standardPairDichotomyTypes_psl hadm).map_of_commute hp2 hq ψ hker
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₀)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁) hc₀R hc₁R hc₀o hc₁o
      hcomm with h | h | ⟨-, W, hW⟩ | ⟨hF, -⟩
    · exact absurd h hne
    · exact absurd h hnc
    · exact ⟨rfl, W, hW⟩
    · exact hF.elim
  by_cases hPSU : t = .PSU ∧ n = 3
  · obtain ⟨rfl, rfl⟩ := hPSU
    obtain rfl := hef (Or.inr rfl)
    have h3 := hK3 .PSU _ (Or.inr rfl) hadm
    obtain ⟨c₀, hc₀R, hc₀u, hc₀o⟩ := exists_involution_lift ψ hker h3 hu₀ ho₀
    obtain ⟨c₁, hc₁R, hc₁u, hc₁o⟩ := exists_involution_lift ψ hker h3 hu₁ ho₁
    have hc₁sq : c₁ * c₁ = 1 := by rw [← pow_two]; exact hc₁o ▸ pow_orderOf_eq_one c₁
    have hcomm : c₀ * c₁ = c₁ * c₀ :=
      (commute_of_commute_map_of_exp_three ψ hker h3 hc₁sq (by
        rw [hc₀u, hc₁u]; exact hc)).eq
    rcases (standardPairDichotomyTypes_psu hadm).map_of_commute hp2 hq ψ hker
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₀)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁) hc₀R hc₁R hc₀o hc₁o
      hcomm with h | h | ⟨hF, -⟩ | ⟨-, W, hW⟩
    · exact absurd h hne
    · exact absurd h hnc
    · exact hF.elim
    · exact (hU3 _ hq W _ _ hW hγ).elim
  exfalso
  by_cases hA2 : t = .PSL ∧ n = 2
  · obtain ⟨rfl, rfl⟩ := hA2
    have h0 := fundamentalSubgroups_eq_top_PSL_two p e Fact.out hadm
    exact hne (by rw [h0 R₀ hR₀, h0 R₁ hR₁])
  · have h1 : ¬ (t = .PSL ∧ n ≤ 3) := by
      rintro ⟨rfl, hn⟩
      have hn2 : 2 ≤ n := hadm.2.2.1
      have : n = 2 ∨ n = 3 := by omega
      rcases this with rfl | rfl
      · exact hA2 ⟨rfl, rfl⟩
      · exact hPSL ⟨rfl, rfl⟩
    by_cases h4 : 4 ≤ p ^ e
    · exact hOrth hp2 t n e hfund hadm h4 h1 hPSU R₀ hR₀
        (isSolvable_centralizer_of_ker_le_center ψ hker R₀ hsolv)
    · have ht : t = .trialityD4 := by
        rcases hexp with rfl | ⟨ht, -⟩
        · omega
        · exact ht
      subst ht
      obtain ⟨c, hc, hco⟩ := exists_orderOf_eq_prime_trialityD4 hadm ψ hker hR₀
      exact hnop c hc hco

end Component

@[expose] def LieA2Bridge' (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), InClass p f Λ → LieSystemMod p f Λ →
    classicalInvolutionOddCore Y ≤ Subgroup.center Y →
    ∀ (S₀ S₁ : Subgroup Y) (z₀ z₁ : Y), S₀ ∈ Λ → S₁ ∈ Λ →
      classicalInvolutionOddCore S₀ = ⊥ → classicalInvolutionOddCore S₁ = ⊥ →
      z₀ ∈ S₀ → z₁ ∈ S₁ → orderOf z₀ = 2 → orderOf z₁ = 2 → z₀ * z₁ = z₁ * z₀ → z₀ ≠ z₁ →
      ¬ Commutes S₀ S₁ → Group.IsSolvable ↥(Subgroup.centralizer (S₀ : Set Y)) →
      (∀ c ∈ Subgroup.centralizer (S₀ : Set Y), orderOf c ≠ p) →
      (∃ a ∈ S₀, orderOf a = p ^ f - 1 ∧ conjSub a S₁ = S₁) →
      ∃ W : Subgroup Y, LinearBlockStandardPair (GaloisField p f) W S₀ S₁

variable {p f : ℕ} [Fact p.Prime]

theorem lieA2Bridge'_of_facts (hOrth : FundamentalCentralizerNotSolvable p)
    (hK3 : CentersExponentThree p) (hU3 : UnitaryPairNoSplitNormalizer p) :
    LieA2Bridge' p f := by
  intro hp2 hq Y _ _ Λ hΛ hLie hO S₀ S₁ z₀ z₁ hS₀ hS₁ hex₀ hex₁ hz₀ hz₁ ho₀ ho₁ hcomm hne hnc
    hsolv hnop hγ
  classical
  obtain ⟨D⟩ := hLie
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨hodd, h5⟩ := CFSG.ClassicalInvolution.ModelFacts.odd_and_five_le_card_galoisField hp2 hq
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card Y
  obtain ⟨w₀, hw₀⟩ := hΛ.classical S₀ hS₀
  obtain ⟨w₁, hw₁⟩ := hΛ.classical S₁ hS₁
  have hperf₀ : S₀ ≤ ⁅S₀, S₀⁆ := (commutator_eq_of_isClassicalMember hw₀).ge
  have hperf₁ : S₁ ≤ ⁅S₁, S₁⁆ := (commutator_eq_of_isClassicalMember hw₁).ge
  obtain ⟨e₀⟩ := hw₀.nonempty_equiv_sl2 hex₀
  obtain ⟨e₁⟩ := hw₁.nonempty_equiv_sl2 hex₁
  have hker : (QuotientGroup.mk' (classicalInvolutionOddCore Y)).ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
    exact hO
  have hmk : ∀ z : Y, orderOf z = 2 →
      orderOf (QuotientGroup.mk' (classicalInvolutionOddCore Y) z) = 2 := by
    intro z hz
    have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
    have hne1 : QuotientGroup.mk' (classicalInvolutionOddCore Y) z ≠ 1 := by
      intro h
      have hzO : z ∈ classicalInvolutionOddCore Y := (QuotientGroup.eq_one_iff _).mp h
      have := Subgroup.orderOf_dvd_natCard (classicalInvolutionOddCore Y) hzO
      rw [hz] at this
      exact hOodd.not_two_dvd_nat this
    exact orderOf_eq_prime (by rw [← map_pow, hz2, map_one]) hne1
  have hne₀ : QuotientGroup.mk' (classicalInvolutionOddCore Y) z₀ ≠ 1 := fun h => by
    have := hmk z₀ ho₀
    rw [h, orderOf_one] at this
    omega
  have hinj₀ := eq_one_of_mem_ker_of_equiv_sl2 (QuotientGroup.mk' (classicalInvolutionOddCore Y))
    hodd hker e₀ hz₀ ho₀ hne₀
  have hm₀ : S₀.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) ∈ oddQuotientFamily Λ :=
    ⟨S₀, hS₀, rfl⟩
  have hm₁ : S₁.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) ∈ oddQuotientFamily Λ :=
    ⟨S₁, hS₁, rfl⟩
  obtain ⟨i₀, R₀, hR₀, hR₀eq⟩ := D.fundamental _ hm₀
  obtain ⟨i₁, R₁, hR₁, hR₁eq⟩ := D.fundamental _ hm₁
  have hnc' : ¬ Commutes (S₀.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
      (S₁.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))) :=
    fun h => hnc (commutes_of_map_commutes hO hperf₀ h)
  have hii : i₀ = i₁ := by
    by_contra hneq
    apply hnc'
    rw [hR₀eq, hR₁eq]
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    exact D.commute i₀ i₁ hneq x y
  subst hii
  have hne' : R₀.map (D.hom i₀) ≠ R₁.map (D.hom i₀) := by
    rw [← hR₀eq, ← hR₁eq]
    intro h
    have hS : S₀ = S₁ := eq_of_map_mk_eq_of_central hO hperf₀ hperf₁ h
    subst hS
    apply hne
    have h0 := (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e₀ ⟨z₀, hz₀⟩).mp
      (by rw [Subgroup.orderOf_mk, ho₀])
    have h1 := (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e₀ ⟨z₁, hz₁⟩).mp
      (by rw [Subgroup.orderOf_mk, ho₁])
    exact congrArg Subtype.val (h0.trans h1.symm)
  have hnc'' : ¬ Commutes (R₀.map (D.hom i₀)) (R₁.map (D.hom i₀)) := by
    rw [← hR₀eq, ← hR₁eq]
    exact hnc'
  have hsolv' : Group.IsSolvable ↥(Subgroup.centralizer
      ((R₀.map (D.hom i₀) : Subgroup (Y ⧸ classicalInvolutionOddCore Y)) :
        Set (Y ⧸ classicalInvolutionOddCore Y))) := by
    rw [← hR₀eq]
    exact isSolvable_centralizer_map hO hperf₀ hsolv
  have hnop' : ∀ c ∈ Subgroup.centralizer ((R₀.map (D.hom i₀) :
      Subgroup (Y ⧸ classicalInvolutionOddCore Y)) : Set (Y ⧸ classicalInvolutionOddCore Y)),
      orderOf c ≠ p := by
    intro c hc hcp
    rw [← hR₀eq] at hc
    obtain ⟨y, hy, rfl⟩ := centralizer_map_le hO hperf₀ hc
    have hdvd : p ∣ orderOf y := hcp ▸ orderOf_map_dvd (QuotientGroup.mk' _) y
    exact hnop _ (Subgroup.pow_mem _ hy _)
      (orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd)
  obtain ⟨a, haS, hao, hanorm⟩ := hγ
  have hγ' : ∃ a' ∈ R₀.map (D.hom i₀), orderOf a' = p ^ f - 1 ∧
      conjSub a' (R₁.map (D.hom i₀)) = R₁.map (D.hom i₀) := by
    refine ⟨QuotientGroup.mk' (classicalInvolutionOddCore Y) a, ?_, ?_, ?_⟩
    · rw [← hR₀eq]
      exact Subgroup.mem_map_of_mem _ haS
    · have := orderOf_injective ((QuotientGroup.mk' (classicalInvolutionOddCore Y)).domRestrict S₀)
        (injective_domRestrict hinj₀) ⟨a, haS⟩
      rw [Subgroup.orderOf_mk] at this
      exact this.trans hao
    · rw [← hR₁eq, conjSub_map, hanorm]
  obtain ⟨-, W, hW⟩ := component_dichotomy' hp2 hq hOrth hK3 hU3 (D.isFundTag i₀)
    (D.admissible i₀) (D.exp_eq i₀) (D.hom i₀) (D.ker_le_center i₀) hR₀ hR₁
    (u₀ := QuotientGroup.mk' (classicalInvolutionOddCore Y) z₀)
    (u₁ := QuotientGroup.mk' (classicalInvolutionOddCore Y) z₁)
    (by rw [← hR₀eq]; exact Subgroup.mem_map_of_mem _ hz₀)
    (by rw [← hR₁eq]; exact Subgroup.mem_map_of_mem _ hz₁) (hmk z₀ ho₀) (hmk z₁ ho₁)
    (by rw [← map_mul, ← map_mul, hcomm]) hne' hnc'' hsolv' hnop' hγ'
  rw [← hR₀eq, ← hR₁eq] at hW
  have hF : OddCoverSL3 (GaloisField p f) :=
    CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3.{0} (GaloisField.card p f hf) hq
  exact linearBlockStandardPair_lift (F := GaloisField p f) (by omega) hF hO hOodd hperf₀ hperf₁ hW

theorem lieA2Bridge' (p f : ℕ) [Fact p.Prime] : LieA2Bridge' p f :=
  lieA2Bridge'_of_facts (fundamentalCentralizerNotSolvable p) (centersExponentThree p)
    (unitaryPairNoSplitNormalizer p)

end CFSG.ClassicalInvolution.RouteD.LieBridge
