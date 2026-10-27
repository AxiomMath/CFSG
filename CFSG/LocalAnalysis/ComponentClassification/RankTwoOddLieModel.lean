module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelBridge
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAll
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.HighestRoot CFSG.ClassicalInvolution
  CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ClassicalInvolution.Generic (modelUniv IsFundTag IsLongestRoot IsClassicalMember)
open CFSG.Open (classicalInvolutionOddCore IsSubnormal)
open scoped MatrixGroups

theorem classicalInvolutionOddCore_eq_bot {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {L : Subgroup Y} (eL : L ≃* SL(2, F)) :
    classicalInvolutionOddCore L = ⊥ := by
  refine sSup_eq_bot.mpr fun N hN => ?_
  have hN : N.Normal ∧ Odd (Nat.card N) := hN
  have hN' : N.map L.subtype = ⊥ := by
    refine eq_bot_of_normal_odd eL hF (map_subtype_le N) (fun l hl => ?_) ?_
    · rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨l, hl⟩ * n * ⟨l, hl⟩⁻¹, hN.1.conj_mem n hn ⟨l, hl⟩, rfl⟩
      · rintro ⟨n, hn, hny⟩
        refine ⟨⟨l, hl⟩⁻¹ * n * ⟨l, hl⟩, by simpa using hN.1.conj_mem n hn ⟨l, hl⟩⁻¹, ?_⟩
        show l⁻¹ * (n : Y) * l = y
        rw [show (n : Y) = l * y * l⁻¹ from hny]
        group
    · rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact hN.2
  exact (Subgroup.map_eq_bot_iff_of_injective N L.subtype_injective).mp hN'

theorem isClassicalMember_of_sl2 {Y : Type} [Group Y] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) {L : Subgroup Y} {z : Y} (eL : L ≃* SL(2, GaloisField p f))
    (hz2 : orderOf z = 2) (hzL : z ∈ L) (hLC : L ≤ centralizer ({z} : Set Y))
    (hCN : centralizer ({z} : Set Y) ≤ normalizer (L : Set Y)) : IsClassicalMember p f L z := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hF : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hcard]
    omega
  exact ⟨hz2, hzL, isPerfect_of_equiv_sl2 h4 eL,
    IsSubnormal.step hLC ((normal_subgroupOf_iff_le_normalizer hLC).mpr hCN) (IsSubnormal.refl _),
    ⟨((QuotientGroup.quotientMulEquivOfEq (classicalInvolutionOddCore_eq_bot hF eL)).trans
      QuotientGroup.quotientBot).trans eL⟩⟩

theorem eq_of_conj_of_involution {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {J : Subgroup K} (eJ : J ≃* SL(2, F)) {z : K} (hzJ : z ∈ J)
    (hz2 : orderOf z = 2) (hCZ : centralizer ({z} : Set K) ≤ normalizer (J : Set K)) (d : K)
    (hzd : z ∈ conjSubgroup d J) : conjSubgroup d J = J := by
  have hzsq : z ^ 2 = 1 := by
    rw [← hz2]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  have hzc : z = centralInv eJ := (eq_one_or_centralInv_of_sq eJ hF hzJ hzsq).resolve_left hz1
  have hzc' : z = d * z * d⁻¹ := by
    have := (eq_one_or_centralInv_of_sq (conjEquiv eJ d) hF hzd hzsq).resolve_left hz1
    rw [centralInv_conjEquiv, ← hzc] at this
    exact this
  have hdC : d ∈ centralizer ({z} : Set K) := by
    rw [mem_centralizer_singleton_iff]
    calc d * z = (d * z * d⁻¹) * d := by group
      _ = z * d := by rw [← hzc']
  rw [conjSubgroup_eq_rightConjugate, rightConjugate_eq_self_iff]
  exact inv_mem (hCZ hdC)

section Models

variable {t : StatedLieTag} {n p e : ℕ} [Fact p.Prime]

theorem nonempty_rankOne_equiv (hp2 : p ≠ 2) (hFT : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) {γ : Fin (modelUniv t n p e Fact.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv t n p e Fact.out).D γ) :
    Nonempty (rankOneGroup (modelUniv t n p e Fact.out).D γ ≃* SL(2, GaloisField p e)) := by
  obtain ⟨eγ⟩ := ModelFacts.fundamentalSL2_of_isFundTag hp2 hFT hadm 1 γ hγ
  exact ⟨(MulEquiv.subgroupCongr (ModelFacts.map_conj_one _)).symm.trans eγ⟩

theorem eq_rankOne_of_classical (hp2 : p ≠ 2) (hFT : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (h5 : 5 ≤ p ^ e)
    {γ : Fin (modelUniv t n p e Fact.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv t n p e Fact.out).D γ) {z : (modelUniv t n p e Fact.out).K}
    (hz : z ∈ rankOneGroup (modelUniv t n p e Fact.out).D γ) (hz2 : orderOf z = 2)
    (hCZ : centralizer ({z} : Set (modelUniv t n p e Fact.out).K) ≤
      normalizer (rankOneGroup (modelUniv t n p e Fact.out).D γ : Set _))
    (L : Subgroup (modelUniv t n p e Fact.out).K)
    (hLC : L ≤ centralizer ({z} : Set (modelUniv t n p e Fact.out).K))
    (hCN : centralizer ({z} : Set (modelUniv t n p e Fact.out).K) ≤ normalizer (L : Set _))
    (hL : Nonempty (L ≃* SL(2, GaloisField p e))) (hzL : z ∈ L) :
    L = rankOneGroup (modelUniv t n p e Fact.out).D γ := by
  obtain ⟨eL⟩ := hL
  obtain ⟨eJ⟩ := nonempty_rankOne_equiv hp2 hFT hadm hγ
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have hF : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e he]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hFT' : ModelFacts.IsFundTag t := by
    cases t <;> trivial
  have : Finite (modelUniv t n p e Fact.out).K := ModelFacts.finite_modelUniv hp2 Fact.out hFT hadm
  have hmem := isClassicalMember_of_sl2 hp2 h5 eL hz2 hzL hLC hCN
  obtain ⟨R, hR, hLR⟩ := ModelFacts.classicalIsFundamental_of_exc (p := p) (f := e)
    ModelFacts.classicalMembersFundamentalExc hp2 h5 t n e Fact.out hFT hadm (Or.inl rfl)
    (modelUniv t n p e Fact.out).K (MonoidHom.id _) Function.surjective_id
    (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
      rw [hx]
      exact one_mem _) L z hmem
  rw [Subgroup.map_id] at hLR
  obtain ⟨g, δ, hδ, rfl⟩ := hR
  have hδ' : IsLongestRoot (modelUniv t n p e Fact.out).D δ := by
    rcases hδ with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hG2
    · exact absurd h hD4
  obtain ⟨c, hc⟩ : ∃ c : (modelUniv t n p e Fact.out).K,
      conjSubgroup c (rankOneGroup (modelUniv t n p e Fact.out).D γ) =
        rankOneGroup (modelUniv t n p e Fact.out).D δ :=
    ModelFacts.exists_conj_of_isLongestRoot t n p e Fact.out hFT' hadm hγ hδ'
  have hLd : L = conjSubgroup (g * c) (rankOneGroup (modelUniv t n p e Fact.out).D γ) := by
    rw [← conjSubgroup_conjSubgroup, hc]
    exact hLR
  rw [hLd]
  exact eq_of_conj_of_involution hF eJ hz hz2 hCZ (g * c) (hLd ▸ hzL)

theorem exists_sl2CentralizerData (hI : OddLieInputs) (h4 : TrialityD4SL2Unique) (hp2 : p ≠ 2)
    (hFT : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hne : (t, n) ≠ (.PSL, 2)) :
    ∃ γ, IsLongestRoot (modelUniv t n p e Fact.out).D γ ∧
      SL2CentralizerData (GaloisField p e) (rankOneGroup (modelUniv t n p e Fact.out).D γ) := by
  by_cases hG2 : t = .G2
  · subst hG2
    obtain rfl : n = 0 := hadm.2.2.1
    obtain ⟨hconj, γ, hγR, hγl, hdata⟩ := hI.g2 p e hp2 hadm
    refine ⟨γ, ⟨hγR, hγl⟩, fun z hz hz2 => ?_⟩
    obtain ⟨hCZ, L₀, -, -, -, hJL₀, hU⟩ := hdata z hz hz2
    exact ⟨hCZ, L₀, hU, Or.inr ⟨hJL₀, hconj⟩⟩
  obtain ⟨γ, hγR, hγl, hCC⟩ := hI.cz t n p e hp2 hFT hadm hne hG2
  refine ⟨γ, ⟨hγR, hγl⟩, fun z hz hz2 => ?_⟩
  obtain ⟨hCZ, hU3⟩ := hCC z hz hz2
  refine ⟨hCZ, rankOneGroup _ γ, fun L h1 h2 h3 h4' => Or.inl ?_, Or.inl rfl⟩
  have he : e ≠ 0 := by
    have := hadm.2.1
    omega
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  by_cases h3' : Nat.card (GaloisField p e) = 3
  · exact hU3 h3' L h1 h2 h3 h4'
  have h5 : 5 ≤ p ^ e := by
    have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    have hpe : p ≤ p ^ e := Nat.le_self_pow he p
    obtain ⟨m, hm⟩ : Odd (p ^ e) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    rw [hcard] at h3'
    omega
  by_cases hD4 : t = .trialityD4
  · subst hD4
    exact h4 n p e hp2 hadm h5 γ ⟨hγR, hγl⟩ z hz hz2 L h1 h2 h3 h4'
  exact eq_rankOne_of_classical hp2 hFT hadm hG2 hD4 h5 ⟨hγR, hγl⟩ hz hz2 hCZ L h1 h2 h3 h4'

end Models

theorem modelHighestRootData_of (hI : OddLieInputs) (h1 : ModelCenterPPrime) (h2 : ModelAutLift)
    (h3 : SL2OuterComm) (h4 : TrialityD4SL2Unique) : ModelHighestRootData := by
  intro t n p e hp hp2 hFT hadm hne G _ _ _ hZ φ hφ hker
  have : Fact p.Prime := ⟨hp⟩
  have he : e ≠ 0 := by
    have := hadm.2.1
    omega
  have : Finite (modelUniv t n p e hp).K := ModelFacts.finite_modelUniv hp2 hp hFT hadm
  have : Group.IsPerfect (modelUniv t n p e hp).K :=
    ⟨(ModelFacts.modelClauseZero t n p e hp hFT hadm).1.1⟩
  have hne' : ¬ (t = .PSL ∧ n = 2) := fun ⟨ht, hn⟩ => hne (by rw [ht, hn])
  have hFT' : ModelFacts.IsFundTag t := by
    cases t <;> trivial
  refine highestRootData_of_datum h3 hp2 he (h1 t n p e hp hp2 hFT hadm)
    (h2 t n p e hp hp2 hFT hadm) (hI.gen t n p e hp2 hFT hadm hne)
    (fun γ γ' hγ hγ' => ModelFacts.exists_conj_of_isLongestRoot t n p e hp hFT' hadm hγ hγ')
    (fun γ hγ => nonempty_rankOne_equiv hp2 hFT hadm hγ) (fun γ hγ x hx hxc => ?_)
    (exists_sl2CentralizerData hI h4 hp2 hFT hadm hne) hZ φ hφ hker
  refine ModelFacts.fundNoncentral_generic p t n e hFT hadm hne'
    (rankOneGroup (modelUniv t n p e hp).D γ) ⟨1, γ, Or.inl hγ, (ModelFacts.map_conj_one _).symm⟩
    x hx fun y => ?_
  rw [← Subgroup.mem_center_iff.mp hxc y, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

end CFSG.ComponentClassification.RankTwoOddLie
