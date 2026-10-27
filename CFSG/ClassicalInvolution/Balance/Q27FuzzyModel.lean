module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyPair
public import CFSG.ClassicalInvolution.Balance.Q27PairData
public import CFSG.ClassicalInvolution.Balance.Q27ThreeD4Model

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.LieType.Steinberg.TwistedD4 (fixedField)
open scoped MatrixGroups

section Case

@[expose] def FieldCase (p f e : ℕ) (t : CFSG.Assembly.LowTwoRank.StatedLieTag) : Prop :=
  5 ≤ p ^ e ∨ (t = .trialityD4 ∧ 3 * e = f ∧ p ^ e = 3)

variable {p f : ℕ} [hp : Fact p.Prime]

theorem fieldCase_of_exp_eq {e : ℕ} {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (he : e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) :
    FieldCase p f e t := by
  by_cases h3 : p ^ e = 3
  · refine Or.inr ?_
    rcases he with rfl | h
    · omega
    · exact ⟨h.1, h.2, h3⟩
  · exact Or.inl (five_le_pow_of_ne_three hp.out hp2 hq (he.imp id And.right) h3)

end Case

section Pair

variable {p : ℕ} [hp : Fact p.Prime]

theorem eq_of_central_pair_trialityD4 {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    (ht : t = .trialityD4) {n e : ℕ}
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p e) {X : Type} [Group X]
    (ψ : (modelUniv t n p e hp.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp.out).K)
    {R₁ R₂ : Subgroup (modelUniv t n p e hp.out).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D)
    (hperf₂ : ⁅R₂, R₂⁆ = R₂) {z₁ z₂ : X} (hz₁ : z₁ ∈ R₁.map ψ) (hz₂ : z₂ ∈ R₂.map ψ)
    (hsq : z₁ * z₁ = 1) (h1 : z₁ ≠ 1) (h2 : z₂ ≠ 1) (hc₂ : ∀ y ∈ R₂.map ψ, z₂ * y = y * z₂)
    (hc₂₁ : ∀ y ∈ R₂.map ψ, z₁ * y = y * z₁) : z₁ = z₂ := by
  subst ht
  have hnc := Bootstrap.fundamentalSubgroups_eq_one_of_central (t := .trialityD4) (n := n)
    (p := p) (e := e) trivial hadm (by simp)
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨c₁, hc₁R, rfl⟩ := hz₁
  obtain ⟨c₂, hc₂R, rfl⟩ := hz₂
  have hc₁1 : c₁ ≠ 1 := fun h => h1 (by rw [h, map_one])
  have hc₂1 : c₂ ≠ 1 := fun h => h2 (by rw [h, map_one])
  have hsq' : c₁ * c₁ = 1 := by
    have hcen : c₁ * c₁ ∈ Subgroup.center (modelUniv .trialityD4 n p e hp.out).K :=
      hker (by rw [MonoidHom.mem_ker, map_mul, hsq])
    refine hnc R₁ hR₁ (c₁ * c₁) (R₁.mul_mem hc₁R hc₁R) fun y => ?_
    have := Subgroup.mem_center_iff.mp hcen y
    have h2' : c₁ * c₁ * y * (c₁ * c₁)⁻¹ * y⁻¹ = 1 := by
      rw [← this]
      group
    rw [h2']
    exact one_mem _
  have cent : ∀ {c : (modelUniv .trialityD4 n p e hp.out).K},
      (∀ y ∈ R₂.map ψ, ψ c * y = y * ψ c) → ∀ r ∈ R₂, c * r = r * c := by
    intro c hc r hr
    have h := Models.Transfer.mem_centralizer_of_map (θ := ψ) hker hperf₂ (g := c)
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm)
    exact (Subgroup.mem_centralizer_iff.mp h r hr).symm
  have hc : c₂ = c₁ :=
    ModelFacts.trialityD4_eq_of_central_in_perfect p e hp2 he hperf₂ hsq' hc₁1 hc₂1 hc₂R
      (cent hc₂) (cent hc₂₁)
  rw [hc]

end Pair

section Member

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G] {a : G}

theorem modOdd_ne_bot_of_member (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : Nonempty (↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField p f))) :
    modOdd a K ≠ ⊥ := by
  intro hbot
  obtain ⟨ψ, hψ⟩ := exists_surjective_of_modOdd hKa hK (u := (modOdd a K).subtype)
    (by rw [Subgroup.range_subtype])
  have hsub : Subsingleton ↥(modOdd a K) := by
    rw [hbot]
    infer_instance
  have hsub' : Subsingleton SL(2, GaloisField p f) := hψ.subsingleton
  have hcard := Finite.card_le_one_iff_subsingleton.2 hsub'
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    GaloisField.card p f (by
      rintro rfl
      simp at hq)] at hcard
  have h24 : 24 ≤ (p ^ f) ^ 2 - 1 := by
    have : 25 ≤ (p ^ f) ^ 2 := by nlinarith
    omega
  have h120 : 5 * 24 ≤ p ^ f * ((p ^ f) ^ 2 - 1) := Nat.mul_le_mul hq h24
  omega

theorem isQuasisimple_range_of_sl2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    {X : Type} [Group X] (φ : SL(2, F) →* X) (hφ : φ.range ≠ ⊥) :
    CFSG.Open.IsQuasisimple ↥φ.range := by
  have hq : CFSG.Open.IsQuasisimple SL(2, F) := isQuasisimple_specialLinearGroup_two h4
  have hq' : CFSG.IsQuasisimple SL(2, F) := ModelFacts.native_isQuasisimple hq
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq'
    (MonoidHom.normal_ker φ).isSubnormal with h | h
  · exfalso
    apply hφ
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    have : x ∈ φ.ker := by rw [h]; exact Subgroup.mem_top x
    rw [MonoidHom.mem_ker.mp this]
    exact Subgroup.one_mem _
  · have hq'' := Quasisimple.central_quotient hq φ.ker h
    exact Components.quasisimple_of_equiv (QuotientGroup.quotientKerEquivRange φ).symm hq''

theorem not_long_of_member_image {n e : ℕ} (hadm : StatedLieAdmissible .trialityD4 n p e)
    (hf : 3 * e = f) {K₂ : Subgroup G} (hK₂a : K₂ ≤ Subgroup.centralizer ({a} : Set G))
    (hK₂e : Nonempty (↥K₂ ⧸ classicalInvolutionOddCore ↥K₂ ≃* SL(2, GaloisField p f)))
    (ψ : (modelUniv .trialityD4 n p e hp.out).K →* OddQuot a)
    {R : Subgroup (modelUniv .trialityD4 n p e hp.out).K} (hK₂R : modOdd a K₂ = R.map ψ)
    (ι : SL(2, fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) →*
      (modelUniv .trialityD4 n p e hp.out).K)
    (hι : ι.range = R) : False := by
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨ψ', hψ'⟩ := exists_surjective_of_modOdd hK₂a hK₂e (ψ.comp ι)
    (by rw [MonoidHom.range_comp, hι, hK₂R])
  have hle := Nat.card_le_card_of_surjective ψ' hψ'
  have hFix : Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) = p ^ e :=
    ModelFacts.card_fixedField_iterateFrobenius he
  have hGF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFix, hGF] at hle
  have h2 : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)
  have hpf : p ^ f = (p ^ e) ^ 3 := by rw [← hf, pow_mul']
  rw [hpf] at hle
  generalize p ^ e = q at h2 hle
  have h3 : q * (q ^ 2 - 1) ≤ q * q ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h4 : 2 ≤ (q ^ 3) ^ 2 - 1 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    have : q ^ 2 ≤ (q ^ 3) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
    omega
  have h5 : q ^ 3 * 2 ≤ q ^ 3 * ((q ^ 3) ^ 2 - 1) := Nat.mul_le_mul_left _ h4
  have h6 : 0 < q ^ 3 := by positivity
  nlinarith

theorem perfect_of_member_image {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ}
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hcase : FieldCase p f e t) (ψ : (modelUniv t n p e hp.out).K →* OddQuot a)
    {R : Subgroup (modelUniv t n p e hp.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D) {K₂ : Subgroup G}
    (hK₂a : K₂ ≤ Subgroup.centralizer ({a} : Set G))
    (hK₂e : Nonempty (↥K₂ ⧸ classicalInvolutionOddCore ↥K₂ ≃* SL(2, GaloisField p f)))
    (hK₂R : modOdd a K₂ = R.map ψ) : ⁅R, R⁆ = R := by
  rcases hcase with h5 | ⟨ht, hf, he3⟩
  · exact commutator_self_eq_of_le
      (ModelFacts.fundPerfect_core t n p e hp2 hfund hadm (by omega) R hR)
  · subst ht
    rcases fundamental_trialityD4_perfect_or_long hadm R hR with h | ⟨ι, hι⟩
    · exact commutator_self_eq_of_le h
    · exact (not_long_of_member_image hadm hf hK₂a hK₂e ψ hK₂R ι hι).elim

theorem isQuasisimple_member_image {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ}
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hcase : FieldCase p f e t) (ψ : (modelUniv t n p e hp.out).K →* OddQuot a)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp.out).K)
    {R : Subgroup (modelUniv t n p e hp.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D) {K₂ : Subgroup G}
    (hK₂a : K₂ ≤ Subgroup.centralizer ({a} : Set G))
    (hK₂e : Nonempty (↥K₂ ⧸ classicalInvolutionOddCore ↥K₂ ≃* SL(2, GaloisField p f)))
    (hK₂R : modOdd a K₂ = R.map ψ) : CFSG.Open.IsQuasisimple ↥(modOdd a K₂) := by
  rcases hcase with h5 | ⟨ht, hf, he3⟩
  · rw [hK₂R]
    exact isQuasisimple_map_of_ker_le_center ψ hker
      (fundQuasisimple_core hp2 hfund hadm (by omega) R hR)
  · subst ht
    have he : 1 ≤ e := hadm.2.1
    rcases fundamental_trialityD4_sl2_range hadm R hR with ⟨ι, hι⟩ | ⟨ι, hι⟩
    · exact (not_long_of_member_image hadm hf hK₂a hK₂e ψ hK₂R ι hι).elim
    · have hrange : (ψ.comp ι).range = modOdd a K₂ := by
        rw [MonoidHom.range_comp, hι, hK₂R]
      have h4 : 4 ≤ Nat.card (GaloisField p (3 * e)) := by
        rw [GaloisField.card p (3 * e) (by omega), hf]
        omega
      have := isQuasisimple_range_of_sl2 h4 (ψ.comp ι)
        (by rw [hrange]; exact modOdd_ne_bot_of_member hq hK₂a hK₂e)
      rwa [hrange] at this

end Member

end CFSG.ClassicalInvolution.Balance.Q27
