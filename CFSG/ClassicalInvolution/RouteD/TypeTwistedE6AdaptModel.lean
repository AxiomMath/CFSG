module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthLayer
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleWitt
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyOrth
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.ClassicalInvolution.RouteD.NonClassicalTwin
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.NonClassicalShape

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem span_eq_of_range_eq (hodd : Odd (Nat.card K)) {F F' : OFrame Q}
    (h : F.La.range = F'.La.range) : F.span = F'.span :=
  Frame.span_eq_of_La_neg_one_eq (IsFundamental.two_ne_zero_of_odd hodd)
    (frame_La_neg_one_eq_of_range_eq hodd h.symm).symm

omit [FiniteDimensional K V] in
theorem span_eq_of_range_eq_swap (hodd : Odd (Nat.card K)) {F F' : OFrame Q}
    (h : F.La.range = F'.swap.La.range) : F.span = F'.span :=
  (span_eq_of_range_eq hodd h).trans
    (Frame.span_eq_of_La_neg_one_eq (IsFundamental.two_ne_zero_of_odd hodd)
      (Frame.La_swap_neg_one F'))

theorem false_of_commutes_linear_pair (hodd : Odd (Nat.card K))
    (hfam : ∀ v : Fin 5 → Bool → V, ¬ IsHypFam Q v)
    {L₁ L₂ L₃ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ : V ≃ₗ[K] V} (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (h₃ : L₃ ∈ fundSet Q) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)))
    (hs : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂))
    (h31 : Commutes L₃ L₁) (h32 : Commutes L₃ L₂) : False := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  have hdim := Frame.finrank_inf_span_eq_two h2 hc.symm (conjSubgroup_eq_of_mem_normalizer hN)
    (exists_ne_of_not_mem_centralizer hC)
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at hs
  obtain ⟨T, hT1, hT2⟩ := Frame.exists_triple h2 hc.symm hdim hs
  have hne : F₁.span ⊓ F₂.span ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hdim
    omega
  have hperp₁ : F₁.span ⊓ F₁.perp = ⊥ := F₁.isCompl_span_perp.disjoint.eq_bot
  have hperp₂ : F₂.span ⊓ F₂.perp = ⊥ := F₂.isCompl_span_perp.disjoint.eq_bot
  have c1 : ¬ F₁.span ≤ F₂.perp := fun h => hne (by
    rw [eq_bot_iff, ← hperp₂]
    exact le_inf inf_le_right (inf_le_left.trans h))
  have c2 : ¬ F₂.span ≤ F₁.perp := fun h => hne (by
    rw [eq_bot_iff, ← hperp₁]
    exact le_inf inf_le_left (inf_le_right.trans h))
  have c3 : F₁.span ≠ F₂.span := by
    intro h
    rw [← h, inf_idem, Frame.finrank_span] at hdim
    omega
  have hm1 : L₃ ∈ insert F₁.swap.La.range
      {S | ∃ F : OFrame Q, F.La.range = S ∧ F.span ≤ F₁.perp} := by
    rw [← nbhd_eq_insert hodd F₁]
    exact ⟨h₃, h31⟩
  have hm2 : L₃ ∈ insert F₂.swap.La.range
      {S | ∃ F : OFrame Q, F.La.range = S ∧ F.span ≤ F₂.perp} := by
    rw [← nbhd_eq_insert hodd F₂]
    exact ⟨h₃, h32⟩
  have hsw : ∀ F : OFrame Q, F.swap.span = F.span := fun F =>
    Frame.span_eq_of_La_neg_one_eq h2 (Frame.La_swap_neg_one F)
  rcases hm1 with rfl | ⟨F, hF, hFperp⟩
  · rcases hm2 with h | ⟨F', hF', hF'perp⟩
    · exact c3 ((hsw F₁).symm.trans ((span_eq_of_range_eq hodd h).trans (hsw F₂)))
    · exact c1 ((span_eq_of_range_eq_swap hodd hF').symm ▸ hF'perp)
  · rcases hm2 with h | ⟨F', hF', hF'perp⟩
    · exact c2 ((span_eq_of_range_eq_swap hodd (hF.trans h)) ▸ hFperp)
    · have hspan : F'.span = F.span := span_eq_of_range_eq hodd (hF'.trans hF.symm)
      have hFperp₂ : F.span ≤ F₂.perp := hspan ▸ hF'perp
      have hp1 : F.span ≤ T.frame01.perp := (Frame.perp_eq_of_span_eq hT1).symm ▸ hFperp
      have hp2 : F.span ≤ T.frame12.perp := (Frame.perp_eq_of_span_eq hT2).symm ▸ hFperp₂
      obtain ⟨o01, o02, o03, o04⟩ := orth_pairs_of_span_le_perp hp1
      obtain ⟨p01, p02, p03, p04⟩ := orth_pairs_of_span_le_perp hp2
      let P : Fin 5 → HypPair Q := ![T.a, T.b, T.c, F.P, F.P']
      have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp only [P] <;>
          first
          | exact absurd rfl hij
          | exact T.ab | exact T.ab.symm | exact T.ac | exact T.ac.symm
          | exact T.bc | exact T.bc.symm | exact F.orth | exact F.orth.symm
          | exact o01 | exact o01.symm | exact o02 | exact o02.symm
          | exact o03 | exact o03.symm | exact o04 | exact o04.symm
          | exact p01 | exact p01.symm | exact p02 | exact p02.symm
          | exact p03 | exact p03.symm | exact p04 | exact p04.symm
      exact hfam _ (isHypFam_of_pairs P hP)

end Geometry

section Spin

variable {p e : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p e) V]
  [FiniteDimensional (GaloisField p e) V] {Q : QuadraticForm (GaloisField p e) V}
  {𝔉 : Set (Subgroup (spinGroup Q))}

theorem exists_overlap_of_linear (S : SpinCtx p e Q 𝔉) {R₁ R₂ : Subgroup (spinGroup Q)}
    (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) :
    ∃ i₁ i₂ : V ≃ₗ[GaloisField p e] V, IsFundamental Q (R₁.map (spinAction Q)) i₁ ∧
      IsFundamental Q (R₂.map (spinAction Q)) i₂ ∧ i₁ * i₂ = i₂ * i₁ ∧
      i₂ ∈ Subgroup.normalizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) ∧
      i₂ ∉ Subgroup.centralizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) ∧
      HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) := by
  have hodd := S.odd_card
  have h2 : (2 : GaloisField p e) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨W, hW⟩ := hlin
  obtain ⟨i₁, hI₁⟩ := S.map R₁ h₁
  obtain ⟨i₂, hI₂⟩ := S.map R₂ h₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ {R : Subgroup (spinGroup Q)}, R ∈ 𝔉 → ∀ {i : V ≃ₗ[GaloisField p e] V},
      IsFundamental Q (R.map (spinAction Q)) i →
        ∃ c ∈ R, orderOf c = 2 ∧ spinAction Q c = i := by
    intro R hR i hI
    obtain ⟨c, hcR, hc⟩ := hI.mem
    have hcc : c * c = 1 := S.inj R hR (c * c) (R.mul_mem hcR hcR)
      (by rw [map_mul, hc]; exact hI.mul_self)
    have hc1 : c ≠ 1 := fun h => hI.ne_one hodd (by rw [← hc, h, map_one])
    exact ⟨c, hcR, orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1, hc⟩
  obtain ⟨c₁, hc₁, ho₁, e₁⟩ := hinv h₁ hI₁
  obtain ⟨c₂, hc₂, ho₂, e₂⟩ := hinv h₂ hI₂
  have hc : c₁ * c₂ = c₂ * c₁ := Gaps.standardPair_involutions_commute h2 hW hc₁ hc₂ ho₁ ho₂
  have hcπ : i₁ * i₂ = i₂ * i₁ := by rw [← e₁, ← e₂, ← map_mul, ← map_mul, hc]
  have hnc : ¬ Commutes R₁ R₂ := not_commutes_of_linearBlockStandardPair hW
  have hL : R₁.map (spinAction Q) ≠ R₂.map (spinAction Q) := fun h =>
    ne_of_linearBlockStandardPair hW (S.eq_of_map_eq h₁ h₂ h)
  have hcent : i₂ ∉ Subgroup.centralizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) :=
    fun hcen => hnc (S.commutes_of_map h₁
      ((IsFundamental.commute_iff hodd hI₁ hI₂ hcπ hL).mpr hcen))
  have hN := S.mem_normalizer ho₁ ho₂ hc hI₁ hI₂ e₁ e₂ hcπ
  obtain ⟨-, hdich⟩ := lemma_6_10_dichotomy S.card_eq S.card_eq' hodd hI₁ hI₂ hcπ hN hcent
  rcases hdich with ⟨hs, -⟩ | ⟨-, huni⟩
  · exact ⟨i₁, i₂, hI₁, hI₂, hcπ, hN, hcent, hs⟩
  · exact (false_of_linear_of_unitary S.hp2 S.hq ⟨W, hW⟩ (S.unitary_of_map h₁ h₂ ⟨_, huni⟩)).elim

theorem false_of_commutes_linear_pair_spin (S : SpinCtx p e Q 𝔉)
    (hfam : ∀ v : Fin 5 → Bool → V, ¬ IsHypFam Q v) {R₁ R₂ R₃ : Subgroup (spinGroup Q)}
    (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉) (h₃ : R₃ ∈ 𝔉)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂)
    (h31 : Commutes R₃ R₁) (h32 : Commutes R₃ R₂) : False := by
  obtain ⟨i₁, i₂, hI₁, hI₂, hc, hN, hC, hs⟩ := exists_overlap_of_linear S h₁ h₂ hlin
  obtain ⟨i₃, hI₃⟩ := S.map R₃ h₃
  have hcomm : ∀ {A B : Subgroup (spinGroup Q)}, Commutes A B →
      Commutes (A.map (spinAction Q)) (B.map (spinAction Q)) := by
    rintro A B hAB _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAB a ha b hb]
  exact false_of_commutes_linear_pair S.odd_card hfam hI₁ hI₂ ⟨i₃, hI₃⟩ hc hN hC hs
    (hcomm h31) (hcomm h32)

end Spin

section Model

variable {p f : ℕ} [Fact p.Prime]

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

@[expose] def NoCommonCommutant (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  ∀ {X : Type} [Group X] (ψ : (Generic.modelUniv t n p e Fact.out).K →* X),
    ψ.ker ≤ Subgroup.center (Generic.modelUniv t n p e Fact.out).K →
    ∀ R₁ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D,
      ∀ R₂ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D,
        ∀ R₃ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D,
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map ψ) (R₂.map ψ)) →
            Commutes R₃ R₁ → Commutes R₃ R₂ → False

theorem noCommonCommutant_pOmegaMinus_five (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    NoCommonCommutant p f .POmegaMinus 5 f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus 5 p f := ⟨Fact.out, hf, by norm_num⟩
  intro X _ ψ hker R₁ hR₁ R₂ hR₂ R₃ hR₃ hlin h31 h32
  have S := spinCtx_pOmegaMinus hadm hp2 hq
  have := S.fin
  have hL := fun {R : Subgroup (Generic.modelUniv .POmegaMinus 5 p f Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 p f Fact.out).D) =>
    fundamentalSubgroups_subset_longest (t := .POmegaMinus) (by decide) (by decide) _ hR
  have hlin' : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂ :=
    Gaps.exists_lin_of_map S.four_le S.hC ψ hker (S.perf_le (hL hR₁)) (S.perf_le (hL hR₂)) hlin
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd S.odd_card
  exact false_of_commutes_linear_pair_spin S
    (fun v => false_of_isHypFam_quadMinus (m := 4) h2 (minusCoeffs_irr p f) S.four_le v)
    (hL hR₁) (hL hR₂) (hL hR₃) hlin' h31 h32

end Model

end CFSG.ClassicalInvolution.RouteD.NonClassical
