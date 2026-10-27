module

public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinD
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic
public import CFSG.ClassicalInvolution.RouteD.TwinYSetup

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Images

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem twin_images {X : Type} [Group X] (π : X →* (V ≃ₗ[F] V))
    (hker : π.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card F)) {𝓕 : Set (Subgroup X)}
    (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R) (hmap : ∀ R ∈ 𝓕, R.map π ∈ fundSet Q)
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ 𝓕, R.map π = L) {R R' : Subgroup X} (hR : R ∈ 𝓕)
    (hR' : R' ∈ 𝓕) (hne : R ≠ R') (hc : Commutes R R')
    (hnb : ∀ S ∈ 𝓕, (S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R')) {r r' : X} (hrR : r ∈ R)
    (hr'R' : r' ∈ R') (hr2 : r * r = 1) (hr'2 : r' * r' = 1) (hr1 : π r ≠ 1) (hr'1 : π r' ≠ 1) :
    ∃ i i' : V ≃ₗ[F] V, IsFundamental Q (R.map π) i ∧ IsFundamental Q (R'.map π) i' ∧
      π r = i ∧ π r' = i' ∧ IsTwinPair (fundSet Q) (R.map π) (R'.map π) := by
  obtain ⟨i, hi⟩ := hmap R hR
  obtain ⟨i', hi'⟩ := hmap R' hR'
  have hπr : orderOf (π r) = 2 :=
    orderOf_eq_prime (by rw [_root_.sq, ← map_mul, hr2, map_one]) hr1
  have hπr' : orderOf (π r') = 2 :=
    orderOf_eq_prime (by rw [_root_.sq, ← map_mul, hr'2, map_one]) hr'1
  refine ⟨i, i', hi, hi', hi.eq_of_orderOf_eq_two hodd (Subgroup.mem_map_of_mem π hrR) hπr,
    hi'.eq_of_orderOf_eq_two hodd (Subgroup.mem_map_of_mem π hr'R') hπr', ?_⟩
  refine ⟨hmap R hR, hmap R' hR', fun h => hne (ModelFacts.eq_of_map_eq_of_isPerfect π hker
    (hperf R hR) (hperf R' hR') h), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  · intro S' hS' h0 h1
    obtain ⟨S, hS, rfl⟩ := hsurj S' hS'
    have key : ∀ T ∈ 𝓕, (S.map π = T.map π ∨ Commutes (S.map π) (T.map π)) ↔
        (S = T ∨ Commutes S T) := by
      intro T hT
      rw [Gaps.commutes_map_iff hker (hperf S hS)]
      constructor
      · rintro (h | h)
        · exact Or.inl (ModelFacts.eq_of_map_eq_of_isPerfect π hker (hperf S hS) (hperf T hT) h)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (by rw [h])
        · exact Or.inr h
    have h := (key R hR).trans ((hnb S hS).trans (key R' hR').symm)
    rwa [or_iff_right h0, or_iff_right h1] at h

end Images

section SameOrOrth

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

@[expose] def SameOrOrth (Q : QuadraticForm F V) : Prop :=
  ∀ (L L' : Subgroup (V ≃ₗ[F] V)) (i i' : V ≃ₗ[F] V), IsFundamental Q L i → IsFundamental Q L' i' →
    IsTwinPair (fundSet Q) L L' → i' = i ∨ i * i' ∈ Subgroup.center (V ≃ₗ[F] V)

theorem neg_mem_center {z : V ≃ₗ[F] V} (hz : ∀ v, z v = -v) :
    z ∈ Subgroup.center (V ≃ₗ[F] V) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext v
  simp [LinearEquiv.mul_apply, hz]

theorem sameOrOrth_of_lt_eight (hodd : Odd (Nat.card F)) (hdim : Module.finrank F V < 8) :
    SameOrOrth Q := fun _ _ _ _ hL hL' hTP =>
  Or.inl (commuting_same_involution hodd hdim hL hL' hTP.2.2.2.1)

theorem sameOrOrth_of_nine_le (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank F V) : SameOrOrth Q := fun _ _ _ _ hL hL' hTP =>
  Or.inl (twin_same_involution hodd hQ hdim hL hL' hTP)

theorem sameOrOrth_of_noOrth (hodd : Odd (Nat.card F))
    (hNo : ∀ F₀ F₁ : OFrame Q, F₁.span ≤ F₀.perp → False) : SameOrOrth Q := by
  intro L L' i i' hL hL' hTP
  rcases Gaps.orth_or_twin hodd hL hL' hTP.2.2.2.1 with horth | heq
  · exfalso
    obtain ⟨F₀, rfl, rfl⟩ := hL
    obtain ⟨F₁, rfl, rfl⟩ := hL'
    exact hNo F₀ F₁ (span_le_perp_of_negSpace hodd horth)
  · exact Or.inl heq

theorem mul_apply_of_orth (hodd : Odd (Nat.card F)) (hdim : Module.finrank F V = 8)
    {F₀ F₁ : OFrame Q}
    (horth : ∀ x ∈ negSpace (F₀.La (-1)), ∀ y ∈ negSpace (F₁.La (-1)), polar Q x y = 0) :
    ∀ v, (F₀.La (-1) * F₁.La (-1)) v = -v := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hsp₁ : F₁.span ≤ F₀.perp := span_le_perp_of_negSpace hodd horth
  have hsp₀ : F₀.span ≤ F₁.perp := span_le_perp_of_negSpace hodd fun x hx y hy => by
    rw [polar_comm]
    exact horth y hy x hx
  have d₀ := ModelFacts.finrank_perp_add_four F₀
  have d₁ := ModelFacts.finrank_perp_add_four F₁
  have e₁ : F₁.span = F₀.perp :=
    Submodule.eq_of_le_of_finrank_eq hsp₁ (by rw [F₁.finrank_span]; omega)
  have e₀ : F₀.span = F₁.perp :=
    Submodule.eq_of_le_of_finrank_eq hsp₀ (by rw [F₀.finrank_span]; omega)
  intro v
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    (F₀.isCompl_span_perp.sup_eq_top ▸ Submodule.mem_top : v ∈ F₀.span ⊔ F₀.perp)
  have a0 := (Frame.mem_span_iff_inv F₀ h2).mp ha
  have a1 := (Frame.mem_perp_iff_fix F₁ h2).mp (by rw [← e₀]; exact ha)
  have b0 := (Frame.mem_perp_iff_fix F₀ h2).mp hb
  have b1 := (Frame.mem_span_iff_inv F₁ h2).mp (by rw [e₁]; exact hb)
  simp only [LinearEquiv.mul_apply, map_add, a0, a1, b0, b1, map_neg, neg_add]

theorem sameOrOrth_of_eight (hodd : Odd (Nat.card F)) (hdim : Module.finrank F V = 8) :
    SameOrOrth Q := by
  intro L L' i i' hL hL' hTP
  rcases Gaps.orth_or_twin hodd hL hL' hTP.2.2.2.1 with horth | heq
  · right
    obtain ⟨F₀, rfl, rfl⟩ := hL
    obtain ⟨F₁, rfl, rfl⟩ := hL'
    exact neg_mem_center (mul_apply_of_orth hodd hdim horth)
  · exact Or.inl heq

end SameOrOrth

section Orth

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem twinProductCentral_orth {X : Type} [Group X] (hodd : Odd (Nat.card F))
    (π : X →* (V ≃ₗ[F] V)) (hker : π.ker ≤ Subgroup.center X)
    (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) {𝓕 : Set (Subgroup X)}
    (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R) (hmap : ∀ R ∈ 𝓕, R.map π ∈ fundSet Q)
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ 𝓕, R.map π = L) (hsl : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, F)))
    (hnc : ∀ R ∈ 𝓕, ∀ r ∈ R, r ∈ Subgroup.center X → r = 1) (hsame : SameOrOrth Q) :
    ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, R ≠ R' → Commutes R R' →
      (∀ S ∈ 𝓕, (S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R')) →
      ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ≠ 1 →
      ∀ r' ∈ R', (∀ s ∈ R', r' * s = s * r') → r' ≠ 1 → r * r' ∈ Subgroup.center X := by
  intro R hR R' hR' hne hc hnb r hrR hrc hr1 r' hr'R hr'c hr'1
  obtain ⟨eR⟩ := hsl R hR
  obtain ⟨eR'⟩ := hsl R' hR'
  obtain ⟨ord, -⟩ := fund_central_involution hodd eR hrR hrc hr1
  obtain ⟨ord', -⟩ := fund_central_involution hodd eR' hr'R hr'c hr'1
  have hr2 : r * r = 1 := by
    have := pow_orderOf_eq_one r
    rwa [ord, _root_.sq] at this
  have hr'2 : r' * r' = 1 := by
    have := pow_orderOf_eq_one r'
    rwa [ord', _root_.sq] at this
  have hπ1 : π r ≠ 1 := fun h => hr1 (hnc R hR r hrR (hker (MonoidHom.mem_ker.mpr h)))
  have hπ1' : π r' ≠ 1 := fun h => hr'1 (hnc R' hR' r' hr'R (hker (MonoidHom.mem_ker.mpr h)))
  obtain ⟨i, i', hi, hi', hπr, hπr', hTP⟩ := twin_images π hker hodd hperf hmap hsurj hR hR' hne hc
    hnb hrR hr'R hr2 hr'2 hπ1 hπ1'
  rcases hsame _ _ i i' hi hi' hTP with h | h
  · have : π (r * r') = 1 := by rw [map_mul, hπr, hπr', h, hi.mul_self]
    exact hker (MonoidHom.mem_ker.mpr this)
  · refine mem_center_of_map_commutes π hker hX fun g => ?_
    rw [map_mul, hπr, hπr']
    exact ((Subgroup.mem_center_iff.mp h) (π g)).symm

end Orth

section Tags

variable {p f : ℕ} [Fact p.Prime]


theorem fund_noncentral_center {t : StatedLieTag} {n : ℕ} (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) (hnA1 : ¬ (t = .PSL ∧ n = 2)) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D, ∀ r ∈ R,
      r ∈ Subgroup.center (modelUniv t n p f Fact.out).K → r = 1 := fun R hR r hr hrc =>
  Gaps.fundNoncentral p t n f hfund hadm hnA1 R hR r hr fun y => by
    have h1 := Subgroup.mem_center_iff.mp hrc y
    rw [← h1]
    simp

theorem commutator_top_of_quasisimple {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X) :
    ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
  have := h.1
  rwa [commutator_def] at this

private theorem commutator_self_eq {X : Type} [Group X] {R : Subgroup X} (h : R ≤ ⁅R, R⁆) :
    ⁅R, R⁆ = R :=
  le_antisymm (Subgroup.commutator_le.mpr fun _ ha _ hb =>
    R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) h

theorem twinProductCentral_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f) : TwinProductCentral p f .POmegaOdd n := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) trivial hadm (by omega : 4 ≤ p ^ f)
  have hqs := ModelFacts.isQuasisimple_modelUniv .POmegaOdd n p f Fact.out trivial hadm
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p f) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hsame : SameOrOrth (quadOdd n (GaloisField p f)) := by
    by_cases hn : n = 3
    · exact sameOrOrth_of_lt_eight hodd (by rw [hdim]; omega)
    · exact sameOrOrth_of_nine_le hodd (nondegenerate_polarBilin_quadOdd n (GaloisField p f)
        (ModelFacts.two_ne_zero_galoisField f hp2)) (by rw [hdim]; omega)
  exact twinProductCentral_orth (X := spinGroup (quadOdd n (GaloisField p f))) hodd
    (spinAction (quadOdd n (GaloisField p f))) (ker_spinAction_le_center _)
    (commutator_top_of_quasisimple hqs)
    (𝓕 := fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)))
    (fun R hR => commutator_self_eq (hperf R hR)) (fundCorr_odd hp2 hq hadm).1
    (fundCorr_odd hp2 hq hadm).2
    (fun R hR => ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaOdd)
      trivial hadm (by decide) (by decide) hR)
    (fund_noncentral_center (t := .POmegaOdd) trivial hadm (by simp)) hsame

theorem twinProductCentral_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f) : TwinProductCentral p f .POmegaMinus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) trivial hadm
    (by omega : 4 ≤ p ^ f)
  have hqs := ModelFacts.isQuasisimple_modelUniv .POmegaMinus n p f Fact.out trivial hadm
  have hdim : Module.finrank (GaloisField p f)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p f) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hsame : SameOrOrth (quadMinus n (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) := by
    by_cases hn : n = 4
    · subst hn
      exact sameOrOrth_of_noOrth hodd
        (fun F₀ F₁ hF => false_of_orth_quadMinus_four (ModelFacts.two_ne_zero_galoisField f hp2)
          (minusCoeffs_irr p f) h4 F₀ F₁ hF)
    · exact sameOrOrth_of_nine_le hodd
        (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField p f) (minusCoeffs_irr p f))
        (by rw [hdim]; omega)
  exact twinProductCentral_orth
    (X := spinGroup (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)) hodd
    (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
    (ker_spinAction_le_center _) (commutator_top_of_quasisimple hqs)
    (𝓕 := fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)))
    (fun R hR => commutator_self_eq (hperf R hR)) (fundCorr_minus hp2 hq hadm).1
    (fundCorr_minus hp2 hq hadm).2
    (fun R hR => ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaMinus)
      trivial hadm (by decide) (by decide) hR)
    (fund_noncentral_center (t := .POmegaMinus) trivial hadm (by simp)) hsame

theorem twinProductCentral_plus_aux {n : ℕ} (hn3 : 3 ≤ n) (hn4 : 4 ≤ n) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (M : LieUniversal)
    (hM : M = ⟨spinGroup (quadPlus n (GaloisField p f)), plusDatum n (GaloisField p f) hn3⟩)
    (hperf : Gaps.FundPerfect .POmegaPlus M.D) (hqs : CFSG.Open.IsQuasisimple M.K)
    (hsl : ∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, Nonempty (R ≃* SL(2, GaloisField p f)))
    (hnc : ∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) :
    ∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ R' ∈ fundamentalSubgroups .POmegaPlus M.D,
      R ≠ R' → Commutes R R' →
      (∀ S ∈ fundamentalSubgroups .POmegaPlus M.D, (S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R')) →
      ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ≠ 1 →
      ∀ r' ∈ R', (∀ s ∈ R', r' * s = s * r') → r' ≠ 1 → r * r' ∈ Subgroup.center M.K := by
  subst hM
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n → GaloisField p f) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hsame : SameOrOrth (quadPlus n (GaloisField p f)) := by
    by_cases hn : n = 4
    · exact sameOrOrth_of_eight hodd (by rw [hdim]; omega)
    · exact sameOrOrth_of_nine_le hodd (nondegenerate_polarBilin_quadPlus n (GaloisField p f))
        (by rw [hdim]; omega)
  exact twinProductCentral_orth (X := spinGroup (quadPlus n (GaloisField p f))) hodd
    (spinAction (quadPlus n (GaloisField p f))) (ker_spinAction_le_center _)
    (commutator_top_of_quasisimple hqs)
    (𝓕 := fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3))
    (fun R hR => commutator_self_eq (hperf R hR)) (fundCorr_plus hp2 hq hn4).1
    (fundCorr_plus hp2 hq hn4).2 hsl hnc hsame

theorem twinProductCentral_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p f) : TwinProductCentral p f .POmegaPlus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) trivial hadm
    (by omega : 4 ≤ p ^ f)
  have hqs := ModelFacts.isQuasisimple_modelUniv .POmegaPlus n p f Fact.out trivial hadm
  exact twinProductCentral_plus_aux hn3 hn4 hp2 hq (modelUniv .POmegaPlus n p f Fact.out)
    (ModelFacts.modelUniv_POmegaPlus hn3) hperf hqs
    (fun R hR => ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaPlus)
      trivial hadm (by decide) (by decide) hR)
    (fund_noncentral_center (t := .POmegaPlus) trivial hadm (by simp))

end Tags

end CFSG.ClassicalInvolution.Asc77.S28
