module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Even

open CFSG Subgroup CatLeaf CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def EvenFiveList (τ : StatedLieTag) (n f : ℕ) : Prop :=
  (τ = .PSL ∧ n = 2 ∧ f = 4) ∨ (τ = .PSL ∧ n = 3 ∧ f = 2) ∨ (τ = .PSU ∧ n = 3 ∧ f = 2)

@[expose] def EvenFiveConc (τ : StatedLieTag) (n f : ℕ) {X : Type} [Group X] (P : Subgroup X) :
    Prop :=
  Nonempty (P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 5)) → EvenFiveList τ n f

@[expose] def EvenFiveOuter (τ : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] (n f : ℕ), StatedLieAdmissible τ n 2 f → Blueprint.LieModel K τ n 2 f →
    ∀ α : MulAut K, orderOf α = 2 → α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P → EvenFiveConc τ n f P

theorem card_alt_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5)) :
    Nat.card X = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_alt_six {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    Nat.card X = 360 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem eq_psl_two_two_of_mul_le_two {τ : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible τ n 2 f) (h : lieSylowExponent τ n * f ≤ 2) :
    τ = .PSL ∧ n = 2 ∧ f = 2 := by
  obtain ⟨-, hf, h'⟩ := hadm
  cases τ with
  | PSL =>
    obtain ⟨h2, h22, -⟩ := h'
    refine ⟨rfl, ?_⟩
    change n * (n - 1) / 2 * f ≤ 2 at h
    rcases Nat.lt_or_ge n 3 with hn | hn
    · obtain rfl : n = 2 := by omega
      refine ⟨rfl, ?_⟩
      have h1 : f ≠ 1 := fun h1 => h22 (by subst h1; norm_num)
      change 2 * (2 - 1) / 2 * f ≤ 2 at h
      norm_num at h
      omega
    · exfalso
      have h3 : 3 ≤ n * (n - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        exact Nat.mul_le_mul hn (by omega)
      nlinarith
  | PSU =>
    exfalso
    obtain ⟨hn, -⟩ := h'
    change n * (n - 1) / 2 * f ≤ 2 at h
    have h3 : 3 ≤ n * (n - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      exact Nat.mul_le_mul hn (by omega)
    nlinarith
  | PSp =>
    exfalso
    obtain ⟨hn, -⟩ := h'
    change n ^ 2 * f ≤ 2 at h
    nlinarith
  | POmegaOdd => exact absurd rfl h'.2
  | POmegaPlus =>
    exfalso
    change n * (n - 1) * f ≤ 2 at h
    have : 12 ≤ n * (n - 1) :=
      le_trans (by norm_num) (Nat.mul_le_mul (h' : 4 ≤ n) (by omega : 3 ≤ n - 1))
    nlinarith
  | POmegaMinus =>
    exfalso
    change n * (n - 1) * f ≤ 2 at h
    have : 12 ≤ n * (n - 1) :=
      le_trans (by norm_num) (Nat.mul_le_mul (h' : 4 ≤ n) (by omega : 3 ≤ n - 1))
    nlinarith
  | G2 => exfalso; simp only [lieSylowExponent] at h; omega
  | F4 => exfalso; simp only [lieSylowExponent] at h; omega
  | E6 => exfalso; simp only [lieSylowExponent] at h; omega
  | E7 => exfalso; simp only [lieSylowExponent] at h; omega
  | E8 => exfalso; simp only [lieSylowExponent] at h; omega
  | twistedE6 => exfalso; simp only [lieSylowExponent] at h; omega
  | trialityD4 => exfalso; simp only [lieSylowExponent] at h; omega
  | twistedB2 =>
    exfalso
    obtain ⟨-, -, -, h3⟩ := h'
    simp only [lieSylowExponent] at h
    omega
  | twistedG2 => exact absurd h'.2.1 (by norm_num)
  | twistedF4 =>
    exfalso
    obtain ⟨-, -, -, h3⟩ := h'
    simp only [lieSylowExponent] at h
    omega
  | Tits => exfalso; simp only [lieSylowExponent] at h; omega

theorem lieModel_card_sixty_even (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible τ n 2 f)
    (hm : Blueprint.LieModel X τ n 2 f) (hX : Nat.card X = 60) : τ = .PSL ∧ n = 2 ∧ f = 2 := by
  obtain ⟨-, -, hfac⟩ := hO X τ n 2 f hadm hm
  rw [hX] at hfac
  have hdvd : 2 ^ (lieSylowExponent τ n * f) ∣ 60 := by
    rw [← hfac]
    exact Nat.ordProj_dvd 60 2
  refine eq_psl_two_two_of_mul_le_two hadm ?_
  by_contra hlt
  push Not at hlt
  have h8 : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 hlt).trans hdvd
  revert h8
  decide

theorem not_card_sixty_of_u33 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hm : Blueprint.LieModel X .PSU 3 3 1) (hX : Nat.card X = 60) : False := by
  have hadm : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  obtain ⟨-, -, hfac⟩ := hO X .PSU 3 3 1 hadm hm
  rw [hX] at hfac
  have hdvd : 3 ^ (lieSylowExponent .PSU 3 * 1) ∣ 60 := by
    rw [← hfac]
    exact Nat.ordProj_dvd 60 3
  revert hdvd
  decide

theorem EvenFiveConc.of_model (hO : LieOrderFormulasInput) {τ : StatedLieTag} {n f : ℕ}
    {X : Type} [Group X] {P : Subgroup X} {τ' : StatedLieTag} {n' f' : ℕ}
    (hadm : StatedLieAdmissible τ' n' 2 f')
    (hm : Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f')
    (himp : τ' = .PSL → n' = 2 → f' = 2 → EvenFiveList τ n f) : EvenFiveConc τ n f P := by
  rintro ⟨e⟩
  obtain ⟨h1, h2, h3⟩ := lieModel_card_sixty_even hO hadm hm (card_alt_five e)
  exact himp h1 h2 h3

theorem EvenFiveConc.of_model_ne (hO : LieOrderFormulasInput) {τ : StatedLieTag} {n f : ℕ}
    {X : Type} [Group X] {P : Subgroup X} {τ' : StatedLieTag} {n' f' : ℕ}
    (hadm : StatedLieAdmissible τ' n' 2 f')
    (hm : Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f') (hne : τ' ≠ .PSL) :
    EvenFiveConc τ n f P :=
  EvenFiveConc.of_model hO hadm hm fun h => absurd h hne

theorem EvenFiveConc.of_u33 (hO : LieOrderFormulasInput) {τ : StatedLieTag} {n f : ℕ} {X : Type}
    [Group X] {P : Subgroup X} (hm : Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSU 3 3 1) :
    EvenFiveConc τ n f P := by
  rintro ⟨e5⟩
  exact (not_card_sixty_of_u33 hO hm (card_alt_five e5)).elim

theorem EvenFiveConc.of_mulEquiv {τ : StatedLieTag} {n f : ℕ} {X Y : Type} [Group X] [Group Y]
    [Finite X] [Finite Y] (Φ : X ≃* Y)
    (h : ∀ M : Subgroup Y, IsPComponent 2 M → EvenFiveConc τ n f M) {P : Subgroup X}
    (hP : IsPComponent 2 P) : EvenFiveConc τ n f P := by
  have hM := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Φ hP
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv'
    (P.equivMapOfInjective Φ.toMonoidHom Φ.injective)
  rintro ⟨e⟩
  exact h _ hM ⟨eZ.symm.trans e⟩

theorem EvenFiveConc.of_simple {τ : StatedLieTag} {n f : ℕ} {X Y : Type} [Group X] [Finite X]
    [Group Y] [IsSimpleGroup Y] (e : X ≃* Y)
    (hY : Nonempty (Y ≃* alternatingGroup (Fin 5)) → EvenFiveList τ n f) {P : Subgroup X}
    (hP : IsPComponent 2 P) : EvenFiveConc τ n f P := by
  have hXs : IsSimpleGroup X := e.isSimpleGroup
  have htop : P = ⊤ := GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hP
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    (((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans e)
  rintro ⟨e5⟩
  exact hY ⟨eZ.symm.trans e5⟩

theorem outcome_of_list {S : Type} [Group S] {τ : StatedLieTag} {n f : ℕ}
    (hm : Blueprint.LieModel S τ n 2 f) (h : EvenFiveList τ n f) : FivePumpOutcome S := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr (Or.inl hm))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hm)))

@[expose] def EvenFiveInner (τ : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ n f : ℕ, Blueprint.LieModel S τ n 2 f → ∀ t : S, orderOf t = 2 →
      ∀ P : Subgroup ↥(centralizer ({t} : Set S)), ¬ IsPComponent 2 P

theorem evenFiveList_of_inner_outer {τ : StatedLieTag} (hin : EvenFiveInner τ)
    (hout : EvenFiveOuter τ) {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ x y : S, x * y ≠ y * x) {n f : ℕ} (hL : Blueprint.LieModel S τ n 2 f)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (e : Nonempty (P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 5))) :
    EvenFiveList τ n f := by
  have := hs
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  · exfalso
    obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    exact hin S hna n f hL t ht2 _ hPc
  · obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
    obtain ⟨e5⟩ := e
    exact hout S n f hL.admissible hL σ hσ2 hout' _ h.2.2.1 ⟨eL.trans e5⟩

theorem fivePumpEven_of_inner_outer {τ : StatedLieTag} (hin : EvenFiveInner τ)
    (hout : EvenFiveOuter τ) : FivePumpEvenClause τ := by
  intro S _ _ hs hna ⟨n, f, hL⟩ σ P hP _ eP _
  exact outcome_of_list hL (evenFiveList_of_inner_outer hin hout hs hna hL hP eP)

end CFSG.ComponentClassification.SolMax.FiveCat.Even
