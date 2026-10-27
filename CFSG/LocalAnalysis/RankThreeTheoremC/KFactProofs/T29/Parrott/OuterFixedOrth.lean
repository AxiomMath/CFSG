module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedBasic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThree
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.LieType.SeitzGeneration.ThreeIndepOrth

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)
open CFSG.RankThree.Classical.SteinbergBY
  (orthogonal_large_prime_semilinear_field_and_diagonal_gates)
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')

theorem exists_E9_of_not_rankLE2_three {G : Type*} [Group G] [Finite G]
    (h : ¬ CFSG.LieType.SeitzGeneration.RankLE2 3 G) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simp only [CFSG.LieType.SeitzGeneration.RankLE2, not_forall, not_le] at h
  obtain ⟨F, hF, hF9⟩ := h
  have hFp : IsPGroup 3 F := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hF.2 g g.2)⟩
  obtain ⟨m, hm⟩ := hFp.exists_card_eq
  have hm3 : 2 ≤ m := by
    by_contra hlt
    have : m ≤ 1 := by omega
    have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 2 ∣ Nat.card F from hm ▸ pow_dvd_pow 3 hm3)
  refine ⟨H.map F.subtype, CFSG.SectionRank.isElemAbelian_map ?_ _, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x _ => Subtype.ext (hF.2 _ x.2)⟩
    exact hF.comm a.1.2 b.1.2
  · rw [Subgroup.card_map_of_injective F.subtype_injective, hH]
    norm_num

theorem exists_fixed_E9_of_congr {P P' : Type} [Group P] [Group P'] (Θ : P ≃* P') {α : MulAut P}
    {δ : MulAut P'} (hΘ : MulAut.congr Θ α = δ)
    (h : ∃ E : Subgroup P', IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, δ e = e) :
    ∃ E : Subgroup P, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, α e = e := by
  obtain ⟨E, hE, hE9, hfix⟩ := h
  obtain ⟨hE', hE9'⟩ := isElemAbelian_card_map_of_E9 Θ.symm.toMonoidHom Θ.symm.injective hE hE9
  refine ⟨_, hE', hE9', ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h0 : (MulAut.congr Θ α) y = y := by
    rw [hΘ]
    exact hfix y hy
  have h1 : Θ (α (Θ.symm y)) = y := h0
  have h2 := congrArg Θ.symm h1
  rw [MulEquiv.symm_apply_apply] at h2
  exact h2

section Fixed

variable {K : Type} [Field K] [Finite K]

theorem two_ne_zero_subfield_of_ringChar (k : Subfield K) (h2 : ringChar K ≠ 2) : (2 : k) ≠ 0 := by
  intro h
  apply Ring.two_ne_zero h2
  have h' := congrArg k.subtype h
  rwa [map_ofNat, map_zero] at h'

theorem exists_E9_fixed_fieldAutT_odd {n : ℕ} (hn : 3 ≤ n) (h2 : ringChar K ≠ 2)
    {σ : K ≃+* K} (g : similarityPairs (coordinateQuadOdd n K)) (hl : g.val.left = 1)
    (hr : g.val.right = σ) :
    ∃ E : Subgroup (matrixProjectiveDerived (coordinateQuadOdd n K)), IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ ∀ e ∈ E, matrixProjectiveConjugationHom _ g e = e := by
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hg : g = fieldPair (coordinateQuadOdd n K) σ (coordinateQuadOdd_fieldAut n σ) :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  have hext := coordinateQuadOdd_isExtension (semilinearFixedSubfield σ) n
  have : Finite (semilinearFixedSubfield σ) := Subtype.finite
  obtain ⟨E₀, hE₀, hE₀9⟩ := exists_E9_of_not_rankLE2_three
    (CFSG.LieType.SeitzGeneration.not_rankLE2_three_odd (K := semilinearFixedSubfield σ) hn
      (two_ne_zero_subfield_of_ringChar _ h2))
  obtain ⟨hE₁, hE₁9⟩ := isElemAbelian_card_map_of_E9
    (coordinateOddWitnessEquiv (semilinearFixedSubfield σ) (MulEquiv.refl _)).toMonoidHom
    (coordinateOddWitnessEquiv (semilinearFixedSubfield σ) (MulEquiv.refl _)).injective hE₀ hE₀9
  obtain ⟨hE, hE9⟩ :=
    isElemAbelian_card_map_of_E9 (incl _ hext) (incl_injective _ hext (by omega)) hE₁ hE₁9
  refine ⟨_, hE, hE9, ?_⟩
  rintro _ ⟨y, -, rfl⟩
  exact fieldAutT_fixes_J _ _ σ _ hext hσk ⟨y, rfl⟩

theorem exists_E9_fixed_fieldAutT_minus {n : ℕ} (hn1 : 1 ≤ n) (hn : 4 ≤ n) {σ : K ≃+* K}
    (b c : semilinearFixedSubfield σ)
    (hirr : ∀ s : semilinearFixedSubfield σ, s ^ 2 + b * s + c ≠ 0)
    (g : similarityPairs (coordinateQuadMinus n K hn1 (b : K) (c : K)))
    (hl : g.val.left = 1) (hr : g.val.right = σ) :
    ∃ E : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K))),
      IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, matrixProjectiveConjugationHom _ g e = e := by
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hg : g = fieldPair (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ
      (coordinateQuadMinus_fieldAut _ n hn1 hσk b c) :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  have hext := coordinateQuadMinus_isExtension (semilinearFixedSubfield σ) n hn1 b c
  have : Finite (semilinearFixedSubfield σ) := Subtype.finite
  obtain ⟨E₀, hE₀, hE₀9⟩ := exists_E9_of_not_rankLE2_three
    (CFSG.LieType.SeitzGeneration.not_rankLE2_three_minus (K := semilinearFixedSubfield σ) hn
      hirr)
  obtain ⟨hE₁, hE₁9⟩ := isElemAbelian_card_map_of_E9
    (coordinateMinusWitnessEquiv (semilinearFixedSubfield σ) hn1 b c
      (MulEquiv.refl _)).toMonoidHom
    (coordinateMinusWitnessEquiv (semilinearFixedSubfield σ) hn1 b c
      (MulEquiv.refl _)).injective hE₀ hE₀9
  obtain ⟨hE, hE9⟩ :=
    isElemAbelian_card_map_of_E9 (incl _ hext) (incl_injective _ hext (by omega)) hE₁ hE₁9
  refine ⟨_, hE, hE9, ?_⟩
  rintro _ ⟨y, -, rfl⟩
  exact fieldAutT_fixes_J _ _ σ _ hext hσk ⟨y, rfl⟩

end Fixed

theorem outerFixesE9_coordOdd {G : Type} [Group G] {n ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaOdd n ℓ f) (hℓ3 : ℓ ≠ 3) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    [Finite (matrixProjectiveDerived (coordinateQuadOdd n K))] :
    OuterFixesE9 (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates
    G .POmegaOdd (Or.inl rfl) n ℓ f h K hK e
  obtain ⟨hℓ, hf, hn3, hℓ2⟩ := h.1
  have h2K : ringChar K ≠ 2 := by
    rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hℓ hf hK]
    exact hℓ2
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn3 h2K
  intro α hα3 hαo
  have hα1 : α ≠ 1 := fun h1 => hαo ⟨1, by rw [h1, map_one]⟩
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have haD : α ∉ (linearConjugationHom (coordinateQuadOdd n K)).range := fun hD =>
    hαo (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.mem_inner_of_mem_D_three hg hD hα3)
  have haE : α ∈ matrixProjectiveImage (coordinateQuadOdd n K) := htop ▸ Subgroup.mem_top α
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent'
    G .POmegaOdd (Or.inl rfl) n ℓ f 3 h Nat.prime_three (by norm_num) K hK e α haE haD hαord
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨-, -, U, -, Q₀, hUκ, hUr, -, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨-, S₀, -, -, hT⟩ := hDisp
  obtain ⟨-, -, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcongr : MulAut.congr Θ α = matrixProjectiveConjugationHom _ g' := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ α) x = Θ (α (Θ.symm x)) := rfl
    rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]
  exact exists_fixed_E9_of_congr Θ hcongr (exists_E9_fixed_fieldAutT_odd hn3 h2K g' hg'l hg'r)

theorem outerFixesE9_coordMinus {G : Type} [Group G] {n ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n ℓ f) (hℓ3 : ℓ ≠ 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) (hn : 1 ≤ n)
    [Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))] :
    OuterFixesE9 (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates
    G .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ f h hn K hK b c hirr e
  obtain ⟨hℓ, hf, hn4⟩ := h.1
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4
    b c hirr
  intro α hα3 hαo
  have hα1 : α ≠ 1 := fun h1 => hαo ⟨1, by rw [h1, map_one]⟩
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have haD : α ∉ (linearConjugationHom (coordinateQuadMinus n K hn b c)).range := fun hD =>
    hαo (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.mem_inner_of_mem_D_three hg hD hα3)
  have haE : α ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c) :=
    htop ▸ Subgroup.mem_top α
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent'
    G .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ f 3 h Nat.prime_three (by norm_num) hn K hK b c hirr e
    α haE haD hαord
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨-, -, U, -, Q₀, hUκ, hUr, -, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', -, S₀, -, -, hT⟩ := hDisp
  obtain ⟨-, -, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcongr : MulAut.congr Θ α = matrixProjectiveConjugationHom _ g' := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ α) x = Θ (α (Θ.symm x)) := rfl
    rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]
  exact exists_fixed_E9_of_congr Θ hcongr
    (exists_E9_fixed_fieldAutT_minus hn hn4 b' c' hirr' g' hg'l hg'r)

theorem outerFixedAt_B3_odd (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid) (hp2 : q.p ≠ 2)
    (hp3 : q.p ≠ 3) : OuterFixedAt ⟨.B 3 q, hv⟩ := by
  refine outerFixedAt_of_model fun G _ _ e => ?_
  have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv hp2 le_rfl e
  obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := id hM
  have : Finite (matrixProjectiveDerived (coordinateQuadOdd 3 F)) :=
    Finite.of_equiv G (coordinateOddWitnessEquiv F f).toEquiv
  exact ⟨_, _, outerFixesE9_coordOdd hM hp3 F hF f, ⟨coordinateOddWitnessEquiv F f⟩⟩

theorem outerFixedAt_twistedD4 (q : PrimePower) (hv : (LieTypeIndex.twistedD 4 q).Valid)
    (hp3 : q.p ≠ 3) : OuterFixedAt ⟨.twistedD 4 q, hv⟩ := by
  refine outerFixedAt_of_model fun G _ _ e => ?_
  have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD 4 q hv e
  obtain ⟨-, F, _, _, hF, b, c, hbc, ⟨f⟩⟩ := id hM
  have h41 : 1 ≤ 4 := by norm_num
  have : Finite (matrixProjectiveDerived (coordinateQuadMinus 4 F h41 b c)) :=
    Finite.of_equiv G (coordinateMinusWitnessEquiv F h41 b c f).toEquiv
  exact ⟨_, _, outerFixesE9_coordMinus hM hp3 F hF b c hbc f h41,
    ⟨coordinateMinusWitnessEquiv F h41 b c f⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
