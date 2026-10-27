module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTransfer
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.Assembly.GL83LieDefs
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedOmega StatedQuadOdd StatedQuadPlus StatedQuadMinus)
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Generic

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q Q' : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem pRank_derived_le_fixed (hp1 : 1 < p) (S : SubfieldSetup k Q₀ Q' σ p) (hd : 0 < d)
    {β : MulAut (matrixProjectiveDerived Q)}
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q' g' (Θ x)) :
    CFSG.Open.pRank p (⊤ : Subgroup (matrixProjectiveDerived Q₀)) ≤
      CFSG.Open.pRank p (fixedSubgroup β) := by
  have h1 : CFSG.Open.pRank p (fixedSubgroup (matrixProjectiveConjugationHom Q' g')) ≤
      CFSG.Open.pRank p (fixedSubgroup β) :=
    pRank_fixed_le_of_intertwine hp1 Θ β (matrixProjectiveConjugationHom Q' g')
      fun x => (hΘ x).symm
  have h2 : fixedSubgroup (matrixProjectiveConjugationHom Q' g') =
      subfieldFixedGroup k Q₀ Q' := by
    rw [matrixProjectiveConjugationHom_eq_fieldAutT S g' hl hr]
    ext t
    exact fieldAutT_apply_iff S t
  rw [h2] at h1
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (matrixProjectiveDerived Q₀)) ≤
      CFSG.Open.pRank p (subfieldFixedGroup k Q₀ Q') := by
    refine (CFSG.SectionRank.pRank_le_map hp1 (incl k S.hext) (incl_injective k S.hext hd)
      ⊤).trans (CFSG.SectionRank.pRank_mono hp1 ?_)
    rintro _ ⟨x, -, rfl⟩
    exact subfieldDerivedImage_le k S.hext ⟨x, rfl⟩
  omega

end Generic

private theorem two_eq_zero_imp_char_two' {F : Type} [Field F] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hchar : ringChar F = ℓ) (h : (2 : F) = 0) : ℓ = 2 := by
  have hcp : CharP F ℓ := hchar ▸ ringChar.charP F
  have h1 : ℓ ∣ 2 := (CharP.cast_eq_zero_iff F ℓ 2).mp (by exact_mod_cast h)
  exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1

theorem pomegaOdd_pRank_fixed {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .POmegaOdd n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    p ∣ f ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = ℓ ^ (f / p) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n F₀)))) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn3, hℓ2⟩, F, _, _, hF, ⟨e⟩⟩ := hcl
  obtain ⟨hchar, -⟩ := coordinate_model_witness_odd hcl' F hF e
  have h2F : (2 : F) ≠ 0 := by
    intro h
    exact hℓ2 (two_eq_zero_imp_char_two' hℓ hchar h)
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaOdd
    (Or.inl rfl) n ℓ f hcl' F hF e
  set θ := coordinateOddWitnessEquiv F e with hθ
  set Q := coordinateQuadOdd n F with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_odd F n hn3 (by omega)]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      K .POmegaOdd (Or.inl rfl) n ℓ f p hcl' hp hp2 F hF e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]; exact hcard
  have hsetup := subfieldSetup_odd (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' hn3 h2F
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  refine ⟨hpf, semilinearFixedSubfield U.val.right, inferInstance, Subtype.finite, hcard', ?_⟩
  have h1 := pRank_derived_le_fixed hp1 hsetup (by omega) Θ g' hg'l (hg'r.trans rfl) hΘ'
  have h2 : CFSG.Open.pRank p (fixedSubgroup β) ≤ CFSG.Open.pRank p (fixedSubgroup α) :=
    pRank_fixed_le_of_intertwine hp1 θ α β fun x => by
      rw [hβdef]
      simp [MulAut.congr_apply]
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n
      (semilinearFixedSubfield U.val.right))))) =
      CFSG.Open.pRank p (⊤ : Subgroup (matrixProjectiveDerived
        (coordinateQuadOdd n (semilinearFixedSubfield U.val.right)))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1
      (coordinateOddWitnessEquiv (semilinearFixedSubfield U.val.right) (MulEquiv.refl _))
  omega

theorem pomegaPlus_pRank_fixed {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD4 : ¬(n = 4 ∧ p = 3)) (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    p ∣ f ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = ℓ ^ (f / p) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F₀)))) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, ⟨e⟩⟩ := hcl
  obtain ⟨hchar, -⟩ := coordinate_model_witness_plus hcl' F hF e
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hcl' F hF e
  set θ := coordinatePlusWitnessEquiv F e with hθ
  set Q := coordinateQuadPlus n F with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · have hp3 : 3 < p := by
        have h3 : p ≠ 3 := fun h3 => hD4 ⟨h4, h3⟩
        have := hp.two_le
        omega
      have hA : Subgroup.zpowers β ≤ familyOrbitKernel Q :=
        hgates.2.2.2.2.2.2.1 p hp hp3 _ (IsPGroup.of_card (n := 1)
          (by rw [Nat.card_zpowers, hβord, pow_one]))
      have h1 := hgates.2.2.2.2.1 (hA (Subgroup.mem_zpowers β))
      rw [hgates.2.2.2.2.2.1] at h1
      exact h1
    · rw [matrixProjectiveImage_eq_top_plus F n h5]
      exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      K .POmegaPlus (Or.inr (Or.inl rfl)) n ℓ f p hcl' hp hp2 F hF e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]; exact hcard
  have hsetup := subfieldSetup_plus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' (n := n) (by omega)
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  refine ⟨hpf, semilinearFixedSubfield U.val.right, inferInstance, Subtype.finite, hcard', ?_⟩
  have h1 := pRank_derived_le_fixed hp1 hsetup (by omega) Θ g' hg'l hg'r hΘ'
  have h2 : CFSG.Open.pRank p (fixedSubgroup β) ≤ CFSG.Open.pRank p (fixedSubgroup α) :=
    pRank_fixed_le_of_intertwine hp1 θ α β fun x => by
      rw [hβdef]
      simp [MulAut.congr_apply]
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n
      (semilinearFixedSubfield U.val.right))))) =
      CFSG.Open.pRank p (⊤ : Subgroup (matrixProjectiveDerived
        (coordinateQuadPlus n (semilinearFixedSubfield U.val.right)))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1
      (coordinatePlusWitnessEquiv (semilinearFixedSubfield U.val.right) (MulEquiv.refl _))
  omega

theorem pomegaMinus_pRank_fixed {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    p ∣ f ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = ℓ ^ (f / p) ∧
      ∃ (b c : F₀), (∀ s : F₀, s ^ 2 + b * s + c ≠ 0) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F₀ b c)))) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hcl
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hchar, -⟩ := coordinate_model_witness_minus hcl' F hF b c hirr e
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hcl' hn1 F hF b c hirr e
  set θ := coordinateMinusWitnessEquiv F hn1 b c e with hθ
  set Q := coordinateQuadMinus n F hn1 b c with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      K .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ f p hcl' hp hp2 hn1 F hF b c hirr e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) F = p := by
    have hK' : Nat.card F = ℓ ^ ((f / p) * p) := by rw [Nat.div_mul_cancel hpf]; exact hF
    exact finrank_subfield_eq _ hℓ hfp hcard' hK'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' hn4 hdeg b' c' hirr'
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom _ g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  refine ⟨hpf, semilinearFixedSubfield U.val.right, inferInstance, Subtype.finite, hcard', b', c',
    hirr', ?_⟩
  have h1 := pRank_derived_le_fixed hp1 hsetup (by omega) Θ g' hg'l hg'r hΘ'
  have h2 : CFSG.Open.pRank p (fixedSubgroup β) ≤ CFSG.Open.pRank p (fixedSubgroup α) :=
    pRank_fixed_le_of_intertwine hp1 θ α β fun x => by
      rw [hβdef]
      simp [MulAut.congr_apply]
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n
      (semilinearFixedSubfield U.val.right) b' c')))) =
      CFSG.Open.pRank p (⊤ : Subgroup (matrixProjectiveDerived
        (coordinateQuadMinus n (semilinearFixedSubfield U.val.right) hn1 b' c'))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1
      (coordinateMinusWitnessEquiv (semilinearFixedSubfield U.val.right) hn1 b' c'
        (MulEquiv.refl _))
  omega

theorem two_le_pRank_statedProj_POmegaOdd {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 3 ≤ n)
    (hf₀ : 1 ≤ f₀) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = p ^ f₀) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n F₀)))) := by
  have hm : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n F₀))) .POmegaOdd n p
      f₀ := ⟨⟨hp, hf₀, hn, by omega⟩, F₀, inferInstance, inferInstance, hF₀, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by omega) hm
  rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h1
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · omega

theorem two_le_pRank_statedProj_POmegaPlus {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 4 ≤ n)
    (hf₀ : 1 ≤ f₀) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = p ^ f₀) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F₀)))) := by
  have hm : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n F₀))) .POmegaPlus n p
      f₀ := ⟨⟨hp, hf₀, hn⟩, F₀, inferInstance, inferInstance, hF₀, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by omega) hm
  rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h1
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · omega

theorem two_le_pRank_statedProj_POmegaMinus {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 4 ≤ n) (hf₀ : 1 ≤ f₀) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = p ^ f₀) (b c : F₀) (hirr : ∀ s : F₀, s ^ 2 + b * s + c ≠ 0) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F₀ b c)))) := by
  have hm : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n F₀ b c))) .POmegaMinus
      n p f₀ := ⟨⟨hp, hf₀, hn⟩, F₀, inferInstance, inferInstance, hF₀, b, c, hirr,
        ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by omega) hm
  rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h1
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · omega

theorem outerFixedRankDefAt_POmegaOdd : OuterFixedRankDefAt .POmegaOdd := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  have hcl : StatedClassicalModel K .POmegaOdd n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨-, hf, hn3, -⟩ := hadm
  obtain ⟨hpf, F₀, _, _, hcard, hrank⟩ := pomegaOdd_pRank_fixed hcl hp (by omega) α hαp hαin
  have hf0 : 1 ≤ f / ℓ := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have := two_le_pRank_statedProj_POmegaOdd hp hp5 hn3 hf0 hcard
  exact Or.inl (by omega)

theorem outerFixedRankDefAt_POmegaPlus : OuterFixedRankDefAt .POmegaPlus := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  have hcl : StatedClassicalModel K .POmegaPlus n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨-, hf, hn4⟩ := hadm
  obtain ⟨hpf, F₀, _, _, hcard, hrank⟩ := pomegaPlus_pRank_fixed hcl hp (by omega)
    (fun h => by omega) α hαp hαin
  have hf0 : 1 ≤ f / ℓ := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have := two_le_pRank_statedProj_POmegaPlus hp hp5 hn4 hf0 hcard
  exact Or.inl (by omega)

theorem outerFixedRankDefAt_POmegaMinus : OuterFixedRankDefAt .POmegaMinus := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  have hcl : StatedClassicalModel K .POmegaMinus n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨-, hf, hn4⟩ := hadm
  obtain ⟨hpf, F₀, _, _, hcard, b, c, hirr, hrank⟩ := pomegaMinus_pRank_fixed hcl hp (by omega) α
    hαp hαin
  have hf0 : 1 ≤ f / ℓ := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have := two_le_pRank_statedProj_POmegaMinus hp hp5 hn4 hf0 hcard b c hirr
  exact Or.inl (by omega)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
