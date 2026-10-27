module

public import CFSG.LocalAnalysis.Gross82.OrderThree
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7f2

public section

namespace CFSG.LocalAnalysis.Gross82

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor lieSylowExponent)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.HardMathSupport.Lang.Coordinator
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
  CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem exists_card_fixedSubgroup_dvd_POmegaPlus_of_mem_matrixProjectiveImage {K : Type}
    [Group K] [Finite K] {n ℓ f p : ℕ} (hcl : StatedClassicalModel K .POmegaPlus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (F : Type) [Field F] [Finite F] (hF : Nat.card F = ℓ ^ f)
    (e : K ≃* CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F)))
    (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K)
    (hE : MulAut.congr (coordinatePlusWitnessEquiv F e) α ∈
      matrixProjectiveImage (coordinateQuadPlus n F)) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .POmegaPlus n (ℓ ^ f₀) := by
  obtain ⟨hℓ, -, hn4⟩ : ℓ.Prime ∧ 1 ≤ f ∧ 4 ≤ n := by
    simpa only [StatedLieAdmissible] using hcl.1
  have hchar := (coordinate_model_witness_plus hcl F hF e).1
  have : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hcl F hF e
  let θ : K ≃* matrixProjectiveDerived (coordinateQuadPlus n F) := coordinatePlusWitnessEquiv F e
  let Q : QuadraticForm F (Fin (2 * n) → F) := coordinateQuadPlus n F
  let β : MulAut (matrixProjectiveDerived Q) := MulAut.congr θ α
  have hβp : β ^ p = 1 := by
    change (MulAut.congr θ α) ^ p = 1
    rw [← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 :=
    fun h1 => hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  rw [← card_fixedSubgroup_congr θ α]
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent'
    K .POmegaPlus (Or.inr (Or.inl rfl)) n ℓ f p hcl hp hp2 F hF e β hE hD hβord
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
  have hfix := card_fixedSubgroup_eq_subfieldFixedGroup hsetup Θ g' hg'l hg'r hΘ'
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hfix, ← hcard']
  by_cases h2F : (2 : F) = 0
  · have h2char : CharP F 2 := by
      have hcp : CharP F ℓ := hchar ▸ ringChar.charP F
      have h1 : ℓ ∣ 2 := (CharP.cast_eq_zero_iff F ℓ 2).mp (by exact_mod_cast h2F)
      exact ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1) ▸ hcp
    exact (card_subfieldFixedGroup_dvd_model _ n hsetup.hext hsetup.hnd₀ hsetup.hT₀
      hsetup.hnd).trans (dvd_of_eq (@card_model_plus_eq F _ _ h2char _ n hn4))
  · have h2k : (2 : semilinearFixedSubfield U.val.right) ≠ 0 := two_ne_zero_of_subfield _ h2F
    exact card_subfieldFixedGroup_plus_dvd _ n (by omega) h2k _

section POmegaPlusEightSylow


theorem exists_card_fixedSubgroup_dvd_POmegaPlus_four_of_fix_sylow {K : Type} [Group K]
    [Finite K] {ℓ f : ℕ} (hmodel : LieModel K .POmegaPlus 4 ℓ f) (α : MulAut K)
    (hα3 : α ^ 3 = 1) (hαin : α ∉ inner K) (P : Sylow 3 K)
    (hP : ∀ x ∈ (P : Subgroup K), α x = x) :
    ∃ f₀ : ℕ, f = 3 * f₀ ∧
      Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .POmegaPlus 4 (ℓ ^ f₀) := by
  classical
  have hcl : StatedClassicalModel K .POmegaPlus 4 ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, ⟨e⟩⟩ := hcl'
  let θ : K ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F) := coordinatePlusWitnessEquiv F e
  let β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) := MulAut.congr θ α
  have hβ3 : β ^ 3 = 1 := by
    change (MulAut.congr θ α) ^ 3 = 1
    rw [← map_pow, hα3, map_one]
  let S : Sylow 3 (matrixProjectiveDerived (coordinateQuadPlus 4 F)) :=
    P.comapOfInjective θ.symm.toMonoidHom θ.symm.injective (by
      rw [MonoidHom.range_eq_top.2 θ.symm.surjective]; exact le_top)
  have hfixS : ∀ x ∈ (S : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 F))),
      β x = x := by
    intro x hx
    have hx' : θ.symm x ∈ (P : Subgroup K) := hx
    change θ (α (θ.symm x)) = x
    rw [hP (θ.symm x) hx', θ.apply_symm_apply]
  have hfam := CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f.d4NoTrialitySylowThree_holds
    F S β ⟨1, by simpa using hβ3⟩ hfixS
  have hEA := coordinate_plus_family_eq_matrixImage hcl F hF e
  have hE : β ∈ matrixProjectiveImage (coordinateQuadPlus 4 F) := by
    rw [← hEA, mem_projectivePointFamilyAut_iff]
    exact hfam
  exact exists_card_fixedSubgroup_dvd_POmegaPlus_of_mem_matrixProjectiveImage hcl
    Nat.prime_three (by norm_num) F hF e α hα3 hαin hE

end POmegaPlusEightSylow

theorem three_dvd_lieOrderNumerator_POmegaPlus {n : ℕ} (hn : 2 ≤ n) (x : ℕ) :
    3 ∣ lieOrderNumerator .POmegaPlus n x := by
  have hmem : 1 ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hnum : lieOrderNumerator .POmegaPlus n x = x ^ (n * (n - 1)) * (x ^ n - 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (x ^ (2 * i) - 1) := by
    simp only [lieOrderNumerator]
  rw [hnum]
  by_cases h3 : 3 ∣ x
  · have h : 3 ∣ x ^ (n * (n - 1)) := dvd_pow h3 (Nat.mul_ne_zero (by omega) (by omega))
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  · have hs : x ^ 2 % 3 = 1 := CFSG.AGLEmbedding.OuterSylow.sq_mod_three x h3
    have hd : 3 ∣ x ^ 2 - 1 := by omega
    exact dvd_mul_of_dvd_right
      (hd.trans (Finset.dvd_prod_of_mem (fun i => x ^ (2 * i) - 1) hmem)) _

section POmegaPlusEightThreeAdic


theorem not_sylow_le_of_POmegaPlus_four_bound {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus 4 ℓ f) (hmodel : LieModel K .POmegaPlus 4 ℓ f)
    {C : Subgroup K}
    (hC : ∃ f₀ : ℕ, f = 3 * f₀ ∧ Nat.card C ∣ lieOrderNumerator .POmegaPlus 4 (ℓ ^ f₀))
    (P : Sylow 3 K) : ¬ (P : Subgroup K) ≤ C := by
  intro hPC
  obtain ⟨-, hcard, -⟩ :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K .POmegaPlus 4 ℓ f hadm hmodel
  have hN : 1 ≤ lieSylowExponent .POmegaPlus 4 :=
    CFSG.AGLEmbedding.OuterSylow.one_le_lieSylowExponent hadm
  have hdiv3 : ¬ 3 ∣ lieOrderDivisor .POmegaPlus 4 (ℓ ^ f) := by
    have h1 : lieOrderDivisor .POmegaPlus 4 (ℓ ^ f) = Nat.gcd 4 ((ℓ ^ f) ^ 4 - 1) := rfl
    rw [h1]
    exact fun h => absurd (h.trans (Nat.gcd_dvd_left 4 _)) (by norm_num)
  have hdiv0 : lieOrderDivisor .POmegaPlus 4 (ℓ ^ f) ≠ 0 := by
    have h1 : lieOrderDivisor .POmegaPlus 4 (ℓ ^ f) = Nat.gcd 4 ((ℓ ^ f) ^ 4 - 1) := rfl
    rw [h1]
    exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hf1 : 1 ≤ f := hadm.2.1
  have hnumK : (lieOrderNumerator .POmegaPlus 4 (ℓ ^ f)).factorization 3 =
      (Nat.card K).factorization 3 := by
    rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' hdiv0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hdiv3, add_zero]
  have hdvdC : 3 ^ (Nat.card K).factorization 3 ∣ Nat.card C := by
    rw [← P.card_eq_multiplicity]
    exact Subgroup.card_dvd_of_le hPC
  obtain ⟨f₀, hf, hfix⟩ := hC
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  let q := ℓ ^ f₀
  have hq₀ : 2 ≤ q := hadm.1.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hqp : q ^ 3 = ℓ ^ f := by
    change (ℓ ^ f₀) ^ 3 = ℓ ^ f
    rw [← pow_mul, hf, Nat.mul_comm f₀ 3]
  have hne : lieOrderNumerator .POmegaPlus 4 q ≠ 0 :=
    CFSG.AGLEmbedding.OuterSylow.lieOrderNumerator_ne_zero (by decide) hN hq₀
  have h1 : (Nat.card K).factorization 3 ≤
      (lieOrderNumerator .POmegaPlus 4 q).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hne).1 (hdvdC.trans hfix)
  have h2 : (lieOrderNumerator .POmegaPlus 4 q).factorization 3 <
      (lieOrderNumerator .POmegaPlus 4 (q ^ 3)).factorization 3 :=
    CFSG.AGLEmbedding.OuterSylow.numerator_factorization_lt (p := 3) (by norm_num) (by norm_num)
      (by decide) (by decide) hN hq₀ (three_dvd_lieOrderNumerator_POmegaPlus (by norm_num) (q ^ 3))
  rw [hqp, hnumK] at h2
  omega

end POmegaPlusEightThreeAdic

section POmegaPlusEightGross


theorem grossThreeInnerOrderThree_POmegaPlus_four {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus 4 ℓ f) (hmodel : LieModel K .POmegaPlus 4 ℓ f) :
    GrossThreeInnerOrderThree K := by
  intro α hα3 P hP
  by_contra hα
  have hbound :=
    exists_card_fixedSubgroup_dvd_POmegaPlus_four_of_fix_sylow hmodel α hα3 hα P hP
  exact not_sylow_le_of_POmegaPlus_four_bound hadm hmodel hbound P (fun x hx => hP x hx)

end POmegaPlusEightGross

end CFSG.LocalAnalysis.Gross82
