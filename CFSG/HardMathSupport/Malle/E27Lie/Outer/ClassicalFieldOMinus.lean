module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldOThree
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Lang.Coordinator
  CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedClassicalModel)
open CFSG.ComponentClassification
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem exists_fixed_perfect_three_POmegaMinus {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .POmegaMinus n ℓ f) (α : MulAut K)
    (hα3 : α ^ 3 = 1) (hαin : α ∉ OuterAutomorphisms.inner K) :
    ∃ D : Subgroup K, (∀ x ∈ D, α x = x) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hcl
  have hn1 : 1 ≤ n := by omega
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : 3 ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hcl' hn1 F hF b c hirr e
  set θ := coordinateMinusWitnessEquiv F hn1 b c e with hθ
  set Q := coordinateQuadMinus n F hn1 b c with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα3, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = 3 := orderOf_eq_prime hβp hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' K .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f 3 hcl' hp hp2 hn1 F hF b c hirr e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = 3 := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) F = 3 := by
    have hK' : Nat.card F = ℓ ^ ((f / 3) * 3) := by rw [Nat.div_mul_cancel hpf]; exact hF
    exact finrank_subfield_eq _ hℓ hfp hcard' hK'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' hn4 hdeg b' c' hirr'
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom _ g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  obtain ⟨π, hπ3, hπ1, hπQ⟩ := exists_perm_minus (semilinearFixedSubfield U.val.right)
    (n := n) hn4 (by omega) b' c'
  have h3 := three_dvd_card_of_perm _ hsetup.hnd₀ hsetup.hT₀ π hπ3 hπ1 hπQ
  obtain ⟨D, hfix, hperf, hdvd⟩ := exists_fixed_perfect_of_subfieldSetup hsetup Θ g' hg'l
    hg'r hΘ' h3
  exact exists_fixed_perfect_of_congr θ α hfix hperf hdvd

end CFSG.HardMathSupport.Malle.E27Lie
