module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOrthPlus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Open (IsElemAbelian)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalGroups.Orthogonal (regular_quadMinus)
open CFSG.GroupTheory.WeirSylow (finrank_quadMinus_space)
open CFSG.LieType.Universal.Spin (coe_quadMinus)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega (isMinusType_quadMinus)

section Minus

theorem minus_outer_fixesPair {L : Type} [Group L] [Finite L] {n f p : ℕ}
    (hcl : StatedClassicalModel L .POmegaMinus n 2 f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hge : ∃ E : Subgroup L, IsElemAbelian p E ∧ Nat.card E = p ^ 2)
    {α : MulAut L} (hα : α ∉ inner L) (hαp : α ^ p = 1) : FixesIndepPair p α := by
  have hp2 : p ≠ 2 := by omega
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hcl
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hchar, -⟩ := coordinate_model_witness_minus hcl' F hF b c hirr e
  haveI : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates L .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f hcl' hn1 F hF b c hirr e
  set θ := coordinateMinusWitnessEquiv F hn1 b c e with hθ
  set Q := coordinateQuadMinus n F hn1 b c with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hα ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' L .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f p hcl' hp hp2 hn1 F hF b c hirr e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) F = p := by
    have hK' : Nat.card F = 2 ^ ((f / p) * p) := by rw [Nat.div_mul_cancel hpf]; exact hF
    exact finrank_subfield_eq _ hℓ hfp hcard' hK'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' hn4 hdeg b' c' hirr'
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom _ g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  set k := semilinearFixedSubfield U.val.right with hk
  have hFk : Nat.card F = Nat.card k ^ p := by
    rw [hF, hcard', ← pow_mul, Nat.div_mul_cancel hpf]
  have hpF : ¬ p ∣ Nat.card F := not_dvd_card_of_card_eq_two_pow hp hp2 hF
  have hcong : (Nat.card F : ZMod p) = (Nat.card k : ZMod p) := by
    rw [hFk]
    push_cast
    exact ZMod.pow_card _
  haveI : CharP F 2 := ringChar.of_eq hchar
  haveI : CharP k 2 := RingHom.charP k.subtype k.subtype_injective 2
  obtain ⟨hQnd, hT⟩ := regular_quadMinus (K := F) (n := n) hn4 hirr
  obtain ⟨hQnd', hT'⟩ := regular_quadMinus (K := k) (n := n) hn4 hirr'
  obtain ⟨E, hE', hEc⟩ := hge
  have hpair : HasIndepPair p (StatedProj (StatedOmega (StatedQuadMinus n k b' c'))) :=
    orth_pair_transfer hp hp2 hn1 (ε := -1) (coe_quadMinus n F b c)
      (finrank_quadMinus_space hn1) hQnd hT (Or.inr ⟨rfl, isMinusType_quadMinus hn1 hirr⟩)
      (coe_quadMinus n k b' c') (finrank_quadMinus_space hn1) hQnd' hT'
      (Or.inr ⟨rfl, isMinusType_quadMinus hn1 hirr'⟩) hpF hcong
      (E := E.map e.toMonoidHom) (hE'.map e.toMonoidHom) (by
        rw [Subgroup.card_map_of_injective e.injective]
        exact hEc)
  have hpair' : HasIndepPair p (matrixProjectiveDerived (coordinateQuadMinus n k hn1 b' c')) :=
    HasIndepPair.of_mulEquiv (coordinateMinusWitnessEquiv k hn1 b' c' (MulEquiv.refl _)) hpair
  exact FixesIndepPair.of_mulEquiv θ
    (fixesPair_of_subfieldSetup hsetup Θ g' hg'l hg'r hΘ' hpair')

end Minus

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
