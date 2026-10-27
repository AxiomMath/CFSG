module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOrthWeir
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResIndepPair
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

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
open CFSG.ClassicalGroups.Orthogonal (regular_quadPlus)
open CFSG.GroupTheory.WeirSylow (isPlusType_quadPlus finrank_quadPlus_space)
open CFSG.LieType.Universal.Spin (coe_quadPlus)

section Fixed

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q Q' : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem fixesPair_of_subfieldSetup (S : SubfieldSetup k Q₀ Q' σ p)
    {β : MulAut (matrixProjectiveDerived Q)}
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q' g' (Θ x))
    (hpair : HasIndepPair p (matrixProjectiveDerived Q₀)) : FixesIndepPair p β := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  have hfa := matrixProjectiveConjugationHom_eq_fieldAutT S g' hl hr
  obtain ⟨y₁, y₂, hc, h1, h2, hi⟩ := hpair
  have hinj := incl_injective k S.hext hd
  have hfix : ∀ y : matrixProjectiveDerived Q₀, β (Θ.symm (incl k S.hext y)) =
      Θ.symm (incl k S.hext y) := by
    intro y
    apply Θ.injective
    rw [hΘ, MulEquiv.apply_symm_apply, hfa,
      fieldAutT_fixes_J k Q' σ S.hQσ S.hext S.hσk ⟨y, rfl⟩]
  refine ⟨Θ.symm (incl k S.hext y₁), Θ.symm (incl k S.hext y₂),
    (hc.map (incl k S.hext)).map Θ.symm, ?_, ?_, fun i j hij => ?_, hfix y₁, hfix y₂⟩
  · rw [← map_pow, ← map_pow, h1, map_one, map_one]
  · rw [← map_pow, ← map_pow, h2, map_one, map_one]
  · rw [← map_zpow, ← map_zpow, ← map_zpow, ← map_zpow, ← map_mul, ← map_mul] at hij
    have h3 := hinj (Θ.symm.injective (hij.trans (by rw [map_one, map_one])))
    exact hi i j h3

end Fixed

section Plus

theorem not_dvd_card_of_card_eq_two_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {F : Type}
    (hF : Nat.card F = 2 ^ f) : ¬ p ∣ Nat.card F := by
  rw [hF]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))

theorem plus_outer_fixesPair {L : Type} [Group L] [Finite L] {n f p : ℕ}
    (hcl : StatedClassicalModel L .POmegaPlus n 2 f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hge : ∃ E : Subgroup L, IsElemAbelian p E ∧ Nat.card E = p ^ 2)
    {α : MulAut L} (hα : α ∉ inner L) (hαp : α ^ p = 1) : FixesIndepPair p α := by
  have hp2 : p ≠ 2 := by omega
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, ⟨e⟩⟩ := hcl
  obtain ⟨hchar, -⟩ := coordinate_model_witness_plus hcl' F hF e
  haveI : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates L .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f hcl' F hF e
  set θ := coordinatePlusWitnessEquiv F e with hθ
  set Q := coordinateQuadPlus n F with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hα ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · have hA : Subgroup.zpowers β ≤ familyOrbitKernel Q :=
        hgates.2.2.2.2.2.2.1 p hp (by omega) _ (IsPGroup.of_card (n := 1)
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
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' L .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f p hcl' hp hp2 F hF e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / p) := by
    rw [hUr]; exact hcard
  have hsetup := subfieldSetup_plus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' (n := n) (by omega)
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q g' (Θ x) := fun x => by
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
  obtain ⟨hQnd, hT⟩ := regular_quadPlus (K := F) (n := n) (by omega)
  obtain ⟨hQnd', hT'⟩ := regular_quadPlus (K := k) (n := n) (by omega)
  obtain ⟨E, hE, hEc⟩ := hge
  have hpair : HasIndepPair p (StatedProj (StatedOmega (StatedQuadPlus n k))) :=
    orth_pair_transfer hp hp2 (by omega : 1 ≤ n) (ε := 1) (coe_quadPlus n F)
      (finrank_quadPlus_space n) hQnd hT (Or.inl ⟨rfl, isPlusType_quadPlus F n⟩)
      (coe_quadPlus n k) (finrank_quadPlus_space n) hQnd' hT'
      (Or.inl ⟨rfl, isPlusType_quadPlus k n⟩) hpF hcong
      (E := E.map e.toMonoidHom) (hE.map e.toMonoidHom) (by
        rw [Subgroup.card_map_of_injective e.injective]
        exact hEc)
  have hpair' : HasIndepPair p (matrixProjectiveDerived (coordinateQuadPlus n k)) :=
    HasIndepPair.of_mulEquiv (coordinatePlusWitnessEquiv k (MulEquiv.refl _)) hpair
  exact FixesIndepPair.of_mulEquiv θ
    (fixesPair_of_subfieldSetup hsetup Θ g' hg'l hg'r hΘ' hpair')

end Plus

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
