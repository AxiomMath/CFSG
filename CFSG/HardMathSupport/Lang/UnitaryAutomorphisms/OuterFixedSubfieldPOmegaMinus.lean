module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedOmega StatedQuadMinus)
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Lang.Coordinator
open CFSG.ComponentClassification
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem exists_fixedSubfieldEmbedding_of_fieldAutT {K F : Type} [Group K] [Field F]
    [Finite F] {n : ℕ} (hn1 : 1 ≤ n) {Q : QuadraticForm F (Fin (2 * n) → F)} {k : Subfield F}
    {b' c' : k} {σ : F ≃+* F} {p : ℕ}
    (hsetup : SubfieldSetup k (coordinateQuadMinus n k hn1 b' c')
      (coordinateQuadMinus n F hn1 (b' : F) (c' : F)) σ p)
    (g' : similarityPairs (coordinateQuadMinus n F hn1 (b' : F) (c' : F)))
    (hg'l : g'.val.left = 1) (hg'r : g'.val.right = σ)
    (θ : K ≃* matrixProjectiveDerived Q) (α : MulAut K)
    {β : MulAut (matrixProjectiveDerived Q)} (hβ : β = MulAut.congr θ α)
    {Θ : matrixProjectiveDerived Q ≃*
      matrixProjectiveDerived (coordinateQuadMinus n F hn1 (b' : F) (c' : F))}
    (hΘ : ∀ x, Θ (β x) = matrixProjectiveConjugationHom
      (coordinateQuadMinus n F hn1 (b' : F) (c' : F)) g' (Θ x)) :
    ∃ ι : StatedProj (StatedOmega (StatedQuadMinus n k b' c')) →* K,
      Function.Injective ι ∧ ∀ y, α (ι y) = ι y := by
  have hfield : matrixProjectiveConjugationHom (coordinateQuadMinus n F hn1 (b' : F) (c' : F))
      g' = fieldAutT (coordinateQuadMinus n F hn1 (b' : F) (c' : F)) σ hsetup.hQσ :=
    matrixProjectiveConjugationHom_eq_fieldAutT hsetup g' hg'l hg'r
  have hΘfix : ∀ x, Θ (β x) = fieldAutT (coordinateQuadMinus n F hn1 (b' : F) (c' : F))
      σ hsetup.hQσ (Θ x) := fun x => by rw [hΘ x, hfield]
  have hfix : ∀ t ∈ subfieldDerivedImage k hsetup.hext,
      fieldAutT (coordinateQuadMinus n F hn1 (b' : F) (c' : F)) σ hsetup.hQσ t = t :=
    fun t ht => fieldAutT_fixes_J k _ σ hsetup.hQσ hsetup.hext hsetup.hσk ht
  have hβfix : ∀ v ∈ subfieldDerivedImage k hsetup.hext, β (Θ.symm v) = Θ.symm v := by
    intro v hv
    apply Θ.injective
    rw [hΘfix, MulEquiv.apply_symm_apply]
    exact hfix v hv
  have hαβ : ∀ z, α (θ.symm z) = θ.symm (β z) := fun z => by
    rw [hβ, MulAut.congr_apply]
    simp
  let w := coordinateMinusWitnessEquiv k hn1 b' c'
    (MulEquiv.refl (StatedProj (StatedOmega (StatedQuadMinus n k b' c'))))
  let ι : StatedProj (StatedOmega (StatedQuadMinus n k b' c')) →* K :=
    θ.symm.toMonoidHom.comp (Θ.symm.toMonoidHom.comp ((incl k hsetup.hext).comp w.toMonoidHom))
  refine ⟨ι, ?_, ?_⟩
  · exact θ.symm.injective.comp (Θ.symm.injective.comp
      ((incl_injective k hsetup.hext (by omega)).comp w.injective))
  · intro y
    show α (θ.symm (Θ.symm (incl k hsetup.hext (w y)))) =
      θ.symm (Θ.symm (incl k hsetup.hext (w y)))
    rw [hαβ]
    rw [hβfix _ ⟨w y, rfl⟩]

theorem omegaMinus_prime_outer_fixed_subfield_embedding {K : Type} [Group K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    p ∣ f ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ℓ) (b c : k),
      Nat.card k = ℓ ^ (f / p) ∧ (∀ s : k, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ ι : StatedProj (StatedOmega (StatedQuadMinus n k b c)) →* K, Function.Injective ι ∧
        ∀ y, α (ι y) = ι y := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hcl
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hchar, -⟩ := coordinate_model_witness_minus hcl' F hF b c hirr e
  have : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hcl' hn1 F hF b c hirr e
  set θ := coordinateMinusWitnessEquiv F hn1 b c e with hθ
  set Q := coordinateQuadMinus n F hn1 b c with hQ
  set β := MulAut.congr θ α with hβ
  have hβp : β ^ p = 1 := by rw [hβ, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨-, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc := Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' K .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p hcl' hp hp2 hn1 F hF b c hirr e β hE hD hβord
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
  have hcharK : CharP ↥(semilinearFixedSubfield U.val.right) ℓ := by
    rw [← hchar]
    exact Subfield.charP (L := semilinearFixedSubfield U.val.right) (p := ringChar F)
  refine ⟨hpf, ↥(semilinearFixedSubfield U.val.right), inferInstance, inferInstance,
    hcharK, b', c', hcard', hirr', ?_⟩
  exact exists_fixedSubfieldEmbedding_of_fieldAutT hn1 hsetup g' hg'l hg'r θ α hβ hΘ'

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
