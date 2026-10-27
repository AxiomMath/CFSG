module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.Assembly.LowTwoRank
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Generic

universe u

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q Q' : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

omit [Finite K] in
theorem matrixProjectiveConjugationHom_eq_fieldAutT' (S : SubfieldSetup k Q₀ Q' σ p)
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = σ) :
    matrixProjectiveConjugationHom Q' g' = fieldAutT Q' σ S.hQσ := by
  unfold fieldAutT
  refine matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar Q' (g := g')
    (h := fieldPair Q' σ S.hQσ) 1 ?_ hr
  rw [hl, fieldPair_left]
  simp

theorem not_isSolvable_autFix_of_setup (S : SubfieldSetup k Q₀ Q' σ p)
    {ζ : MulAut (matrixProjectiveDerived Q)}
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (ζ x) = matrixProjectiveConjugationHom Q' g' (Θ x)) :
    ¬ Group.IsSolvable ↥(autFix ζ) := by
  intro hsolv
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hsimple, a, b, hab⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  have hκ := matrixProjectiveConjugationHom_eq_fieldAutT' S g' hl hr
  have hfix : ∀ y : matrixProjectiveDerived Q₀,
      fieldAutT Q' σ S.hQσ (incl k S.hext y) = incl k S.hext y := fun y =>
    (fieldAutT_apply_iff S _).mpr (subfieldDerivedImage_le k S.hext ⟨y, rfl⟩)
  let ψ : matrixProjectiveDerived Q₀ →* ↥(autFix ζ) :=
    { toFun := fun y => ⟨Θ.symm (incl k S.hext y), by
        change ζ (Θ.symm (incl k S.hext y)) = Θ.symm (incl k S.hext y)
        apply Θ.injective
        rw [hΘ, MulEquiv.apply_symm_apply, hκ, hfix]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hψ : Function.Injective ψ := fun x y hxy =>
    incl_injective k S.hext hd (Θ.symm.injective (congrArg Subtype.val hxy))
  have hs : Group.IsSolvable (matrixProjectiveDerived Q₀) :=
    Group.isSolvable_of_isSolvable_injective hψ
  have := hsimple
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b)

end Generic

section Families

theorem orth_outer_false_plus {G : Type} [Group G] {n ℓ f p : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    (ζ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (hζE : ζ ∈ matrixProjectiveImage (coordinateQuadPlus n K))
    (hζD : ζ ∉ (linearConjugationHom (coordinateQuadPlus n K)).range) (hζp : ζ ^ p = 1) :
    ¬ Group.IsSolvable ↥(autFix ζ) := by
  have hn4 : 4 ≤ n := h.1.2.2
  have hζ1 : ζ ≠ 1 := fun h1 => hζD (h1 ▸ one_mem _)
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ζ = p := orderOf_eq_prime hζp hζ1
  have hdesc := CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p h hp hp2 K hK e ζ hζE hζD hord
  obtain ⟨g, hg⟩ := hζE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord'' : orderOf U.val.right = p := by rw [hUr]; exact hord'
  have hsetup := subfieldSetup_plus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord'' (n := n) (by omega)
  have hΘ' : ∀ x, Θ (ζ x) = matrixProjectiveConjugationHom _ g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  exact not_isSolvable_autFix_of_setup hsetup Θ g' hg'l hg'r hΘ'

theorem orth_outer_false_minus {G : Type} [Group G] {n ℓ f p : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n ℓ f) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    (ζ : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)))
    (hζE : ζ ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c))
    (hζD : ζ ∉ (linearConjugationHom (coordinateQuadMinus n K hn b c)).range)
    (hζp : ζ ^ p = 1) : ¬ Group.IsSolvable ↥(autFix ζ) := by
  have hℓ : ℓ.Prime := h.1.1
  have hf : 1 ≤ f := h.1.2.1
  have hn4 : 4 ≤ n := h.1.2.2
  have hζ1 : ζ ≠ 1 := fun h1 => hζD (h1 ▸ one_mem _)
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ζ = p := orderOf_eq_prime hζp hζ1
  have hdesc := CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p h hp hp2 hn K hK b c hirr e ζ hζE hζD hord
  obtain ⟨g, hg⟩ := hζE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord'' : orderOf U.val.right = p := by rw [hUr]; exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) K = p := by
    have hK' : Nat.card K = ℓ ^ ((f / p) * p) := by rw [Nat.div_mul_cancel hpf]; exact hK
    exact finrank_subfield_eq _ hℓ hfp hcard' hK'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord'' hn4 hdeg b' c' hirr'
  have hΘ' : ∀ x, Θ (ζ x) = matrixProjectiveConjugationHom _ g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  exact not_isSolvable_autFix_of_setup hsetup Θ g' hg'l hg'r hΘ'

end Families

end CFSG.HardMathSupport.Curtis.Coordinator
