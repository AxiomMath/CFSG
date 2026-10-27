module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinGL

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  isComponentOf_map_of_injective)

@[expose] def NotBC3 (p : ℕ) (L : Type) [Group L] : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ), ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) ∧
    StatedLieAdmissible t n p f ∧ Blueprint.LieModel (L ⧸ center L) t n p f

theorem NotBC3.of_centerQuotient_equiv {p : ℕ} {L M : Type} [Group L] [Group M]
    (e : L ⧸ center L ≃* M ⧸ center M) (h : NotBC3 p M) : NotBC3 p L := by
  obtain ⟨t, n, f, ht, hadm, hM⟩ := h
  exact ⟨t, n, f, ht, hadm, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hM⟩

theorem NotBC3.of_mulEquiv {p : ℕ} {L M : Type} [Group L] [Group M] (e : L ≃* M)
    (h : NotBC3 p M) : NotBC3 p L :=
  h.of_centerQuotient_equiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))

theorem NotBC3.noSpin7 (hO : LieOrderFormulasInput) {p : ℕ} (hp2 : p ≠ 2) {L : Type}
    [Group L] (h : NotBC3 p L) : NoSpin7 p L := by
  obtain ⟨t, n, f, ht, hadm, hL⟩ := h
  exact noSpin7_of_lieModel hO hp2 hadm hL ht

theorem notBC3_of_component_equiv {X Y : Type} [Group X] [Group Y] (Φ : X ≃* Y) {p : ℕ}
    (h : ∀ M : Subgroup Y, IsComponent M → NotBC3 p M) {L : Subgroup X}
    (hL : IsComponent L) : NotBC3 p L :=
  NotBC3.of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (h _ (LocalCores.isComponent_map_mulEquiv Φ hL))

theorem notBC3_prod {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] {p : ℕ}
    (h₁ : ∀ M : Subgroup G₁, IsComponent M → NotBC3 p M)
    (h₂ : ∀ M : Subgroup G₂, IsComponent M → NotBC3 p M)
    {L : Subgroup (G₁ × G₂)} (hL : IsComponent L) : NotBC3 p L := by
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hL with h2 | h1
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component (MulEquiv.refl _) hL h2
    exact NotBC3.of_mulEquiv (MonoidHom.ofInjective hρi) (h₁ _ hρc)
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component MulEquiv.prodComm hL h1
    exact NotBC3.of_mulEquiv (MonoidHom.ofInjective hρi) (h₂ _ hρc)

theorem notBC3_GL {k : Type} [Field k] [Finite k] {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hj : 1 ≤ j) (hk : Nat.card k = p ^ j) {n : ℕ} (hn : 1 ≤ n) {L : Subgroup (GL (Fin n) k)}
    (hL : IsComponent L) : NotBC3 p L := by
  by_cases hsmall : n = 1 ∨ n = 2 ∧ (Nat.card k = 2 ∨ Nat.card k = 3)
  · have := CatalogueBGeneralLinear.generalLinear_small_solvable n k hsmall
    exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
  obtain ⟨hn2, -, h23⟩ := CatalogueBGeneralLinear.retained_parameters n k hn hsmall
  obtain ⟨hadm, hm⟩ := X10Lin.centralModel_GL_component_two_le hp hp2 hj hk hn2 h23 hL
  exact ⟨.PSL, n, j, by simp, hadm, hm⟩

theorem notBC3_glCentralizer {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 2 ≤ n)
    (A : GL (Fin n) K) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1) (lambda : Kˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) lambda)
    {L : Subgroup (Subgroup.centralizer ({A} : Set (GL (Fin n) K)))} (hL : IsComponent L) :
    NotBC3 p L := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, -, hr, hs, -, e, -⟩ :=
      CatalogueBProjectiveInvolution.square_projective_centralizer_structure n hn A lambda h2
        hne hsq hsquare
    exact notBC3_of_component_equiv e
      (fun M hM => notBC3_prod (fun M₁ hM₁ => notBC3_GL hp hp2 hf hK hr hM₁)
        (fun M₂ hM₂ => notBC3_GL hp hp2 hf hK hs hM₂) hM) hL
  · let : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    let : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite lambda.val
    have hm := (CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A lambda hsq
      hsquare).2
    exact notBC3_of_component_equiv
      (CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq)
      (fun M hM => notBC3_GL hp hp2 (j := 2 * f) (by omega)
        (by rw [CatLeafProof.OddInner.card_extension, hK, ← pow_mul, mul_comm]) hm hM) hL

theorem notBC3_inner_psl {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .PSL n p f)
    (A : GL (Fin n) K) (hA : orderOf (innerDiagonalAction n K A) = 2)
    {L : Subgroup (fixedSubgroup (innerDiagonalAction n K A))} (hL : IsComponent L) :
    NotBC3 p L := by
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · right
      have hn2 : n = 2 := by omega
      have h3' : p ^ f ≠ 3 := fun h => hadm.2.2.2.2 (by rw [hn2, h])
      rw [hK]
      exact CatLeafProof.OddInner.five_le_pow hp hp2 hf h3'
    · exact Or.inl h3
  have hne : innerDiagonalAction n K A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hsq2 : innerDiagonalAction n K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  obtain ⟨hmk, -, c, hc⟩ :=
    CatalogueBHigherLinearInner.inner_involution_projective_data n K hn hparameter A hne hsq2
  set Z := center (SpecialLinearGroup (Fin n) K)
  set ψ := slConjugation n K A
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : innerDiagonalAction n K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact innerDiagonalAction_mk n K A g
  let eF := MulEquiv.subgroupCongr (congrArg fixedSubgroup heq)
  have hL' := LocalCores.isComponent_map_mulEquiv eF hL
  obtain ⟨M, hM, ⟨eLM⟩⟩ := exists_component_of_quotientFixed Z le_rfl ψ hinv hL'
  have hmap : (FixedCommutingProduct.fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
        CatalogueBGeneralLinear.specialLinearRange n K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [toGL_slConjugation] at h1
      calc SpecialLinearGroup.toGL g * A =
          (A * SpecialLinearGroup.toGL g * A⁻¹) * A := by rw [h1]
        _ = A * SpecialLinearGroup.toGL g := by group
    · intro hy
      obtain ⟨hyC, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_slConjugation, ← Subgroup.mem_centralizer_singleton_iff.mp hyC,
        mul_inv_cancel_right]
  have hMF : Assembly.IsComponentOf (M.map (FixedCommutingProduct.fixedSubgroup ψ).subtype)
      (FixedCommutingProduct.fixedSubgroup ψ) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le M)).2 ?_
    have hMM : (M.map (FixedCommutingProduct.fixedSubgroup ψ).subtype).subgroupOf
        (FixedCommutingProduct.fixedSubgroup ψ) = M :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) M
    rw [hMM]
    exact hM
  have h1 := isComponentOf_map_of_injective hMF SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective
  rw [hmap] at h1
  have hnormal : ((Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
      CatalogueBGeneralLinear.specialLinearRange n K).subgroupOf
        (Subgroup.centralizer ({A} : Set (GL (Fin n) K)))).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (CatalogueBGeneralLinear.specialLinearRangeNormal n K).conj_mem _ hxS (g : GL (Fin n) K)
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  have hGL := notBC3_glCentralizer hp hp2 hf hK hn A hmk c hc h3
  have hMo : NotBC3 p M :=
    NotBC3.of_mulEquiv
      ((M.equivMapOfInjective (FixedCommutingProduct.fixedSubgroup ψ).subtype
        (subtype_injective _)).trans
        ((M.map (FixedCommutingProduct.fixedSubgroup ψ).subtype).equivMapOfInjective
          SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective))
      (NotBC3.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2.1).symm hGL)
  exact NotBC3.of_mulEquiv (L.equivMapOfInjective eF.toMonoidHom eF.injective)
    (NotBC3.of_centerQuotient_equiv eLM hMo)

theorem notBC3_of_conj_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (g : X) {p : ℕ}
    (h : ∀ M : Subgroup (fixedSubgroup (MulAut.conj (e g))), IsComponent M → NotBC3 p M)
    {L : Subgroup (fixedSubgroup (MulAut.conj g))} (hL : IsComponent L) : NotBC3 p L := by
  have hfix : (fixedSubgroup (MulAut.conj g)).map e.toMonoidHom =
      fixedSubgroup (MulAut.conj (e g)) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x', hx', hxx'⟩
      rw [← hxx']
      change MulAut.conj (e g) (e x') = e x'
      change MulAut.conj g x' = x' at hx'
      rw [MulAut.conj_apply] at hx' ⊢
      rw [← map_mul, ← map_inv, ← map_mul, hx']
    · intro hx
      refine ⟨x, ?_, rfl⟩
      change MulAut.conj (e g) (e x) = e x at hx
      change MulAut.conj g x = x
      rw [MulAut.conj_apply] at hx ⊢
      apply e.injective
      rw [map_mul, map_mul, map_inv, hx]
  exact notBC3_of_component_equiv
    (((fixedSubgroup (MulAut.conj g)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hfix)) h hL

theorem orderOf_conj_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (g : X) :
    orderOf (MulAut.conj (e g)) = orderOf (MulAut.conj g) := by
  have hcg : MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
    ext y
    change e (g * e.symm y * g⁻¹) = e g * y * (e g)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [← hcg]
  exact orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _

theorem famNoSpin7_psl (hO : LieOrderFormulasInput) : FamNoSpin7 .PSL := by
  intro X _ n p f hp hp2 hadm hX g hg L hL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hX
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (e g)
  have hconj : innerDiagonalAction n K (SpecialLinearGroup.toGL s) = MulAut.conj (e g) := by
    rw [← hs, ← pglAction_toPGL n K (s : Matrix.ProjectiveSpecialLinearGroup (Fin n) K),
      Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, innerDiagonalAction_eq_pglAction]
  have hord : orderOf (innerDiagonalAction n K (SpecialLinearGroup.toGL s)) = 2 := by
    rw [hconj, orderOf_conj_mulEquiv]
    exact hg
  refine NotBC3.noSpin7 hO hp2 (notBC3_of_conj_mulEquiv e g (fun M hM => ?_) hL)
  let Ψ := MulEquiv.subgroupCongr (congrArg fixedSubgroup hconj.symm)
  exact NotBC3.of_mulEquiv (M.equivMapOfInjective Ψ.toMonoidHom Ψ.injective)
    (notBC3_inner_psl hp hp2 hK hadm _ hord (LocalCores.isComponent_map_mulEquiv Ψ hM))

end CFSG.ComponentClassification.HarrisLit.T1.P51e
