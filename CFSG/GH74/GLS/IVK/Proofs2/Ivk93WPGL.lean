module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L52
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93W

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBGeneralLinear
open scoped MatrixGroups commutatorElement

theorem Ivk93W.exists_pgl {F : Type} [Field F] [Finite F] {n : ℕ}
    {x : StatedProj (StatedSL n F)} {q : ℕ} {B : Subgroup (StatedProj (StatedSL n F))}
    (h : Ivk93W x q B) :
    ∃ A : GL (Fin n) F, CatFactsL4U4.projToPGL n F x = Matrix.ProjGenLinGroup.mk A ∧
      Matrix.ProjGenLinGroup.mk A ≠ 1 ∧ Matrix.ProjGenLinGroup.mk A ^ 2 = 1 ∧
      B.map (CatFactsL4U4.projToPGL n F) ≤
        centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F)) ∧
      IsPComponent 2 ((B.map (CatFactsL4U4.projToPGL n F)).subgroupOf
        (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F)))) := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  set φ := CatFactsL4U4.projToPGL n F with hφdef
  have hφ : Function.Injective φ := CatFactsL4U4.projToPGL_injective n
  have := projToPGL_range_normal n F
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (φ x)
  have hx2 : x ^ 2 = 1 := by rw [← h.ord, pow_orderOf_eq_one]
  obtain ⟨hKle, hK⟩ := isPComponent_map_of_normal φ hφ h.le h.comp.2
  refine ⟨A, hA.symm, ?_, ?_, ?_, ?_⟩
  · rw [hA]; intro h1; exact h.ne_one (hφ (h1.trans (map_one φ).symm))
  · rw [hA, ← map_pow, hx2, map_one]
  · rw [hA]; exact hKle
  · rw [hA]; exact hK

@[expose] def Ivk93WBlockData {F : Type} [Field F] [Finite F] {n : ℕ}
    (x : StatedProj (StatedSL n F)) (B : Subgroup (StatedProj (StatedSL n F))) : Prop :=
  ∃ (A : GL (Fin n) F) (r s : ℕ)
    (e : ↥(centralizer ({A} : Set (GL (Fin n) F))) ≃* GL (Fin r) F × GL (Fin s) F)
    (L : Subgroup ↥(centralizer ({A} : Set (GL (Fin n) F)))),
    CatFactsL4U4.projToPGL n F x = Matrix.ProjGenLinGroup.mk A ∧
    Matrix.ProjGenLinGroup.mk A ≠ 1 ∧ Matrix.ProjGenLinGroup.mk A ^ 2 = 1 ∧
    1 ≤ r ∧ 1 ≤ s ∧ r + s = n ∧
    (∀ c : Fˣ, e (ordinaryCentralizerScalar A c) =
      (Matrix.GeneralLinearGroup.scalar (Fin r) c, Matrix.GeneralLinearGroup.scalar (Fin s) c)) ∧
    IsPComponent 2 L ∧ 2 ≤ r ∧ L.map e.toMonoidHom = (specialLinearRange r F).prod ⊥ ∧
    L.map (ordinaryCentralizerProjection A) = (B.map (CatFactsL4U4.projToPGL n F)).subgroupOf
      (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))) ∧
    B.map (CatFactsL4U4.projToPGL n F) ≤
      centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F)) ∧
    Nonempty (SL(r, F) ≃* ↥B)

theorem ivk93w_map_prodComm_bot_prod {r s : ℕ} {F : Type} [Field F]
    (K : Subgroup (GL (Fin s) F)) :
    ((⊥ : Subgroup (GL (Fin r) F)).prod K).map (MulEquiv.prodComm).toMonoidHom =
      K.prod (⊥ : Subgroup (GL (Fin r) F)) := by
  ext ⟨a, b⟩
  rw [mem_map]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, h⟩
    have h' : (v, u) = (a, b) := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    exact ⟨hv, hu⟩
  · rintro ⟨ha, hb⟩
    exact ⟨(b, a), ⟨hb, ha⟩, rfl⟩

theorem ivk93w_blockData_of_first {F : Type} [Field F] [Finite F] {n : ℕ}
    {x : StatedProj (StatedSL n F)} {B : Subgroup (StatedProj (StatedSL n F))}
    (A : GL (Fin n) F) (hA : CatFactsL4U4.projToPGL n F x = Matrix.ProjGenLinGroup.mk A)
    (hne : Matrix.ProjGenLinGroup.mk A ≠ 1) (hinv : Matrix.ProjGenLinGroup.mk A ^ 2 = 1)
    (hBle : B.map (CatFactsL4U4.projToPGL n F) ≤
      centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F)))
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : r + s = n)
    (e : ↥(centralizer ({A} : Set (GL (Fin n) F))) ≃* GL (Fin r) F × GL (Fin s) F)
    (hscal : ∀ c : Fˣ, e (ordinaryCentralizerScalar A c) =
      (Matrix.GeneralLinearGroup.scalar (Fin r) c, Matrix.GeneralLinearGroup.scalar (Fin s) c))
    {L : Subgroup ↥(centralizer ({A} : Set (GL (Fin n) F)))} (hL : IsPComponent 2 L)
    (h2r : 2 ≤ r) (he : L.map e.toMonoidHom = (specialLinearRange r F).prod ⊥)
    (hLM : L.map (ordinaryCentralizerProjection A) = (B.map (CatFactsL4U4.projToPGL n F)).subgroupOf
      (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F)))) :
    Ivk93WBlockData x B := by
  classical
  have hφ : Function.Injective (CatFactsL4U4.projToPGL n F) := CatFactsL4U4.projToPGL_injective n
  have hker : (ordinaryCentralizerProjection A).ker ≤ (ordinaryCentralizerScalar A).range :=
    (ordinaryCentralizerProjection_kernel_eq_scalar A).le
  refine ⟨A, r, s, e, L, hA, hne, hinv, hr, hs, hrs, hscal, hL, h2r, he, hLM, hBle, ?_⟩
  obtain ⟨φ₁⟩ := ivk93l_equiv_fst e he
  obtain ⟨ψ⟩ := ivk93l_equiv_map (ordinaryCentralizerProjection A)
    (ivk93l_inf_ker_fst hs e (ordinaryCentralizerScalar A) hscal _ hker he)
  exact ⟨φ₁.trans (ψ.trans ((MulEquiv.subgroupCongr hLM).trans
    ((Subgroup.subgroupOfEquivOfLe hBle).trans
      (B.equivMapOfInjective (CatFactsL4U4.projToPGL n F) hφ).symm)))⟩

theorem ivk93w_nonsquare_false {F : Type} [Field F] [Finite F]
    {x : StatedProj (StatedSL 4 F)} {B : Subgroup (StatedProj (StatedSL 4 F))}
    (A : GL (Fin 4) F) (hA : CatFactsL4U4.projToPGL 4 F x = Matrix.ProjGenLinGroup.mk A)
    (hxB : x ∈ B)
    (lambda : Fˣ) (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 4) lambda)
    (hns : ¬ IsSquare lambda.val)
    (L : Subgroup ↥(centralizer ({A} : Set (GL (Fin 4) F)))) (hL : IsPComponent 2 L)
    (hLM : L.map (ordinaryCentralizerProjection A) = (B.map (CatFactsL4U4.projToPGL 4 F)).subgroupOf
      (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin 4) F)))) :
    False := by
  classical
  have : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
  have : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
    quadraticExtension_finite lambda.val
  let := CatalogueBProjectiveQuadratic.matrixModule A lambda hsq
  have hmdim := CatalogueBProjectiveQuadratic.matrixDimension_twice A lambda hsq
  set m := CatalogueBProjectiveQuadratic.matrixDimension A lambda hsq with hm
  have hm2 : m = 2 := by
    simp only [Fintype.card_fin] at hmdim
    omega
  let e := CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq
  obtain ⟨-, -, -, k, -⟩ := CatalogueBGeneralLinear.pComponent_classification m _ (by omega) 2 _
    (CatalogueBAlternating.pComponent_map_equiv 2 e _ hL)
  have hmemY : Matrix.ProjGenLinGroup.mk A ∈
      centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin 4) F)) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hmemM : (⟨Matrix.ProjGenLinGroup.mk A, hmemY⟩ :
      ↥(centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin 4) F)))) ∈
      (B.map (CatFactsL4U4.projToPGL 4 F)).subgroupOf
        (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin 4) F))) := by
    rw [mem_subgroupOf]
    exact ⟨x, hxB, hA⟩
  rw [← hLM] at hmemM
  obtain ⟨ℓ, hℓL, hℓ⟩ := hmemM
  have hℓ' : Matrix.ProjGenLinGroup.mk (ℓ.val : GL (Fin 4) F) = Matrix.ProjGenLinGroup.mk A :=
    congrArg Subtype.val hℓ
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 hℓ'
  let a₀ : ↥(centralizer ({A} : Set (GL (Fin 4) F))) :=
    ⟨A, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have ha₀ : a₀ = ℓ * ordinaryCentralizerScalar A u := Subtype.ext hu.symm
  have hdet1 : Matrix.GeneralLinearGroup.det (e ℓ) = 1 := by
    have h1 : e ℓ ∈ specialLinearRange m (CatalogueBProjectiveQuadratic.extension lambda.val) := by
      rw [← k]
      exact ⟨ℓ, hℓL, rfl⟩
    rw [← MonoidHom.mem_ker, ← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact h1
  have hdet2 : (((Matrix.GeneralLinearGroup.det (e a₀) :
      (CatalogueBProjectiveQuadratic.extension lambda.val)ˣ)) :
        CatalogueBProjectiveQuadratic.extension lambda.val) =
      (algebraMap F (CatalogueBProjectiveQuadratic.extension lambda.val) u.val) ^ m := by
    rw [ha₀, map_mul, map_mul, hdet1, one_mul,
      CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv_scalar A lambda hsq u,
      Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    simp [← hm]
  have hmat : ((e a₀ : GL (Fin m) (CatalogueBProjectiveQuadratic.extension lambda.val)) :
      Matrix (Fin m) (Fin m) (CatalogueBProjectiveQuadratic.extension lambda.val)) =
      Matrix.scalar (Fin m) (AdjoinRoot.root
        (CatalogueBProjectiveQuadratic.quadraticPolynomial lambda.val)) := by
    let b := CatalogueBProjectiveQuadratic.matrixBasis A lambda hsq
    have hmul :=
      CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv_mulVec A lambda hsq a₀
    have h1 : ∀ w : Fin m → CatalogueBProjectiveQuadratic.extension lambda.val,
        ((e a₀ : GL (Fin m) (CatalogueBProjectiveQuadratic.extension lambda.val)) :
          Matrix (Fin m) (Fin m) (CatalogueBProjectiveQuadratic.extension lambda.val)).mulVec w =
        AdjoinRoot.root (CatalogueBProjectiveQuadratic.quadraticPolynomial lambda.val) • w := by
      intro w
      obtain ⟨v, rfl⟩ := b.equivFun.surjective w
      rw [hmul v, ← CatalogueBProjectiveQuadratic.matrixModule_root_smul A lambda hsq v, map_smul]
    ext i j
    have := congrFun (h1 (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.scalar_apply, Matrix.diagonal_apply, Pi.single_apply,
      eq_comm] using this
  have hdet3 : (((Matrix.GeneralLinearGroup.det (e a₀) :
      (CatalogueBProjectiveQuadratic.extension lambda.val)ˣ)) :
        CatalogueBProjectiveQuadratic.extension lambda.val) =
      (AdjoinRoot.root (CatalogueBProjectiveQuadratic.quadraticPolynomial lambda.val)) ^ m := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hmat, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hdet3, hm2, CatalogueBProjectiveQuadratic.extension_root_square] at hdet2
  have hlam : lambda.val = u.val ^ 2 := by
    apply (algebraMap F (CatalogueBProjectiveQuadratic.extension lambda.val)).injective
    rw [map_pow]
    exact hdet2
  exact hns ⟨u.val, by rw [hlam]; ring⟩

theorem Ivk93W.blockData {F : Type} [Field F] [Finite F] (htwo : (2 : F) ≠ 0) {n : ℕ}
    (hn : n = 3 ∨ n = 4 ∨ n = 5) {x : StatedProj (StatedSL n F)} {q : ℕ}
    {B : Subgroup (StatedProj (StatedSL n F))} (h : Ivk93W x q B) : Ivk93WBlockData x B := by
  classical
  have hn2 : 2 ≤ n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨A, hA, hne, hinv, hBle, hM⟩ := h.exists_pgl
  obtain ⟨L, hL, hLM⟩ := ivk93l_lift_map A hM
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinv
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, -, hr, hs, hrs, e, -, hscal, -⟩ :=
      square_projective_centralizer_structure n hn2 A lambda htwo hne hsq hsquare
    rcases ivk93l_block hr hs e hL with ⟨h2r, he⟩ | ⟨h2s, he⟩
    · exact ivk93w_blockData_of_first A hA hne hinv hBle hr hs hrs e hscal hL h2r he hLM
    · let e' := e.trans (MulEquiv.prodComm : _ ≃* _)
      have hscal' : ∀ c : Fˣ, e' (ordinaryCentralizerScalar A c) =
          (Matrix.GeneralLinearGroup.scalar _ c, Matrix.GeneralLinearGroup.scalar _ c) := by
        intro c
        simp [e', hscal]
      have he' : L.map e'.toMonoidHom = (specialLinearRange _ F).prod ⊥ := by
        have : e'.toMonoidHom = (MulEquiv.prodComm : _ ≃* _).toMonoidHom.comp e.toMonoidHom := rfl
        rw [this, ← Subgroup.map_map, he, ivk93w_map_prodComm_bot_prod]
      exact ivk93w_blockData_of_first A hA hne hinv hBle hs hr (by omega) e' hscal' hL h2s he'
        hLM
  · exfalso
    have : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    have : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      quadraticExtension_finite lambda.val
    have hm := CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn2 A lambda hsq hsquare
    rcases hn with rfl | rfl | rfl
    · omega
    · exact ivk93w_nonsquare_false A hA h.mem lambda hsq hsquare L hL hLM
    · omega


open CFSG.ComponentClassification.CatalogueBPrimeJoin in
theorem ivk93w_primeResidual_eq_top {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hquasisimple : CFSG.IsQuasisimple G) (hdvd : p ∣ Nat.card G) : primeResidual p G = ⊤ := by
  let : (primeResidual p G).Characteristic := primeResidual_characteristic p G
  have hnative := CatalogueBAlternating.quasisimple_iff_native.mp hquasisimple
  rcases Quasisimple.normal_le_center_or_eq_top hnative (primeResidual p G) with
    hcentral | htop
  · exfalso
    let : Group.IsPerfect G := hquasisimple.1
    let : Nontrivial G := Quasisimple.nontrivial hnative
    let P : Sylow p G := Classical.choice inferInstance
    have hPCentral : (P : Subgroup G) ≤ Subgroup.center G :=
      (pSubgroup_le_residual p _ P.isPGroup').trans hcentral
    let : IsMulCommutative (P : Subgroup G) := isMulCommutative_iff.mpr
      fun x y => Subtype.ext ((Subgroup.mem_center_iff.mp (hPCentral x.property)) y).symm
    have hnormalizer : Subgroup.normalizer (P : Set G) ≤
        Subgroup.centralizer (P : Set G) := by
      intro x _
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      exact ((Subgroup.mem_center_iff.mp (hPCentral hy)) x).symm
    let transfer := MonoidHom.transferSylow P hnormalizer
    have htransfer : transfer = 1 := PerfectAutomorphisms.hom_eq_one_of_commutative transfer
    have hkernel : transfer.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr htransfer
    have hnotP : ¬ p ∣ Nat.card G := by
      have hnot := MonoidHom.not_dvd_card_ker_transferSylow P hnormalizer
      change ¬ p ∣ Nat.card transfer.ker at hnot
      simpa only [hkernel, Subgroup.card_top] using hnot
    exact hnotP hdvd
  · exact htop

theorem ivk93w_isPComponent_of_normal {X : Type*} [Group X] [Finite X] (N : Subgroup X)
    [hN : N.Normal] (hq : CFSG.IsQuasisimple N) (hdvd : 2 ∣ Nat.card N) : IsPComponent 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 N).2
    ⟨hN.isSubnormal, ivk93w_primeResidual_eq_top 2 hq hdvd, ?_⟩
  have hnative := CatalogueBAlternating.quasisimple_iff_native.mp hq
  rcases Quasisimple.normal_le_center_or_eq_top hnative (pPrimeCore 2 N) with hc | htop
  · exact CatalogueBAlternating.quasisimple_iff_native.mpr
      (Quasisimple.central_quotient hnative _ hc)
  · exfalso
    have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥N)
    rw [htop, Subgroup.card_top] at hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)

theorem ivk93w_pComponent_map_proj {F : Type} [Field F] [Finite F] {n : ℕ} [Nonempty (Fin n)]
    (A : GL (Fin n) F) {L : Subgroup ↥(centralizer ({A} : Set (GL (Fin n) F)))}
    (hL : IsPComponent 2 L) :
    IsPComponent 2 (L.map (ordinaryCentralizerProjection A)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Matrix.ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  have := ordinaryCentralizerProjection_range_normal A
  set f := ordinaryCentralizerProjection A with hf
  have h1 := CatalogueBCentralQuotient.pComponent_map 2 f.rangeRestrict f.rangeRestrict_surjective
    (ordinaryCentralizerProjection_rangeRestrict_kernel_central A) L hL
  have hle : L.map f ≤ f.range := Subgroup.map_le_range f L
  have h2 : L.map f = (L.map f.rangeRestrict).map f.range.subtype := by
    rw [Subgroup.map_map]; rfl
  have h3 : (L.map f).subgroupOf f.range = L.map f.rangeRestrict := by
    rw [h2]; exact Subgroup.comap_map_eq_self_of_injective f.range.subtype_injective _
  exact (CatalogueBFixedCentralQuotient.pComponent_normal_iff 2 f.range (L.map f) hle).1
    (h3 ▸ h1)

theorem ivk93w_perfect_le_range {F : Type} [Field F] (n : ℕ)
    {T : Subgroup (Matrix.ProjGenLinGroup (Fin n) F)} (hT : ⁅T, T⁆ = T) :
    T ≤ (CatFactsL4U4.projToPGL n F).range := by
  calc T = ⁅T, T⁆ := hT.symm
    _ ≤ (CatFactsL4U4.projToPGL n F).range := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective a
      obtain ⟨h, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective b
      have hdet : ((⁅g, h⁆ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det ⁅g, h⁆ = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
        rw [← Matrix.GeneralLinearGroup.val_det_apply, h1]
        rfl
      have hmem : ⁅g, h⁆ ∈ StatedSL n F := Subgroup.subset_closure hdet
      refine ⟨QuotientGroup.mk ⟨⁅g, h⁆, hmem⟩, ?_⟩
      rw [CatFactsL4U4.projToPGL_mk]
      simp [map_commutatorElement]

theorem ivk93w_isPCompIn_comap {F : Type} [Field F] [Finite F] {n : ℕ}
    {x : StatedProj (StatedSL n F)} {A : GL (Fin n) F}
    (hA : CatFactsL4U4.projToPGL n F x = Matrix.ProjGenLinGroup.mk A)
    {T : Subgroup (Matrix.ProjGenLinGroup (Fin n) F)}
    (hTle : T ≤ centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F)))
    (hTr : T ≤ (CatFactsL4U4.projToPGL n F).range)
    (hT : IsPComponent 2 (T.subgroupOf
      (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))))) :
    IsPCompIn 2 (centralizer ({x} : Set (StatedProj (StatedSL n F))))
      (T.comap (CatFactsL4U4.projToPGL n F)) ∧
    (T.comap (CatFactsL4U4.projToPGL n F)).map (CatFactsL4U4.projToPGL n F) = T := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  set φ := CatFactsL4U4.projToPGL n F with hφdef
  have hφ : Function.Injective φ := CatFactsL4U4.projToPGL_injective n
  have := projToPGL_range_normal n F
  set L := T.comap φ with hL
  have hLT : L.map φ = T := by
    rw [hL, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hTr
  have hLC : L ≤ centralizer ({x} : Set (StatedProj (StatedSL n F))) := by
    intro j hj
    rw [mem_centralizer_singleton_iff]
    apply hφ
    have h1 := mem_centralizer_singleton_iff.1 (hTle hj)
    rw [map_mul, map_mul, hA]
    exact h1
  set e : StatedProj (StatedSL n F) ≃* φ.range := MonoidHom.ofInjective hφ with he
  have hex : ∀ m, ((e m : φ.range) : Matrix.ProjGenLinGroup (Fin n) F) = φ m := fun m => rfl
  have h := isPComponent_subgroupOf_restrict (G := φ.range) hTle hTr hT
  have h1 : T.subgroupOf φ.range = L.map e.toMonoidHom := by
    ext ⟨y, hy⟩
    simp only [mem_subgroupOf, mem_map]
    constructor
    · intro hyT
      obtain ⟨m, rfl⟩ := hy
      exact ⟨m, hyT, Subtype.ext rfl⟩
    · rintro ⟨m, hm, hmy⟩
      have : φ m = y := (hex m).symm.trans (congrArg Subtype.val hmy)
      rw [← this]
      exact hm
  have h2 : (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))).subgroupOf
      φ.range = centralizer ({e x} : Set φ.range) := by
    ext z
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← hA]
    constructor
    · intro hz
      exact Subtype.ext (by simpa [hex] using hz)
    · intro hz
      simpa [hex] using congrArg Subtype.val hz
  rw [h1, h2, ← map_centralizer_singleton_equiv e x] at h
  exact ⟨⟨hLC, (isPComponent_subgroupOf_map_iff e hLC).mpr h⟩, hLT⟩


theorem ivk93w_klein_sl4 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    ∃ u v : SL(4, F), u ^ 2 = 1 ∧ v ^ 2 = 1 ∧ (u * v) ^ 2 = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u * v ≠ 1 := by
  have hdet1 : (Matrix.diagonal ![(-1 : F), -1, 1, 1]).det = 1 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_four]
  have hdet2 : (Matrix.diagonal ![(1 : F), -1, -1, 1]).det = 1 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_four]
  have hne : (-1 : F) ≠ 1 := by
    intro h
    exact h2 (by linear_combination -h)
  obtain ⟨u, hu⟩ : ∃ u : SL(4, F),
      (u : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![(-1 : F), -1, 1, 1] := ⟨⟨_, hdet1⟩, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : SL(4, F),
      (v : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![(1 : F), -1, -1, 1] := ⟨⟨_, hdet2⟩, rfl⟩
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hu, Matrix.SpecialLinearGroup.coe_one, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hv, Matrix.SpecialLinearGroup.coe_one, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, hu, hv,
      Matrix.SpecialLinearGroup.coe_one, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · intro h
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simp [hu] at this
    exact hne this
  · intro h
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F) 1 1) h
    simp [hv] at this
    exact hne this
  · intro h
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simp [Matrix.mul_apply, Matrix.diagonal_apply, hu, hv] at this
    exact hne this

theorem ivk93w_involution_sl {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {s : ℕ} (hs : s = 2 ∨ s = 3) :
    ∃ u : SL(s, F), u ^ 2 = 1 ∧ u ≠ 1 := by
  have hne : (-1 : F) ≠ 1 := by
    intro h
    exact h2 (by linear_combination -h)
  rcases hs with rfl | rfl
  · have hdet : (Matrix.diagonal ![(-1 : F), -1]).det = 1 := by
      simp [Matrix.det_diagonal, Fin.prod_univ_two]
    obtain ⟨u, hu⟩ : ∃ u : SL(2, F),
        (u : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(-1 : F), -1] := ⟨⟨_, hdet⟩, rfl⟩
    refine ⟨u, ?_, ?_⟩
    · apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, hu, Matrix.SpecialLinearGroup.coe_one, pow_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
    · intro h
      have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simp [hu] at this
      exact hne this
  · obtain ⟨u, v, hu2, -, -, hu1, -, -⟩ := ivk93l5_klein_sl3 h2
    exact ⟨u, hu2, hu1⟩

theorem ivk93w_other_block {F : Type} [Field F] [Finite F] {n : ℕ}
    {x : StatedProj (StatedSL n F)} {q : ℕ} {B : Subgroup (StatedProj (StatedSL n F))}
    (h : Ivk93W x q B) (A : GL (Fin n) F)
    (hA : CatFactsL4U4.projToPGL n F x = Matrix.ProjGenLinGroup.mk A)
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : r + s = n)
    (e : ↥(centralizer ({A} : Set (GL (Fin n) F))) ≃* GL (Fin r) F × GL (Fin s) F)
    {L : Subgroup ↥(centralizer ({A} : Set (GL (Fin n) F)))} (hL : IsPComponent 2 L)
    (he : L.map e.toMonoidHom = (specialLinearRange r F).prod ⊥)
    (hLM : L.map (ordinaryCentralizerProjection A) = (B.map (CatFactsL4U4.projToPGL n F)).subgroupOf
      (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))))
    (hqs : CFSG.IsQuasisimple SL(s, F)) (hev : ∃ u : SL(s, F), u ^ 2 = 1 ∧ u ≠ 1) :
    False := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Matrix.ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  have := projToPGL_range_normal n F
  set φ := CatFactsL4U4.projToPGL n F with hφdef
  have hφ : Function.Injective φ := CatFactsL4U4.projToPGL_injective n
  have hfN := ordinaryCentralizerProjection_range_normal A
  let K : Subgroup (GL (Fin r) F × GL (Fin s) F) :=
    (⊥ : Subgroup (GL (Fin r) F)).prod (specialLinearRange s F)
  set L' : Subgroup ↥(centralizer ({A} : Set (GL (Fin n) F))) := K.map e.symm.toMonoidHom
    with hL'
  have hL'e : L'.map e.toMonoidHom = K := by
    rw [hL', Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun y => e.apply_symm_apply y
    rw [this, Subgroup.map_id]
  have hSLn : (specialLinearRange s F).Normal := by
    have : specialLinearRange s F = Matrix.GeneralLinearGroup.det.ker :=
      Matrix.SpecialLinearGroup.range_toGL_eq_ker_det
    rw [this]
    exact MonoidHom.normal_ker _
  have hKn : K.Normal := Subgroup.prod_normal _ _
  have hL'n : L'.Normal := Subgroup.Normal.map hKn e.symm.toMonoidHom e.symm.surjective
  obtain ⟨φ₁⟩ := ivk93l_equiv_snd e hL'e
  have hqL' : CFSG.IsQuasisimple ↥L' := CFSG.LocalCores.isQuasisimple_of_mulEquiv φ₁ hqs
  have hevL' : 2 ∣ Nat.card ↥L' := by
    obtain ⟨u, hu2, hu1⟩ := hev
    have h1 : 2 ∣ Nat.card SL(s, F) := by
      have := orderOf_dvd_natCard u
      rwa [orderOf_eq_prime hu2 hu1] at this
    rwa [← Nat.card_congr φ₁.symm.toEquiv] at h1
  have hL'2 : IsPComponent 2 L' := ivk93w_isPComponent_of_normal L' hqL' hevL'
  have hT := ivk93w_pComponent_map_proj A hL'2
  set T : Subgroup (Matrix.ProjGenLinGroup (Fin n) F) := (L'.map (ordinaryCentralizerProjection A)).map (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))).subtype with hTdef
  have hTsub : T.subgroupOf (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))) = L'.map (ordinaryCentralizerProjection A) :=
    Subgroup.comap_map_eq_self_of_injective (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))).subtype_injective _
  have hTle : T ≤ (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hTperf : ⁅T, T⁆ = T := by
    have hT' : T = L'.map ((centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))).subtype.comp (ordinaryCentralizerProjection A)) := by rw [hTdef, Subgroup.map_map]
    have hperf : ⁅L', L'⁆ = L' :=
      Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect hL'2)
    rw [hT', ← Subgroup.map_commutator, hperf]
  have hTr : T ≤ φ.range := ivk93w_perfect_le_range n hTperf
  obtain ⟨hB'comp, hB'map⟩ := ivk93w_isPCompIn_comap hA hTle hTr (by rw [hTsub]; exact hT)
  have hB'B := h.uniq _ hB'comp
  have hTB : T = B.map φ := by rw [← hB'map, hB'B]
  have hLL' : L.map (ordinaryCentralizerProjection A) = L'.map (ordinaryCentralizerProjection A) := by
    rw [hLM, ← hTsub, hTB]
  have hcentral := ordinaryCentralizerProjection_rangeRestrict_kernel_central A
  have himages : L.map (ordinaryCentralizerProjection A).rangeRestrict = L'.map (ordinaryCentralizerProjection A).rangeRestrict := by
    have h1 : ∀ M : Subgroup ↥(centralizer ({A} : Set (GL (Fin n) F))),
        M.map (ordinaryCentralizerProjection A) = (M.map (ordinaryCentralizerProjection A).rangeRestrict).map (ordinaryCentralizerProjection A).range.subtype := by
      intro M
      rw [Subgroup.map_map]; rfl
    apply Subgroup.map_injective (ordinaryCentralizerProjection A).range.subtype_injective
    rw [← h1, ← h1, hLL']
  have hLeq : L = L' :=
    CatalogueBCentralQuotient.pComponent_lift_unique 2 (ordinaryCentralizerProjection A).rangeRestrict hcentral L L' hL hL'2 himages
  have : Nontrivial ↥L := CatalogueBAlternating.pComponent_nontrivial hL
  obtain ⟨ℓ, hℓ⟩ := exists_ne (1 : ↥L)
  have h1 : e (ℓ : ↥(centralizer ({A} : Set (GL (Fin n) F)))) ∈ L.map e.toMonoidHom :=
    ⟨ℓ, ℓ.2, rfl⟩
  have h2 : e (ℓ : ↥(centralizer ({A} : Set (GL (Fin n) F)))) ∈ L'.map e.toMonoidHom :=
    ⟨ℓ, by rw [← hLeq]; exact ℓ.2, rfl⟩
  rw [he] at h1
  rw [hL'e] at h2
  apply hℓ
  have h3 : e (ℓ : ↥(centralizer ({A} : Set (GL (Fin n) F)))) = 1 :=
    Prod.ext (Subgroup.mem_bot.1 h2.1) (Subgroup.mem_bot.1 h1.2)
  have h4 : (ℓ : ↥(centralizer ({A} : Set (GL (Fin n) F)))) = 1 := by
    apply e.injective
    rw [h3, map_one]
  exact Subtype.ext h4


theorem Ivk93W.false_of_equiv_sl {J : Type} [Group J] [Finite J] {x : J} {q : ℕ}
    {B : Subgroup J} (h : Ivk93W x q B) {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {r : ℕ}
    (hr3 : 3 ≤ r) (hr4 : r ≤ 4) (e : SL(r, F) ≃* ↥B) : False := by
  obtain ⟨u, v, hu2, hv2, -, hu1, hv1, huv1⟩ : ∃ u v : SL(r, F), u ^ 2 = 1 ∧ v ^ 2 = 1 ∧
      (u * v) ^ 2 = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u * v ≠ 1 := by
    rcases (by omega : r = 3 ∨ r = 4) with rfl | rfl
    · exact ivk93l5_klein_sl3 h2
    · exact ivk93w_klein_sl4 h2
  have key : ∀ g : SL(r, F), g ^ 2 = 1 → g ≠ 1 → ((e g : ↥B) : J) = x := by
    intro g hg2 hg1
    apply h.unique_involution (e g).2
    · rw [← Subgroup.coe_mul, ← map_mul, ← pow_two, hg2, map_one]
      rfl
    · intro h1
      apply hg1
      apply e.injective
      exact Subtype.ext (by simpa using h1)
  have heq : e u = e v := Subtype.ext ((key u hu2 hu1).trans (key v hv2 hv1).symm)
  apply huv1
  rw [e.injective heq, ← pow_two]
  exact hv2

theorem Ivk93W.five_le_of_equiv_sl2 {J : Type} [Group J] [Finite J] {x : J} {q : ℕ}
    {B : Subgroup J} (h : Ivk93W x q B) {F : Type} [Field F] [Finite F]
    (e : SL(2, F) ≃* ↥B) : 5 ≤ Nat.card F := by
  by_contra hlt
  have h1 : Nat.card ↥B = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
  have h2 := h.card_ge
  have h3 := sl2_card_mono (show Nat.card F ≤ 4 by omega)
  norm_num at h3
  omega

theorem Ivk93W.false_of_psl_four_five {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {n : ℕ} (hn : n = 4 ∨ n = 5) {x : StatedProj (StatedSL n F)} {q : ℕ}
    {B : Subgroup (StatedProj (StatedSL n F))} (h : Ivk93W x q B) : False := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  obtain ⟨A, r, s, e, L, hA, hne, hinv, hr, hs, hrs, hscal, hL, h2r, he, hLM, hBle, ⟨ψ⟩⟩ :=
    h.blockData h2 (by omega)
  by_cases hr3 : 3 ≤ r
  · exact h.false_of_equiv_sl h2 hr3 (by omega) ψ
  · have hr2 : r = 2 := by omega
    subst hr2
    have h5 : 5 ≤ Nat.card F := h.five_le_of_equiv_sl2 ψ
    have hs23 : s = 2 ∨ s = 3 := by omega
    have hqs : CFSG.IsQuasisimple SL(s, F) :=
      specialLinear_quasisimple s F (by omega) (by omega) (by omega)
    exact ivk93w_other_block h A hA (by omega) hs hrs e hL he hLM hqs
      (ivk93w_involution_sl h2 hs23)

end CFSG.GH74.GLS.IVK.Proofs2
