module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L4Core
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution

section Lift

variable {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]

theorem exists_pComponent_lifts (f : X →* Y) (hcentral : f.ker ≤ center X) [f.range.Normal]
    [Group.IsSolvable (Y ⧸ f.range)] {L₁ L₂ : Subgroup Y} (h₁ : IsPComponent 2 L₁)
    (h₂ : IsPComponent 2 L₂) (hne : L₁ ≠ L₂) :
    ∃ M₁ M₂ : Subgroup X, IsPComponent 2 M₁ ∧ IsPComponent 2 M₂ ∧ M₁ ≠ M₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : f.rangeRestrict.ker ≤ center X := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hcentral
  obtain ⟨hle₁, hr₁⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2 f.range L₁ h₁
  obtain ⟨hle₂, hr₂⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2 f.range L₂ h₂
  obtain ⟨M₁, hM₁, hm₁, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2
    f.rangeRestrict f.rangeRestrict_surjective hc _ hr₁
  obtain ⟨M₂, hM₂, hm₂, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2
    f.rangeRestrict f.rangeRestrict_surjective hc _ hr₂
  refine ⟨M₁, M₂, hM₁, hM₂, fun h => hne ?_⟩
  rw [h, hm₂] at hm₁
  have h12 := subgroupOf_inj.mp hm₁
  rw [inf_of_le_left hle₂, inf_of_le_left hle₁] at h12
  exact h12.symm

end Lift

section Product

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

theorem isPComponent_fst {L : Subgroup (X × Y)} (hL : IsPComponent 2 L)
    (hleft : L = (L.map (MonoidHom.fst X Y)).prod ⊥) :
    IsPComponent 2 (L.map (MonoidHom.fst X Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := (⊤ : Subgroup X).prod (⊥ : Subgroup Y)
  have : N.Normal := Subgroup.prod_normal _ _
  have hLN : L ≤ N := hleft.le.trans (Subgroup.prod_mono le_top le_rfl)
  let e : N ≃* X :=
    (CatalogueBProjectiveInvolutionProduct.leftFactorEquiv (⊤ : Subgroup X)).trans
      Subgroup.topEquiv
  have h1 := CatalogueBFixedCentralQuotient.pComponent_restrict_normal 2 N L hLN hL
  have h2 := CatalogueBAlternating.pComponent_map_equiv 2 e _ h1
  convert h2 using 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hLN hz⟩, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem isPComponent_snd {L : Subgroup (X × Y)} (hL : IsPComponent 2 L)
    (hright : L = (⊥ : Subgroup X).prod (L.map (MonoidHom.snd X Y))) :
    IsPComponent 2 (L.map (MonoidHom.snd X Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := (⊥ : Subgroup X).prod (⊤ : Subgroup Y)
  have : N.Normal := Subgroup.prod_normal _ _
  have hLN : L ≤ N := hright.le.trans (Subgroup.prod_mono le_rfl le_top)
  let e : N ≃* Y :=
    (CatalogueBProjectiveInvolutionProduct.rightFactorEquiv (⊤ : Subgroup Y)).trans
      Subgroup.topEquiv
  have h1 := CatalogueBFixedCentralQuotient.pComponent_restrict_normal 2 N L hLN hL
  have h2 := CatalogueBAlternating.pComponent_map_equiv 2 e _ h1
  convert h2 using 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hLN hz⟩, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

end Product

theorem two_le_of_two_pComponents_prod {F : Type*} [Field F] [Finite F] {r s : ℕ} (hr : 1 ≤ r)
    (hs : 1 ≤ s) {L₁ L₂ : Subgroup (GL (Fin r) F × GL (Fin s) F)} (h₁ : IsPComponent 2 L₁)
    (h₂ : IsPComponent 2 L₂) (hne : L₁ ≠ L₂) : 2 ≤ r ∧ 2 ≤ s := by
  have cl := fun {t : ℕ} (ht : 1 ≤ t) (L : Subgroup (GL (Fin t) F)) (hL : IsPComponent 2 L) =>
    CatalogueBGeneralLinear.pComponent_classification t F ht 2 L hL
  rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 L₁ h₁ with
    hl₁ | hr₁ <;>
  rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 L₂ h₂ with
    hl₂ | hr₂
  · exfalso
    obtain ⟨-, -, -, e₁, -⟩ := cl hr _ (isPComponent_fst h₁ hl₁)
    obtain ⟨-, -, -, e₂, -⟩ := cl hr _ (isPComponent_fst h₂ hl₂)
    exact hne (by rw [hl₁, hl₂, e₁, e₂])
  · exact ⟨(cl hr _ (isPComponent_fst h₁ hl₁)).1, (cl hs _ (isPComponent_snd h₂ hr₂)).1⟩
  · exact ⟨(cl hr _ (isPComponent_fst h₂ hl₂)).1, (cl hs _ (isPComponent_snd h₁ hr₁)).1⟩
  · exfalso
    obtain ⟨-, -, -, e₁, -⟩ := cl hs _ (isPComponent_snd h₁ hr₁)
    obtain ⟨-, -, -, e₂, -⟩ := cl hs _ (isPComponent_snd h₂ hr₂)
    exact hne (by rw [hr₁, hr₂, e₁, e₂])

theorem split_of_two_pComponents {F : Type} [Field F] [Finite F] (htwo : (2 : F) ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) (A : GL (Fin n) F) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hinv : Matrix.ProjGenLinGroup.mk A ^ 2 = 1)
    {L₁ L₂ : Subgroup (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _))}
    (h₁ : IsPComponent 2 L₁) (h₂ : IsPComponent 2 L₂) (hL : L₁ ≠ L₂) :
    ∃ r s : ℕ, 2 ≤ r ∧ 2 ≤ s ∧ r + s = n := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have := ordinaryCentralizerProjection_range_normal A
  have := projectiveCentralizerModuloOrdinary_solvable A
  have hc : (ordinaryCentralizerProjection A).ker ≤ center (centralizer ({A} : Set _)) := by
    have := ordinaryCentralizerProjection_rangeRestrict_kernel_central A
    rwa [MonoidHom.ker_rangeRestrict] at this
  obtain ⟨M₁, M₂, hM₁, hM₂, hM⟩ :=
    exists_pComponent_lifts (ordinaryCentralizerProjection A) hc h₁ h₂ hL
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinv
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, -, hr, hs, hrs, e, -⟩ :=
      square_projective_centralizer_structure n hn A lambda htwo hne hsq hsquare
    obtain ⟨h1, h2⟩ := two_le_of_two_pComponents_prod hr hs
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hM₁)
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hM₂)
      (fun h => hM (map_injective e.injective h))
    exact ⟨_, _, h1, h2, hrs⟩
  · exfalso
    have : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    have : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      quadraticExtension_finite lambda.val
    have hm := (CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A lambda hsq
      hsquare).2
    let e := CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq
    obtain ⟨-, -, -, k₁, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ _ hm 2 _
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hM₁)
    obtain ⟨-, -, -, k₂, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ _ hm 2 _
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hM₂)
    exact hM (map_injective e.injective (k₁.trans k₂.symm))

section Normal

variable {M Y : Type*} [Group M] [Finite M] [Group Y] [Finite Y]

theorem isPComponent_map_of_normal (φ : M →* Y) (hφ : Function.Injective φ) [φ.range.Normal]
    {x : M} {L : Subgroup M} (hL : L ≤ centralizer ({x} : Set M))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set M)))) :
    L.map φ ≤ centralizer ({φ x} : Set Y) ∧
      IsPComponent 2 ((L.map φ).subgroupOf (centralizer ({φ x} : Set Y))) := by
  set e : M ≃* φ.range := MonoidHom.ofInjective hφ with he
  have hex : ∀ m : M, ((e m : φ.range) : Y) = φ m := fun m => rfl
  have hLe := (isPComponent_subgroupOf_map_iff e hL).mp hLc
  rw [map_centralizer_singleton_equiv] at hLe
  have hLR : L.map φ ≤ φ.range := map_le_range φ L
  have hLC : L.map φ ≤ centralizer ({φ x} : Set Y) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (hL hm)]
  refine ⟨hLC, isPComponent_subgroupOf_extend hLC hLR ?_⟩
  have h1 : (L.map φ).subgroupOf φ.range = L.map e.toMonoidHom := by
    ext ⟨y, hy⟩
    simp only [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨m, hm, hmy⟩
      exact ⟨m, hm, Subtype.ext ((hex m).trans hmy)⟩
    · rintro ⟨m, hm, hmy⟩
      exact ⟨m, hm, (hex m).symm.trans (congrArg Subtype.val hmy)⟩
  have h2 : (centralizer ({φ x} : Set Y)).subgroupOf φ.range =
      centralizer ({e x} : Set φ.range) := by
    ext z
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact Subtype.ext (by simpa [hex] using h)
    · intro h
      simpa [hex] using congrArg Subtype.val h
  rw [h1, h2]
  exact hLe

end Normal

theorem projToPGL_range_normal (n : ℕ) (F : Type) [Field F] :
    (CatFactsL4U4.projToPGL n F).range.Normal := by
  constructor
  rintro _ ⟨y, rfl⟩ g
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have hA : (A : GL (Fin n) F) ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) F →* GL (Fin n) F).range := by
    rw [← statedSL_eq_range_toGL]
    exact A.2
  obtain ⟨A₀, hA₀⟩ := hA
  have hdet : ((B * (A : GL (Fin n) F) * B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      1 := by
    rw [← hA₀]
    simp only [Units.val_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.toGL]
    rw [mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one, one_mul]
    exact A₀.2
  have hmem : B * (A : GL (Fin n) F) * B⁻¹ ∈ StatedSL n F := by
    have h : B * (A : GL (Fin n) F) * B⁻¹ ∈ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin n) F →* GL (Fin n) F).range := ⟨⟨_, hdet⟩, Units.ext rfl⟩
    rwa [← statedSL_eq_range_toGL] at h
  refine ⟨QuotientGroup.mk ⟨_, hmem⟩, ?_⟩
  rw [CatFactsL4U4.projToPGL_mk, CatFactsL4U4.projToPGL_mk]
  simp only [map_mul, map_inv]

theorem two_ne_zero_of_odd_natCard {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro h
  have := (FiniteField.even_card_iff_char_two (F := F)).mp h
  rw [← Nat.card_eq_fintype_card] at this
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr this)

theorem PairConfig.exists_pgl {F : Type} [Field F] [Finite F] {n : ℕ}
    {x : StatedProj (StatedSL n F)} {K K' : Subgroup (StatedProj (StatedSL n F))}
    (hc : PairConfig _ x K K') :
    ∃ A : GL (Fin n) F, CatFactsL4U4.projToPGL n F x = Matrix.ProjGenLinGroup.mk A ∧
      Matrix.ProjGenLinGroup.mk A ≠ 1 ∧ Matrix.ProjGenLinGroup.mk A ^ 2 = 1 ∧
      ∃ L₁ L₂ : Subgroup (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _)),
        IsPComponent 2 L₁ ∧ IsPComponent 2 L₂ ∧ L₁ ≠ L₂ := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  set φ := CatFactsL4U4.projToPGL n F with hφdef
  have hφ : Function.Injective φ := CatFactsL4U4.projToPGL_injective n
  have := projToPGL_range_normal n F
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (φ x)
  have hx2 : x ^ 2 = 1 := by rw [← hc.orderOf_x, pow_orderOf_eq_one]
  refine ⟨A, hA.symm, ?_, ?_, ?_⟩
  · rw [hA]
    intro h
    have h1 : x = 1 := hφ (h.trans (map_one φ).symm)
    have := hc.orderOf_x
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  · rw [hA, ← map_pow, hx2, map_one]
  obtain ⟨-, hK⟩ := isPComponent_map_of_normal φ hφ hc.K_le hc.isPComponent_K
  obtain ⟨hK'le, hK'⟩ := isPComponent_map_of_normal φ hφ hc.K'_le hc.isPComponent_K'
  have hKle : K.map φ ≤ centralizer ({φ x} : Set _) :=
    (isPComponent_map_of_normal φ hφ hc.K_le hc.isPComponent_K).1
  rw [← hA] at hK hK' hKle hK'le
  refine ⟨_, _, hK, hK', fun h => hc.ne ?_⟩
  have h1 := subgroupOf_inj.mp h
  rw [inf_of_le_left hKle, inf_of_le_left hK'le] at h1
  exact map_injective hφ h1

theorem pairConfig_psl_three_false {F : Type} [Field F] [Finite F] (htwo : (2 : F) ≠ 0)
    {x : StatedProj (StatedSL 3 F)} {K K' : Subgroup (StatedProj (StatedSL 3 F))}
    (hc : PairConfig _ x K K') : False := by
  obtain ⟨A, -, hne, hinv, L₁, L₂, h₁, h₂, hL⟩ := hc.exists_pgl
  obtain ⟨r, s, hr, hs, hrs⟩ := split_of_two_pComponents htwo (by norm_num) A hne hinv h₁ h₂ hL
  omega

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

include c in
theorem false_of_psl_three {p f : ℕ} (hp2 : p ≠ 2)
    (hG : StatedClassicalModel ↥(generalizedFitting H) .PSL 3 p f) : False := by
  obtain ⟨⟨hp, -, -⟩, F, _, _, hF, ⟨φ⟩⟩ := hG
  have : Finite (StatedProj (StatedSL 3 F)) := Finite.of_equiv _ φ.toEquiv
  have htwo : (2 : F) ≠ 0 := by
    have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
    exact two_ne_zero_of_odd_natCard hodd
  exact pairConfig_psl_three_false htwo (c.pairConfig φ)

end Config

end CFSG.ComponentClassification.Sp4Rec
