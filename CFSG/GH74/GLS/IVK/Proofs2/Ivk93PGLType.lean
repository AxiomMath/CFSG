module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinSL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGL

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBGeneralLinear
open scoped MatrixGroups

theorem ivk93l_lift_map {F : Type} [Field F] [Finite F] {n : ℕ} [Nonempty (Fin n)]
    (A : GL (Fin n) F)
    {M : Subgroup (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _))} (hM : IsPComponent 2 M) :
    ∃ L : Subgroup (centralizer ({A} : Set _)), IsPComponent 2 L ∧
      L.map (ordinaryCentralizerProjection A) = M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Matrix.ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  have := ordinaryCentralizerProjection_range_normal A
  have := projectiveCentralizerModuloOrdinary_solvable A
  set f := ordinaryCentralizerProjection A with hf
  have hc : f.rangeRestrict.ker ≤ center (centralizer ({A} : Set _)) :=
    ordinaryCentralizerProjection_rangeRestrict_kernel_central A
  obtain ⟨hle, hr⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2 f.range M hM
  obtain ⟨L, hL, hmap, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2
    f.rangeRestrict f.rangeRestrict_surjective hc _ hr
  refine ⟨L, hL, ?_⟩
  have h1 : L.map f = (L.map f.rangeRestrict).map f.range.subtype := by
    rw [Subgroup.map_map]; rfl
  rw [h1, hmap, Subgroup.map_subgroupOf_eq_of_le hle]

section Blocks

variable {F : Type} [Field F] [Finite F] {X : Type*} [Group X] {r s : ℕ}

theorem ivk93l_block (hr : 1 ≤ r) (hs : 1 ≤ s) (e : X ≃* GL (Fin r) F × GL (Fin s) F)
    {L : Subgroup X} (hL : IsPComponent 2 L) :
    (2 ≤ r ∧ L.map e.toMonoidHom = (specialLinearRange r F).prod ⊥) ∨
    (2 ≤ s ∧ L.map e.toMonoidHom =
      (⊥ : Subgroup (GL (Fin r) F)).prod (specialLinearRange s F)) := by
  have hL' := CatalogueBAlternating.pComponent_map_equiv 2 e L hL
  rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 _ hL' with
    hl | hr'
  · left
    obtain ⟨h2, -, -, heq, -⟩ := pComponent_classification r F hr 2 _ (isPComponent_fst hL' hl)
    exact ⟨h2, hl.trans (by rw [heq])⟩
  · right
    obtain ⟨h2, -, -, heq, -⟩ := pComponent_classification s F hs 2 _ (isPComponent_snd hL' hr')
    exact ⟨h2, hr'.trans (by rw [heq])⟩

theorem ivk93l_pair_block (hr : 1 ≤ r) (hs : 1 ≤ s) (e : X ≃* GL (Fin r) F × GL (Fin s) F)
    {L₁ L₂ : Subgroup X} (h₁ : IsPComponent 2 L₁) (h₂ : IsPComponent 2 L₂) (hne : L₁ ≠ L₂) :
    (2 ≤ r ∧ L₁.map e.toMonoidHom = (specialLinearRange r F).prod ⊥ ∧ 2 ≤ s ∧
      L₂.map e.toMonoidHom = (⊥ : Subgroup (GL (Fin r) F)).prod (specialLinearRange s F)) ∨
    (2 ≤ s ∧ L₁.map e.toMonoidHom = (⊥ : Subgroup (GL (Fin r) F)).prod (specialLinearRange s F) ∧
      2 ≤ r ∧ L₂.map e.toMonoidHom = (specialLinearRange r F).prod ⊥) := by
  rcases ivk93l_block hr hs e h₁ with ⟨hr₁, e₁⟩ | ⟨hs₁, e₁⟩ <;>
  rcases ivk93l_block hr hs e h₂ with ⟨hr₂, e₂⟩ | ⟨hs₂, e₂⟩
  · exact absurd (Subgroup.map_injective e.injective (e₁.trans e₂.symm)) hne
  · exact Or.inl ⟨hr₁, e₁, hs₂, e₂⟩
  · exact Or.inr ⟨hs₁, e₁, hr₂, e₂⟩
  · exact absurd (Subgroup.map_injective e.injective (e₁.trans e₂.symm)) hne

omit [Finite F] in
theorem ivk93l_equiv_fst (e : X ≃* GL (Fin r) F × GL (Fin s) F) {K : Subgroup X}
    (hK : K.map e.toMonoidHom = (specialLinearRange r F).prod ⊥) : Nonempty (SL(r, F) ≃* ↥K) :=
  ⟨((K.equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr hK).trans
      ((CatalogueBProjectiveInvolutionProduct.leftFactorEquiv _).trans
        (rangeEquivSpecialLinear r F)))).symm⟩

omit [Finite F] in
theorem ivk93l_equiv_snd (e : X ≃* GL (Fin r) F × GL (Fin s) F) {K : Subgroup X}
    (hK : K.map e.toMonoidHom = (⊥ : Subgroup (GL (Fin r) F)).prod (specialLinearRange s F)) :
    Nonempty (SL(s, F) ≃* ↥K) :=
  ⟨((K.equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr hK).trans
      ((CatalogueBProjectiveInvolutionProduct.rightFactorEquiv _).trans
        (rangeEquivSpecialLinear s F)))).symm⟩

omit [Finite F] in
theorem ivk93l_inf_ker_fst {Y : Type*} [Group Y] (hs : 1 ≤ s)
    (e : X ≃* GL (Fin r) F × GL (Fin s) F) (σ : Fˣ →* X)
    (hσ : ∀ c, e (σ c) =
      (Matrix.GeneralLinearGroup.scalar (Fin r) c, Matrix.GeneralLinearGroup.scalar (Fin s) c))
    (g : X →* Y) (hg : g.ker ≤ σ.range) {K : Subgroup X}
    (hK : K.map e.toMonoidHom = (specialLinearRange r F).prod ⊥) : K ⊓ g.ker = ⊥ := by
  rw [eq_bot_iff]
  rintro k ⟨hkK, hkg⟩
  obtain ⟨c, rfl⟩ := hg hkg
  have h1 : e (σ c) ∈ K.map e.toMonoidHom := ⟨σ c, hkK, rfl⟩
  rw [hK, hσ] at h1
  have h2 : Matrix.GeneralLinearGroup.scalar (Fin s) c = 1 := Subgroup.mem_bot.mp h1.2
  have : c = 1 := ivk95l_scalar_eq_one hs h2
  rw [this, map_one]
  exact Subgroup.one_mem _

omit [Finite F] in
theorem ivk93l_inf_ker_snd {Y : Type*} [Group Y] (hr : 1 ≤ r)
    (e : X ≃* GL (Fin r) F × GL (Fin s) F) (σ : Fˣ →* X)
    (hσ : ∀ c, e (σ c) =
      (Matrix.GeneralLinearGroup.scalar (Fin r) c, Matrix.GeneralLinearGroup.scalar (Fin s) c))
    (g : X →* Y) (hg : g.ker ≤ σ.range) {K : Subgroup X}
    (hK : K.map e.toMonoidHom = (⊥ : Subgroup (GL (Fin r) F)).prod (specialLinearRange s F)) :
    K ⊓ g.ker = ⊥ := by
  rw [eq_bot_iff]
  rintro k ⟨hkK, hkg⟩
  obtain ⟨c, rfl⟩ := hg hkg
  have h1 : e (σ c) ∈ K.map e.toMonoidHom := ⟨σ c, hkK, rfl⟩
  rw [hK, hσ] at h1
  have h2 : Matrix.GeneralLinearGroup.scalar (Fin r) c = 1 := Subgroup.mem_bot.mp h1.1
  have : c = 1 := ivk95l_scalar_eq_one hr h2
  rw [this, map_one]
  exact Subgroup.one_mem _

end Blocks

theorem ivk93l_equiv_map {X Y : Type*} [Group X] [Group Y] (g : X →* Y) {K : Subgroup X}
    (hK : K ⊓ g.ker = ⊥) : Nonempty (↥K ≃* ↥(K.map g)) := by
  refine ⟨MulEquiv.ofBijective (g.subgroupMap K) ⟨?_, g.subgroupMap_surjective K⟩⟩
  rw [injective_iff_map_eq_one]
  intro k hk
  have h1 : g (k : X) = 1 := congrArg Subtype.val hk
  have h2 : (k : X) ∈ K ⊓ g.ker := ⟨k.2, h1⟩
  rw [hK, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

theorem ivk93l_pgl_two_blocks {F : Type} [Field F] [Finite F] (htwo : (2 : F) ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) (A : GL (Fin n) F) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hinv : Matrix.ProjGenLinGroup.mk A ^ 2 = 1)
    {M₁ M₂ : Subgroup (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _))}
    (h₁ : IsPComponent 2 M₁) (h₂ : IsPComponent 2 M₂) (hM : M₁ ≠ M₂) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a + b = n ∧ Nonempty (SL(a, F) ≃* ↥M₁) ∧
      Nonempty (SL(b, F) ≃* ↥M₂) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨L₁, hL₁, hm₁⟩ := ivk93l_lift_map A h₁
  obtain ⟨L₂, hL₂, hm₂⟩ := ivk93l_lift_map A h₂
  have hLne : L₁ ≠ L₂ := fun h => hM (by rw [← hm₁, ← hm₂, h])
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinv
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, -, hr, hs, hrs, e, -, hscal, -⟩ :=
      square_projective_centralizer_structure n hn A lambda htwo hne hsq hsquare
    have hker : (ordinaryCentralizerProjection A).ker ≤ (ordinaryCentralizerScalar A).range :=
      (ordinaryCentralizerProjection_kernel_eq_scalar A).le
    rcases ivk93l_pair_block hr hs e hL₁ hL₂ hLne with
      ⟨h2r, e₁, h2s, e₂⟩ | ⟨h2s, e₁, h2r, e₂⟩
    · refine ⟨_, _, h2r, h2s, hrs, ?_, ?_⟩
      · obtain ⟨φ⟩ := ivk93l_equiv_fst e e₁
        obtain ⟨ψ⟩ := ivk93l_equiv_map (ordinaryCentralizerProjection A)
          (ivk93l_inf_ker_fst hs e (ordinaryCentralizerScalar A) hscal _ hker e₁)
        exact ⟨φ.trans (ψ.trans (MulEquiv.subgroupCongr hm₁))⟩
      · obtain ⟨φ⟩ := ivk93l_equiv_snd e e₂
        obtain ⟨ψ⟩ := ivk93l_equiv_map (ordinaryCentralizerProjection A)
          (ivk93l_inf_ker_snd hr e (ordinaryCentralizerScalar A) hscal _ hker e₂)
        exact ⟨φ.trans (ψ.trans (MulEquiv.subgroupCongr hm₂))⟩
    · refine ⟨_, _, h2s, h2r, by omega, ?_, ?_⟩
      · obtain ⟨φ⟩ := ivk93l_equiv_snd e e₁
        obtain ⟨ψ⟩ := ivk93l_equiv_map (ordinaryCentralizerProjection A)
          (ivk93l_inf_ker_snd hr e (ordinaryCentralizerScalar A) hscal _ hker e₁)
        exact ⟨φ.trans (ψ.trans (MulEquiv.subgroupCongr hm₁))⟩
      · obtain ⟨φ⟩ := ivk93l_equiv_fst e e₂
        obtain ⟨ψ⟩ := ivk93l_equiv_map (ordinaryCentralizerProjection A)
          (ivk93l_inf_ker_fst hs e (ordinaryCentralizerScalar A) hscal _ hker e₂)
        exact ⟨φ.trans (ψ.trans (MulEquiv.subgroupCongr hm₂))⟩
  · exfalso
    have : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    have : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      quadraticExtension_finite lambda.val
    have hm := (CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A lambda hsq
      hsquare).2
    let e := CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq
    obtain ⟨-, -, -, k₁, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ _ hm 2 _
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hL₁)
    obtain ⟨-, -, -, k₂, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ _ hm 2 _
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hL₂)
    exact hLne (map_injective e.injective (k₁.trans k₂.symm))

theorem Ivk93Cfg.two_blocks {F : Type} [Field F] [Finite F] (htwo : (2 : F) ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) {x : StatedProj (StatedSL n F)} {q : ℕ}
    {L₁ L₂ : Subgroup (StatedProj (StatedSL n F))} (h : Ivk93Cfg x q L₁ L₂) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a + b = n ∧ Nonempty (SL(a, F) ≃* ↥L₁) ∧
      Nonempty (SL(b, F) ≃* ↥L₂) := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  set φ := CatFactsL4U4.projToPGL n F with hφdef
  have hφ : Function.Injective φ := CatFactsL4U4.projToPGL_injective n
  have := projToPGL_range_normal n F
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (φ x)
  have hx2 : x ^ 2 = 1 := by rw [← h.ord, pow_orderOf_eq_one]
  have hne : Matrix.ProjGenLinGroup.mk A ≠ 1 := by
    rw [hA]
    intro h1
    exact h.ne_one (hφ (h1.trans (map_one φ).symm))
  have hinv : Matrix.ProjGenLinGroup.mk A ^ 2 = 1 := by
    rw [hA, ← map_pow, hx2, map_one]
  obtain ⟨hK₁le, hK₁⟩ := isPComponent_map_of_normal φ hφ h.le₁ h.comp₁.2
  obtain ⟨hK₂le, hK₂⟩ := isPComponent_map_of_normal φ hφ h.le₂ h.comp₂.2
  rw [← hA] at hK₁ hK₂ hK₁le hK₂le
  have hMne : (L₁.map φ).subgroupOf (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _)) ≠
      (L₂.map φ).subgroupOf (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _)) := by
    intro heq
    apply h.ne
    have h1 := subgroupOf_inj.mp heq
    rw [inf_of_le_left hK₁le, inf_of_le_left hK₂le] at h1
    exact map_injective hφ h1
  obtain ⟨a, b, ha, hb, hab, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    ivk93l_pgl_two_blocks htwo hn A hne hinv hK₁ hK₂ hMne
  exact ⟨a, b, ha, hb, hab,
    ⟨e₁.trans ((Subgroup.subgroupOfEquivOfLe hK₁le).trans
      (L₁.equivMapOfInjective φ hφ).symm)⟩,
    ⟨e₂.trans ((Subgroup.subgroupOfEquivOfLe hK₂le).trans
      (L₂.equivMapOfInjective φ hφ).symm)⟩⟩

theorem Ivk93Cfg.five_le_of_equiv_sl2 {J : Type} [Group J] [Finite J] {x : J} {q : ℕ}
    {L₁ L₂ : Subgroup J} (h : Ivk93Cfg x q L₁ L₂) {F : Type} [Field F] [Finite F]
    (e : SL(2, F) ≃* ↥L₁) : 5 ≤ Nat.card F := by
  by_contra hlt
  have h1 : Nat.card ↥L₁ = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
  have h2 := h.card_ge₁
  have h3 := sl2_card_mono (show Nat.card F ≤ 4 by omega)
  norm_num at h3
  omega

end CFSG.GH74.GLS.IVK.Proofs2
