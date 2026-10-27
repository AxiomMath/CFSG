module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGL

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB

theorem exists_of_two_pComponents_prod {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (hX : ∀ J₁ J₂ : Subgroup X, IsPComponent 2 J₁ → IsPComponent 2 J₂ → J₁ = J₂)
    (hY : ∀ J₁ J₂ : Subgroup Y, IsPComponent 2 J₁ → IsPComponent 2 J₂ → J₁ = J₂)
    {L₁ L₂ : Subgroup (X × Y)} (h₁ : IsPComponent 2 L₁) (h₂ : IsPComponent 2 L₂)
    (hne : L₁ ≠ L₂) :
    (∃ J : Subgroup X, IsPComponent 2 J) ∧ ∃ J : Subgroup Y, IsPComponent 2 J := by
  rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 L₁ h₁ with
    hl₁ | hr₁ <;>
  rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 L₂ h₂ with
    hl₂ | hr₂
  · exact (hne (by rw [hl₁, hl₂, hX _ _ (isPComponent_fst h₁ hl₁) (isPComponent_fst h₂ hl₂)])).elim
  · exact ⟨⟨_, isPComponent_fst h₁ hl₁⟩, ⟨_, isPComponent_snd h₂ hr₂⟩⟩
  · exact ⟨⟨_, isPComponent_fst h₂ hl₂⟩, ⟨_, isPComponent_snd h₁ hr₁⟩⟩
  · exact (hne (by rw [hr₁, hr₂, hY _ _ (isPComponent_snd h₁ hr₁) (isPComponent_snd h₂ hr₂)])).elim

variable {p f : ℕ} {E : Type} [Field E]

theorem sesqUnitary_pComponent_eq {W : Type*} [AddCommGroup W] [Module E W]
    (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E W] (hW : 1 ≤ finrank E W)
    {C : W →ₛₗ[h.bar] W →ₗ[E] E} (hC : C.IsSymm) (hl : C.SeparatingLeft)
    {J₁ J₂ : Subgroup (sesqUnitaryGroup C)} (h₁ : IsPComponent 2 J₁) (h₂ : IsPComponent 2 J₂) :
    2 ≤ finrank E W ∧ J₁ = J₂ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  set e := sesqUnitaryIsometryEquiv h C
  have k₁ := CatalogueBAlternating.pComponent_map_equiv 2 e _ h₁
  have k₂ := CatalogueBAlternating.pComponent_map_equiv 2 e _ h₂
  obtain ⟨-, hsmall, hbig⟩ := CatalogueBUnitaryTwo.odd_unitary_all_dimensional_isometry_p_components
    p f hp h.one_le h.card_eq_sq C hC (nondegenerate_of_isSymm hC hl) hW
  by_cases hs : finrank E W = 1 ∨ (finrank E W, p ^ f) = (2, 3)
  · exact ((hsmall hs).2 2 _ k₁).elim
  · push Not at hs
    have e₁ := (hbig hs).2 2 Nat.prime_two _ k₁
    have e₂ := (hbig hs).2 2 Nat.prime_two _ k₂
    exact ⟨by omega, map_injective e.injective (e₁.trans e₂.symm)⟩

variable {V : Type} [AddCommGroup V] [Module E V]

theorem unitary_dim_of_two_pComponents (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {M₁ M₂ : Subgroup (centralizer
      ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} : Set (sesqProjUnitary h B)))}
    (h₁ : IsPComponent 2 M₁) (h₂ : IsPComponent 2 M₂) (hne : M₁ ≠ M₂) :
    4 ≤ finrank E V ∨ Even (finrank E V) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hM, hcompl, hsplit, hpaired, -, hnormal, hindex, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  rw [← range_centralizerImageHom] at hnormal hindex
  have := hnormal
  have := CatalogueRelativeB.quotient_solvable_of_index_le_two _ hindex
  obtain ⟨N₁, N₂, hN₁, hN₂, hNne⟩ := exists_pComponent_lifts (centralizerImageHom A)
    (ker_centralizerImageHom_le_center A) h₁ h₂ hne
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  rcases hN with hN | hN
  · left
    obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    have hP1 := Submodule.one_le_finrank_iff.mpr hP
    have hM1 := Submodule.one_le_finrank_iff.mpr hM
    obtain ⟨⟨J, hJ⟩, ⟨J', hJ'⟩⟩ := exists_of_two_pComponents_prod
      (fun J₁ J₂ k₁ k₂ => (sesqUnitary_pComponent_eq h hp hP1 (hsymm _) hlP k₁ k₂).2)
      (fun J₁ J₂ k₁ k₂ => (sesqUnitary_pComponent_eq h hp hM1 (hsymm _) hlM k₁ k₂).2)
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hN₁)
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hN₂)
      (fun k => hNne (map_injective e.injective k))
    have d₁ := (sesqUnitary_pComponent_eq h hp hP1 (hsymm _) hlP hJ hJ).1
    have d₂ := (sesqUnitary_pComponent_eq h hp hM1 (hsymm _) hlM hJ' hJ').1
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  · right
    obtain ⟨-, -, -, h2, -⟩ := hpaired hN
    exact ⟨finrank E (eigenPlus l (unitaryOp A)), by omega⟩

theorem PairConfig.exists_unitary {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    {x : StatedProj (StatedSU (2 * r + ε) (p ^ f) K)}
    {L L' : Subgroup (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))}
    (hc : PairConfig _ x L L') :
    ∃ hud : UnitaryFieldData p f K, ∃ A : sesqUnitaryGroup (hypForm hud r ε),
      orderOf (QuotientGroup.mk A : sesqProjUnitary hud (hypForm hud r ε)) = 2 ∧
      ∃ M₁ M₂ : Subgroup (centralizer
          ({QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε)) A} :
            Set (sesqProjUnitary hud (hypForm hud r ε)))),
        IsPComponent 2 M₁ ∧ IsPComponent 2 M₂ ∧ M₁ ≠ M₂ := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud hr hε).1
  set θ := (hypPSUEquivStatedProj hud hR (by omega)).symm
  set ι : hypPSU hud r ε →* sesqProjUnitary hud (hypForm hud r ε) :=
    (projSpecial hud (hypForm hud r ε)).subtype.comp (hypModelEquiv hud).toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp (hypModelEquiv hud).injective
  set φ := ι.comp θ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := hι.comp θ.injective
  have hrange : φ.range = projSpecial hud (hypForm hud r ε) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hypModelEquiv hud (θ y)).2
    · intro hz
      obtain ⟨w, hw⟩ := (hypModelEquiv hud).surjective ⟨z, hz⟩
      refine ⟨θ.symm w, ?_⟩
      rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        hιdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hw]
      rfl
  have : φ.range.Normal := by
    rw [hrange]
    infer_instance
  have hK₁ := isPComponent_map_of_normal φ hφ hc.K_le hc.isPComponent_K
  have hK₂ := isPComponent_map_of_normal φ hφ hc.K'_le hc.isPComponent_K'
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (sesqNormOneScalars hud (hypForm hud r ε)) (φ x)
  rw [← hA] at hK₁ hK₂
  refine ⟨hud, A, ?_, _, _, hK₁.2, hK₂.2, fun k => hc.ne ?_⟩
  · change orderOf ((QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε))) A) = 2
    rw [hA, orderOf_injective φ hφ x, hc.orderOf_x]
  · have h1 := subgroupOf_inj.mp k
    rw [inf_of_le_left hK₁.1, inf_of_le_left hK₂.1] at h1
    exact map_injective hφ h1

theorem pairConfig_psu_three_false {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    {x : StatedProj (StatedSU (2 * 1 + 1) (p ^ f) K)}
    {L L' : Subgroup (StatedProj (StatedSU (2 * 1 + 1) (p ^ f) K))}
    (hc : PairConfig _ x L L') : False := by
  obtain ⟨hud, A, hA, M₁, M₂, h₁, h₂, hne⟩ := hc.exists_unitary hp hf hK le_rfl le_rfl
  have : Finite K := hud.finite
  have hdim : finrank K (HypIndex 1 1 → K) = 3 := UnitaryHigher.finrank_hypIndex_fun
  rcases unitary_dim_of_two_pComponents hud hp2 (by omega) (hypForm_isSymm hud)
    (hypForm_separatingLeft hud) hA h₁ h₂ hne with h | ⟨k, hk⟩ <;> omega

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

include c in
theorem false_of_psu_three {p f : ℕ} (hp2 : p ≠ 2)
    (hG : StatedClassicalModel ↥(generalizedFitting H) .PSU 3 p f) : False := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨φ⟩⟩ := hG
  have : Finite (StatedProj (StatedSU (2 * 1 + 1) (p ^ f) K)) := Finite.of_equiv _ φ.toEquiv
  exact pairConfig_psu_three_false hp hp2 hf hK (c.pairConfig (M := StatedProj
    (StatedSU (2 * 1 + 1) (p ^ f) K)) φ)

end Config

end CFSG.ComponentClassification.Sp4Rec
