module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviModelPieces
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedDMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviModelInputs

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

local instance f4PilotGraphTwistedLeviModelMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Block

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem barSU6_mem_block {g : uGroup6 h}
    (hg : gramSUToSL h _ g ∈ blockSpecialLinear (K := F) lin6BlockA) :
    gramSUToSL h _ (barSU6 h g) ∈ blockSpecialLinear (K := F) lin6BlockA := by
  intro i j hij
  have e := hg i j hij
  rw [coe_gramSUToSL] at e ⊢
  rw [coe_barSU6, Matrix.map_apply, e]
  by_cases hij' : i = j
  · subst hij'
    simp
  · simp [Matrix.one_apply_ne hij']

theorem uEmbed6_mem_block {s : StatedSp 3 h.fixedField}
    (hs : sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA) :
    gramSUToSL h _ (uEmbed6 h s) ∈ blockSpecialLinear (K := F) lin6BlockA := by
  intro i j hij
  have e := hs i j hij
  rw [coe_gramSUToSL, coe_uEmbed6, Matrix.map_apply, e]
  by_cases hij' : i = j
  · subst hij'
    simp
  · simp [Matrix.one_apply_ne hij']

theorem coe_twParamEquiv_barSU6
    [Finite F] [CharP F 2] (g : uGroup6 h) :
    ((twParamEquiv h (barSU6 h g) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
      fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom
        ((twParamEquiv h g : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) := by
  rw [coe_twParamEquiv, coe_twParamEquiv, sigmaHat_twParamHom]

end Block

section Agree

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {h : UnitaryFieldData 2 f F}
  {ε : h.fixedField ≃+* K}

theorem twAgree_of_rigidity (hR : TwistedA3MatrixRigidityInput) (hf : 2 ≤ f) {t : G}
    {e₁ : L ≃* adjointGroup .F4 K}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hrX : ΦX.range = neighbourCore e₁ .X)
    (hkX : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    (hcX : ∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        t * ΦX x * t⁻¹ = ΦX y)
    (hnX : IsLeviNormalizedU h ε e₁ ΦX)
    {ΦY : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes →* G}
    (hcY : ∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes,
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        t * ΦY x * t⁻¹ = ΦY y)
    (hYM : ∀ x, twLeviRestrict ΦY one_two_subset_Y x ∈ pieceCore e₁ {1, 2})
    (hP : ∀ (x : twLevi F h.barEquiv.toRingHom {1, 2}) (s : StatedSp 3 h.fixedField),
      sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
      ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x →
      twLeviRestrict ΦY one_two_subset_Y x = levi6Hom e₁ ε s) :
    (∀ x : twLevi F h.barEquiv.toRingHom {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
        twLeviRestrict ΦY one_two_subset_Y x) ∨
      (∀ x y : twLevi F h.barEquiv.toRingHom {1, 2},
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          twLeviRestrict ΦX one_two_subset_X x = twLeviRestrict ΦY one_two_subset_Y y) := by
  obtain ⟨SB, hSB⟩ : ∃ SB : Subgroup (uGroup6 h), SB = (blockSpecialLinear (K := F)
      lin6BlockA).comap (gramSUToSL h ((graphGram6 F : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F)) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : uGroup6 h →* G, Ψ = ΦX.comp (twParamEquiv h).toMonoidHom :=
    ⟨_, rfl⟩
  have hSBmem : ∀ g, g ∈ SB ↔ gramSUToSL h _ g ∈ blockSpecialLinear (K := F) lin6BlockA := by
    intro g
    rw [hSB]
    rfl
  have hΨapp : ∀ g, Ψ g = ΦX (twParamEquiv h g) := by
    intro g
    rw [hΨ]
    rfl
  have hΨi : Function.Injective (Ψ.comp SB.subtype) := by
    subst hΨ hSB
    exact twParam_block_injective hkX
  have hΨr : (Ψ.comp SB.subtype).range = pieceCore e₁ {1, 2} := by
    rw [MonoidHom.range_comp, range_subtype, pieceCore_one_two_eq_map hf hrX hkX hnX, hΨ, hSB]
  have hle : (twLeviRestrict ΦY one_two_subset_Y).range ≤ (Ψ.comp SB.subtype).range := by
    rintro _ ⟨x, rfl⟩
    rw [hΨr]
    exact hYM x
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : twLevi F h.barEquiv.toRingHom {1, 2} →* (Ψ.comp SB.subtype).range,
      ∀ x, (θ₀ x : G) = twLeviRestrict ΦY one_two_subset_Y x :=
    ⟨(Subgroup.inclusion hle).comp (twLeviRestrict ΦY one_two_subset_Y).rangeRestrict,
      fun _ => rfl⟩
  obtain ⟨θ, hθSB, hkey⟩ : ∃ θ : twLevi F h.barEquiv.toRingHom {1, 2} →* uGroup6 h,
      (∀ x, θ x ∈ SB) ∧ ∀ x, Ψ (θ x) = twLeviRestrict ΦY one_two_subset_Y x := by
    refine ⟨SB.subtype.comp ((MonoidHom.ofInjective hΨi).symm.toMonoidHom.comp θ₀),
      fun x => (((MonoidHom.ofInjective hΨi).symm (θ₀ x)) : SB).2, fun x => ?_⟩
    have h1 := (MonoidHom.ofInjective hΨi).apply_symm_apply (θ₀ x)
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply, hθ₀] at h2
    exact h2
  have huniq : ∀ g g' : uGroup6 h, g ∈ SB → g' ∈ SB → Ψ g = Ψ g' → g = g' := by
    intro g g' hg hg' he
    have := hΨi (a₁ := ⟨g, hg⟩) (a₂ := ⟨g', hg'⟩) he
    exact congrArg Subtype.val this
  have htΨ : ∀ g, t * Ψ g * t⁻¹ = Ψ (barSU6 h g) := by
    intro g
    rw [hΨapp, hΨapp]
    exact hcX (twParamEquiv h g) (twParamEquiv h (barSU6 h g)) (coe_twParamEquiv_barSU6 h g)
  have hB : ∀ x, gramSUToSL h _ (θ x) ∈ blockSpecialLinear (K := F) lin6BlockA :=
    fun x => (hSBmem _).1 (hθSB x)
  have hPθ : ∀ (x : twLevi F h.barEquiv.toRingHom {1, 2}) (s : StatedSp 3 h.fixedField),
      sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
      ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x → θ x = uEmbed6 h s := by
    intro x s hs hx
    refine huniq _ _ (hθSB x) ((hSBmem _).2 (uEmbed6_mem_block h hs)) ?_
    rw [hkey, hP x s hs hx, hΨapp]
    exact (hnX s).symm
  have hσθ : ∀ x y : twLevi F h.barEquiv.toRingHom {1, 2},
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        θ y = barSU6 h (θ x) := by
    intro x y hxy
    refine huniq _ _ (hθSB y) ((hSBmem _).2 (barSU6_mem_block h (hB x))) ?_
    rw [hkey, ← htΨ, hkey, twLeviRestrict_apply, twLeviRestrict_apply]
    exact (hcY ⟨x, CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_Y x.2⟩
      ⟨y, CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_Y y.2⟩ hxy).symm
  rcases hR f hf F h θ hB hPθ hσθ with h1 | h2
  · refine .inl fun x => ?_
    refine Eq.trans ?_ ((hΨapp (θ x)).symm.trans (hkey x))
    rw [twLeviRestrict_apply]
    congr 1
    exact Subtype.ext (h1 x).symm
  · refine .inr fun x y hxy => ?_
    have e2 : ((twParamEquiv h (barSU6 h (θ y)) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x :=
      (h2 y).trans hxy
    have e3 : ((twParamEquiv h (θ y) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x := by
      have e4 := coe_twParamEquiv_barSU6 h (barSU6 h (θ y))
      rw [barSU6_barSU6, e2, sigmaHat_sigmaHat] at e4
      exact e4
    have e5 : (⟨(x : fixedGroup F h.barEquiv.toRingHom),
        CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_X x.2⟩ :
          twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) = twParamEquiv h (θ y) :=
      Subtype.ext e3.symm
    exact ((twLeviRestrict_apply ΦX one_two_subset_X x).trans (congrArg ΦX e5)).trans
      ((hΨapp (θ y)).symm.trans (hkey y))

end Agree

section Main

theorem barSU6_uEmbed6 {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)
    (s : StatedSp 3 h.fixedField) : barSU6 h (uEmbed6 h s) = uEmbed6 h s := by
  have hs : uEmbed6 h s ∈ fixedSubgroup (barSU6 h) := by
    rw [fixedSubgroup_barSU6]
    exact ⟨s, rfl⟩
  exact hs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {h : UnitaryFieldData 2 f F}

omit [Finite G] in
theorem twLeviRestrict_eq_levi6Hom_of_model (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {c : K}
    (hc : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0)
    {Θ : StatedOmega (StatedQuadMinus 4 K 1 c) ≃*
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes}
    (hΘ : ∀ g, ((Θ (omegaMinusBetaC K 1 c g) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom (Θ g))
    {s₀ : StatedSp 3 K} {e₁ e₂ : L ≃* adjointGroup .F4 K} {ε : h.fixedField ≃+* K}
    {ε' : K ≃+* K}
    (hε' : ∀ (sA : StatedSp 3 h.fixedField) (sD : StatedSp 3 K),
      sp6ToSL6 sA ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
      ((Θ (omegaMinusIota hK hf hc sD) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
          fixedGroup F h.barEquiv.toRingHom) =
        ((twParamEquiv h (uEmbed6 h sA) :
          twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
            fixedGroup F h.barEquiv.toRingHom) →
      levi6Hom e₁ ε sA = levi6Hom e₂ ε' (s₀ * sD * s₀⁻¹))
    {ΦY : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes →* G}
    (hnY : ∀ s, ΦY (Θ (omegaMinusIota hK hf hc s)) = levi6Hom e₂ ε' (s₀ * s * s₀⁻¹))
    (x : twLevi F h.barEquiv.toRingHom {1, 2}) (s : StatedSp 3 h.fixedField)
    (hs : sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA)
    (hx : ((twParamEquiv h (uEmbed6 h s) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x) :
    twLeviRestrict ΦY one_two_subset_Y x = levi6Hom e₁ ε s := by
  obtain ⟨y, hyx, hy⟩ : ∃ y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes,
      (y : fixedGroup F h.barEquiv.toRingHom) = x ∧ twLeviRestrict ΦY one_two_subset_Y x = ΦY y :=
    ⟨_, rfl, twLeviRestrict_apply ΦY one_two_subset_Y x⟩
  have hσy : sigmaHat h.barEquiv.toRingHom (y : fixedGroup F h.barEquiv.toRingHom) = y := by
    rw [hyx, ← hx, ← coe_twParamEquiv_barSU6, barSU6_uEmbed6]
  obtain ⟨z, hz⟩ := Θ.surjective y
  have hβ : omegaMinusBetaC K 1 c z = z := by
    apply Θ.injective
    apply Subtype.ext
    refine (hΘ z).trans ?_
    rw [hz]
    exact hσy
  have hfix : z ∈ (omegaMinusIota hK hf hc).range :=
    (range_omegaMinusIota hK hf hc).ge hβ
  obtain ⟨sD, hsD⟩ := hfix
  have hΘsD : Θ (omegaMinusIota hK hf hc sD) = y := by
    rw [hsD, hz]
  rw [hy, ← hΘsD, hnY]
  refine (hε' s sD hs ?_).symm
  rw [hΘsD, hyx, hx]

omit [Finite G] [Finite K] [CharP K 2] [Finite F] [CharP F 2]
  in
theorem commute_twLevi_of_symm {k : Type} [Field k] {θ : k →+* k} {M : Type} [Group M]
    (Θ : M ≃* twLevi k θ AmalgamNeighbour.Y.nodes) {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ AmalgamNeighbour.Y.nodes) {m : M}
    (hc : ∀ x : twLevi k θ AmalgamNeighbour.Y.nodes, (x : fixedGroup k θ) ∈ twLevi k θ J →
      Commute (Θ.symm x) m) (x : twLevi k θ J) :
    Commute (⟨x, CFSG.LieType.CurtisTits.levi_mono _ hJ x.2⟩ :
      twLevi k θ AmalgamNeighbour.Y.nodes) (Θ m) := by
  have h1 := (hc ⟨x, CFSG.LieType.CurtisTits.levi_mono _ hJ x.2⟩ x.2).map Θ.toMonoidHom
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using h1

theorem twistedE6GraphRowModelLeviInput_of_inputs (hR : TwistedA3MatrixRigidityInput)
    (hY : TwistedLeviPiModelInput) : TwistedE6GraphRowModelLeviInput := by
  intro G _ _ L K _ _ _ e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ e₂ he₂ F _ _ _ h ε ΦX hrX hkX hcX hnX
  obtain ⟨c, hc, Θ, hΘ, s₀, hT12, hT0, ⟨εX, hεX⟩, ⟨εY, hεY⟩⟩ :=
    @hY f hf F _ _ _ h K _ _ _ (‹CharP K 2› : CharP K CFSG.LieType.Ree.ReeTag.F4.prime)
      hw.card_eq ε
  obtain ⟨ε', hε'⟩ : ∃ ε' : K ≃+* K, ∀ (sA : StatedSp 3 h.fixedField) (sD : StatedSp 3 K),
      sp6ToSL6 sA ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
      ((Θ (omegaMinusIota hw.card_eq hf hc sD) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
          fixedGroup F h.barEquiv.toRingHom) =
        ((twParamEquiv h (uEmbed6 h sA) :
          twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
            fixedGroup F h.barEquiv.toRingHom) →
      levi6Hom e₁ ε sA = levi6Hom e₂ ε' (s₀ * sD * s₀⁻¹) := by
    rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h1 : e₁ = e := he₁
      obtain ⟨_, rfl⟩ := he₂
      subst h1
      refine ⟨εX, fun sA sD hb hx => ?_⟩
      simp only [levi6Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
        MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
      rw [hεX sA sD hb hx]
    · obtain ⟨_, rfl⟩ := he₁
      have h2 : e₂ = e := he₂
      subst h2
      refine ⟨εY, fun sA sD hb hx => ?_⟩
      simp only [levi6Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
        MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
      rw [hεY sA sD hb hx]
  refine ⟨c, hc, Θ, hΘ, ε', s₀, fun ΦY hrY hiY hcY hnY => ?_⟩
  have hrX' : ΦX.range = neighbourCore e₁ .X := hrX.trans (neighbourFrame_eq he₁).1
  have hrY' : ΦY.range = neighbourCore e₂ .X := hrY.trans (neighbourFrame_eq he₂).1
  obtain ⟨t₀, ht₀θ, ht₀⟩ := exists_barFixed_unit_sq_ne_one h hf
  have hθ : ∀ c, h.barEquiv.toRingHom (h.barEquiv.toRingHom c) = c := h.bar_bar
  obtain ⟨ι', hι'⟩ : ∃ ι' : StatedSp 3 K →* twLevi F h.barEquiv.toRingHom
      AmalgamNeighbour.Y.nodes, ∀ s, ι' s = Θ (omegaMinusIota hw.card_eq hf hc s) :=
    ⟨Θ.toMonoidHom.comp (omegaMinusIota hw.card_eq hf hc), fun _ => rfl⟩
  have hnY' : ∀ s, ΦY (ι' s) = levi6Hom e₂ ε' (s₀ * s * s₀⁻¹) := fun s => by rw [hι', hnY]
  have hY12 : (twLeviRestrict ΦY one_two_subset_Y).range ≤ pieceCore e₂ {1, 2} := by
    refine range_twLeviRestrict_le_pieceCore_of_commute hrY' hnY' one_two_subset_Y
      one_two_subset_X (map_levi6Hom_sp6TorusA e₂ ε') (fun x s hs => ?_)
      (commutator_twLevi_one_two h.barEquiv.toRingHom hθ ht₀θ ht₀)
    obtain ⟨a, -, rfl⟩ := hs
    rw [hι']
    exact commute_twLevi_of_symm Θ one_two_subset_Y (fun y hy => hT12 y hy a) x
  have hY0 : (twLeviRestrict ΦY zero_subset_Y).range ≤ pieceCore e₂ {3} := by
    refine range_twLeviRestrict_le_pieceCore_of_commute hrY' hnY' zero_subset_Y
      three_subset_X (map_levi6Hom_sp6Torus3 e₂ ε') (fun x s hs => ?_)
      (commutator_twLevi_zero h.barEquiv.toRingHom hθ ht₀θ ht₀)
    obtain ⟨p, -, rfl⟩ := hs
    rw [hι']
    exact commute_twLevi_of_symm Θ zero_subset_Y (fun y hy => hT0 y hy p) x
  have hX3 := range_twLeviRestrict_three_le_pieceCore hf hrX' hnX
  have hYM : ∀ x, twLeviRestrict ΦY one_two_subset_Y x ∈ pieceCore e₁ {1, 2} := by
    intro x
    rw [pieceCore_one_two_of_frame he₁, ← pieceCore_one_two_of_frame he₂]
    exact hY12 ⟨x, rfl⟩
  have hagree := twAgree_of_rigidity hR hf hrX' hkX hcX hnX hcY hYM
    (twLeviRestrict_eq_levi6Hom_of_model hw.card_eq hf hc hΘ hε' hnY)
  refine ⟨hagree, fun a b => ?_⟩
  have hk : TwistedE6RowKinds e t f := by
    rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [Or.inl ⟨h6, h8⟩, Or.inr ⟨h8, h6⟩]
  have h03 := twistedE6RowPieceCommInput_holds G L K e t f hw hf hk
  have ha := hY0 ⟨a, rfl⟩
  have hb := hX3 ⟨b, rfl⟩
  rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h1 : e₁ = e := he₁
    obtain ⟨_, rfl⟩ := he₂
    subst h1
    rw [pieceCore_three_trans_graphAutF4_symm] at ha
    exact h03 _ ha _ hb
  · obtain ⟨_, rfl⟩ := he₁
    have h2 : e₂ = e := he₂
    subst h2
    rw [pieceCore_three_trans_graphAutF4_symm] at hb
    exact (h03 _ hb _ ha).symm

theorem twistedE6GraphRowDInput_of_inputs (hR : TwistedA3MatrixRigidityInput)
    (hY : TwistedLeviPiModelInput) : TwistedE6GraphRowDInput :=
  twistedE6GraphRowDInput_of_modelLeviInput (twistedE6GraphRowModelLeviInput_of_inputs hR hY)

end Main

end CFSG.SeitzReduction.F4Pilot
