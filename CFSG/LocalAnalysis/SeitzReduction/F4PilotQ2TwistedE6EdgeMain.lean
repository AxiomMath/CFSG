module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6EdgeFrame
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6RelayMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6EdgeMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6EdgeMu

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial TauCeti.GLSymplecticFin
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (antidiag)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt)
open CFSG.Timmesfeld.LieEmbed (c3ToF4)
open CFSG.Assembly.LowTwoRank (StatedSp StatedOmega StatedQuadPlus)
open CFSG.SeitzReduction.SymplecticPilot (q2OmIota)
open CFSG.LieType.Ree (ReeTag)
open scoped MatrixGroups

local instance f4PilotQ2TwistedE6EdgeMainNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2TwistedE6EdgeMainNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Block

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)

theorem coe_relayTwBlockEquiv_symm {σ : Fin 4 ⊕ Fin 2 ≃ Fin 6} {J' : Matrix (Fin 2) (Fin 2) F}
    {I : Finset (Fin 6)}
    (hJ : (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 :
      Matrix (Fin 6) (Fin 6) F) = reindex σ σ (fromBlocks (antidiag 4) 0 0 J'))
    (hl : ∀ i, σ (Sum.inl i) ∈ I) (hr : ∀ j, σ (Sum.inr j) ∉ I) (x : relayTwBlock h I) :
    ((((relayTwBlockEquiv h hJ hl hr).symm x : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)) :
      GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (((x : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).submatrix (σ ∘ Sum.inl)
        (σ ∘ Sum.inl) := by
  set g := (relayTwBlockEquiv h hJ hl hr).symm x with hg
  have hx : x = relayTwBlockEquiv h hJ hl hr g := by
    rw [hg, MulEquiv.apply_symm_apply]
  have hcoe : (((relayTwBlockEquiv h hJ hl hr g : relayTwBlock h I) : uGroup6 h) : GL (Fin 6) F) =
      (relayTwSU h hJ g : GL (Fin 6) F) := rfl
  rw [hx, hcoe, coe_relayTwSU]
  ext i j
  rw [Matrix.submatrix_apply, Function.comp_apply, Function.comp_apply, relayTwExt_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, fromBlocks_apply₁₁]

omit [Finite F] [CharP F 2] in
theorem twSub_transvection {f : Fin 4 → Fin 6} (hf : Function.Injective f) {p q : Fin 6}
    (hpq : p ≠ q) {i j : Fin 4} (hi : f i = p) (hj : f j = q) (c : F) :
    ((SpecialLinearGroup.transvection hpq c : SpecialLinearGroup (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F).submatrix f f = 1 + single i j c := by
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    ← hi, ← hj, hf.eq_iff]

omit [Finite F] [CharP F 2] in
theorem twSub_transvection_mul {f : Fin 4 → Fin 6} (hf : Function.Injective f) {p q p' q' : Fin 6}
    (hpq : p ≠ q) (hpq' : p' ≠ q') (hqp : q ≠ p') {i j i' j' : Fin 4} (hi : f i = p) (hj : f j = q)
    (hi' : f i' = p') (hj' : f j' = q') (c d : F) :
    ((SpecialLinearGroup.transvection hpq c * SpecialLinearGroup.transvection hpq' d :
      SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).submatrix f f =
      1 + single i j c + single i' j' d := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  have hprod : ((1 : Matrix (Fin 6) (Fin 6) F) + single p q c) * (1 + single p' q' d) =
      1 + single p q c + single p' q' d := by
    rw [add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      single_mul_single_of_ne (h := hqp), add_zero]
    abel
  rw [hprod]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    ← hi, ← hj, ← hi', ← hj', hf.eq_iff]

omit [Finite F] in
theorem twA_map_castHom {i j : Fin 4} :
    ((1 + single i j 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) F)) =
      1 + single i j 1 := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single,
    map_one]

omit [Finite F] in
theorem twA2_map_castHom {i j i' j' : Fin 4} :
    ((1 + single i j 1 + single i' j' 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).map
      (ZMod.castHom (dvd_refl 2) F)) = 1 + single i j 1 + single i' j' 1 := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single, Matrix.map_single, map_one]

theorem relayTwBlockEquiv_symm_eq_twSUOfZ2 {σ : Fin 4 ⊕ Fin 2 ≃ Fin 6}
    {J' : Matrix (Fin 2) (Fin 2) F} {I : Finset (Fin 6)}
    (hJ : (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 :
      Matrix (Fin 6) (Fin 6) F) = reindex σ σ (fromBlocks (antidiag 4) 0 0 J'))
    (hl : ∀ i, σ (Sum.inl i) ∈ I) (hr : ∀ j, σ (Sum.inr j) ∉ I) {x : relayTwBlock h I}
    {A₀ : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : A₀ᵀ * antidiag 4 * A₀ = antidiag 4)
    (hd : A₀.det = 1)
    (hx : (((x : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).submatrix (σ ∘ Sum.inl)
      (σ ∘ Sum.inl) = A₀.map (ZMod.castHom (dvd_refl 2) F)) :
    (relayTwBlockEquiv h hJ hl hr).symm x = twSUOfZ2 h A₀ hA hd := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_relayTwBlockEquiv_symm, hx]
  rfl

end Block

section Alpha

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] (hK : Nat.card K = 2) {X₀ : Subgroup (adjointGroup .F4 K)}
  {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
  {σ : Fin 4 ⊕ Fin 2 ≃ Fin 6} {J' : Matrix (Fin 2) (Fin 2) F} {I : Finset (Fin 6)}
  (hJ : (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 :
    Matrix (Fin 6) (Fin 6) F) = reindex σ σ (fromBlocks (antidiag 4) 0 0 J'))
  (hl : ∀ i, σ (Sum.inl i) ∈ I) (hr : ∀ j, σ (Sum.inr j) ∉ I)

@[expose] noncomputable def twEdgeAlpha (e : L ≃* adjointGroup .F4 K) (g : adjointGroup .F4 K)
    (Φ₁ : StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) :
    relayTwBlock h I →* G :=
  (twEdgeYParam e g Φ₁).comp ((twMu h hK).comp (relayTwBlockEquiv h hJ hl hr).symm.toMonoidHom)

variable {e : L ≃* adjointGroup .F4 K} {g : adjointGroup .F4 K}
  {Φ₁ : StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
    centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)}

theorem twEdgeAlpha_apply (x : relayTwBlock h I) :
    twEdgeAlpha hK h hJ hl hr e g Φ₁ x =
      twEdgeYParam e g Φ₁ (twMu h hK ((relayTwBlockEquiv h hJ hl hr).symm x)) :=
  rfl

theorem twEdgeAlpha_injective : Function.Injective (twEdgeAlpha hK h hJ hl hr e g Φ₁) :=
  (twEdgeYParam_injective Φ₁).comp
    ((twMu_injective h hK).comp (relayTwBlockEquiv h hJ hl hr).symm.injective)

theorem twEdgeAlpha_eq_of
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀
      (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl) Φ₁)
    {x : relayTwBlock h I} {g' : gramSU h (antidiag 4 : Matrix (Fin 4) (Fin 4) F)}
    (hx : (relayTwBlockEquiv h hJ hl hr).symm x = g') {s : StatedSp 3 K}
    (hs : q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl s = twMu h hK g')
    {m : adjointGroup .F4 K} (hm : g * graphAutF4 K (c3LeviHom K s) * g⁻¹ = m) :
    twEdgeAlpha hK h hJ hl hr e g Φ₁ x = ((e.symm m : L) : G) := by
  rw [twEdgeAlpha_apply, hx, ← hs, twEdgeYParam_iota hΦ₁, hm]

theorem commute_twEdgeAlpha_of
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀
      (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl) Φ₁)
    {s : StatedSp 3 K} {v : adjointGroup .F4 K}
    (hgv : g * graphAutF4 K (c3LeviHom K s) * g⁻¹ = v) {x : relayTwBlock h I}
    (hc : Commute (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl s)
      (twMu h hK ((relayTwBlockEquiv h hJ hl hr).symm x))) :
    Commute ((e.symm v : L) : G) (twEdgeAlpha hK h hJ hl hr e g Φ₁ x) := by
  rw [twEdgeAlpha_apply, ← hgv, ← twEdgeYParam_iota hΦ₁]
  exact hc.map (twEdgeYParam e g Φ₁)

theorem range_twEdgeAlpha_le
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀
      (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl) Φ₁)
    {β : Fin (Tag.rank .F4) → ℤ} (hX₀ : X₀ = zpowers (chainZ K rootR))
    (hg0 : g * graphAutF4 K (chainZ K rootR) * g⁻¹ = chainZ K rootR * chainZ K β)
    (hgc : g * graphAutF4 K (c3LeviHom K (elt (.positiveLong 0) 1 * elt (.negativeLong 0) 1)) *
      g⁻¹ = chainZ K rootR * (chainZ K β)⁻¹)
    (hzc : chainZ K rootR * chainZ K β = chainZ K β * chainZ K rootR)
    (hzo : chainZ K rootR ^ 3 = 1) :
    (twEdgeAlpha hK h hJ hl hr e g Φ₁).range ≤
      centralizer ((subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)) : Subgroup G) :
        Set G) := by
  set zr := chainZ K rootR with hzr
  set zb := chainZ K β with hzb
  have hzr2 : zr = (zr * zb * (zr * zb⁻¹)) ^ 2 := by
    have h1 : zr * zb * (zr * zb⁻¹) = zr ^ 2 :=
      calc zr * zb * (zr * zb⁻¹) = zr * (zb * zr) * zb⁻¹ := by group
        _ = zr * (zr * zb) * zb⁻¹ := by rw [hzc]
        _ = zr ^ 2 := by rw [mul_assoc, mul_inv_cancel_right, sq]
    rw [h1, ← pow_mul]
    calc zr = zr ^ 3 * zr := by rw [hzo, one_mul]
      _ = zr ^ (2 * 2) := by group
  have hzb2 : zb = zr⁻¹ * (zr * zb) := by group
  have hall : ∀ x : relayTwBlock h I,
      Commute (twEdgeAlpha hK h hJ hl hr e g Φ₁ x) ((e.symm zr : L) : G) ∧
        Commute (twEdgeAlpha hK h hJ hl hr e g Φ₁ x) ((e.symm zb : L) : G) := by
    intro x
    set y := twMu h hK ((relayTwBlockEquiv h hJ hl hr).symm x) with hy
    have c1 : Commute (twEdgeYParam e g Φ₁ y) ((e.symm (zr * zb) : L) : G) := by
      have h1 := commute_twEdgeYParam (g := g) Φ₁ y (z := zr) (by rw [hX₀]; exact mem_zpowers _)
      rwa [hg0] at h1
    have c2 : Commute (twEdgeYParam e g Φ₁ y) ((e.symm (zr * zb⁻¹) : L) : G) := by
      have h1 := twEdgeYParam_iota (g := g) hΦ₁ (elt (.positiveLong 0) 1 * elt (.negativeLong 0) 1)
      rw [hgc, q2OmIota_cPrime hK] at h1
      rw [← h1]
      exact ((commute_omPXhK_twMu h hK _).map (twEdgeYParam e g Φ₁)).symm
    have hr' : Commute (twEdgeYParam e g Φ₁ y) ((e.symm zr : L) : G) := by
      rw [hzr2, map_pow, map_mul, Subgroup.coe_pow, Subgroup.coe_mul]
      exact (c1.mul_right c2).pow_right 2
    refine ⟨hr', ?_⟩
    rw [hzb2, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hr'.inv_right.mul_right c1
  rintro _ ⟨x, rfl⟩
  rw [mem_centralizer_iff]
  intro y hy
  have hle : (subgroupToG e X₀ ⊔ subgroupToG e (zpowers zb) : Subgroup G) ≤
      centralizer {twEdgeAlpha hK h hJ hl hr e g Φ₁ x} := by
    have hXz : subgroupToG e X₀ = zpowers ((e.symm zr : L) : G) := by
      rw [← subgroupToG_zpowers, ← hX₀]
    refine sup_le ?_ ?_
    · rw [hXz, zpowers_le, mem_centralizer_singleton_iff]
      exact (hall x).1.eq.symm
    · rw [subgroupToG_zpowers, zpowers_le, mem_centralizer_singleton_iff]
      exact (hall x).2.eq.symm
  exact mem_centralizer_singleton_iff.1 (hle hy)

end Alpha

section XSide

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)

theorem twGram_root021 :
    gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField ![0, 2, 1] 1)) =
      SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 4 by decide)
        ((1 : h.fixedField) : F) := by
  rw [gramSUToSL_uEmbed6, relaySp6ToSL6_x_root021, map_transvection]
  rfl

theorem twGram_neg_root021 :
    gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField (-![0, 2, 1]) 1)) =
      SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 1 by decide)
        ((1 : h.fixedField) : F) := by
  rw [gramSUToSL_uEmbed6, relaySp6ToSL6_x_neg_root021, map_transvection]
  rfl

theorem twGram_single_zero :
    gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField (Pi.single 0 1) 1)) =
      SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) ((1 : h.fixedField) : F) *
        SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 3 by decide)
          ((-1 : h.fixedField) : F) := by
  rw [gramSUToSL_uEmbed6, relayTwSp6ToSL6_x_single_zero, map_mul, map_transvection,
    map_transvection]
  rfl

theorem twGram_single_one :
    gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField (Pi.single 1 1) 1)) =
      SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 2 by decide) ((1 : h.fixedField) : F) *
        SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide)
          ((-1 : h.fixedField) : F) := by
  rw [gramSUToSL_uEmbed6, sp6ToSL6_x_single_one, map_mul, map_transvection, map_transvection]
  rfl

omit [Finite F] in
theorem twCoe_neg_one : ((-1 : h.fixedField) : F) = 1 := by
  rw [NegMemClass.coe_neg, OneMemClass.coe_one, CharTwo.neg_eq]

theorem twX_map_twEdgeTheta (c : F) :
    (1 + single 0 1 c + single 2 3 (h.barEquiv.toRingHom c) : Matrix (Fin 4) (Fin 4) F).map
      (twEdgeTheta h) = twX (twEdgeTheta h c) := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single, Matrix.map_single, twX]
  congr 2
  change twEdgeTheta h (h.barEquiv c) = _
  rw [UnitaryFieldData.barEquiv_apply, twEdgeTheta_bar]

theorem twX'_map_twEdgeTheta (c : F) :
    (1 + single 1 0 c + single 3 2 (h.barEquiv.toRingHom c) : Matrix (Fin 4) (Fin 4) F).map
      (twEdgeTheta h) = twX' (twEdgeTheta h c) := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single, Matrix.map_single, twX']
  congr 2
  change twEdgeTheta h (h.barEquiv c) = _
  rw [UnitaryFieldData.barEquiv_apply, twEdgeTheta_bar]

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G}

theorem twChainSU6_uEmbed6_x {e : L ≃* adjointGroup .F4 K} {ε : h.fixedField ≃+* K}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hn : IsLeviNormalizedU h ε e ΦX) (τ : Fin 3 → ℤ) :
    chainSU6 h ΦX (uEmbed6 h (Sp.x 3 h.fixedField τ 1)) =
      ((e.symm (Adjoint.f4Par K (c3ToF4 τ) 1) : L) : G) := by
  rw [chainSU6_apply, hn, levi6Hom_x_alignTw, map_one]

end XSide

section Overlaps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] (hK : Nat.card K = 2) {X₀ : Subgroup (adjointGroup .F4 K)}
  {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
  {e : L ≃* adjointGroup .F4 K} {ε : h.fixedField ≃+* K}
  {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
  {Φ₁ : StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
    centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)}

theorem twEdgeInput_three (hX₀ : X₀ = zpowers (chainZ K rootR))
    (hn : IsLeviNormalizedU h ε e ΦX)
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀
      (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl) Φ₁) :
    ∃ α' : relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ →* G,
      Function.Injective α' ∧
      α'.range ≤ centralizer ((subgroupToG e X₀ ⊔
        subgroupToG e (zpowers (chainZ K (Pi.single 1 1))) : Subgroup G) : Set G) ∧
      (∀ x : relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ,
        (x : uGroup6 h) ∈ relayTwAgree3 h → α' x = chainSU6 h ΦX x) ∧
      ∀ x : relayTwBlock h ({2, 5} : Finset (Fin 6))ᶜ, (x : uGroup6 h) ∈ relayTwGens3 h →
        Commute ((e.symm (relayAlign K root1242) : L) : G) (α' x) ∧
          Commute ((e.symm (relayAlign' K root1242) : L) : G) (α' x) := by
  have hf : Function.Injective (relayTwSigma25 ∘ Sum.inl) :=
    relayTwSigma25.injective.comp Sum.inl_injective
  refine ⟨twEdgeAlpha hK h (blockSwapJ_eq_relayTwSigma25 F) relayTwSigma25_inl relayTwSigma25_inr e
      (edgeH1 K * wRep K [3, 2]) Φ₁, twEdgeAlpha_injective hK h _ _ _,
    range_twEdgeAlpha_le hK h _ _ _ hΦ₁ hX₀ (frame1_chainZ_rootR hK)
      ((frame1_cPrime hK).trans (by rw [chainZ_inv_charTwo])) (chainZ_rootR_comm_a2 hK)
      (by rw [← orderOf_chainZ_rootR hK]; exact pow_orderOf_eq_one _), ?_, ?_⟩
  · intro x hx
    simp only [relayTwAgree3, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx | hx
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma25 F) relayTwSigma25_inl
          relayTwSigma25_inr).symm x = twG03 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA03_gram twA03_det ?_
        rw [← coe_gramSUToSL, hx, gramSUToSL_uEmbed6_x_root221,
          twSub_transvection hf (show (0 : Fin 6) ≠ 3 by decide) (i := 0) (j := 3) rfl rfl, twA03,
          twA_map_castHom]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, c3ToF4_root221]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_P12_twMu h hK) (frame1_P12 hK)
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma25 F) relayTwSigma25_inl
          relayTwSigma25_inr).symm x = twG30 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA30_gram twA30_det ?_
        rw [← coe_gramSUToSL, hx, gramSUToSL_uEmbed6_x_neg_root221,
          twSub_transvection hf (show (0 : Fin 6) ≠ 3 by decide).symm (i := 3) (j := 0) rfl rfl,
          twA30, twA_map_castHom]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, map_neg, c3ToF4_root221]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_M12_twMu h hK) (frame1_M12 hK)
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma25 F) relayTwSigma25_inl
          relayTwSigma25_inr).symm x = twG12 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA12_gram twA12_det ?_
        rw [← coe_gramSUToSL, hx, twGram_root021,
          twSub_transvection hf (show (1 : Fin 6) ≠ 4 by decide) (i := 1) (j := 2) rfl rfl, twA12,
          twA_map_castHom]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, c3ToF4_root021_twEdge]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_D12_twMu h hK) (frame1_D12 hK)
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma25 F) relayTwSigma25_inl
          relayTwSigma25_inr).symm x = twG21 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA21_gram twA21_det ?_
        rw [← coe_gramSUToSL, hx, twGram_neg_root021,
          twSub_transvection hf (show (4 : Fin 6) ≠ 1 by decide) (i := 2) (j := 1) rfl rfl, twA21,
          twA_map_castHom]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, map_neg, c3ToF4_root021_twEdge]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_D21_twMu h hK) (frame1_D21 hK)
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma25 F) relayTwSigma25_inl
          relayTwSigma25_inr).symm x = twG0123 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA0123_gram twA0123_det ?_
        rw [← coe_gramSUToSL, hx, twGram_single_zero,
          twSub_transvection_mul hf (show (0 : Fin 6) ≠ 1 by decide)
            (show (4 : Fin 6) ≠ 3 by decide) (show (1 : Fin 6) ≠ 4 by decide) (i := 0) (j := 1)
            (i' := 2) (j' := 3) rfl rfl rfl rfl, twA0123, twA2_map_castHom, twCoe_neg_one]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, c3ToF4_single_zero_twEdge]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_L2_twMu h hK) (twFrame1_L2 hK)
  · rintro x ⟨c, hc | hc⟩
    · have hτ : (((twTau h ((relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma25 F)
          relayTwSigma25_inl relayTwSigma25_inr).symm x) :
            CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
              Matrix (Fin 4) (Fin 4) TwF4) = twX (twEdgeTheta h c) := by
        rw [coe_twTau, coe_relayTwBlockEquiv_symm, ← coe_gramSUToSL, hc,
          twSub_transvection_mul hf (show (0 : Fin 6) ≠ 1 by decide)
            (show (4 : Fin 6) ≠ 3 by decide) (show (1 : Fin 6) ≠ 4 by decide) (i := 0) (j := 1)
            (i' := 2) (j' := 3) rfl rfl rfl rfl, twX_map_twEdgeTheta]
      exact ⟨commute_twEdgeAlpha_of hK h _ _ _ hΦ₁ (frame1_relay hK)
          (commute_q2OmIota_relay_twMu_twX hK h hτ),
        commute_twEdgeAlpha_of hK h _ _ _ hΦ₁ (frame1_relay' hK)
          (commute_q2OmIota_relay'_twMu_twX hK h hτ)⟩
    · have hτ : (((twTau h ((relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma25 F)
          relayTwSigma25_inl relayTwSigma25_inr).symm x) :
            CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
              Matrix (Fin 4) (Fin 4) TwF4) = twX' (twEdgeTheta h c) := by
        rw [coe_twTau, coe_relayTwBlockEquiv_symm, ← coe_gramSUToSL, hc,
          twSub_transvection_mul hf (show (1 : Fin 6) ≠ 0 by decide)
            (show (3 : Fin 6) ≠ 4 by decide) (show (0 : Fin 6) ≠ 3 by decide) (i := 1) (j := 0)
            (i' := 3) (j' := 2) rfl rfl rfl rfl, twX'_map_twEdgeTheta]
      exact ⟨commute_twEdgeAlpha_of hK h _ _ _ hΦ₁ (frame1_relay hK)
          (commute_q2OmIota_relay_twMu_twX' hK h hτ),
        commute_twEdgeAlpha_of hK h _ _ _ hΦ₁ (frame1_relay' hK)
          (commute_q2OmIota_relay'_twMu_twX' hK h hτ)⟩

theorem twEdgeInput_two (hX₀ : X₀ = zpowers (chainZ K rootR))
    (hn : IsLeviNormalizedU h ε e ΦX)
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀
      (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl) Φ₁) :
    ∃ α' : relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ →* G,
      Function.Injective α' ∧
      α'.range ≤ centralizer ((subgroupToG e X₀ ⊔
        subgroupToG e (zpowers (chainZ K rootE1mE2Align)) : Subgroup G) : Set G) ∧
      (∀ x : relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ,
        (x : uGroup6 h) ∈ relayTwAgree2 h → α' x = chainSU6 h ΦX x) ∧
      ∀ x : relayTwBlock h ({0, 3} : Finset (Fin 6))ᶜ, (x : uGroup6 h) ∈ relayTwGens2 h →
        Commute ((e.symm (relayAlign K rootE2pE3Align) : L) : G) (α' x) ∧
          Commute ((e.symm (relayAlign' K rootE2pE3Align) : L) : G) (α' x) := by
  have hf : Function.Injective (relayTwSigma03 ∘ Sum.inl) :=
    relayTwSigma03.injective.comp Sum.inl_injective
  refine ⟨twEdgeAlpha hK h (blockSwapJ_eq_relayTwSigma03 F) relayTwSigma03_inl relayTwSigma03_inr e
      (edgeH3 K * wRep K []) Φ₁, twEdgeAlpha_injective hK h _ _ _,
    range_twEdgeAlpha_le hK h _ _ _ hΦ₁ hX₀ (frame3_chainZ_rootR hK)
      ((frame3_cPrime hK).trans (by rw [chainZ_inv_charTwo])) (chainZ_rootR_comm_e1e2 hK)
      (by rw [← orderOf_chainZ_rootR hK]; exact pow_orderOf_eq_one _), ?_, ?_⟩
  · intro x hx
    simp only [relayTwAgree2, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx | hx
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma03 F) relayTwSigma03_inl
          relayTwSigma03_inr).symm x = twG03 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA03_gram twA03_det ?_
        rw [← coe_gramSUToSL, hx, twGram_root021,
          twSub_transvection hf (show (1 : Fin 6) ≠ 4 by decide) (i := 0) (j := 3) rfl rfl, twA03,
          twA_map_castHom]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, c3ToF4_root021_twEdge]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_P12_twMu h hK) (frame3_P12 hK)
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma03 F) relayTwSigma03_inl
          relayTwSigma03_inr).symm x = twG30 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA30_gram twA30_det ?_
        rw [← coe_gramSUToSL, hx, twGram_neg_root021,
          twSub_transvection hf (show (4 : Fin 6) ≠ 1 by decide) (i := 3) (j := 0) rfl rfl, twA30,
          twA_map_castHom]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, map_neg, c3ToF4_root021_twEdge]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_M12_twMu h hK) (frame3_M12 hK)
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma03 F) relayTwSigma03_inl
          relayTwSigma03_inr).symm x = twG12 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA12_gram twA12_det ?_
        rw [← coe_gramSUToSL, hx, gramSUToSL_uEmbed6_x_single_two,
          twSub_transvection hf (show (2 : Fin 6) ≠ 5 by decide) (i := 1) (j := 2) rfl rfl, twA12,
          twA_map_castHom]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, c3ToF4_single_two_chainTw]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_D12_twMu h hK) (frame3_D12 hK)
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma03 F) relayTwSigma03_inl
          relayTwSigma03_inr).symm x = twG21 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA21_gram twA21_det ?_
        rw [← coe_gramSUToSL, hx, gramSUToSL_uEmbed6_x_neg_single_two,
          twSub_transvection hf (show (2 : Fin 6) ≠ 5 by decide).symm (i := 2) (j := 1) rfl rfl,
          twA21, twA_map_castHom]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, map_neg, c3ToF4_single_two_chainTw]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_D21_twMu h hK) (frame3_D21 hK)
    · have hβ : (relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma03 F) relayTwSigma03_inl
          relayTwSigma03_inr).symm x = twG0123 h := by
        refine relayTwBlockEquiv_symm_eq_twSUOfZ2 h _ _ _ twA0123_gram twA0123_det ?_
        rw [← coe_gramSUToSL, hx, twGram_single_one,
          twSub_transvection_mul hf (show (1 : Fin 6) ≠ 2 by decide)
            (show (5 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 5 by decide) (i := 0) (j := 1)
            (i' := 2) (j' := 3) rfl rfl rfl rfl, twA0123, twA2_map_castHom, twCoe_neg_one]
        rfl
      rw [hx, twChainSU6_uEmbed6_x h hn, c3ToF4_single_one_twEdge]
      exact twEdgeAlpha_eq_of hK h _ _ _ hΦ₁ hβ (q2OmIota_L2_twMu h hK) (twFrame3_L2 hK)
  · rintro x ⟨c, hc | hc⟩
    · have hτ : (((twTau h ((relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma03 F)
          relayTwSigma03_inl relayTwSigma03_inr).symm x) :
            CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
              Matrix (Fin 4) (Fin 4) TwF4) = twX (twEdgeTheta h c) := by
        rw [coe_twTau, coe_relayTwBlockEquiv_symm, ← coe_gramSUToSL, hc,
          twSub_transvection_mul hf (show (1 : Fin 6) ≠ 2 by decide)
            (show (5 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 5 by decide) (i := 0) (j := 1)
            (i' := 2) (j' := 3) rfl rfl rfl rfl, twX_map_twEdgeTheta]
      exact ⟨commute_twEdgeAlpha_of hK h _ _ _ hΦ₁ (frame3_relay hK)
          (commute_q2OmIota_relay_twMu_twX hK h hτ),
        commute_twEdgeAlpha_of hK h _ _ _ hΦ₁ (frame3_relay' hK)
          (commute_q2OmIota_relay'_twMu_twX hK h hτ)⟩
    · have hτ : (((twTau h ((relayTwBlockEquiv h (blockSwapJ_eq_relayTwSigma03 F)
          relayTwSigma03_inl relayTwSigma03_inr).symm x) :
            CFSG.LieType.Chevalley.C2E6Overlap.SU) : GL (Fin 4) TwF4) :
              Matrix (Fin 4) (Fin 4) TwF4) = twX' (twEdgeTheta h c) := by
        rw [coe_twTau, coe_relayTwBlockEquiv_symm, ← coe_gramSUToSL, hc,
          twSub_transvection_mul hf (show (2 : Fin 6) ≠ 1 by decide)
            (show (4 : Fin 6) ≠ 5 by decide) (show (1 : Fin 6) ≠ 4 by decide) (i := 1) (j := 0)
            (i' := 3) (j' := 2) rfl rfl rfl rfl, twX'_map_twEdgeTheta]
      exact ⟨commute_twEdgeAlpha_of hK h _ _ _ hΦ₁ (frame3_relay hK)
          (commute_q2OmIota_relay_twMu_twX' hK h hτ),
        commute_twEdgeAlpha_of hK h _ _ _ hΦ₁ (frame3_relay' hK)
          (commute_q2OmIota_relay'_twMu_twX' hK h hτ)⟩

end Overlaps

section Main

theorem twoTwistedE6RelayEdgeInput_holds : TwoTwistedE6RelayEdgeInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' F _ _ _ h ε ΦX hr hker hconj hn
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨Φ₁, hΦ₁⟩ := twoOmegaPlusParamInput_holds K hK X₀ hXJ hcyc hX₀ G L
    (e.trans (graphAutF4 K).symm) t hw hκ'
  have hXe : X₀ = zpowers (chainZ K rootR) :=
    eq_of_le_rootSL2 hK isRoot_rootR (le_rootSL2_rootR_of_le_highestRootRankOne hXJ)
      (zpowers_chainZ_le isRoot_rootR) hX₀ (by rw [Nat.card_zpowers, orderOf_chainZ_rootR hK])
  exact ⟨twEdgeInput_three hK h hXe hn hΦ₁, twEdgeInput_two hK h hXe hn hΦ₁⟩

end Main

end CFSG.SeitzReduction.F4Pilot
