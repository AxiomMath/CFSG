module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification
open scoped MatrixGroups commutatorElement

open CFSG.ComponentClassification in
@[expose] def SLFrameAct {τ : Tag} {L : Type} [Field L] (ψ : SL(3, L) →* ModGL τ L)
    (g : ModGL τ L) (B : GL (Fin 3) L) (ε : Bool) : Prop :=
  ∀ X : SL(3, L), g * ψ X * g⁻¹ =
    ψ (CatalogueBHigherLinearAction.slConjugation 3 L B
      (if ε then CatalogueBGraphForm.slGraphAut 3 L X else X))

private theorem u3frame_frameAct_false_iff {τ : Tag} {L : Type} [Field L]
    {ψ : SL(3, L) →* ModGL τ L} {g : ModGL τ L} {B : GL (Fin 3) L} :
    SLFrameAct ψ g B false ↔
      ∀ X : SL(3, L), g * ψ X * g⁻¹ =
        ψ (CatalogueBHigherLinearAction.slConjugation 3 L B X) := by
  simp [SLFrameAct]

private def u3frame_frameActSubgroup {τ : Tag} {L : Type} [Field L]
    (ψ : SL(3, L) →* ModGL τ L) : Subgroup (ModGL τ L) where
  carrier := {g | ∃ B : GL (Fin 3) L, SLFrameAct ψ g B false}
  one_mem' := ⟨1, u3frame_frameAct_false_iff.mpr fun X => by simp⟩
  mul_mem' := by
    rintro g h ⟨B, hB⟩ ⟨C, hC⟩
    refine ⟨B * C, u3frame_frameAct_false_iff.mpr fun X => ?_⟩
    have hC' := (u3frame_frameAct_false_iff.mp hC) X
    have hB' := (u3frame_frameAct_false_iff.mp hB)
      (CatalogueBHigherLinearAction.slConjugation 3 L C X)
    calc (g * h) * ψ X * (g * h)⁻¹
        = g * (h * ψ X * h⁻¹) * g⁻¹ := by group
      _ = g * ψ (CatalogueBHigherLinearAction.slConjugation 3 L C X) * g⁻¹ := by rw [hC']
      _ = ψ (CatalogueBHigherLinearAction.slConjugation 3 L B
            (CatalogueBHigherLinearAction.slConjugation 3 L C X)) := hB'
      _ = ψ (CatalogueBHigherLinearAction.slConjugation 3 L (B * C) X) := by
            rw [map_mul]; rfl
  inv_mem' := by
    rintro g ⟨B, hB⟩
    refine ⟨B⁻¹, u3frame_frameAct_false_iff.mpr fun X => ?_⟩
    have h1 := (u3frame_frameAct_false_iff.mp hB)
      (CatalogueBHigherLinearAction.slConjugation 3 L B⁻¹ X)
    have h2 : CatalogueBHigherLinearAction.slConjugation 3 L B
        (CatalogueBHigherLinearAction.slConjugation 3 L B⁻¹ X) =
        CatalogueBHigherLinearAction.slConjugation 3 L (B * B⁻¹) X := by
      rw [map_mul]; rfl
    rw [h2] at h1
    have h1' : g * ψ (CatalogueBHigherLinearAction.slConjugation 3 L B⁻¹ X) * g⁻¹ =
        ψ X := by simpa using h1
    calc g⁻¹ * ψ X * g
        = g⁻¹ * (g * ψ (CatalogueBHigherLinearAction.slConjugation 3 L B⁻¹ X) * g⁻¹) * g := by
            rw [← h1']
      _ = ψ (CatalogueBHigherLinearAction.slConjugation 3 L B⁻¹ X) := by group

private theorem u3frame_conjDiagn_slConj {L : Type} [Field L] (d : Fin 3 → Lˣ)
    (X : SL(3, L)) :
    CFSG.RankThree.PartOne.KE.conjDiagn d X =
      CatalogueBHigherLinearAction.slConjugation 3 L
        (CFSG.RankThree.PartOne.KE.diagGLn d) X := by
  apply Subtype.ext
  rw [CFSG.RankThree.PartOne.KE.coe_conjDiagn,
    CatalogueBHigherLinearAction.slConjugation_matrix]

private theorem u3frame_slConj_toGL {L : Type} [Field L] (Y X : SL(3, L)) :
    CatalogueBHigherLinearAction.slConjugation 3 L (Matrix.SpecialLinearGroup.toGL Y) X =
      Y * X * Y⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation]
  simp only [map_mul, map_inv]

theorem exists_frameAct_of_mem_toralRootGroup
    {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    {g : ModGL τ L} (hg : g ∈ toralRootGroup τ L a) :
    ∃ B : GL (Fin 3) L, SLFrameAct ψ g B false := by
  have htorus : torusGroup τ L ≤ u3frame_frameActSubgroup ψ := by
    rw [torusGroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨j, u⟩, rfl⟩
    refine ⟨CFSG.RankThree.PartOne.KE.diagGLn
      (fun k => rootChar (fun l => u ^ τ.cartan j l) (σ k ⟨0, by decide⟩)),
      u3frame_frameAct_false_iff.mpr fun X => ?_⟩
    simp only [Prod.fst, Prod.snd]
    rw [torusElt_eq_rootDiagUnit j u,
      hψ.torus ⟨0, by decide⟩ (fun l => u ^ τ.cartan j l) X,
      u3frame_conjDiagn_slConj]
  have hroot : rootSpan τ L (rootCharKernel a) ≤ u3frame_frameActSubgroup ψ := by
    have hkr : rootCharKernel a = kernelRoots (rootCharHom a) := rfl
    rw [hkr, ← iSup_componentRootSpan (χ := rootCharHom a) L]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst j
      intro g hg
      have hrange : componentRootSpan L (rootCharHom a) i = ψ.range := by
        change rootSpan τ L (componentRoots (rootCharHom a) i) = ψ.range
        rw [hΨ, hψ.range]
      rw [hrange] at hg
      obtain ⟨Y, rfl⟩ := hg
      refine ⟨Matrix.SpecialLinearGroup.toGL Y, u3frame_frameAct_false_iff.mpr fun X => ?_⟩
      rw [u3frame_slConj_toGL Y X]
      simp only [map_mul, map_inv]
    · intro g hg
      refine ⟨1, u3frame_frameAct_false_iff.mpr fun X => ?_⟩
      have hψX : ψ X ∈ componentRootSpan L (rootCharHom a) i := by
        change ψ X ∈ rootSpan τ L (componentRoots (rootCharHom a) i)
        rw [hΨ, ← hψ.range]
        exact ⟨X, rfl⟩
      have hcomm := CFSG.LieType.AlgebraicGroups.commute_of_mem_componentRootSpan
        (k := L) (i := j) (i' := i) hji hg hψX
      have h1 : CatalogueBHigherLinearAction.slConjugation 3 L 1 X = X := by simp
      rw [h1, hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  exact sup_le htorus hroot hg

private theorem u3frame_core
    {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (θ : SL(3, L) →* ModGL τ L) (π : Equiv.Perm (Fin 3))
    (hθ : ∀ (a b : Fin 3) (hab : a ≠ b), ∃ β : Lˣ, ∀ c : L,
      θ (Matrix.SpecialLinearGroup.transvection hab c) =
        pinnedX τ L (σ (π a) (π b)) ((β : L) * c)) :
    ∃ B : GL (Fin 3) L, ∀ X, θ X =
      ψ (CatalogueBHigherLinearAction.slConjugation 3 L B X) := by
  classical
  choose β hβ using hθ
  choose ε hε using hψ.transv
  let G : Fin 3 → Fin 3 → Lˣ := fun a b =>
    if h : a ≠ b then (ε (π a) (π b) (π.injective.ne h))⁻¹ * β a b h else 1
  have hG : ∀ a b (hab : a ≠ b), G a b =
      (ε (π a) (π b) (π.injective.ne hab))⁻¹ * β a b hab := by
    intro a b hab
    simp only [G, dif_pos hab]
  have hg : ∀ (a b : Fin 3) (hab : a ≠ b) (c : L),
      θ (Matrix.SpecialLinearGroup.transvection hab c) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab)
          ((G a b : L) * c)) := by
    intro a b hab c
    have h2 := hε (π a) (π b) (π.injective.ne hab) ((G a b : L) * c)
    have hβG : ε (π a) (π b) (π.injective.ne hab) * G a b = β a b hab := by
      rw [hG a b hab]; group
    rw [hβ a b hab c, h2]
    congr 1
    rw [← hβG, Units.val_mul, mul_assoc]
  have hinj : ∀ (a b : Fin 3) (hab : a ≠ b) (e e' : L),
      ψ (Matrix.SpecialLinearGroup.transvection hab e) =
        ψ (Matrix.SpecialLinearGroup.transvection hab e') → e = e' := by
    intro a b hab e e' heq
    have h1 := hε a b hab e
    have h2 := hε a b hab e'
    rw [h1, h2] at heq
    exact mul_left_cancel₀ (Units.ne_zero (ε a b hab))
      (pinnedX_injective τ L (σ a b) heq)
  have hcocycle : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c → G a b * G b c = G a c := by
    intro a b c hab hbc hac
    have h1 : θ ⁅Matrix.SpecialLinearGroup.transvection hab (1 : L),
        Matrix.SpecialLinearGroup.transvection hbc (1 : L)⁆ =
        θ (Matrix.SpecialLinearGroup.transvection hac (1 : L)) := by
      rw [Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) (1 : L),
        mul_one]
    rw [map_commutatorElement, hg a b hab 1, hg b c hbc 1, hg a c hac 1,
      ← map_commutatorElement, mul_one, mul_one] at h1
    have hπ := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (π.injective.ne hab) (π.injective.ne hbc) (π.injective.ne hac)
      ((G a b : L)) ((G b c : L))
    rw [hπ] at h1
    have he := hinj (π a) (π c) (π.injective.ne hac)
      ((G a b : L) * (G b c : L)) ((G a c : L) * 1) h1
    rw [mul_one] at he
    exact Units.ext (by rw [Units.val_mul]; exact he)
  have third : ∀ y z : Fin 3, y ≠ z → ∃ x, x ≠ y ∧ x ≠ z := by decide
  have hGinv : ∀ y z (hyz : y ≠ z), G y z * G z y = 1 := by
    intro y z hyz
    obtain ⟨x, hxy, hxz⟩ := third y z hyz
    have h1 := hcocycle x y z hxy hyz hxz
    have h2 := hcocycle x z y hxz hyz.symm hxy
    have h3 : G x y * (G y z * G z y) = G x y * 1 := by
      rw [mul_one, ← mul_assoc, h1, h2]
    exact mul_left_cancel h3
  let d : Fin 3 → Lˣ := fun a => if _ : a ≠ (0 : Fin 3) then G a 0 else 1
  have hd0 : d 0 = 1 := by simp [d]
  have hda : ∀ a (ha : a ≠ (0 : Fin 3)), d a = G a 0 := by
    intro a ha; simp [d, ha]
  have hgd : ∀ a b (hab : a ≠ b), G a b = d a * (d b)⁻¹ := by
    intro a b hab
    by_cases ha0 : a = 0
    · subst ha0
      rw [hd0, one_mul, hda b (Ne.symm hab)]
      exact eq_inv_of_mul_eq_one_left (hGinv 0 b hab)
    · by_cases hb0 : b = 0
      · subst hb0
        rw [hd0, inv_one, mul_one, hda a ha0]
      · rw [hda a ha0, hda b hb0, ← hcocycle a 0 b ha0 (Ne.symm hb0) hab,
          eq_inv_of_mul_eq_one_left (hGinv 0 b (Ne.symm hb0))]
  let P : GL (Fin 3) L := TauCeti.permutationGL π
  let D : GL (Fin 3) L := TauCeti.diagGL d
  let B : GL (Fin 3) L := P * D
  have htoGL : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t) =
        TauCeti.transvectionUnit hij t := by
    intro i j hij t
    apply Units.ext
    change ((Matrix.SpecialLinearGroup.transvection hij t : SL(3, L)) :
      Matrix (Fin 3) (Fin 3) L) =
      (TauCeti.transvectionUnit hij t : Matrix (Fin 3) (Fin 3) L)
    rw [TauCeti.coe_transvectionUnit, CFSG.LinearGroups.coe_transvection]
    rfl
  have hconj : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      CatalogueBHigherLinearAction.slConjugation 3 L B
        (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection (π.injective.ne hij) ((G i j : L) * t) := by
    intro i j hij t
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CatalogueBHigherLinearAction.toGL_slConjugation, htoGL i j hij t,
      htoGL (π i) (π j) (π.injective.ne hij) ((G i j : L) * t)]
    change (P * D) * TauCeti.transvectionUnit hij t * (P * D)⁻¹ =
      TauCeti.transvectionUnit (π.injective.ne hij) ((G i j : L) * t)
    have hD : D * TauCeti.transvectionUnit hij t * D⁻¹ =
        TauCeti.transvectionUnit hij ((d i : L) * t * ((d j)⁻¹ : Lˣ)) :=
      TauCeti.diagGL_mul_transvectionUnit_mul_inv (A := L) (N := 3) hij d t
    have hP : P * TauCeti.transvectionUnit hij ((d i : L) * t * ((d j)⁻¹ : Lˣ)) * P⁻¹ =
        TauCeti.transvectionUnit (π.injective.ne hij)
          ((d i : L) * t * ((d j)⁻¹ : Lˣ)) := by
      have hsymm : TauCeti.permutationGL (k := L) π.symm =
          (TauCeti.permutationGL (k := L) π)⁻¹ := by
        rw [← map_inv]
        rfl
      have h := TauCeti.permutationGL_inv_mul_transvectionUnit_mul_permutationGL
        (A := L) (n := Fin 3) π.symm hij ((d i : L) * t * ((d j)⁻¹ : Lˣ))
      rw [hsymm, inv_inv] at h
      simpa only [P] using h
    calc (P * D) * TauCeti.transvectionUnit hij t * (P * D)⁻¹
        = P * (D * TauCeti.transvectionUnit hij t * D⁻¹) * P⁻¹ := by group
      _ = P * TauCeti.transvectionUnit hij ((d i : L) * t * ((d j)⁻¹ : Lˣ)) * P⁻¹ := by
            rw [hD]
      _ = TauCeti.transvectionUnit (π.injective.ne hij)
            ((d i : L) * t * ((d j)⁻¹ : Lˣ)) := hP
      _ = TauCeti.transvectionUnit (π.injective.ne hij) ((G i j : L) * t) := by
            rw [hgd i j hij]
            congr 1
            push_cast
            ring
  refine ⟨B, fun X => ?_⟩
  have heq : θ = ψ.comp (CatalogueBHigherLinearAction.slConjugation 3 L B).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    show θ (Matrix.SpecialLinearGroup.transvection hij t) =
      ψ (CatalogueBHigherLinearAction.slConjugation 3 L B
        (Matrix.SpecialLinearGroup.transvection hij t))
    rw [hg i j hij t, hconj i j hij t]
  exact DFunLike.congr_fun heq X

theorem exists_frameAct_of_semilinear
    {τ : Tag} {L : Type} [Field L] {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    (φ : ModGL τ L →* ModGL τ L) (η : L ≃+* L)
    (f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (hmaps : ∀ a b, a ≠ b → f (σ a b) ∈ frameRoots σ)
    (hneg : ∀ γ, f (-γ) = -f γ)
    (hform : ∀ γ δ, iform (f γ) (f δ) = iform γ δ)
    (hφ : ∀ a b, a ≠ b → ∃ β : Lˣ, ∀ c : L,
      φ (pinnedX τ L (σ a b) c) = pinnedX τ L (f (σ a b)) ((β : L) * η c)) :
    ∃ (B : GL (Fin 3) L) (ε : Bool), ∀ X : SL(3, L), φ (ψ X) =
      ψ (CatalogueBHigherLinearAction.slConjugation 3 L B
        (if ε then stdUnitary η.toRingHom X else Matrix.SpecialLinearGroup.map η.toRingHom X)) := by
  classical
  let θ : SL(3, L) →* ModGL τ L :=
    (φ.comp ψ).comp (Matrix.SpecialLinearGroup.map η.symm.toRingHom)
  have hηMap : ∀ X : SL(3, L), Matrix.SpecialLinearGroup.map η.symm.toRingHom
      (Matrix.SpecialLinearGroup.map η.toRingHom X) = X := by
    intro X
    apply Subtype.ext
    ext i j
    change η.symm (η ((X : Matrix (Fin 3) (Fin 3) L) i j)) = _
    exact η.symm_apply_apply _
  have hθ : ∀ a b (hab : a ≠ b), ∃ β : Lˣ, ∀ c : L,
      θ (Matrix.SpecialLinearGroup.transvection hab c) =
        pinnedX τ L (f (σ a b)) ((β : L) * c) := by
    intro a b hab
    obtain ⟨β, hβ⟩ := hφ a b hab
    obtain ⟨e, he⟩ := hψ.transv a b hab
    refine ⟨β * Units.map η.toRingHom.toMonoidHom e, fun c => ?_⟩
    dsimp only [θ, MonoidHom.comp_apply]
    rw [slMap_transvection, he, hβ, map_mul]
    have hcancel : η (η.symm.toRingHom c) = c := η.apply_symm_apply c
    rw [hcancel]
    simp only [Units.val_mul, Units.coe_map, RingEquiv.coe_toRingHom]
    rw [mul_assoc]
    rfl
  rcases hψ.aut_cases (le_refl 3) hκ hnorm f hmaps hneg hform with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · obtain ⟨B, hB⟩ := u3frame_core hψ θ π (by
      intro a b hab
      obtain ⟨β, hβ⟩ := hθ a b hab
      exact ⟨β, fun c => by rw [hβ c, hπ a b hab]⟩)
    refine ⟨B, false, fun X => ?_⟩
    change φ (ψ X) = ψ (CatalogueBHigherLinearAction.slConjugation 3 L B
      (Matrix.SpecialLinearGroup.map η.toRingHom X))
    have h := hB (Matrix.SpecialLinearGroup.map η.toRingHom X)
    dsimp only [θ, MonoidHom.comp_apply] at h
    rwa [hηMap] at h
  · let θ' : SL(3, L) →* ModGL τ L := θ.comp (stdUnitary (RingHom.id L))
    obtain ⟨B, hB⟩ := u3frame_core hψ θ' π (by
      intro a b hab
      obtain ⟨β, hβ⟩ := hθ b a hab.symm
      refine ⟨(-1 : Lˣ) * β, fun c => ?_⟩
      dsimp only [θ', MonoidHom.comp_apply]
      rw [stdUnitary_transvection, RingHom.id_apply, hβ, hπ b a hab.symm]
      congr 1
      push_cast
      ring)
    refine ⟨B, true, fun X => ?_⟩
    change φ (ψ X) = ψ (CatalogueBHigherLinearAction.slConjugation 3 L B (stdUnitary η.toRingHom X))
    have h := hB (stdUnitary η.toRingHom X)
    have hdouble : stdUnitary (RingHom.id L) (stdUnitary η.toRingHom X) =
        Matrix.SpecialLinearGroup.map η.toRingHom X := by
      change CFSG.RankThree.Classical2.invTransposeSL
        (CFSG.RankThree.Classical2.invTransposeSL (Matrix.SpecialLinearGroup.map η.toRingHom X)) = _
      exact CFSG.RankThree.Classical2.invTransposeSL_invTransposeSL _
    dsimp only [θ', θ, MonoidHom.comp_apply] at h
    rwa [hdouble, hηMap] at h

theorem exists_frameAct_canonicalRep
    {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {ψ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) {w : WeylGroup τ}
    (hwΨ : (fun γ => w • γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i) :
    ∃ (B : GL (Fin 3) L) (ε : Bool), SLFrameAct ψ (canonicalRep (coxeterSystem τ) L w) B ε := by
  classical
  have hmaps : ∀ x y, x ≠ y → (fun γ => w • γ) (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : w • σ x y ∈ (fun γ => w • γ) '' componentRoots (rootCharHom a) i :=
      ⟨σ x y, by rw [hΨ]; exact ⟨x, y, hxy, rfl⟩, rfl⟩
    rw [hwΨ] at h1
    rwa [hΨ] at h1
  rcases hψ.aut_cases (le_refl 3) hκ hnorm (fun γ => w • γ) hmaps
    (fun γ => smul_neg w γ) (fun γ δ => iform_smul w γ δ) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    have hψw := hψ.transport w
    obtain ⟨B, hB⟩ := u3frame_core hψ
      ((MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom.comp ψ) π (by
        intro a b hab
        obtain ⟨ε, hε⟩ := hψw.transv a b hab
        refine ⟨ε, fun c => ?_⟩
        show ((MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom.comp ψ)
            (Matrix.SpecialLinearGroup.transvection hab c) =
          pinnedX τ L (σ (π a) (π b)) ((↑ε : L) * c)
        rw [hε c, hπ a b hab])
    exact ⟨B, false, fun X => by simpa [MulAut.conj_apply] using hB X⟩
  ·
    have hψw := hψ.transport w
    have hδtrans : ∀ (a b : Fin 3) (hab : a ≠ b) (c : L),
        CatalogueBGraphForm.slGraphAut 3 L (Matrix.SpecialLinearGroup.transvection hab c) =
          Matrix.SpecialLinearGroup.transvection hab.symm (-c) := by
      intro a b hab c
      apply Matrix.SpecialLinearGroup.toGL_injective
      apply Units.ext
      rw [CatalogueBGraphForm.toGL_slGraphAut, CatalogueBGraphForm.glGraphAut_matrix,
        ← map_inv, Matrix.SpecialLinearGroup.transvection_inv]
      change ((Matrix.SpecialLinearGroup.transvection hab (-c) : SL(3, L)) :
          Matrix (Fin 3) (Fin 3) L).transpose =
        ((Matrix.SpecialLinearGroup.transvection hab.symm (-c) : SL(3, L)) :
          Matrix (Fin 3) (Fin 3) L)
      rw [CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection,
        Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    obtain ⟨B, hB⟩ := u3frame_core hψ
      (((MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom.comp ψ).comp
        (CatalogueBGraphForm.slGraphAut 3 L).toMonoidHom) π (by
        intro a b hab
        obtain ⟨ε, hε⟩ := hψw.transv b a hab.symm
        refine ⟨(-1 : Lˣ) * ε, fun c => ?_⟩
        show ((MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom.comp ψ)
            (CatalogueBGraphForm.slGraphAut 3 L (Matrix.SpecialLinearGroup.transvection hab c)) =
          pinnedX τ L (σ (π a) (π b)) ((↑((-1 : Lˣ) * ε) : L) * c)
        rw [hδtrans a b hab c, hε (-c), hπ b a hab.symm]
        congr 1
        push_cast
        ring)
    refine ⟨B, true, fun X => ?_⟩
    have hX := hB (CatalogueBGraphForm.slGraphAut 3 L X)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hX
    have hδδ : CatalogueBGraphForm.slGraphAut 3 L (CatalogueBGraphForm.slGraphAut 3 L X) = X :=
      (CatalogueBGraphForm.slGraphAut 3 L).left_inv X
    rw [hδδ] at hX
    simpa [MulAut.conj_apply] using hX

private theorem u3frame_inv_diagonal {L : Type} [Field L] (v : Fin 3 → L) (hv : ∀ i, v i ≠ 0)
    (X : SL(3, L)) (hX : (X : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal v) :
    ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal (fun i => (v i)⁻¹) := by
  have hdet : (Matrix.diagonal (fun i => (v i)⁻¹)).det = 1 := by
    rw [Matrix.det_diagonal]
    have h1 : (Matrix.diagonal v).det = 1 := by
      rw [← hX]; exact X.2
    rw [Matrix.det_diagonal] at h1
    rw [Finset.prod_inv_distrib, h1, inv_one]
  let Y : SL(3, L) := ⟨Matrix.diagonal (fun i => (v i)⁻¹), hdet⟩
  have hmul : X * Y = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    change (X : Matrix (Fin 3) (Fin 3) L) * Matrix.diagonal (fun i => (v i)⁻¹) = 1
    rw [hX, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [mul_inv_cancel₀ (hv i)]
    · simp [Matrix.diagonal, hij]
  have hXY : X⁻¹ = Y := inv_eq_of_mul_eq_one_right hmul
  rw [hXY]

theorem false_of_graph_trivial {L : Type} [Field L] [IsAlgClosed L] (h2 : (2 : L) = 0) {G : Type*}
    [Group G] (ψ : SL(3, L) →* G) (hker : ψ.ker ≤ Subgroup.center SL(3, L)) (B : GL (Fin 3) L)
    (h : ∀ X : SL(3, L), ψ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      3 L B (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 L X)) = ψ X) :
    False := by
  classical
  have hscal : ∀ X : SL(3, L), ∃ r : L, r ^ 3 = 1 ∧
      (CatalogueBHigherLinearAction.slConjugation 3 L B
        (CatalogueBGraphForm.slGraphAut 3 L X) : Matrix (Fin 3) (Fin 3) L) =
        Matrix.scalar (Fin 3) r * (X : Matrix (Fin 3) (Fin 3) L) := by
    intro X
    let Y : SL(3, L) := CatalogueBHigherLinearAction.slConjugation 3 L B
      (CatalogueBGraphForm.slGraphAut 3 L X) * X⁻¹
    have hYker : Y ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      show ψ (CatalogueBHigherLinearAction.slConjugation 3 L B
        (CatalogueBGraphForm.slGraphAut 3 L X) * X⁻¹) = 1
      rw [map_mul, map_inv, h X, mul_inv_cancel]
    obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hYker)
    refine ⟨r, by simpa using hr, ?_⟩
    have hYeq : (Y : Matrix (Fin 3) (Fin 3) L) =
        (CatalogueBHigherLinearAction.slConjugation 3 L B
          (CatalogueBGraphForm.slGraphAut 3 L X) : Matrix (Fin 3) (Fin 3) L) *
        ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) := by
      rw [show Y = CatalogueBHigherLinearAction.slConjugation 3 L B
          (CatalogueBGraphForm.slGraphAut 3 L X) * X⁻¹ from rfl,
        Matrix.SpecialLinearGroup.coe_mul]
    have hXinv : ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) *
        (X : Matrix (Fin 3) (Fin 3) L) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    calc (CatalogueBHigherLinearAction.slConjugation 3 L B
          (CatalogueBGraphForm.slGraphAut 3 L X) : Matrix (Fin 3) (Fin 3) L)
        = (CatalogueBHigherLinearAction.slConjugation 3 L B
            (CatalogueBGraphForm.slGraphAut 3 L X) : Matrix (Fin 3) (Fin 3) L) *
            ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) *
            (X : Matrix (Fin 3) (Fin 3) L) := by
          rw [mul_assoc, hXinv, mul_one]
      _ = (Y : Matrix (Fin 3) (Fin 3) L) * (X : Matrix (Fin 3) (Fin 3) L) := by
          rw [← hYeq]
      _ = Matrix.scalar (Fin 3) r * (X : Matrix (Fin 3) (Fin 3) L) := by
          rw [← hscalar]
  have hfin : ({t : L | t = 0 ∨ t ^ 12 = 1}).Finite := by
    have hp : (Polynomial.X ^ 12 - Polynomial.C (1 : L) : Polynomial L) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (by norm_num) 1
    have hset : {t : L |
        (Polynomial.X ^ 12 - Polynomial.C (1 : L) : Polynomial L).IsRoot t} =
        {t : L | t ^ 12 = 1} := by
      ext t
      simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, sub_eq_zero]
    have hroot := Polynomial.finite_setOf_isRoot hp
    rw [hset] at hroot
    exact (Set.finite_singleton (0 : L)).union hroot
  obtain ⟨t, ht⟩ := Set.Finite.exists_notMem hfin
  have ht0 : t ≠ 0 := fun h0 => ht (Or.inl h0)
  have ht12 : t ^ 12 ≠ 1 := fun h12 => ht (Or.inr h12)
  let v : Fin 3 → L := fun i => if i = 0 then t else if i = 1 then t else (t⁻¹) ^ 2
  have hdet : (Matrix.diagonal v).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp [v]
    field_simp [ht0]
  let X : SL(3, L) := ⟨Matrix.diagonal v, hdet⟩
  have hXcoe : (X : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal v := rfl
  obtain ⟨r, hr3, hrX⟩ := hscal X
  have htrace : ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L).trace =
      r * (X : Matrix (Fin 3) (Fin 3) L).trace := by
    have h1 : (CatalogueBHigherLinearAction.slConjugation 3 L B
        (CatalogueBGraphForm.slGraphAut 3 L X) : Matrix (Fin 3) (Fin 3) L) =
        r • (X : Matrix (Fin 3) (Fin 3) L) := by
      rw [hrX]
      rw [show Matrix.scalar (Fin 3) r = r • (1 : Matrix (Fin 3) (Fin 3) L) by
        ext i j; simp [Matrix.scalar, Matrix.diagonal, Matrix.one_apply]]
      rw [Matrix.smul_mul, one_mul]
    calc ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L).trace
        = (CatalogueBHigherLinearAction.slConjugation 3 L B
            (CatalogueBGraphForm.slGraphAut 3 L X) : Matrix (Fin 3) (Fin 3) L).trace := by
          rw [CatalogueBHigherLinearAction.slConjugation_matrix,
            CatalogueBGraphForm.slGraphAut_matrix, Matrix.trace_units_conj,
            Matrix.trace_transpose]
      _ = (r • (X : Matrix (Fin 3) (Fin 3) L)).trace := by rw [h1]
      _ = r * (X : Matrix (Fin 3) (Fin 3) L).trace := by
          rw [Matrix.trace_smul, smul_eq_mul]
  have htraceX : (X : Matrix (Fin 3) (Fin 3) L).trace = t + t + (t⁻¹) ^ 2 := by
    rw [hXcoe, Matrix.trace_diagonal, Fin.sum_univ_three]
    simp [v]
  have htraceXinv : ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L).trace =
      t⁻¹ + t⁻¹ + ((t⁻¹) ^ 2)⁻¹ := by
    have hv : ∀ i, v i ≠ 0 := by
      intro i
      fin_cases i <;> simp [v, ht0]
    rw [u3frame_inv_diagonal v hv X hXcoe, Matrix.trace_diagonal, Fin.sum_univ_three]
    simp [v]
  rw [htraceX, htraceXinv] at htrace
  have hsum1 : t⁻¹ + t⁻¹ + ((t⁻¹) ^ 2)⁻¹ = (2 : L) * t⁻¹ + ((t⁻¹) ^ 2)⁻¹ := by ring
  have hsum2 : t + t + (t⁻¹) ^ 2 = (2 : L) * t + (t⁻¹) ^ 2 := by ring
  rw [hsum1, hsum2, h2, zero_mul, zero_add, zero_mul, zero_add] at htrace
  have hr4 : r = t ^ 4 := by
    have hs : t ^ 2 = r * (t⁻¹) ^ 2 := by
      rw [← htrace]
      field_simp
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    have hmul : t ^ 2 * t ^ 2 = r := by
      calc t ^ 2 * t ^ 2 = (r * (t⁻¹) ^ 2) * t ^ 2 := by rw [hs]
        _ = r := by
            rw [show (t⁻¹) ^ 2 = (t ^ 2)⁻¹ by field_simp]
            rw [mul_assoc, inv_mul_cancel₀ ht2, mul_one]
    rw [← hmul]
    ring
  have h12 : t ^ 12 = 1 := by
    have h3 := hr3
    rw [hr4] at h3
    rw [← pow_mul] at h3
    norm_num at h3
    exact h3
  exact ht12 h12

end CFSG.HardMathSupport.Timmesfeld.CrossChar

end
