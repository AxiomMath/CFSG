module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactLevel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoresForms

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.SymplecticPilot (planeEnum planeEnum_injective liftParam diagSpEntry
  diagSpEntry_inl diagSpEntry_inr)

section Param

variable {K : Type} [Field K] {m : ℕ}

@[expose] def flipPermFun (P : Finset (Fin m)) : Fin m ⊕ Fin m → Fin m ⊕ Fin m
  | Sum.inl i => if i ∈ P then Sum.inr i else Sum.inl i
  | Sum.inr i => if i ∈ P then Sum.inl i else Sum.inr i

theorem flipPermFun_flipPermFun (P : Finset (Fin m)) (a : Fin m ⊕ Fin m) :
    flipPermFun P (flipPermFun P a) = a := by
  rcases a with i | i <;> by_cases hi : i ∈ P <;> simp [flipPermFun, hi]

@[expose] def flipPerm (P : Finset (Fin m)) : Equiv.Perm (Fin m ⊕ Fin m) where
  toFun := flipPermFun P
  invFun := flipPermFun P
  left_inv := flipPermFun_flipPermFun P
  right_inv := flipPermFun_flipPermFun P

theorem flipPerm_apply (P : Finset (Fin m)) (a : Fin m ⊕ Fin m) :
    flipPerm P a = flipPermFun P a := rfl

theorem flipPerm_symm (P : Finset (Fin m)) : (flipPerm P).symm = flipPerm P := rfl

variable (K) in
@[expose] def flipParam (P : Finset (Fin m)) : (Fin m → Kˣ) →* (Fin m → Kˣ) where
  toFun t i := if i ∈ P then (t i)⁻¹ else t i
  map_one' := by
    funext i
    split_ifs <;> simp
  map_mul' t s := by
    funext i
    simp only [Pi.mul_apply]
    split_ifs
    · rw [mul_inv, mul_comm]
    · rfl

theorem flipParam_apply (P : Finset (Fin m)) (t : Fin m → Kˣ) (i : Fin m) :
    flipParam K P t i = if i ∈ P then (t i)⁻¹ else t i := rfl

theorem flipParam_flipParam (P : Finset (Fin m)) (t : Fin m → Kˣ) :
    flipParam K P (flipParam K P t) = t := by
  funext i
  simp only [flipParam_apply]
  split_ifs <;> simp

@[expose] def signedLevelParam (J P : Finset (Fin m)) : Subgroup (Fin m → Kˣ) :=
  (levelParam J).comap (flipParam K P)

theorem rootParam_le_signedLevelParam {k : Fin m} {J : Finset (Fin m)} (hk : k ∉ J)
    (P : Finset (Fin m)) : rootParam (K := K) k ≤ signedLevelParam J P := by
  rintro _ ⟨c, rfl⟩
  change flipParam K P (Pi.mulSingle k c) ∈ levelParam J
  intro i hi j hj
  have hik : i ≠ k := fun e => hk (e ▸ hi)
  have hjk : j ≠ k := fun e => hk (e ▸ hj)
  simp only [flipParam_apply, Pi.mulSingle_eq_of_ne (M := fun _ : Fin m => Kˣ) hik c,
    Pi.mulSingle_eq_of_ne (M := fun _ : Fin m => Kˣ) hjk c, inv_one, ite_self]

theorem diagSpEntry_flipParam (P : Finset (Fin m)) (t : Fin m → Kˣ) (a : Fin m ⊕ Fin m) :
    diagSpEntry (flipParam K P t) a = diagSpEntry t (flipPerm P a) := by
  rcases a with i | i
  · by_cases hi : i ∈ P <;> simp [flipPerm_apply, flipPermFun, flipParam_apply, hi]
  · by_cases hi : i ∈ P <;> simp [flipPerm_apply, flipPermFun, flipParam_apply, hi]

theorem liftParam_flipParam {F : Type} [Field F] (ι : K →+* F) (P : Finset (Fin m))
    (t : Fin m → Kˣ) : liftParam ι (flipParam K P t) = flipParam F P (liftParam ι t) := by
  funext i
  simp only [liftParam, flipParam_apply]
  split_ifs
  · exact map_inv _ _
  · rfl

end Param

section Flip

variable {F : Type} [Field F] {m : ℕ}

theorem flipPerm_mul_self (P : Finset (Fin m)) : flipPerm P * flipPerm P = 1 :=
  Equiv.ext (flipPermFun_flipPermFun P)

theorem permMatrix_flipPerm_mul_self (P : Finset (Fin m)) :
    (flipPerm P).permMatrix F * (flipPerm P).permMatrix F = 1 := by
  rw [← Matrix.permMatrix_mul, flipPerm_mul_self, Matrix.permMatrix_one]

variable (F) in
@[expose] noncomputable def flipGL (P : Finset (Fin m)) : GL (Fin m ⊕ Fin m) F :=
  ⟨(flipPerm P).permMatrix F, (flipPerm P).permMatrix F, permMatrix_flipPerm_mul_self P,
    permMatrix_flipPerm_mul_self P⟩

theorem coe_flipGL (P : Finset (Fin m)) :
    ((flipGL F P : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) =
      (flipPerm P).permMatrix F := rfl

theorem flipGL_inv (P : Finset (Fin m)) : (flipGL F P)⁻¹ = flipGL F P :=
  inv_eq_of_mul_eq_one_right (Units.ext (permMatrix_flipPerm_mul_self P))

theorem flipGL_isometry (P : Finset (Fin m)) (v : Fin m ⊕ Fin m → F) :
    StatedQuadPlus m F ((flipGL F P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v) =
      StatedQuadPlus m F v := by
  rw [coe_flipGL, Matrix.permMatrix_mulVec]
  unfold StatedQuadPlus
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ P <;> simp [flipPerm_apply, flipPermFun, hi, mul_comm]

theorem mem_normalizer_statedOmega_of_mem_isometryClosure {x : GL (Fin m ⊕ Fin m) F}
    (hx : x ∈ isometryClosure F m) :
    x ∈ normalizer (StatedOmega (StatedQuadPlus m F) : Set (GL (Fin m ⊕ Fin m) F)) := by
  set C := isometryClosure F m
  have key : ∀ g ∈ C, ∀ y ∈ ⁅C, C⁆, g * y * g⁻¹ ∈ ⁅C, C⁆ := by
    intro g hgC y hy
    have hmap : (⁅C, C⁆).map (MulAut.conj g).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator]
      have hC : C.map (MulAut.conj g).toMonoidHom = C := by
        ext z
        simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact mul_mem (mul_mem hgC hw) (inv_mem hgC)
        · intro hz
          exact ⟨g⁻¹ * z * g, mul_mem (mul_mem (inv_mem hgC) hz) hgC, by group⟩
      rw [hC]
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  rw [statedOmega_eq_commutator_isometryClosure]
  constructor
  · exact key _ hx y
  · intro hy
    have := key _ (inv_mem hx) _ hy
    simpa [mul_assoc] using this

theorem flipGL_mem_normalizer (P : Finset (Fin m)) :
    flipGL F P ∈ normalizer (StatedOmega (StatedQuadPlus m F) : Set (GL (Fin m ⊕ Fin m) F)) :=
  mem_normalizer_statedOmega_of_mem_isometryClosure (Subgroup.subset_closure (flipGL_isometry P))

theorem flipGL_mul_diagOmega_mul_inv (P : Finset (Fin m)) (t : Fin m → Fˣ) :
    flipGL F P * diagOmega F m t * (flipGL F P)⁻¹ = diagOmega F m (flipParam F P t) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, flipGL_inv, coe_flipGL, diagOmega_coe, diagOmega_coe]
  change (flipPerm P).toPEquiv.toMatrix * diagonal (diagSpEntry t) *
    (flipPerm P).toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
    flipPerm_symm, Function.comp_id, Function.id_comp, submatrix_diagonal_equiv]
  congr 1
  funext a
  rw [Function.comp_apply, diagSpEntry_flipParam]

theorem perfectCore_statedOmega_inf_centralizer_flipParam [Finite F] (P : Finset (Fin m))
    (D : Set (Fin m → Fˣ)) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓
        centralizer (diagOmega F m '' (flipParam F P '' D))) =
      (perfectCore (StatedOmega (StatedQuadPlus m F) ⊓ centralizer (diagOmega F m '' D))).map
        (MulAut.conj (flipGL F P)).toMonoidHom := by
  rw [CFSG.Quasithin.map_perfectCore]
  congr 1
  set g := flipGL F P
  have hg := flipGL_mem_normalizer (F := F) P
  ext x
  simp only [mem_map, mem_inf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_centralizer_iff,
    Set.mem_image]
  constructor
  · rintro ⟨hxO, hxC⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by group⟩
    · have := (mem_normalizer_iff.1 (inv_mem hg) x).1 hxO
      simpa [mul_assoc] using this
    · rintro _ ⟨s, hs, rfl⟩
      have h1 := hxC (diagOmega F m (flipParam F P s)) ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      rw [← flipGL_mul_diagOmega_mul_inv] at h1
      calc diagOmega F m s * (g⁻¹ * x * g) =
            g⁻¹ * (g * diagOmega F m s * g⁻¹ * x) * g := by group
        _ = g⁻¹ * (x * (g * diagOmega F m s * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * x * g * diagOmega F m s := by group
  · rintro ⟨y, ⟨hyO, hyC⟩, rfl⟩
    refine ⟨(mem_normalizer_iff.1 hg y).1 hyO, ?_⟩
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have h1 := hyC (diagOmega F m s) ⟨s, hs, rfl⟩
    rw [← flipGL_mul_diagOmega_mul_inv]
    calc g * diagOmega F m s * g⁻¹ * (g * y * g⁻¹) = g * (diagOmega F m s * y) * g⁻¹ := by group
      _ = g * (y * diagOmega F m s) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * (g * diagOmega F m s * g⁻¹) := by group

theorem perfectCore_statedOmega_inf_centralizer_eq_signedLevel [Finite F] (hF : 4 ≤ Nat.card F)
    {J : Finset (Fin m)} (hJ : 2 ≤ J.card) (P : Finset (Fin m)) (D : Set (Fin m → Fˣ))
    (hlevel : ∀ s ∈ D, ∀ i ∈ J, ∀ j ∈ J, s i = s j)
    (hsep : ∀ a b : Fin m ⊕ Fin m, a ≠ b → ¬ SameSide J a b →
      ∃ s ∈ D, diagSpEntry s a ≠ diagSpEntry s b) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓
        centralizer (diagOmega F m '' (flipParam F P '' D))) =
      ((omegaLeviSL F J.card).map (spEmbedGL (planeEnum J) (planeEnum_injective J))).map
        (MulAut.conj (flipGL F P)).toMonoidHom := by
  rw [perfectCore_statedOmega_inf_centralizer_flipParam,
    perfectCore_statedOmega_inf_centralizer_eq_level hF hJ D hlevel hsep]

end Flip

section SignedLift

variable {K : Type} [Field K] {F : Type} [Field F] {m : ℕ}

theorem image_liftParam_signedLevelParam (ι : K →+* F) (J P : Finset (Fin m)) :
    liftParam ι '' ((signedLevelParam J P : Subgroup (Fin m → Kˣ)) : Set (Fin m → Kˣ)) =
      flipParam F P '' (liftParam ι '' ((levelParam J : Subgroup (Fin m → Kˣ)) :
        Set (Fin m → Kˣ))) := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨liftParam ι (flipParam K P t), ⟨flipParam K P t, ht, rfl⟩, ?_⟩
    rw [← liftParam_flipParam, flipParam_flipParam]
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨flipParam K P u, ?_, liftParam_flipParam ι P u⟩
    change flipParam K P (flipParam K P u) ∈ levelParam J
    rw [flipParam_flipParam]
    exact hu

theorem perfectCore_statedOmega_inf_centralizer_signedLevelTorus [Finite F]
    (hF : 4 ≤ Nat.card F) (ι : K →+* F) {κ : Kˣ} (hκ : κ * κ ≠ 1) {J : Finset (Fin m)}
    (hJ : 2 ≤ J.card) (P : Finset (Fin m)) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓
        centralizer (diagOmega F m '' (liftParam ι ''
          ((signedLevelParam J P : Subgroup (Fin m → Kˣ)) : Set (Fin m → Kˣ))))) =
      ((omegaLeviSL F J.card).map (spEmbedGL (planeEnum J) (planeEnum_injective J))).map
        (MulAut.conj (flipGL F P)).toMonoidHom := by
  rw [image_liftParam_signedLevelParam, perfectCore_statedOmega_inf_centralizer_flipParam,
    perfectCore_statedOmega_inf_centralizer_levelTorus hF ι hκ hJ]

end SignedLift

section SignedCores

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono)

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

variable (K) in
@[expose] noncomputable def plusSignedLevelTorus (J P : Finset (Fin n)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  plusFrameTorus K (signedLevelParam J P)

theorem pairTorus_le_plusSignedLevelTorus {k : Fin n} {J : Finset (Fin n)} (hk : k ∉ J)
    (P : Finset (Fin n)) : pairTorus k ≤ plusSignedLevelTorus K J P := by
  rw [← plusFrameTorus_rootParam]
  exact frameTorusOf_mono (rootParam_le_signedLevelParam hk P)

@[expose] noncomputable def plusSignedLevelCore
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (J P : Finset (Fin n)) :
    Subgroup G :=
  centralizerPerfectCore (modelToG e (plusSignedLevelTorus K J P))

theorem plusSignedLevelCore_le_plusNeighbourCore
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {k : Fin n} {J : Finset (Fin n)}
    (hk : k ∉ J) (P : Finset (Fin n)) : plusSignedLevelCore e J P ≤ plusNeighbourCore e k :=
  centralizerPerfectCore_anti (modelToG_mono e (pairTorus_le_plusSignedLevelTorus hk P))

variable {hn : 1 ≤ n} {b c : K}

end SignedCores

end CFSG.SeitzReduction.OmegaPilot
