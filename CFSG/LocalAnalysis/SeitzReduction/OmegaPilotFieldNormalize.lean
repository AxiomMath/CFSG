module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactQuot
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactSigned
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactGL

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL leviEmbedSL leviEmbedSL_injective)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeEnum planeEnum_injective liftParam
  siegelBlock)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open scoped commutatorElement

section Param

variable {K : Type} [Field K] {m : ℕ}

@[expose] def restrictParam (k : Fin (m + 1)) : (Fin (m + 1) → Kˣ) →* (Fin m → Kˣ) where
  toFun t := t ∘ k.succAbove
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restrictParam_apply (k : Fin (m + 1)) (t : Fin (m + 1) → Kˣ) (i : Fin m) :
    restrictParam k t i = t (k.succAbove i) := rfl

@[expose] def preimagePlanes (k : Fin (m + 1)) (J : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter fun i => k.succAbove i ∈ J

theorem mem_preimagePlanes {k : Fin (m + 1)} {J : Finset (Fin (m + 1))} {i : Fin m} :
    i ∈ preimagePlanes k J ↔ k.succAbove i ∈ J := by
  simp [preimagePlanes]

theorem flipParam_restrictParam (k : Fin (m + 1)) (P : Finset (Fin (m + 1)))
    (t : Fin (m + 1) → Kˣ) :
    flipParam K (preimagePlanes k P) (restrictParam k t) = restrictParam k (flipParam K P t) := by
  funext i
  simp only [flipParam_apply, restrictParam_apply, mem_preimagePlanes]

theorem image_restrictParam_signedLevelParam {k : Fin (m + 1)} {J : Finset (Fin (m + 1))}
    (hk : k ∉ J) (P : Finset (Fin (m + 1))) :
    restrictParam k '' ((signedLevelParam J P : Subgroup (Fin (m + 1) → Kˣ)) :
        Set (Fin (m + 1) → Kˣ)) =
      ((signedLevelParam (preimagePlanes k J) (preimagePlanes k P) :
        Subgroup (Fin m → Kˣ)) : Set (Fin m → Kˣ)) := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    change flipParam K _ (restrictParam k t) ∈ levelParam _
    rw [flipParam_restrictParam]
    intro i hi j hj
    exact ht _ (mem_preimagePlanes.1 hi) _ (mem_preimagePlanes.1 hj)
  · intro hs
    refine ⟨Fin.insertNth (α := fun _ => Kˣ) k 1 s, ?_, ?_⟩
    · change flipParam K P (Fin.insertNth (α := fun _ => Kˣ) k 1 s) ∈ levelParam J
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (fun h : x = k => hk (h ▸ hx))
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (fun h : y = k => hk (h ▸ hy))
      have h := hs i (mem_preimagePlanes.2 hx) j (mem_preimagePlanes.2 hy)
      simp only [flipParam_apply, mem_preimagePlanes] at h
      simp only [flipParam_apply, Fin.insertNth_apply_succAbove]
      exact h
    · funext i
      simp only [restrictParam_apply, Fin.insertNth_apply_succAbove]

@[expose] def liftParamHom {F : Type} [Field F] (ι : K →+* F) : (Fin m → Kˣ) →* (Fin m → Fˣ) where
  toFun := liftParam ι
  map_one' := by
    funext i
    simp [liftParam]
  map_mul' _ _ := by
    funext i
    simp [liftParam]

variable {F : Type} [Field F]

@[expose] noncomputable def neighbourDiag (ι : K →+* F) (k : Fin (m + 1)) :
    (Fin (m + 1) → Kˣ) →* GL (Fin m ⊕ Fin m) F :=
  (diagOmega F m).comp ((liftParamHom ι).comp (restrictParam k))

theorem neighbourDiag_apply (ι : K →+* F) (k : Fin (m + 1)) (t : Fin (m + 1) → Kˣ) :
    neighbourDiag ι k t = diagOmega F m (liftParam ι (restrictParam k t)) := rfl

theorem neighbourDiag_mem_normalizer (ι : K →+* F) (k : Fin (m + 1)) (t : Fin (m + 1) → Kˣ) :
    neighbourDiag ι k t ∈
      normalizer (StatedOmega (StatedQuadPlus m F) : Set (GL (Fin m ⊕ Fin m) F)) :=
  diagOmega_mem_normalizer _

theorem image_neighbourDiag_signedLevelParam (ι : K →+* F) {k : Fin (m + 1)}
    {J : Finset (Fin (m + 1))} (hk : k ∉ J) (P : Finset (Fin (m + 1))) :
    neighbourDiag ι k '' ((signedLevelParam J P : Subgroup (Fin (m + 1) → Kˣ)) :
        Set (Fin (m + 1) → Kˣ)) =
      diagOmega F m '' (liftParam ι '' ((signedLevelParam (preimagePlanes k J)
        (preimagePlanes k P) : Subgroup (Fin m → Kˣ)) : Set (Fin m → Kˣ))) := by
  rw [← image_restrictParam_signedLevelParam hk P, Set.image_image, Set.image_image]
  rfl

end Param

section SiegelGL

variable {F : Type} [Field F] {m : ℕ}

variable (F) in
@[expose] noncomputable def siegelBlockGL (B : Finset (Fin m)) : Subgroup (GL (Fin m ⊕ Fin m) F) :=
  (siegelBlock F B).map (StatedSp m F).subtype

theorem siegelBlockGL_le_omegaLeviSL (B : Finset (Fin m)) :
    siegelBlockGL F B ≤ omegaLeviSL F m := by
  rintro _ ⟨x, ⟨C, -, rfl⟩, rfl⟩
  exact ⟨leviEmbedSL F m C, ⟨C, rfl⟩, rfl⟩

theorem commutator_siegelBlockGL [Finite F] (hF : 4 ≤ Nat.card F) {B : Finset (Fin m)}
    (hB : 2 ≤ B.card) : ⁅siegelBlockGL F B, siegelBlockGL F B⁆ = siegelBlockGL F B := by
  rw [siegelBlockGL, ← Subgroup.map_commutator, SymplecticPilot.commutator_siegelBlock_eq
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hB hF)]

theorem siegelBlockGL_le_statedOmega [Finite F] (hF : 4 ≤ Nat.card F) {B : Finset (Fin m)}
    (hB : 2 ≤ B.card) : siegelBlockGL F B ≤ StatedOmega (StatedQuadPlus m F) :=
  (siegelBlockGL_le_omegaLeviSL B).trans
    (omegaLeviSL_le_statedOmega hF (hB.trans (by simpa using Finset.card_le_univ B)))

theorem coe_diagSp_eq_diagOmega (t : Fin m → Fˣ) :
    ((SymplecticPilot.diagSp F m t : StatedSp m F) : GL (Fin m ⊕ Fin m) F) = diagOmega F m t := by
  apply Units.ext
  rw [diagOmega_coe]
  exact SymplecticPilot.mat_diagSp t

theorem siegelBlockGL_le_centralizer {B : Finset (Fin m)} {D : Set (Fin m → Fˣ)}
    (hconst : ∀ s ∈ D, ∀ i ∈ B, ∀ j ∈ B, s i = s j) :
    siegelBlockGL F B ≤ centralizer (diagOmega F m '' D) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  have h := (SymplecticPilot.commute_siegelBlock_diagSp (hconst s hs) hx).eq
  have h' := congrArg (fun y : StatedSp m F => (y : GL (Fin m ⊕ Fin m) F)) h
  simp only [Subgroup.coe_mul, coe_diagSp_eq_diagOmega] at h'
  exact h'.symm

theorem natCard_siegelBlockGL (B : Finset (Fin m)) :
    Nat.card (siegelBlockGL F B) = Nat.card (Matrix.SpecialLinearGroup (Fin B.card) F) := by
  rw [siegelBlockGL, Subgroup.card_map_of_injective (StatedSp m F).subtype_injective]
  exact (Nat.card_congr (SymplecticPilot.siegelBlockEquiv (F := F) B).toEquiv).symm

theorem siegelBlockGL_eq_map_omegaLeviSL [Finite F] (hF : 4 ≤ Nat.card F) {B : Finset (Fin m)}
    (hB : 2 ≤ B.card) :
    siegelBlockGL F B =
      (omegaLeviSL F B.card).map (spEmbedGL (planeEnum B) (planeEnum_injective B)) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hF
  have hcore := perfectCore_statedOmega_inf_centralizer_levelTorus hF (RingHom.id F) hκ hB
  rw [← hcore]
  refine Subgroup.eq_of_le_of_card_ge (le_perfectCore_of_perfect (le_inf
    (siegelBlockGL_le_statedOmega hF hB) (siegelBlockGL_le_centralizer ?_))
    (commutator_siegelBlockGL hF hB)) ?_
  · rintro _ ⟨t, ht, rfl⟩ i hi j hj
    simp only [liftParam, ht i hi j hj]
  · rw [hcore, natCard_siegelBlockGL, Subgroup.card_map_of_injective (spEmbedGL_injective _)]
    exact (Nat.card_congr (omegaLeviSLEquiv (F := F) (k := B.card)).toEquiv).ge

end SiegelGL

section Generic

variable {E M : Type*} [Group E] [Group M]

theorem commutatorElement_mul_left_of_mem_center (a c : E) {z : E} (hz : z ∈ center E) :
    ⁅a * z, c⁆ = ⁅a, c⁆ := by
  have h := mem_center_iff.1 hz c
  rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev]
  calc a * z * c * (z⁻¹ * a⁻¹) * c⁻¹ = a * (z * c) * z⁻¹ * a⁻¹ * c⁻¹ := by group
    _ = a * (c * z) * z⁻¹ * a⁻¹ * c⁻¹ := by rw [h]
    _ = a * c * a⁻¹ * c⁻¹ := by group

theorem commutatorElement_mul_right_of_mem_center (c a : E) {z : E} (hz : z ∈ center E) :
    ⁅c, a * z⁆ = ⁅c, a⁆ := by
  have h := mem_center_iff.1 hz c⁻¹
  rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev]
  calc c * (a * z) * c⁻¹ * (z⁻¹ * a⁻¹) = c * a * (z * c⁻¹) * z⁻¹ * a⁻¹ := by group
    _ = c * a * (c⁻¹ * z) * z⁻¹ * a⁻¹ := by rw [h]
    _ = c * a * c⁻¹ * a⁻¹ := by group

theorem le_of_map_le_of_perfect {π : E →* M} (hker : π.ker ≤ center E) {A B : Subgroup E}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) (hAB : A.map π ≤ B.map π) : A ≤ B := by
  have hdec : ∀ a ∈ A, ∃ b ∈ B, ∃ z ∈ center E, a = b * z := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := hAB ⟨a, ha, rfl⟩
    refine ⟨b, hb, b⁻¹ * a, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hba, inv_mul_cancel]
  rw [← hA, ← hB, Subgroup.commutator_le]
  intro a₁ ha₁ a₂ ha₂
  obtain ⟨b₁, hb₁, z₁, hz₁, rfl⟩ := hdec a₁ (hA ▸ ha₁)
  obtain ⟨b₂, hb₂, z₂, hz₂, rfl⟩ := hdec a₂ (hA ▸ ha₂)
  rw [commutatorElement_mul_left_of_mem_center _ _ hz₁,
    commutatorElement_mul_right_of_mem_center _ _ hz₂]
  exact Subgroup.commutator_mem_commutator (hB ▸ hb₁) (hB ▸ hb₂)

theorem eq_of_map_eq_of_perfect {π : E →* M} (hker : π.ker ≤ center E) {A B : Subgroup E}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) (hAB : A.map π = B.map π) : A = B :=
  le_antisymm (le_of_map_le_of_perfect hker hA hB hAB.le)
    (le_of_map_le_of_perfect hker hB hA hAB.ge)

theorem le_centralizer_of_map_commute {π : E →* M} (hker : π.ker ≤ center E) {A B : Subgroup E}
    (hB : ⁅B, B⁆ = B) (h : ∀ a ∈ A, ∀ b ∈ B, π a * π b = π b * π a) :
    A ≤ centralizer (B : Set E) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  have hc : ∀ x : B, ⁅(x : E), a⁆ ∈ center E := fun x => hker (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (h a ha x x.2).symm)
  let δ : B →* center E :=
    { toFun := fun x => ⟨⁅(x : E), a⁆, hc x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [Subgroup.coe_mul]
        have h1 := mem_center_iff.mp (hc y) (x : E)
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def] at *
        calc (x : E) * y * a * ((x : E) * y)⁻¹ * a⁻¹
            = x * (y * a * (y : E)⁻¹ * a⁻¹) * (a * (x : E)⁻¹ * a⁻¹) := by group
          _ = y * a * (y : E)⁻¹ * a⁻¹ * x * (a * (x : E)⁻¹ * a⁻¹) := by rw [h1]
          _ = x * a * (x : E)⁻¹ * a⁻¹ * (y * a * (y : E)⁻¹ * a⁻¹) := by
            have h2 := mem_center_iff.mp (hc y) ((x : E) * a * (x : E)⁻¹ * a⁻¹)
            rw [commutatorElement_def] at h2
            calc (y : E) * a * (y : E)⁻¹ * a⁻¹ * x * (a * (x : E)⁻¹ * a⁻¹)
                = y * a * (y : E)⁻¹ * a⁻¹ * (x * a * (x : E)⁻¹ * a⁻¹) := by group
              _ = _ := h2.symm }
  have : Group.IsPerfect B := Subgroup.isPerfect_iff.mpr hB
  have hk : commutator B ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [Group.IsPerfect.commutator_eq_top] at hk
  have hb' : δ ⟨b, hb⟩ = 1 := hk (mem_top _)
  have hb'' : ⁅b, a⁆ = 1 := congrArg Subtype.val hb'
  exact commutatorElement_eq_one_iff_mul_comm.1 hb''

end Generic

section Supp

open CFSG.SeitzReduction.SymplecticPilot (suppGL planeOf)

variable {F : Type} [Field F]

theorem commute_of_mem_suppGL_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι] {S T : Set ι}
    (hST : Disjoint S T) {x y : GL ι F} (hx : x ∈ suppGL F S) (hy : y ∈ suppGL F T) :
    Commute x y := by
  have hx' : ∀ r t, ¬(r ∈ S ∧ t ∈ S) → (x : Matrix ι ι F) r t = (1 : Matrix ι ι F) r t := hx
  have hy' : ∀ r t, ¬(r ∈ T ∧ t ∈ T) → (y : Matrix ι ι F) r t = (1 : Matrix ι ι F) r t := hy
  have h1 : ((x : Matrix ι ι F) - 1) * ((y : Matrix ι ι F) - 1) = 0 := by
    ext r s
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t ∈ S
    · have hyt := hy' t s (fun h => Set.disjoint_left.1 hST ht h.1)
      simp only [Matrix.sub_apply, hyt, sub_self, mul_zero]
    · have hxt := hx' r t (fun h => ht h.2)
      simp only [Matrix.sub_apply, hxt, sub_self, zero_mul]
  have h2 : ((y : Matrix ι ι F) - 1) * ((x : Matrix ι ι F) - 1) = 0 := by
    ext r s
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t ∈ S
    · have hyt := hy' r t (fun h => Set.disjoint_left.1 hST ht h.2)
      simp only [Matrix.sub_apply, hyt, sub_self, zero_mul]
    · have hxt := hx' t s (fun h => ht h.1)
      simp only [Matrix.sub_apply, hxt, sub_self, mul_zero]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have e1 : (x : Matrix ι ι F) * y = 1 + (x - 1) + (y - 1) + (x - 1) * (y - 1) := by noncomm_ring
  have e2 : (y : Matrix ι ι F) * x = 1 + (y - 1) + (x - 1) + (y - 1) * (x - 1) := by noncomm_ring
  rw [e1, e2, h1, h2]
  abel

variable {m : ℕ}

theorem disjoint_planeCoords {I J : Finset (Fin m)} (h : Disjoint I J) :
    Disjoint (planeCoords I) (planeCoords J) :=
  Set.disjoint_left.2 fun _ ha hb => Finset.disjoint_left.1 h ha hb

theorem siegelBlockGL_le_suppGL (B : Finset (Fin m)) :
    siegelBlockGL F B ≤ suppGL F (planeCoords B) := by
  rintro _ ⟨x, hx, rfl⟩ a b hab
  exact SymplecticPilot.siegelBlock_le_spBlock B hx a b hab

theorem flipPerm_mem_planeCoords_iff (P B : Finset (Fin m)) (a : Fin m ⊕ Fin m) :
    flipPerm P a ∈ planeCoords B ↔ a ∈ planeCoords B := by
  rcases a with i | i <;> by_cases hi : i ∈ P <;>
    simp [flipPerm_apply, flipPermFun, hi, SymplecticPilot.mem_planeCoords]

theorem flipGL_conj_apply (P : Finset (Fin m)) (x : GL (Fin m ⊕ Fin m) F)
    (a b : Fin m ⊕ Fin m) :
    ((flipGL F P * x * (flipGL F P)⁻¹ : GL (Fin m ⊕ Fin m) F) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) a b =
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (flipPerm P a) (flipPerm P b) := by
  rw [Units.val_mul, Units.val_mul, flipGL_inv, coe_flipGL]
  have e : (flipPerm P).permMatrix F * (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *
      (flipPerm P).permMatrix F =
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F).submatrix (flipPerm P) (flipPerm P) := by
    change (flipPerm P).toPEquiv.toMatrix * (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *
      (flipPerm P).toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
      flipPerm_symm, Function.comp_id, Function.id_comp]
  rw [e, submatrix_apply]

theorem map_flipGL_suppGL_le (P B : Finset (Fin m)) :
    (suppGL F (planeCoords B)).map (MulAut.conj (flipGL F P)).toMonoidHom ≤
      suppGL F (planeCoords B) := by
  rintro _ ⟨x, hx, rfl⟩ a b hab
  change ((flipGL F P * x * (flipGL F P)⁻¹ : GL (Fin m ⊕ Fin m) F) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) a b = _
  rw [flipGL_conj_apply, hx _ _ (by rwa [flipPerm_mem_planeCoords_iff,
    flipPerm_mem_planeCoords_iff])]
  simp only [Matrix.one_apply, (flipPerm P).injective.eq_iff]

theorem commute_of_mem_flip_siegelBlockGL {I J P P' : Finset (Fin m)} (hIJ : Disjoint I J)
    {x y : GL (Fin m ⊕ Fin m) F}
    (hx : x ∈ (siegelBlockGL F I).map (MulAut.conj (flipGL F P)).toMonoidHom)
    (hy : y ∈ (siegelBlockGL F J).map (MulAut.conj (flipGL F P')).toMonoidHom) : Commute x y :=
  commute_of_mem_suppGL_of_disjoint (disjoint_planeCoords hIJ)
    (map_flipGL_suppGL_le P I (map_mono (siegelBlockGL_le_suppGL I) hx))
    (map_flipGL_suppGL_le P' J (map_mono (siegelBlockGL_le_suppGL J) hy))

end Supp

section Signed

variable {K : Type} [Field K] {m : ℕ}

theorem signedLevelParam_of_disjoint {J P : Finset (Fin m)} (h : Disjoint J P) :
    signedLevelParam (K := K) J P = levelParam J := by
  ext t
  change flipParam K P t ∈ levelParam J ↔ t ∈ levelParam J
  have e : ∀ i ∈ J, flipParam K P t i = t i := fun i hi => by
    simp [flipParam_apply, Finset.disjoint_left.1 h hi]
  constructor
  · intro ht i hi j hj
    rw [← e i hi, ← e j hj]
    exact ht i hi j hj
  · intro ht i hi j hj
    rw [e i hi, e j hj]
    exact ht i hi j hj

theorem flipGL_empty {F : Type} [Field F] : flipGL F (∅ : Finset (Fin m)) = 1 := by
  apply Units.ext
  rw [coe_flipGL, Units.val_one]
  have : flipPerm (∅ : Finset (Fin m)) = 1 := by
    ext a
    rcases a with i | i <;> simp [flipPerm_apply, flipPermFun]
  rw [this, Matrix.permMatrix_one]

theorem map_conj_one_eq {M : Type*} [Group M] (H : Subgroup M) :
    H.map (MulAut.conj (1 : M)).toMonoidHom = H := by
  ext x
  simp

theorem preimagePlanes_empty (k : Fin (m + 1)) : preimagePlanes k ∅ = ∅ := by
  ext i
  simp [mem_preimagePlanes]

theorem card_preimagePlanes {k : Fin (m + 1)} {J : Finset (Fin (m + 1))} (hk : k ∉ J) :
    (preimagePlanes k J).card = J.card := by
  have hmap : (preimagePlanes k J).map ⟨k.succAbove, Fin.succAbove_right_injective⟩ = J := by
    ext x
    simp only [Finset.mem_map, mem_preimagePlanes, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (fun h : x = k => hk (h ▸ hx))
      exact ⟨i, hx, rfl⟩
  calc (preimagePlanes k J).card =
        ((preimagePlanes k J).map ⟨k.succAbove, Fin.succAbove_right_injective⟩).card :=
        (Finset.card_map _).symm
    _ = J.card := by rw [hmap]

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ}

theorem plusSignedLevelCore_of_disjoint
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {J P : Finset (Fin n)}
    (h : Disjoint J P) : plusSignedLevelCore e J P = plusLevelCore e J := by
  simp only [plusSignedLevelCore, plusLevelCore, plusSignedLevelTorus, plusLevelTorus,
    signedLevelParam_of_disjoint h]

end Signed

section Cover

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] {m : ℕ}

structure PlusFieldCover (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K))
    (ι : K →+* F) (k : Fin (m + 1)) where
  π : plusNeighbourCore e k →* StatedOmega (StatedQuadPlus m F)
  surjective : Function.Surjective π
  ker_le : π.ker ≤ center (plusNeighbourCore e k)
  equivariant : ∀ (t : Fin (m + 1) → Kˣ)
    (hn : ((e.symm ((isHypFrame_plus K (m + 1)).frameHom t) : L) : G) ∈
      normalizer (plusNeighbourCore e k : Set G)) (x : plusNeighbourCore e k),
    π ((plusNeighbourCore e k).normalizerMonoidHom ⟨_, hn⟩ x) =
      (StatedOmega (StatedQuadPlus m F)).normalizerMonoidHom
        ⟨neighbourDiag ι k t, neighbourDiag_mem_normalizer ι k t⟩ (π x)

variable [Finite G] [Finite F]
  {e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)} {ι : K →+* F}
  {k : Fin (m + 1)}

theorem PlusFieldCover.map_signedLevelCore (C : PlusFieldCover e ι k) (hK : 4 ≤ Nat.card K)
    (hF : 4 ≤ Nat.card F) {J : Finset (Fin (m + 1))} (hk : k ∉ J) (hJ : 2 ≤ J.card)
    (P : Finset (Fin (m + 1))) :
    (((plusSignedLevelCore e J P).subgroupOf (plusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus m F)).subtype =
      (siegelBlockGL F (preimagePlanes k J)).map
        (MulAut.conj (flipGL F (preimagePlanes k P))).toMonoidHom := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hK
  have hJ' : 2 ≤ (preimagePlanes k J).card := by
    rw [card_preimagePlanes hk]
    exact hJ
  have h := map_frameCore_eq_of_conjDiag_quot (isHypFrame_plus K (m + 1)) e (neighbourDiag ι k)
    (neighbourDiag_mem_normalizer ι k) (P := signedLevelParam J P)
    (X := modelToG e (pairTorus (K := K) k))
    (modelToG_mono e (pairTorus_le_plusSignedLevelTorus hk P)) C.π C.surjective C.ker_le
    (fun t _ hn x => C.equivariant t hn x)
  rw [image_neighbourDiag_signedLevelParam ι hk P,
    perfectCore_statedOmega_inf_centralizer_signedLevelTorus hF ι hκ hJ' (preimagePlanes k P),
    ← siegelBlockGL_eq_map_omegaLeviSL hF hJ'] at h
  exact h

end Cover

end CFSG.SeitzReduction.OmegaPilot
