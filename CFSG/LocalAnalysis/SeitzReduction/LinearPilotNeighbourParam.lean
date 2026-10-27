module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotLeviFactPiece
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open scoped commutatorElement

section Generic

variable {S E Q : Type*} [Group S] [Group E] [Group Q]

theorem eq_of_comp_eq_of_ker_le_center [Group.IsPerfect S] {p : E →* Q}
    (hp : p.ker ≤ center E) {φ ψ : S →* E} (h : ∀ x, p (φ x) = p (ψ x)) : φ = ψ := by
  have hδ : ∀ x, φ x * (ψ x)⁻¹ ∈ center E := fun x => hp (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h x, mul_inv_cancel])
  let δ : S →* center E :=
    { toFun := fun x => ⟨φ x * (ψ x)⁻¹, hδ x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [map_mul, _root_.mul_inv_rev, Subgroup.coe_mul]
        have h1 := mem_center_iff.mp (hδ y) (φ x)
        have h2 := mem_center_iff.mp (hδ y) (φ x * (ψ x)⁻¹)
        calc φ x * φ y * ((ψ y)⁻¹ * (ψ x)⁻¹) = φ x * (φ y * (ψ y)⁻¹) * (ψ x)⁻¹ := by group
          _ = φ y * (ψ y)⁻¹ * φ x * (ψ x)⁻¹ := by rw [h1]
          _ = φ y * (ψ y)⁻¹ * (φ x * (ψ x)⁻¹) := by group
          _ = φ x * (ψ x)⁻¹ * (φ y * (ψ y)⁻¹) := h2.symm }
  have hker : commutator S ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  ext x
  have hx : δ x = 1 := hker (mem_top x)
  have hx' : φ x * (ψ x)⁻¹ = 1 := congrArg Subtype.val hx
  exact mul_inv_eq_one.mp hx'

theorem exists_section_specialLinear {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 3 ≤ m)
    (hF : 5 ≤ Nat.card F) {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin m) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) :
    ∃ s : SpecialLinearGroup (Fin m) F →* E, ∀ g, π (s g) = g := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central (by omega) hF hπ
    hcen

theorem exists_surjective_lift_of_ker_le_center {F : Type} [Field F] [Finite F] {m : ℕ}
    (hm : 3 ≤ m) (hF : 5 ≤ Nat.card F) {E : Type*} [Group E] [Group.IsPerfect E]
    {p : E →* LinearFlag.projectiveSL m F} (hp : Function.Surjective p)
    (hpker : p.ker ≤ center E) :
    ∃ Φ : SpecialLinearGroup (Fin m) F →* E, (∀ x, p (Φ x) = LinearFlag.proj m F x) ∧
      Function.Surjective Φ ∧ Φ.ker ≤ center (SpecialLinearGroup (Fin m) F) := by
  obtain ⟨s, hs⟩ := exists_section_specialLinear hm hF
    (CFSG.LieType.Steinberg.pullbackFst_surjective (β := LinearFlag.proj m F) hp)
    (CFSG.LieType.Steinberg.ker_pullbackFst_le_center hpker)
  let Φ : SpecialLinearGroup (Fin m) F →* E :=
    ((MonoidHom.snd _ E).comp
      (CFSG.LieType.Steinberg.pullback (LinearFlag.proj m F) p).subtype).comp s
  have hΦ : ∀ x, p (Φ x) = LinearFlag.proj m F x := fun x => by
    have hmem := CFSG.LieType.Steinberg.mem_pullback.1 (s x).2
    have h1 : ((s x : CFSG.LieType.Steinberg.pullback (LinearFlag.proj m F) p) :
        SpecialLinearGroup (Fin m) F × E).1 = x := hs x
    change p ((s x : CFSG.LieType.Steinberg.pullback (LinearFlag.proj m F) p) :
      SpecialLinearGroup (Fin m) F × E).2 = _
    rw [← hmem, h1]
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · have hdecomp : ∀ y : E, ∃ x, y * (Φ x)⁻¹ ∈ center E := fun y => by
      obtain ⟨x, hx⟩ := LinearFlag.proj_surjective m F (p y)
      exact ⟨x, hpker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hΦ, hx, mul_inv_cancel])⟩
    have hcomm : commutator E ≤ Φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro y _ z _
      obtain ⟨x, hx⟩ := hdecomp y
      obtain ⟨x', hx'⟩ := hdecomp z
      have e : ⁅y, z⁆ = ⁅Φ x, Φ x'⁆ := by
        have h := CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hx hx' (Φ x)
          (Φ x')
        rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
      rw [e, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro y
    exact hcomm (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top y)
  · intro x hx
    have h1 : LinearFlag.proj m F x = 1 := by rw [← hΦ, MonoidHom.mem_ker.1 hx, map_one]
    rw [LinearFlag.proj_eq_one_iff, LinearFlag.scalars_eq_center] at h1
    exact h1

end Generic

section Block

variable {n : ℕ}

@[expose] noncomputable def blockSLEquiv {R : Type*} [Field R] (N : Finset (Fin n)) {m : ℕ}
    (eN : N ≃ Fin m) : SpecialLinearGroup (Fin m) R ≃* blockSpecialLinear (K := R) N :=
  (reindexSpecialLinear eN.symm).trans ((MonoidHom.ofInjective (blockEmbed_injective N)).trans
    (MulEquiv.subgroupCongr (range_blockEmbed N)))

theorem coe_blockSLEquiv {R : Type*} [Field R] (N : Finset (Fin n)) {m : ℕ} (eN : N ≃ Fin m)
    (x : SpecialLinearGroup (Fin m) R) :
    ((blockSLEquiv N eN x : blockSpecialLinear (K := R) N) : SpecialLinearGroup (Fin n) R) =
      blockEmbed N (reindexSpecialLinear eN.symm x) :=
  rfl

theorem coe_blockSLEquiv_apply {R : Type*} [Field R] (N : Finset (Fin n)) {m : ℕ}
    (eN : N ≃ Fin m) (x : SpecialLinearGroup (Fin m) R) (i j : Fin n) :
    (((blockSLEquiv N eN x : blockSpecialLinear (K := R) N) : SpecialLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R) i j =
      if h : i ∈ N ∧ j ∈ N then (x : Matrix (Fin m) (Fin m) R) (eN ⟨i, h.1⟩) (eN ⟨j, h.2⟩)
      else (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [coe_blockSLEquiv, coe_blockEmbed, blockMatrix_apply]
  split_ifs with h
  · change (reindex eN.symm eN.symm (x : Matrix (Fin m) (Fin m) R)) ⟨i, h.1⟩ ⟨j, h.2⟩ = _
    rw [reindex_apply, submatrix_apply, Equiv.symm_symm]
  · rfl

theorem blockSLEquiv_map {R R' : Type*} [Field R] [Field R'] (f : R →+* R')
    (N : Finset (Fin n)) {m : ℕ} (eN : N ≃ Fin m) (x : SpecialLinearGroup (Fin m) R) :
    ((blockSLEquiv N eN (SpecialLinearGroup.map f x) : blockSpecialLinear (K := R') N) :
      SpecialLinearGroup (Fin n) R') =
      SpecialLinearGroup.map f
        ((blockSLEquiv N eN x : blockSpecialLinear (K := R) N) : SpecialLinearGroup (Fin n) R) := by
  ext i j
  have h1 := coe_blockSLEquiv_apply N eN (SpecialLinearGroup.map f x) i j
  have h2 := coe_blockSLEquiv_apply N eN x i j
  rw [h1, SpecialLinearGroup.map_apply_coe f
    ((blockSLEquiv N eN x : blockSpecialLinear (K := R) N) : SpecialLinearGroup (Fin n) R),
    RingHom.mapMatrix_apply, Matrix.map_apply, h2]
  split_ifs with h
  · simp [SpecialLinearGroup.map_apply_coe]
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

@[expose] noncomputable def mapBlock {F : Type*} [Field F] (σ : F ≃+* F) (N : Finset (Fin n)) :
    MulAut (blockSpecialLinear (K := F) N) where
  toFun x := ⟨SpecialLinearGroup.map σ.toRingHom x,
    map_ringHom_mem_blockSpecialLinear σ.toRingHom x.2⟩
  invFun x := ⟨SpecialLinearGroup.map σ.symm.toRingHom x,
    map_ringHom_mem_blockSpecialLinear σ.symm.toRingHom x.2⟩
  left_inv x := by
    apply Subtype.ext
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  right_inv x := by
    apply Subtype.ext
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  map_mul' x y := by
    apply Subtype.ext
    simp

theorem coe_mapBlock_apply {F : Type*} [Field F] (σ : F ≃+* F) (N : Finset (Fin n))
    (x : blockSpecialLinear (K := F) N) :
    ((mapBlock σ N x : blockSpecialLinear (K := F) N) : SpecialLinearGroup (Fin n) F) =
      SpecialLinearGroup.map σ.toRingHom x :=
  rfl

theorem mapBlock_blockSLEquiv {F : Type*} [Field F] (σ : F ≃+* F) (N : Finset (Fin n)) {m : ℕ}
    (eN : N ≃ Fin m) (x : SpecialLinearGroup (Fin m) F) :
    mapBlock σ N (blockSLEquiv N eN x) =
      blockSLEquiv N eN (SpecialLinearGroup.map σ.toRingHom x) :=
  Subtype.ext (blockSLEquiv_map σ.toRingHom N eN x).symm

@[expose] def unitDiagGL {m : ℕ} {F : Type*} [Field F] (d : Fin m → Fˣ) : GL (Fin m) F :=
  ⟨diagonal fun i => (d i : F), diagonal fun i => (((d i)⁻¹ : Fˣ) : F),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem coe_unitDiagGL {m : ℕ} {F : Type*} [Field F] (d : Fin m → Fˣ) :
    ((unitDiagGL d : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal fun i => (d i : F) :=
  rfl

theorem coe_unitDiagGL_inv {m : ℕ} {F : Type*} [Field F] (d : Fin m → Fˣ) :
    (((unitDiagGL d)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      diagonal fun i => (((d i)⁻¹ : Fˣ) : F) :=
  rfl

@[expose] def torusBlockUnits {K F : Type*} [Field K] [Field F] (ι : K →+* F)
    {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) : Fin m → Fˣ :=
  fun a => Units.map ι.toMonoidHom (c.1 ((eN.symm a : N) : Fin n))

theorem coe_map_torusDiagSL {K F : Type*} [Field K] [Field F] (ι : K →+* F)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) :
    ((SpecialLinearGroup.map ι (torusDiagSL c) : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = diagonal fun i => ι ((c.1 i : Kˣ) : K) := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_torusDiagSL,
    diagonal_map (map_zero ι)]

theorem conjDiag_blockSLEquiv {K F : Type*} [Field K] [Field F] (ι : K →+* F)
    (N : Finset (Fin n)) {m : ℕ} (eN : N ≃ Fin m)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) (x : SpecialLinearGroup (Fin m) F) :
    conjDiag ι N c (blockSLEquiv N eN x) =
      blockSLEquiv N eN (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m F
        (unitDiagGL (torusBlockUnits ι eN c)) x) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hL : (((conjDiag ι N c (blockSLEquiv N eN x) : blockSpecialLinear (K := F) N) :
      SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (diagonal fun i => ι ((c.1 i : Kˣ) : K)) *
        (((blockSLEquiv N eN x : blockSpecialLinear (K := F) N) : SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) * (diagonal fun i => ι (((c⁻¹).1 i : Kˣ) : K)) := by
    rw [coe_conjDiag_apply, ← map_inv, ← map_inv]
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_map_torusDiagSL]
  rw [hL, mul_diagonal, diagonal_mul, coe_blockSLEquiv_apply, coe_blockSLEquiv_apply]
  split_ifs with h
  · rw [LinearFlag.coe_slConjugation, coe_unitDiagGL, coe_unitDiagGL_inv, mul_diagonal,
      diagonal_mul]
    simp only [torusBlockUnits, Equiv.symm_apply_apply, Units.coe_map, Units.coe_map_inv,
      MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe, InvMemClass.coe_inv, Pi.inv_apply]
  · rw [Matrix.one_apply]
    split_ifs with hij
    · subst hij
      rw [mul_one, ← map_mul]
      simp
    · rw [mul_zero, zero_mul]

end Block

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type*}
  [Field F]

structure FieldNeighbourParam (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (ι : K →+* F)
    (σ : F ≃+* F) (X : Subgroup G) (N : Finset (Fin n)) where
  Φ : blockSpecialLinear (K := F) N →* G
  range_eq : Φ.range = centralizerPerfectCore X
  ker_le : Φ.ker ≤ center (blockSpecialLinear (K := F) N)
  N1 : ∀ x : blockSpecialLinear (K := K) N,
    Φ ⟨SpecialLinearGroup.map ι x, map_ringHom_mem_blockSpecialLinear ι x.2⟩ =
      ((e.symm (LinearFlag.proj n K x) : L) : G)
  N2 : ∀ (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) (x : blockSpecialLinear (K := F) N),
    Φ (conjDiag ι N c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ x *
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹
  N3 : ∀ x : blockSpecialLinear (K := F) N, t * Φ x * t⁻¹ = Φ (mapBlock σ N x)

theorem FieldNeighbourParam.pieceCore_eq_map [Finite G] [Finite F]
    {e : L ≃* LinearFlag.projectiveSL n K} {t : G} {ι : K →+* F} {σ : F ≃+* F} {X : Subgroup G}
    {N : Finset (Fin n)} (P : FieldNeighbourParam e t ι σ X N) {I : Finset (Fin n)}
    (hIN : I ⊆ N)
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ c ∈ blockTorusParam (K := K) I, c i ≠ c j)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I)
    (hXI : X ≤ modelToG e (blockTorus (K := K) I)) :
    pieceCore e I = ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map P.Φ :=
  pieceCore_eq_map_of_conjDiag e ι hIN hsep hperf hXI P.Φ P.ker_le P.range_eq
    (fun c _ x => P.N2 c x)

end Param

section FromProj

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F]

theorem nonempty_fieldNeighbourParam_of_proj [Finite G] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (ι : K →+* F) (σ : F ≃+* F)
    {X : Subgroup G} {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m) (hm : 3 ≤ m)
    (hF : 5 ≤ Nat.card F) (p : centralizerPerfectCore X →* LinearFlag.projectiveSL m F)
    (hp : Function.Surjective p) (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (hD : modelToG e (blockSL (K := K) N) ≤ centralizerPerfectCore X)
    (h1 : ∀ x : SpecialLinearGroup (Fin m) K,
      p ⟨((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G),
        hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2))⟩ =
        LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (ht : t ∈ normalizer (centralizerPerfectCore X : Set G))
    (h3 : ∀ y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y) =
      LinearFlag.fieldAut m F σ (p y))
    (hg : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G))
    (h2 : ∀ c y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨_, hg c⟩ y) =
      LinearFlag.conjAut m F (unitDiagGL (torusBlockUnits ι eN c)) (p y)) :
    Nonempty (FieldNeighbourParam e t ι σ X N) := by
  set E := centralizerPerfectCore X with hE
  have : Group.IsPerfect E :=
    Subgroup.isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have : Group.IsPerfect (SpecialLinearGroup (Fin m) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm
  have : Group.IsPerfect (SpecialLinearGroup (Fin m) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm
  obtain ⟨Φ₀, hΦ₀, hsurj, hker⟩ := exists_surjective_lift_of_ker_le_center hm hF hp hpker
  let ψ₁ : SpecialLinearGroup (Fin m) K →* E :=
    MonoidHom.codRestrict (L.subtype.comp (e.symm.toMonoidHom.comp ((LinearFlag.proj n K).comp
      ((blockSpecialLinear (K := K) N).subtype.comp (blockSLEquiv N eN).toMonoidHom)))) E
      (fun x => hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2)))
  have hN1 : Φ₀.comp (SpecialLinearGroup.map ι) = ψ₁ :=
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, hΦ₀]
      exact (h1 x).symm
  have hN3 : (E.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (SpecialLinearGroup.map σ.toRingHom) :=
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h3, hΦ₀, hΦ₀,
        LinearFlag.fieldAut_proj]
  have hN2 : ∀ c, (E.normalizerMonoidHom ⟨_, hg c⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m F
        (unitDiagGL (torusBlockUnits ι eN c))).toMonoidHom := fun c =>
    eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, h2, hΦ₀, hΦ₀, LinearFlag.conjAut_proj]
  let Φ : blockSpecialLinear (K := F) N →* G :=
    E.subtype.comp (Φ₀.comp (blockSLEquiv N eN).symm.toMonoidHom)
  have hΦ : ∀ x', Φ (blockSLEquiv N eN x') = (Φ₀ x' : G) := fun x' => by
    change ((Φ₀ ((blockSLEquiv N eN).symm (blockSLEquiv N eN x')) : E) : G) = _
    rw [MulEquiv.symm_apply_apply]
  refine ⟨⟨Φ, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    have hs : Function.Surjective (Φ₀.comp (blockSLEquiv N eN).symm.toMonoidHom) := fun y => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨blockSLEquiv N eN x, by simp⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hs, ← MonoidHom.range_eq_map,
      range_subtype]
  ·
    intro x hx
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    have hx' : Φ₀ x' = 1 := by
      apply Subtype.ext
      rw [← hΦ]
      exact hx
    have hz := hker hx'
    rw [mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y', rfl⟩ := (blockSLEquiv N eN).surjective y
    rw [← map_mul, ← map_mul, hz y']
  ·
    intro x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    have hx : (⟨SpecialLinearGroup.map ι (blockSLEquiv N eN x' : SpecialLinearGroup (Fin n) K),
        map_ringHom_mem_blockSpecialLinear ι (blockSLEquiv N eN x').2⟩ :
          blockSpecialLinear (K := F) N) = blockSLEquiv N eN (SpecialLinearGroup.map ι x') :=
      Subtype.ext (blockSLEquiv_map ι N eN x').symm
    rw [hx, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) K →* E => (φ x' : G)) hN1
    exact this
  ·
    intro c x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    rw [conjDiag_blockSLEquiv, hΦ, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) F →* E => (φ x' : G)) (hN2 c)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    exact this.symm
  ·
    intro x
    obtain ⟨x', rfl⟩ := (blockSLEquiv N eN).surjective x
    rw [mapBlock_blockSLEquiv, hΦ, hΦ]
    have := congrArg (fun φ : SpecialLinearGroup (Fin m) F →* E => (φ x' : G)) hN3
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    exact this

end FromProj

end CFSG.SeitzReduction.LinearPilot
