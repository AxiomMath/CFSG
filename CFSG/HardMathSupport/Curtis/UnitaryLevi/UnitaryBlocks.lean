module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockExtension
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.FlagLeviMat
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.AGLEmbedding.UnitaryLevi
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def hypMap {r' r ε' ε : ℕ} (φ : Fin r' → Fin r) (ψ : Fin ε' → Fin ε) :
    HypIndex r' ε' → HypIndex r ε :=
  Sum.map φ (Sum.map ψ φ)

theorem hypMap_injective {r' r ε' ε : ℕ} {φ : Fin r' → Fin r} {ψ : Fin ε' → Fin ε}
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    Function.Injective (hypMap φ ψ) :=
  hφ.sumMap (hψ.sumMap hφ)

theorem hypMap_partner {r' r ε' ε : ℕ} (φ : Fin r' → Fin r) (ψ : Fin ε' → Fin ε)
    (x : HypIndex r' ε') : hypMap φ ψ (hypPartner x) = hypPartner (hypMap φ ψ x) := by
  rcases x with i | k | i <;> rfl

section Hyp

variable {r' r ε' ε : ℕ} (h : UnitaryFieldData p f K) (θ : HypIndex r' ε' → HypIndex r ε)
  (hθ : Function.Injective θ) (hp : ∀ a, θ (hypPartner a) = hypPartner (θ a))

include hp

theorem extId_mem_hypSU (g : hypSU h r' ε') :
    extGL θ hθ (g : GL (HypIndex r' ε') K) ∈ hypSU h r ε := by
  have hg := mem_hypSU.mp g.2
  rw [mem_hypSU, coe_extGL]
  refine ⟨?_, ?_⟩
  · refine extId_isometry θ hθ _ h.bar _ _ (fun i j => ?_) (fun i y hy => ?_) (fun i y hy => ?_) hg.1
    · rw [hypGram_apply, hypGram_apply, ← hp]
      simp only [hθ.eq_iff]
    · rw [hypGram_apply, ite_eq_right_iff]
      rintro rfl
      exact absurd ⟨hypPartner i, hp i⟩ hy
    · rw [hypGram_apply, ite_eq_right_iff]
      intro hc
      exfalso
      apply hy
      refine ⟨hypPartner i, ?_⟩
      rw [hp, hc, hypPartner_hypPartner]
  · rw [det_extId]
    exact hg.2

@[expose] noncomputable def extHyp : hypSU h r' ε' →* hypSU h r ε :=
  MonoidHom.codRestrict ((extGL θ hθ).comp (hypSU h r' ε').subtype) (hypSU h r ε)
    fun g => extId_mem_hypSU h θ hθ hp g

theorem coe_extHyp (g : hypSU h r' ε') :
    (((extHyp h θ hθ hp g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      extId θ hθ (((g : GL (HypIndex r' ε') K)) : Matrix (HypIndex r' ε') (HypIndex r' ε') K) :=
  rfl

theorem extHyp_injective : Function.Injective (extHyp h θ hθ hp) := by
  intro g g' hgg
  have h1 := congrArg (fun x : hypSU h r ε => ((x : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K)) hgg
  simp only [coe_extHyp] at h1
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (congrFun h1 (θ i)) (θ j)
  rwa [extId_apply_map, extId_apply_map] at this

end Hyp

section Cut

variable {r ε : ℕ} (h : UnitaryFieldData p f K)

theorem mulVec_mem_posFlag_of_cut {i : ℕ} {M : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hM : ∀ a b, i ≤ fullPos a → fullPos b < i → M a b = 0) {v : HypIndex r ε → K}
    (hv : v ∈ posFlag r ε K i) : M *ᵥ v ∈ posFlag r ε K i := by
  intro a ha
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : i ≤ fullPos b
  · rw [hv b hb, mul_zero]
  · rw [hM a b ha (not_le.mp hb), zero_mul]

theorem smul_hypFlag_eq_of_cut {i : ℕ} (hir : i ≤ r) (g : hypSU h r ε)
    (hg : ∀ a b, i ≤ fullPos a → fullPos b < i →
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0)
    (hg' : ∀ a b, i ≤ fullPos a → fullPos b < i →
      (((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0) :
    g • hypFlag h r ε i = hypFlag h r ε i := by
  rw [hypFlag, ite_eq_left hir, isoFlag_eq_posFlag hir, Subgroup.smul_def]
  refine smul_eq_of_mulVec_mem (fun v hv => mulVec_mem_posFlag_of_cut hg hv) (fun v hv => ?_)
  have : (((g : hypSU h r ε) : GL (HypIndex r ε) K)⁻¹) =
      ((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) := by
    rw [Subgroup.coe_inv]
  rw [this]
  exact mulVec_mem_posFlag_of_cut hg' hv

theorem hom_smul_hypFlag {G : Type*} [Group G] (ρ : G →* hypSU h r ε) {i : ℕ} (hir : i ≤ r)
    (hcut : ∀ g : G, ∀ a b, i ≤ fullPos a → fullPos b < i →
      ((ρ g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0) (g : G) :
    ρ g • hypFlag h r ε i = hypFlag h r ε i :=
  smul_hypFlag_eq_of_cut h hir (ρ g) (hcut g) (by simpa [map_inv] using hcut g⁻¹)

end Cut

section LeviSL

noncomputable section

variable (h : UnitaryFieldData p f K) (m : ℕ) {ε : ℕ}

@[expose] def cinvM (A : Matrix.SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K :=
  (((A⁻¹ : Matrix.SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ

variable {m}

theorem cinvM_mul (A A' : Matrix.SpecialLinearGroup (Fin m) K) :
    cinvM h m (A * A') = cinvM h m A * cinvM h m A' := by
  simp [cinvM, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul,
    transpose_mul]

theorem cinvM_one : cinvM h m (1 : Matrix.SpecialLinearGroup (Fin m) K) = 1 := by
  simp [cinvM]

@[expose] def leviSLMat (A : Matrix.SpecialLinearGroup (Fin m) K) :
    Matrix (HypIndex m ε) (HypIndex m ε) K :=
  levi (A : Matrix (Fin m) (Fin m) K) (cinvM h m A)

theorem leviSLMat_mul (A A' : Matrix.SpecialLinearGroup (Fin m) K) :
    leviSLMat (ε := ε) h (A * A') = leviSLMat (ε := ε) h A * leviSLMat (ε := ε) h A' := by
  simp only [leviSLMat, levi_mul, Matrix.SpecialLinearGroup.coe_mul, cinvM_mul]

theorem leviSLMat_one :
    leviSLMat (ε := ε) h (1 : Matrix.SpecialLinearGroup (Fin m) K) = 1 := by
  simp [leviSLMat, levi, cinvM_one, fromBlocks_one]

theorem leviSLMat_isometry (A : Matrix.SpecialLinearGroup (Fin m) K) :
    ((leviSLMat (ε := ε) h A).map h.bar)ᵀ * hypGram m ε K * leviSLMat (ε := ε) h A = hypGram m ε K := by
  refine levi_isometry h _ _ ?_
  have hAA : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *
      (A : Matrix (Fin m) (Fin m) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  simp only [cinvM]
  rw [← transpose_mul, ← Matrix.map_mul, hAA]
  simp

theorem det_leviSLMat (A : Matrix.SpecialLinearGroup (Fin m) K) :
    (leviSLMat (ε := ε) h A).det = 1 := by
  have hX : (((A⁻¹ : Matrix.SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K).map
      h.bar).det = 1 := by
    have := RingHom.map_det h.bar
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K)
    rw [Matrix.SpecialLinearGroup.det_coe, map_one] at this
    exact this.symm
  simp only [leviSLMat, levi, det_fromBlocks_zero₂₁, det_one, one_mul,
    Matrix.SpecialLinearGroup.det_coe, cinvM, det_transpose, hX]

@[expose] def leviSLMulHom :
    Matrix.SpecialLinearGroup (Fin m) K →* Matrix (HypIndex m ε) (HypIndex m ε) K where
  toFun := leviSLMat h
  map_one' := leviSLMat_one h
  map_mul' := leviSLMat_mul h

variable (m) in
@[expose] def leviSLHom : Matrix.SpecialLinearGroup (Fin m) K →* hypSU h m ε :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits (leviSLMulHom (ε := ε) h)) (hypSU h m ε)
    fun A => mem_hypSU.mpr ⟨leviSLMat_isometry h A, det_leviSLMat (ε := ε) h A⟩

theorem coe_leviSLHom (A : Matrix.SpecialLinearGroup (Fin m) K) :
    (((leviSLHom (ε := ε) h m A : hypSU h m ε) : GL (HypIndex m ε) K) :
      Matrix (HypIndex m ε) (HypIndex m ε) K) = levi (A : Matrix (Fin m) (Fin m) K) (cinvM h m A) :=
  rfl

theorem leviSLHom_smul_hypFlag_top (A : Matrix.SpecialLinearGroup (Fin m) K) :
    leviSLHom (ε := ε) h m A • hypFlag h m ε m = hypFlag h m ε m := by
  refine hom_smul_hypFlag h (leviSLHom (ε := ε) h m) le_rfl (fun g x y hx hy => ?_) A
  rw [coe_leviSLHom]
  rcases x with c | k | c <;> rcases y with d | l | d
  · simp only [fullPos_inl] at hx
    exact absurd c.2 (by omega)
  · simp [levi]
  · simp [levi]
  · simp [levi]
  · simp only [fullPos_inr_inl] at hx hy
    omega
  · simp [levi]
  · simp [levi]
  · simp only [fullPos_inr_inr, fullPos_inr_inl] at hx hy
    omega
  · simp only [fullPos_inr_inr] at hx hy
    have := d.2
    omega

end

end LeviSL

section Node

variable (h : UnitaryFieldData p f K) {r ε : ℕ} (a : ℕ) (ha : a + 2 ≤ r)

@[expose] def nodeMap : HypIndex 2 0 → HypIndex r ε :=
  hypMap (fun i : Fin 2 => (⟨a + i, by have := i.2; omega⟩ : Fin r)) (fun k : Fin 0 => k.elim0)

theorem nodeMap_injective : Function.Injective (nodeMap (ε := ε) a ha) :=
  hypMap_injective (fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij))
    (fun k => k.elim0)

theorem nodeMap_partner (x : HypIndex 2 0) :
    nodeMap (ε := ε) a ha (hypPartner x) = hypPartner (nodeMap a ha x) :=
  hypMap_partner _ _ x

theorem nodeMap_inl (c : Fin 2) :
    nodeMap (ε := ε) a ha (.inl c) = .inl ⟨a + c, by have := c.2; omega⟩ := rfl

theorem nodeMap_inr_inr (c : Fin 2) :
    nodeMap (ε := ε) a ha (.inr (.inr c)) = .inr (.inr ⟨a + c, by have := c.2; omega⟩) := rfl

@[expose] noncomputable def nodeHom : Matrix.SpecialLinearGroup (Fin 2) K →* hypSU h r ε :=
  (extHyp h (nodeMap (ε := ε) a ha) (nodeMap_injective a ha) (nodeMap_partner a ha)).comp
    (leviSLHom (ε := 0) h 2)

theorem coe_nodeHom (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((nodeHom (ε := ε) h a ha A : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      extId (nodeMap a ha) (nodeMap_injective a ha)
        (levi (A : Matrix (Fin 2) (Fin 2) K) (cinvM h 2 A)) :=
  rfl

theorem nodeHom_smul_hypFlag (A : Matrix.SpecialLinearGroup (Fin 2) K) {i : ℕ} (hi : i ≠ a + 1)
    (hir : i ≤ r) : nodeHom (ε := ε) h a ha A • hypFlag h r ε i = hypFlag h r ε i := by
  refine hom_smul_hypFlag h (nodeHom (ε := ε) h a ha) hir (fun g x y hx hy => ?_) A
  rw [coe_nodeHom]
  refine extId_cut _ _ _ fullPos ?_ x y hx hy
  intro x' y' hx' hy'
  rcases x' with c | k | c <;> rcases y' with d | l | d
  · exfalso
    simp only [nodeMap_inl, fullPos_inl] at hx' hy'
    have := c.2
    have := d.2
    omega
  · exact l.elim0
  · simp [levi]
  · exact k.elim0
  · exact k.elim0
  · exact k.elim0
  · simp [levi]
  · exact l.elim0
  · exfalso
    simp only [nodeMap_inr_inr, fullPos_inr_inr] at hx' hy'
    have := c.2
    have := d.2
    omega

end Node

section Scalars

variable {r ε : ℕ}

theorem scalar_entry {ι : Type} [Fintype ι] [DecidableEq ι] (c : Kˣ) (x y : ι) :
    ((Matrix.GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) x y =
      if x = y then (c : K) else 0 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  simp [Matrix.scalar_apply, diagonal_apply]

theorem exists_scalar_entry {h : UnitaryFieldData p f K} {g : hypSU h r ε}
    (hg : g ∈ hypScalars h r ε) : ∃ c : Kˣ, ∀ x y : HypIndex r ε,
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) x y =
        if x = y then (c : K) else 0 := by
  obtain ⟨c, -, -, hc⟩ := hg
  exact ⟨c, fun x y => by rw [hc, scalar_entry]⟩

end Scalars

section Tail

variable (h : UnitaryFieldData p f K) {ε : ℕ} (s : ℕ)

@[expose] def tailMap : HypIndex 2 ε → HypIndex (s + 2) ε :=
  hypMap (Fin.natAdd s) id

theorem tailMap_injective : Function.Injective (tailMap (ε := ε) s) :=
  hypMap_injective (fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij))
    Function.injective_id

theorem tailMap_partner (x : HypIndex 2 ε) :
    tailMap s (hypPartner x) = hypPartner (tailMap s x) :=
  hypMap_partner _ _ x

@[expose] noncomputable def tailHom : hypSU h 2 ε →* hypSU h (s + 2) ε :=
  extHyp h (tailMap s) (tailMap_injective s) (tailMap_partner s)

theorem coe_tailHom (g : hypSU h 2 ε) :
    (((tailHom h s g : hypSU h (s + 2) ε) : GL (HypIndex (s + 2) ε) K) :
      Matrix (HypIndex (s + 2) ε) (HypIndex (s + 2) ε) K) =
      extId (tailMap s) (tailMap_injective s)
        (((g : GL (HypIndex 2 ε) K)) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) :=
  rfl

theorem tailHom_injective : Function.Injective (tailHom (ε := ε) h s) :=
  extHyp_injective h _ _ _

theorem tailHom_smul_hypFlag (g : hypSU h 2 ε) {i : ℕ} (hi : i ≤ s) :
    tailHom h s g • hypFlag h (s + 2) ε i = hypFlag h (s + 2) ε i := by
  refine hom_smul_hypFlag h (tailHom (ε := ε) h s) (by omega) (fun g x y hx hy => ?_) g
  rw [coe_tailHom]
  refine extId_cut _ _ _ fullPos ?_ x y hx hy
  intro x' y' hx' hy'
  exfalso
  rcases y' with d | l | d
  · simp [tailMap, hypMap] at hy'
    omega
  · simp [tailMap, hypMap] at hy'
    omega
  · simp [tailMap, hypMap] at hy'
    have := d.2
    omega

theorem tailHom_eq_one_of_mem_scalars (hs : 1 ≤ s) (g : hypSU h 2 ε)
    (hg : tailHom h s g ∈ hypScalars h (s + 2) ε) : tailHom h s g = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_entry hg
  have hx : (.inl ⟨0, by omega⟩ : HypIndex (s + 2) ε) ∉ Set.range (tailMap (ε := ε) s) := by
    rintro ⟨y, hy⟩
    rcases y with d | l | d <;> simp [tailMap, hypMap] at hy
    have := congrArg Fin.val hy
    simp at this
    omega
  have h1 := hc (.inl ⟨0, by omega⟩) (.inl ⟨0, by omega⟩)
  rw [coe_tailHom, extId_apply_of_not_left _ _ _ hx] at h1
  have hc1 : c = 1 := Units.ext (by simpa using h1.symm)
  apply Subtype.ext
  apply Units.ext
  ext x y
  rw [hc x y, hc1]
  simp [one_apply]

end Tail

section Diag

@[expose] def dgMat (u : Kˣ) : Matrix (Fin 2) (Fin 2) K :=
  diagonal ![(u : K), ((u⁻¹ : Kˣ) : K)]

theorem det_dgMat (u : Kˣ) : (dgMat u).det = 1 := by
  simp [dgMat, det_diagonal, Fin.prod_univ_two]

@[expose] def dg (u : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K := ⟨dgMat u, det_dgMat u⟩

@[expose] def dgHom : Kˣ →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun := dg
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, dgMat]
  map_mul' u v := by
    apply Subtype.ext
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show diagonal ![(u * v : Kˣ).1, ((u * v)⁻¹ : Kˣ).1] i j = (diagonal ![u.1, (u⁻¹ : Kˣ).1] * diagonal ![v.1, (v⁻¹ : Kˣ).1]) i j
    rw [diagonal_mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem coe_dgHom (u : Kˣ) :
    ((dgHom u : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = dgMat u :=
  rfl

variable (h : UnitaryFieldData p f K) {r ε : ℕ} (a : ℕ) (ha : a + 2 ≤ r)

theorem isDiag_cinvM_dgHom (u : Kˣ) : (cinvM h 2 (dgHom u)).IsDiag := by
  have : ((dgHom u)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) = dgHom u⁻¹ :=
    (map_inv dgHom u).symm
  unfold cinvM
  rw [this, coe_dgHom]
  exact ((isDiag_diagonal _).map (map_zero h.bar)).transpose

theorem isDiag_nodeHom_dgHom (u : Kˣ) :
    (((nodeHom (ε := ε) h a ha (dgHom u) : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K).IsDiag := by
  rw [coe_nodeHom]
  refine extId_isDiag _ _ _ ?_
  rw [coe_dgHom]
  exact IsDiag.fromBlocks (isDiag_diagonal _) (IsDiag.fromBlocks isDiag_one
    (isDiag_cinvM_dgHom h u))

theorem commute_nodeHom_dgHom {a₁ a₂ : ℕ} (ha₁ : a₁ + 2 ≤ r) (ha₂ : a₂ + 2 ≤ r) (u v : Kˣ) :
    Commute (nodeHom (ε := ε) h a₁ ha₁ (dgHom u)) (nodeHom (ε := ε) h a₂ ha₂ (dgHom v)) := by
  show _ * _ = _ * _
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact (commute_of_isDiag (isDiag_nodeHom_dgHom h a₁ ha₁ u) (isDiag_nodeHom_dgHom h a₂ ha₂ v)).eq

theorem nodeHom_dgHom_inl (u : Kˣ) (k : Fin r) :
    (((nodeHom (ε := ε) h a ha (dgHom u) : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl k) (.inl k) =
      if k.val = a then (u : K) else if k.val = a + 1 then ((u⁻¹ : Kˣ) : K) else 1 := by
  rw [coe_nodeHom]
  by_cases h0 : k.val = a
  · have hk : (.inl k : HypIndex r ε) = nodeMap a ha (.inl 0) := by
      simp [nodeMap_inl, Fin.ext_iff, h0]
    rw [hk, extId_apply_map]
    simp [levi, coe_dgHom, dgMat, h0]
  · by_cases h1 : k.val = a + 1
    · have hk : (.inl k : HypIndex r ε) = nodeMap a ha (.inl 1) := by
        simp [nodeMap_inl, Fin.ext_iff, h1]
      rw [hk, extId_apply_map]
      simp [levi, coe_dgHom, dgMat, h1]
    · have hk : (.inl k : HypIndex r ε) ∉ Set.range (nodeMap (ε := ε) a ha) := by
        rintro ⟨x', hx'⟩
        rcases x' with c | l | c
        · rw [nodeMap_inl] at hx'
          have := congrArg Fin.val (Sum.inl_injective hx')
          have := c.2
          simp at *
          omega
        · exact l.elim0
        · rw [nodeMap_inr_inr] at hx'
          exact absurd hx' (by simp)
      rw [extId_apply_of_not_left _ _ _ hk, one_apply_eq]
      simp [h0, h1]

theorem nodeHom_inr_inl (A : Matrix.SpecialLinearGroup (Fin 2) K) (k : Fin ε) :
    (((nodeHom (ε := ε) h a ha A : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (.inr (.inl k)) (.inr (.inl k)) = 1 := by
  have hk : (.inr (.inl k) : HypIndex r ε) ∉ Set.range (nodeMap (ε := ε) a ha) := by
    rintro ⟨x', hx'⟩
    rcases x' with c | l | c
    · rw [nodeMap_inl] at hx'
      exact absurd hx' (by simp)
    · exact l.elim0
    · rw [nodeMap_inr_inr] at hx'
      exact absurd hx' (by simp)
  rw [coe_nodeHom, extId_apply_of_not_left _ _ _ hk, one_apply_eq]

end Diag

end CFSG.HardMathSupport.Curtis.UnitaryLevi
