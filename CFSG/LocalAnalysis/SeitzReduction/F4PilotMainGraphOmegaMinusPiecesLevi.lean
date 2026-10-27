module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesBlocks
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesPlane
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactLevel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadMinus StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)
open CFSG.SeitzReduction.SymplecticPilot (suppGL)
open scoped commutatorElement

local notation "ι₈" => Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2

section BlockHom

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {F : Type}
  [Field F] {e : ι' → ι}

omit [DecidableEq ι] [DecidableEq ι'] in
theorem submatrix_mul_of_vanish (he : Function.Injective e) {M N : Matrix ι ι F}
    (hM : ∀ i c, c ∉ Set.range e → M (e i) c = 0) :
    (M * N).submatrix e e = M.submatrix e e * N.submatrix e e := by
  ext i j
  rw [submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
    sum_eq_sum_comp_of_vanish he _ (fun c hc => by rw [hM i c hc, zero_mul])]
  rfl

@[expose] noncomputable def blockHom (B : Subgroup (GL ι F)) (he : Function.Injective e)
    (hB : ∀ x ∈ B, ∀ i c, c ∉ Set.range e → (x : Matrix ι ι F) (e i) c = 0) : B →* GL ι' F :=
  MonoidHom.toHomUnits
    { toFun := fun x => ((x : GL ι F) : Matrix ι ι F).submatrix e e
      map_one' := by
        simp only [OneMemClass.coe_one, Units.val_one]
        exact submatrix_one e he
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, Units.val_mul]
        exact submatrix_mul_of_vanish he (hB x x.2) }

theorem coe_blockHom (B : Subgroup (GL ι F)) (he : Function.Injective e)
    (hB : ∀ x ∈ B, ∀ i c, c ∉ Set.range e → (x : Matrix ι ι F) (e i) c = 0) (x : B) :
    ((blockHom B he hB x : GL ι' F) : Matrix ι' ι' F) =
      ((x : GL ι F) : Matrix ι ι F).submatrix e e :=
  rfl

end BlockHom

section Plane

variable {k : Type} [Field k]

@[expose] def planeEmb : Fin 2 → ι₈ := fun j => Sum.inr (Sum.inr j)

theorem planeEmb_injective : Function.Injective planeEmb :=
  fun _ _ h => Sum.inr_injective (Sum.inr_injective h)

@[expose] def planeVec (w : Fin 2 → k) : ι₈ → k :=
  Sum.elim 0 (Sum.elim 0 w)

theorem statedQuadMinus_planeVec (b c : k) (w : Fin 2 → k) :
    StatedQuadMinus 4 k b c (planeVec w) = anisoNorm b c w := by
  simp [StatedQuadMinus, planeVec, anisoNorm]

theorem mulVec_planeVec {M : Matrix ι₈ ι₈ k}
    (hcol : ∀ a j, a ∉ Set.range planeEmb → M a (planeEmb j) = 0) (w : Fin 2 → k) :
    M *ᵥ planeVec w = planeVec (M.submatrix planeEmb planeEmb *ᵥ w) := by
  funext a
  simp only [mulVec, dotProduct]
  rw [sum_eq_sum_comp_of_vanish planeEmb_injective _ (fun c hc => by
    rcases c with i | i | j
    · simp [planeVec]
    · simp [planeVec]
    · exact absurd ⟨j, rfl⟩ hc)]
  rcases a with i | i | j
  · simp only [planeVec, Sum.elim_inl, Pi.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by
      rw [hcol _ j (by rintro ⟨l, hl⟩; exact Sum.inr_ne_inl hl), zero_mul]
  · simp only [planeVec, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by
      rw [hcol _ j (by rintro ⟨l, hl⟩; exact Sum.inr_ne_inl (Sum.inr_injective hl)), zero_mul]
  · simp only [planeVec, Sum.elim_inr, mulVec, dotProduct, submatrix_apply]
    rfl

end Plane

section Coords

@[expose] def minusEmbThree : Fin 2 ⊕ Fin 2 → ι₈ :=
  Sum.map (Fin.succ : Fin 2 → Fin (4 - 1)) (fun i => Sum.inl (Fin.succ i : Fin (4 - 1)))

theorem minusEmbThree_injective : Function.Injective minusEmbThree :=
  Sum.map_injective.2 ⟨Fin.succ_injective _,
    fun _ _ h => Fin.succ_injective _ (Sum.inl_injective h)⟩

theorem mem_range_minusEmbThree_of {a : ι₈} (ha : a ∈ Set.range minusEmbA)
    (hP : a ∉ Set.range planeEmb) : a ∈ Set.range minusEmbThree := by
  obtain ⟨x | x | x, rfl⟩ := ha
  · exact ⟨Sum.inl x, rfl⟩
  · exact ⟨Sum.inr x, rfl⟩
  · exact absurd ⟨x, rfl⟩ hP

variable {k : Type} [Field k]

theorem isCoordSplit_minusEmbThree (b c : k) :
    IsCoordSplit (StatedQuadMinus 4 k b c) (StatedQuadPlus 2 k) minusEmbThree := by
  refine ⟨fun v => v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2,
    fun v => ?_, fun v w h => ?_⟩
  · simp only [StatedQuadMinus, StatedQuadPlus, Function.comp_apply, minusEmbThree, Sum.map_inl,
      Sum.map_inr]
    rw [Fin.sum_univ_succ (n := 2)]
    ring
  · have h0 : (Sum.inl 0 : ι₈) ∉ Set.range minusEmbThree := by
      rintro ⟨x | x, hx⟩ <;> simp [minusEmbThree] at hx
    have h1 : (Sum.inr (Sum.inl 0) : ι₈) ∉ Set.range minusEmbThree := by
      rintro ⟨x | x, hx⟩ <;> simp [minusEmbThree] at hx
    have hp : ∀ j, (Sum.inr (Sum.inr j) : ι₈) ∉ Set.range minusEmbThree := by
      rintro j ⟨x | x, hx⟩ <;> simp [minusEmbThree] at hx
    simp only [h _ h0, h _ h1, h _ (hp 0), h _ (hp 1)]

end Coords

section Centralizer

variable {k : Type} [Field k]

theorem mat_eq_zero_of_mem_centralizer_diagOmegaMinus {Ts : Set (Fin 3 → kˣ)} {x : GL ι₈ k}
    (hx : x ∈ centralizer (diagOmegaMinus k '' Ts)) {t : Fin 3 → kˣ} (ht : t ∈ Ts) {a b : ι₈}
    (hab : minusWeight k t a ≠ minusWeight k t b) : (x : Matrix ι₈ ι₈ k) a b = 0 :=
  (SymplecticPilot.commute_of_diag_iff (fun a b hab => diagOmegaMinus_apply_ne t hab) x).1
    ((mem_centralizer_iff.1 hx) _ ⟨t, ht, rfl⟩).symm a b
    (by rwa [diagOmegaMinus_apply_self, diagOmegaMinus_apply_self])

@[expose] def levelOne (κ : kˣ) : Fin 3 → kˣ := fun i => if i = 0 then 1 else κ

theorem levelOne_mem (κ : kˣ) : levelOne κ ∈ {t : Fin 3 → kˣ | t 2 = t 1} := by
  simp [levelOne]

theorem mat_eq_zero_of_not_mem_range_minusEmbA {κ : kˣ} (hκ : κ * κ ≠ 1) {x : GL ι₈ k}
    (hx : x ∈ centralizer (diagOmegaMinus k '' {t : Fin 3 → kˣ | t 2 = t 1})) {a : ι₈}
    (ha : a ∉ Set.range minusEmbA) {b : ι₈} (hba : b ≠ a) :
    (x : Matrix ι₈ ι₈ k) a b = 0 ∧ (x : Matrix ι₈ ι₈ k) b a = 0 := by
  have hmem : Pi.mulSingle (0 : Fin 3) κ ∈ {t : Fin 3 → kˣ | t 2 = t 1} := by simp
  have hne := minusWeight_mulSingle_ne hκ 0 hba.symm (eq_of_not_mem_range_minusEmbA ha)
  exact ⟨mat_eq_zero_of_mem_centralizer_diagOmegaMinus hx hmem hne,
    mat_eq_zero_of_mem_centralizer_diagOmegaMinus hx hmem hne.symm⟩

theorem mat_planeEmb_eq_zero {κ : kˣ} (hκ : κ * κ ≠ 1) {x : GL ι₈ k}
    (hx : x ∈ centralizer (diagOmegaMinus k '' {t : Fin 3 → kˣ | t 2 = t 1})) {a : ι₈}
    (ha : a ∉ Set.range planeEmb) (j : Fin 2) :
    (x : Matrix ι₈ ι₈ k) (planeEmb j) a = 0 ∧ (x : Matrix ι₈ ι₈ k) a (planeEmb j) = 0 := by
  have hκ1 : κ ≠ 1 := SymplecticPilot.units_ne_one_of_mul_self_ne_one hκ
  have hc1 : ((κ : kˣ) : k) ≠ 1 := fun h => hκ1 (Units.val_eq_one.1 h)
  have hne : planeEmb j ≠ a := fun h => ha ⟨j, h⟩
  by_cases hA : a ∈ Set.range minusEmbA
  · obtain ⟨y | y | y, rfl⟩ := hA
    · have hw : minusWeight k (levelOne κ) (planeEmb j) ≠
          minusWeight k (levelOne κ) (minusEmbA (Sum.inl y)) := by
        simp [minusWeight, planeEmb, minusEmbA, levelOne, Fin.succ_ne_zero, hc1.symm]
      exact ⟨mat_eq_zero_of_mem_centralizer_diagOmegaMinus hx (levelOne_mem κ) hw,
        mat_eq_zero_of_mem_centralizer_diagOmegaMinus hx (levelOne_mem κ) hw.symm⟩
    · have hw : minusWeight k (levelOne κ) (planeEmb j) ≠
          minusWeight k (levelOne κ) (minusEmbA (Sum.inr (Sum.inl y))) := by
        simp [minusWeight, planeEmb, minusEmbA, levelOne, Fin.succ_ne_zero, hκ1]
      exact ⟨mat_eq_zero_of_mem_centralizer_diagOmegaMinus hx (levelOne_mem κ) hw,
        mat_eq_zero_of_mem_centralizer_diagOmegaMinus hx (levelOne_mem κ) hw.symm⟩
    · exact absurd ⟨y, rfl⟩ ha
  · exact (mat_eq_zero_of_not_mem_range_minusEmbA hκ hx hA hne).symm

theorem mat_minusEmbThree_inl_inr_eq_zero {κ : kˣ} (hκ : κ * κ ≠ 1) {x : GL ι₈ k}
    (hx : x ∈ centralizer (diagOmegaMinus k '' {t : Fin 3 → kˣ | t 2 = t 1})) (i j : Fin 2) :
    (x : Matrix ι₈ ι₈ k) (minusEmbThree (Sum.inl i)) (minusEmbThree (Sum.inr j)) = 0 ∧
      (x : Matrix ι₈ ι₈ k) (minusEmbThree (Sum.inr i)) (minusEmbThree (Sum.inl j)) = 0 := by
  have hκi : κ ≠ κ⁻¹ := fun h => hκ (mul_eq_one_iff_eq_inv.2 h)
  have hci : ((κ : kˣ) : k) ≠ ((κ : kˣ) : k)⁻¹ := fun h =>
    hκi (Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h))
  have hw : ∀ i j : Fin 2, minusWeight k (levelOne κ) (minusEmbThree (Sum.inl i)) ≠
      minusWeight k (levelOne κ) (minusEmbThree (Sum.inr j)) := fun i j => by
    simp [minusWeight, minusEmbThree, levelOne, Fin.succ_ne_zero, hci]
  exact ⟨mat_eq_zero_of_mem_centralizer_diagOmegaMinus hx (levelOne_mem κ) (hw i j),
    mat_eq_zero_of_mem_centralizer_diagOmegaMinus hx (levelOne_mem κ) (hw j i).symm⟩

end Centralizer

section Reduction

theorem perfectCore_omegaMinus8_M3_le (k : Type) [Field k] [Finite k] [CharP k 2] {b c : k}
    (hk : 4 ≤ Nat.card k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
      centralizer (diagOmegaMinus k '' {t : Fin 3 → kˣ | t 2 = t 1})) ≤
      suppGL k (Set.range minusEmbThree) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hk
  set B := StatedOmega (StatedQuadMinus 4 k b c) ⊓
    centralizer (diagOmegaMinus k '' {t : Fin 3 → kˣ | t 2 = t 1}) with hBdef
  have hBC : ∀ x ∈ B, x ∈ centralizer (diagOmegaMinus k '' {t : Fin 3 → kˣ | t 2 = t 1}) :=
    fun x hx => (mem_inf.1 hx).2
  have h1 : ⁅B, B⁆ ≤ suppGL k (Set.range minusEmbA) :=
    SymplecticPilot.commutator_le_suppGL fun x hx a ha b' hb' =>
      mat_eq_zero_of_not_mem_range_minusEmbA hκ (hBC x hx) ha hb'
  set φ := blockHom B planeEmb_injective
    (fun x hx i c hc => (mat_planeEmb_eq_zero hκ (hBC x hx) hc i).1) with hφ
  have htype : ∀ x : B, ∃ n, AnisoType b c n ((φ x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    intro x
    have hiso : ∀ w, anisoNorm b c (((φ x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ w) =
        anisoNorm b c w := by
      intro w
      rw [hφ, coe_blockHom, ← statedQuadMinus_planeVec, ← statedQuadMinus_planeVec,
        ← mulVec_planeVec (fun a j ha => (mat_planeEmb_eq_zero hκ (hBC x x.2) ha j).2)]
      exact isometry_of_mem_statedOmega (mem_inf.1 x.2).1 _
    rcases isAnisoRot_or_isAnisoRef hirr hiso with h | h
    · exact ⟨0, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨1, Or.inr ⟨rfl, h⟩⟩
  set D := (anisoRotGL b c).comap φ with hD
  have h2 : ⁅B, B⁆ ≤ D.map B.subtype := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    refine ⟨⁅(⟨g, hg⟩ : B), ⟨h, hh⟩⁆, ?_, rfl⟩
    change φ ⁅(⟨g, hg⟩ : B), ⟨h, hh⟩⁆ ∈ anisoRotGL b c
    rw [map_commutatorElement, mem_anisoRotGL, commutatorElement_def, Units.val_mul,
      Units.val_mul, Units.val_mul]
    obtain ⟨m, hm⟩ := htype ⟨g, hg⟩
    obtain ⟨m', hm'⟩ := htype (⟨g, hg⟩ : B)⁻¹
    obtain ⟨n, hn⟩ := htype ⟨h, hh⟩
    obtain ⟨n', hn'⟩ := htype (⟨h, hh⟩ : B)⁻¹
    rw [map_inv] at hm' hn'
    exact isAnisoRot_mul_mul_mul (ne_zero_of_irr hirr) hm hm' hn hn'
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hDker : ⁅D, D⁆ ≤ φ.ker := by
    have hle : (⁅D, D⁆).map φ ≤ ⊥ := by
      rw [Subgroup.map_commutator, ← commutator_anisoRotGL (b := b) (c := c)]
      exact Subgroup.commutator_mono (Subgroup.map_comap_le _ _) (Subgroup.map_comap_le _ _)
    intro x hx
    exact (Subgroup.mem_bot.1 (hle ⟨x, hx, rfl⟩))
  have h3 : ⁅⁅B, B⁆, ⁅B, B⁆⁆ ≤ φ.ker.map B.subtype :=
    calc ⁅⁅B, B⁆, ⁅B, B⁆⁆ ≤ ⁅D.map B.subtype, D.map B.subtype⁆ := Subgroup.commutator_mono h2 h2
      _ = (⁅D, D⁆).map B.subtype := (Subgroup.map_commutator _ _ _).symm
      _ ≤ φ.ker.map B.subtype := Subgroup.map_mono hDker
  have h4 : φ.ker.map B.subtype ⊓ suppGL k (Set.range minusEmbA) ≤
      suppGL k (Set.range minusEmbThree) := by
    rintro _ ⟨⟨y, hyker, rfl⟩, hyS⟩
    have hy1 : ((y : GL ι₈ k) : Matrix ι₈ ι₈ k).submatrix planeEmb planeEmb = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hyker)
      rwa [hφ, coe_blockHom, Units.val_one] at this
    have hyC := hBC _ y.2
    intro a b' hab
    by_cases hA : a ∈ Set.range minusEmbA ∧ b' ∈ Set.range minusEmbA
    · by_cases ha : a ∈ Set.range planeEmb
      · obtain ⟨i, rfl⟩ := ha
        by_cases hb : b' ∈ Set.range planeEmb
        · obtain ⟨j, rfl⟩ := hb
          have h := congrFun (congrFun hy1 i) j
          rw [submatrix_apply] at h
          rw [B.coe_subtype, h, Matrix.one_apply, Matrix.one_apply]
          exact if_congr planeEmb_injective.eq_iff.symm rfl rfl
        · rw [B.coe_subtype, (mat_planeEmb_eq_zero hκ hyC hb i).1,
            Matrix.one_apply_ne (fun h => hb ⟨i, h⟩)]
      · by_cases hb : b' ∈ Set.range planeEmb
        · obtain ⟨j, rfl⟩ := hb
          rw [B.coe_subtype, (mat_planeEmb_eq_zero hκ hyC ha j).2,
            Matrix.one_apply_ne (fun h => ha ⟨j, h.symm⟩)]
        · exact absurd ⟨mem_range_minusEmbThree_of hA.1 ha, mem_range_minusEmbThree_of hA.2 hb⟩
            hab
    · exact hyS a b' hA
  have hpc : perfectCore B ≤ ⁅B, B⁆ :=
    calc perfectCore B = ⁅perfectCore B, perfectCore B⁆ := (perfectCore_perfect B).symm
      _ ≤ ⁅B, B⁆ := Subgroup.commutator_mono (perfectCore_le B) (perfectCore_le B)
  calc perfectCore B = ⁅perfectCore B, perfectCore B⁆ := (perfectCore_perfect B).symm
    _ ≤ ⁅⁅B, B⁆, ⁅B, B⁆⁆ := Subgroup.commutator_mono hpc hpc
    _ ≤ φ.ker.map B.subtype ⊓ suppGL k (Set.range minusEmbA) :=
        le_inf h3 ((Subgroup.commutator_le_self _).trans h1)
    _ ≤ suppGL k (Set.range minusEmbThree) := h4

theorem perfectCore_omegaMinus8_M3_eq_inf_suppGL (k : Type) [Field k] [Finite k] [CharP k 2]
    {b c : k} (hk : 4 ≤ Nat.card k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
      centralizer (diagOmegaMinus k '' {t : Fin 3 → kˣ | t 2 = t 1})) =
      perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
        centralizer (diagOmegaMinus k '' {t : Fin 3 → kˣ | t 2 = t 1}) ⊓
        suppGL k (Set.range minusEmbThree)) :=
  le_antisymm (le_perfectCore_of_perfect
      (le_inf (perfectCore_le _) (perfectCore_omegaMinus8_M3_le k hk hirr)) (perfectCore_perfect _))
    (perfectCore_mono inf_le_left)

end Reduction

section LeviPiece

variable {k : Type} [Field k]

theorem minusWeight_minusEmbThree_inl {t : Fin 3 → kˣ} (ht : t 2 = t 1) (i j : Fin 2) :
    minusWeight k t (minusEmbThree (Sum.inl i)) = minusWeight k t (minusEmbThree (Sum.inl j)) := by
  have h : ∀ i : Fin 2, t i.succ = t 1 := fun i => by
    fin_cases i
    · rfl
    · exact ht
  simp [minusWeight, minusEmbThree, h]

theorem minusWeight_minusEmbThree_inr {t : Fin 3 → kˣ} (ht : t 2 = t 1) (i j : Fin 2) :
    minusWeight k t (minusEmbThree (Sum.inr i)) = minusWeight k t (minusEmbThree (Sum.inr j)) := by
  have h : ∀ i : Fin 2, t i.succ = t 1 := fun i => by
    fin_cases i
    · rfl
    · exact ht
  simp [minusWeight, minusEmbThree, h]

theorem perfectCore_omegaMinus8_M3_eq (k : Type) [Field k] [Finite k] [CharP k 2] {b c : k}
    (hk : 4 ≤ Nat.card k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
      Subgroup.centralizer (diagOmegaMinus k '' {t | t 2 = t 1})) =
      (OmegaPilot.omegaLeviSL k 2).map (coordEmbedGL minusEmbThree minusEmbThree_injective) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hk
  rw [perfectCore_omegaMinus8_M3_eq_inf_suppGL k hk hirr]
  set C := centralizer (diagOmegaMinus k '' {t : Fin 3 → kˣ | t 2 = t 1}) with hC
  set φ := coordEmbedGL (F := k) minusEmbThree minusEmbThree_injective with hφ
  have hsplit := isCoordSplit_minusEmbThree (k := k) b c
  have hB : StatedOmega (StatedQuadMinus 4 k b c) ⊓ C ⊓ suppGL k (Set.range minusEmbThree) ≤
      (OmegaPilot.omegaLeviGL k 2).map φ := by
    intro x hx
    obtain ⟨⟨hxO, hxC⟩, hxS⟩ := hx
    obtain ⟨y, hy, rfl⟩ :=
      hsplit.statedOmega_inf_suppGL_le_map minusEmbThree_injective (mem_inf.2 ⟨hxO, hxS⟩)
    refine ⟨y, OmegaPilot.mem_omegaLeviGL_of_isometry (isometry_of_mem_isoClosure hy)
      (fun i j => ?_) (fun i j => ?_), rfl⟩
    · rw [← coordEmbedMat_apply_image minusEmbThree_injective (y : Matrix _ _ k) (Sum.inl i)
        (Sum.inr j)]
      exact (mat_minusEmbThree_inl_inr_eq_zero hκ hxC i j).1
    · rw [← coordEmbedMat_apply_image minusEmbThree_injective (y : Matrix _ _ k) (Sum.inr i)
        (Sum.inl j)]
      exact (mat_minusEmbThree_inl_inr_eq_zero hκ hxC i j).2
  have hL : (OmegaPilot.omegaLeviSL k 2).map φ ≤
      StatedOmega (StatedQuadMinus 4 k b c) ⊓ C ⊓ suppGL k (Set.range minusEmbThree) := by
    refine le_inf (le_inf ((map_mono (OmegaPilot.omegaLeviSL_le_statedOmega hk le_rfl)).trans
      (hsplit.map_statedOmega_le minusEmbThree_injective)) ?_) ?_
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨A, hA⟩ := OmegaPilot.mem_omegaLeviGL.1 (OmegaPilot.omegaLeviSL_le_omegaLeviGL hz)
      rw [hC, mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      refine ((SymplecticPilot.commute_of_diag_iff
        (fun a b hab => diagOmegaMinus_apply_ne t hab) _).2 fun a b' hab => ?_).eq.symm
      rw [diagOmegaMinus_apply_self, diagOmegaMinus_apply_self] at hab
      have hne : a ≠ b' := fun e => hab (e ▸ rfl)
      by_cases h : a ∈ Set.range minusEmbThree ∧ b' ∈ Set.range minusEmbThree
      · obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := h
        rw [hφ, coe_coordEmbedGL, coordEmbedMat_apply_image minusEmbThree_injective, ← hA,
          OmegaPilot.coe_leviEmbedGL]
        rcases u with i | i <;> rcases v with j | j
        · exact absurd (minusWeight_minusEmbThree_inl ht i j) hab
        · simp
        · simp
        · exact absurd (minusWeight_minusEmbThree_inr ht i j) hab
      · rw [hφ, coe_coordEmbedGL, coordEmbedMat_apply_of_not_mem _ h, Matrix.one_apply_ne hne]
    · rintro _ ⟨z, -, rfl⟩
      exact coordEmbedGL_mem_suppGL minusEmbThree_injective z
  refine le_antisymm ?_ (le_perfectCore_of_perfect hL
    (by rw [← Subgroup.map_commutator, OmegaPilot.commutator_omegaLeviSL hk le_rfl]))
  calc perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓ C ⊓
        suppGL k (Set.range minusEmbThree)) ≤
        perfectCore ((OmegaPilot.omegaLeviGL k 2).map φ) := perfectCore_mono hB
    _ = (perfectCore (OmegaPilot.omegaLeviGL k 2)).map φ :=
        (CFSG.Quasithin.map_perfectCore _ _).symm
    _ ≤ (OmegaPilot.omegaLeviSL k 2).map φ := by
        refine map_mono ?_
        calc perfectCore (OmegaPilot.omegaLeviGL k 2) =
              ⁅perfectCore (OmegaPilot.omegaLeviGL k 2),
                perfectCore (OmegaPilot.omegaLeviGL k 2)⁆ := (perfectCore_perfect _).symm
          _ ≤ ⁅OmegaPilot.omegaLeviGL k 2, OmegaPilot.omegaLeviGL k 2⁆ :=
              Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)
          _ ≤ OmegaPilot.omegaLeviSL k 2 := OmegaPilot.commutator_omegaLeviGL_le

theorem card_perfectCore_omegaMinus8_M3 (k : Type) [Field k] [Finite k] [CharP k 2] {b c : k}
    (hk : 4 ≤ Nat.card k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
      Subgroup.centralizer (diagOmegaMinus k '' {t | t 2 = t 1}))) = ordSL 2 (Nat.card k) := by
  rw [perfectCore_omegaMinus8_M3_eq k hk hirr,
    Subgroup.card_map_of_injective (coordEmbedGL_injective minusEmbThree_injective),
    ← Nat.card_congr (OmegaPilot.omegaLeviSLEquiv (F := k) (k := 2)).toEquiv]
  exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)

end LeviPiece

end CFSG.SeitzReduction.F4Pilot
