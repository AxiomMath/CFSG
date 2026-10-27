module

public import CFSG.Open.StatedDefs
public import Mathlib

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open

variable {F : Type} [Field F]

@[expose] noncomputable def diagHom : (Fin 4 → Fˣ) →* GL (Fin 4) F :=
  (Units.map (Matrix.diagonalRingHom (Fin 4) F : (Fin 4 → F) →+* Matrix (Fin 4) (Fin 4) F).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin 4 => F)).symm.toMonoidHom

private lemma diagHom_coe (a : Fin 4 → Fˣ) :
    ((diagHom a : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal fun i => (a i : F) := rfl

theorem diagHom_mulVec (a : Fin 4 → Fˣ) (v : Fin 4 → F) :
    ((diagHom a : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec v = fun i => (a i : F) * v i := by
  funext i
  rw [diagHom_coe, Matrix.mulVec_diagonal]

theorem diagHom_injective : Function.Injective (diagHom (F := F)) := by
  intro a b hab
  funext i
  have ha := congrFun (diagHom_mulVec (F := F) a (Pi.single i 1)) i
  have hb := congrFun (diagHom_mulVec (F := F) b (Pi.single i 1)) i
  rw [hab] at ha
  have key : (a i : F) * (Pi.single i 1 : Fin 4 → F) i =
      (b i : F) * (Pi.single i 1 : Fin 4 → F) i := ha.symm.trans hb
  simp only [Pi.single_eq_same, mul_one] at key
  exact Units.ext key

@[expose] def torusT (F : Type) [Field F] (q : ℕ) : Subgroup (Fin 4 → Fˣ) where
  carrier := {a | (∀ i, a i ^ (q + 1) = 1) ∧ ∏ i, a i = 1}
  one_mem' := ⟨fun i => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.mul_apply]
      rw [mul_pow, ha1 i, hb1 i, mul_one]
    · simp only [Pi.mul_apply]
      rw [Finset.prod_mul_distrib, ha2, hb2, mul_one]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.inv_apply]
      rw [inv_pow, ha1 i, inv_one]
    · simp only [Pi.inv_apply]
      rw [Finset.prod_inv_distrib, ha2, inv_one]

@[expose] def torusTi (F : Type) [Field F] (q : ℕ) (i : Fin 4) : Subgroup (Fin 4 → Fˣ) :=
  torusT F q ⊓ (Pi.evalMonoidHom (fun _ : Fin 4 => Fˣ) i).ker

theorem mem_torusTi {q : ℕ} {i : Fin 4} {a : Fin 4 → Fˣ} :
    a ∈ torusTi F q i ↔ a ∈ torusT F q ∧ a i = 1 := Iff.rfl

private lemma mem_torusT_iff {q : ℕ} {a : Fin 4 → Fˣ} :
    a ∈ torusT F q ↔ (∀ i, a i ^ (q + 1) = 1) ∧ ∏ i, a i = 1 := Iff.rfl

theorem diagHom_mem_statedSU {q : ℕ} (hq : 1 ≤ q) {a : Fin 4 → Fˣ} (ha : a ∈ torusT F q) :
    diagHom a ∈ StatedSU 4 q F := by
  obtain ⟨ha1, ha2⟩ := mem_torusT_iff.1 ha
  unfold StatedSU
  refine Subgroup.subset_closure ?_
  have h0 : (0 : F) ^ q = 0 := zero_pow (by omega)
  have hi : ∀ i, (a i : F) ^ q * (a i : F) = 1 := fun i => by
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, ha1 i, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [diagHom_coe, Matrix.det_diagonal, ← Units.coe_prod, ha2, Units.val_one]
  · rw [diagHom_coe, Matrix.diagonal_map (f := fun x : F => x ^ q) h0, Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hi i

@[expose] noncomputable def torusDiagSU (q : ℕ) (hq : 1 ≤ q) : ↥(torusT F q) →* ↥(StatedSU 4 q F) :=
  ((diagHom (F := F)).comp (torusT F q).subtype).codRestrict (StatedSU 4 q F)
    fun a => diagHom_mem_statedSU hq a.2

private lemma torusDiagSU_coe {q : ℕ} (hq : 1 ≤ q) (c : ↥(torusT F q)) :
    (((torusDiagSU q hq c : ↥(StatedSU 4 q F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal fun i => ((c : Fin 4 → Fˣ) i : F) :=
  rfl

theorem torusDiagSU_mulVec {q : ℕ} (hq : 1 ≤ q) (a : ↥(torusT F q)) (v : Fin 4 → F) :
    (((torusDiagSU q hq a : ↥(StatedSU 4 q F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec v =
      fun i => ((a : Fin 4 → Fˣ) i : F) * v i := by
  rw [torusDiagSU_coe hq a]
  funext i
  rw [Matrix.mulVec_diagonal]

theorem torusDiagSU_injective {q : ℕ} (hq : 1 ≤ q) : Function.Injective (torusDiagSU (F := F) q hq) := by
  intro a b hab
  apply Subtype.ext
  apply diagHom_injective
  exact congrArg Subtype.val hab

theorem torusT_pow {q : ℕ} (a : ↥(torusT F q)) : a ^ (q + 1) = 1 := by
  obtain ⟨ha1, -⟩ := mem_torusT_iff.1 a.2
  apply Subtype.ext
  funext i
  rw [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply]
  exact ha1 i

private lemma mulSingle_mul_inv_mem {q : ℕ} {x : Fˣ} (hx : x ^ (q + 1) = 1) {k l : Fin 4}
    (hkl : k ≠ l) : Pi.mulSingle k x * Pi.mulSingle l x⁻¹ ∈ torusT F q := by
  have hpow : ∀ (c : Fin 4) (y : Fˣ), y ^ (q + 1) = 1 → ∀ m : Fin 4,
      (Pi.mulSingle (M := fun _ : Fin 4 => Fˣ) c y m) ^ (q + 1) = 1 := by
    intro c y hy m
    by_cases h : m = c
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact hy
    · rw [Pi.mulSingle_eq_of_ne h, one_pow]
  refine mem_torusT_iff.2 ⟨fun m => ?_, ?_⟩
  · rw [Pi.mul_apply, mul_pow, hpow k x hx m,
      hpow l x⁻¹ (by rw [inv_pow, hx, inv_one]) m, mul_one]
  · simp [Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle']

theorem torusTi_sup {q : ℕ} {i j : Fin 4} (hij : i ≠ j) :
    torusTi F q i ⊔ torusTi F q j = torusT F q := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  intro a ha
  obtain ⟨ha1, ha2⟩ := mem_torusT_iff.1 ha
  have hk : ∀ i j : Fin 4, i ≠ j → ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := hk i j hij
  have hb'T : Pi.mulSingle i (a i) * Pi.mulSingle k (a i)⁻¹ ∈ torusT F q :=
    mulSingle_mul_inv_mem (ha1 i) hki.symm
  have hb'j : Pi.mulSingle i (a i) * Pi.mulSingle k (a i)⁻¹ ∈ torusTi F q j := by
    rw [mem_torusTi]
    refine ⟨hb'T, ?_⟩
    rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hij.symm, Pi.mulSingle_eq_of_ne hkj.symm, mul_one]
  have hbi : a * (Pi.mulSingle i (a i) * Pi.mulSingle k (a i)⁻¹)⁻¹ ∈ torusTi F q i := by
    rw [mem_torusTi]
    refine ⟨mul_mem ha (inv_mem hb'T), ?_⟩
    simp [Pi.mulSingle_eq_of_ne hki.symm]
  have h := Subgroup.mul_mem_sup hbi hb'j
  rwa [inv_mul_cancel_right] at h

theorem torusTi_le (q : ℕ) (i : Fin 4) : torusTi F q i ≤ torusT F q := inf_le_left

theorem exists_mem_torusTi_apply {q : ℕ} {ω : F} (hω : ω ^ (q + 1) = 1) (hω1 : ω ≠ 1)
    {j k : Fin 4} (hjk : k ≠ j) :
    ∃ a ∈ torusTi F q j, ((a k : Fˣ) : F) = ω := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero q)] at hω
    exact zero_ne_one hω
  obtain ⟨ω', hω'⟩ : ∃ w : Fˣ, (w : F) = ω := ⟨Units.mk0 ω hω0, Units.val_mk0 hω0⟩
  have hω'pow : ω' ^ (q + 1) = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hω', Units.val_one]; exact hω)
  have hl : ∀ j k : Fin 4, k ≠ j → ∃ l : Fin 4, l ≠ j ∧ l ≠ k := by decide
  obtain ⟨l, hlj, hlk⟩ := hl j k hjk
  refine ⟨Pi.mulSingle k ω' * Pi.mulSingle l ω'⁻¹, ?_, ?_⟩
  · rw [mem_torusTi]
    refine ⟨mulSingle_mul_inv_mem hω'pow hlk.symm, ?_⟩
    rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hjk.symm, Pi.mulSingle_eq_of_ne hlj.symm, mul_one]
  · rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hlk.symm, mul_one, hω']

theorem exists_mem_torusT_head {q : ℕ} {ω : F} (hω : ω ^ (q + 1) = 1) (hω0 : ω ≠ 0) :
    ∃ a ∈ torusT F q, ((a 0 : Fˣ) : F) = ω := by
  obtain ⟨ω', hω'⟩ : ∃ w : Fˣ, (w : F) = ω := ⟨Units.mk0 ω hω0, Units.val_mk0 hω0⟩
  have hω'pow : ω' ^ (q + 1) = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hω', Units.val_one]; exact hω)
  refine ⟨Pi.mulSingle 0 ω' * Pi.mulSingle 1 ω'⁻¹, mulSingle_mul_inv_mem hω'pow (by decide), ?_⟩
  rw [Pi.mul_apply, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (show (0 : Fin 4) ≠ 1 by decide), mul_one, hω']

private lemma permMatrix_apply' (ρ : Equiv.Perm (Fin 4)) (i k : Fin 4) :
    ρ.permMatrix F i k = if ρ i = k then (1 : F) else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

private lemma permMatrix_mul_diagonal (ρ : Equiv.Perm (Fin 4)) (d : Fin 4 → F) :
    ρ.permMatrix F * Matrix.diagonal d = Matrix.diagonal (fun i => d (ρ i)) * ρ.permMatrix F := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, permMatrix_apply']
  split_ifs with h
  · subst h
    simp
  · simp

private lemma permMatrix_mul_transpose_eq_one (ρ : Equiv.Perm (Fin 4)) :
    ρ.permMatrix F * (ρ.permMatrix F)ᵀ = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

private lemma permMatrix_transpose_mul_eq_one (ρ : Equiv.Perm (Fin 4)) :
    (ρ.permMatrix F)ᵀ * ρ.permMatrix F = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

private lemma permMatrix_map_pow (ρ : Equiv.Perm (Fin 4)) {q : ℕ} (hq : 1 ≤ q) :
    (ρ.permMatrix F).map (fun x : F => x ^ q) = ρ.permMatrix F := by
  ext i k
  rw [Matrix.map_apply, permMatrix_apply']
  split_ifs
  · exact one_pow q
  · exact zero_pow (by omega)

private lemma permMatrix_det_eq_one (ρ : Equiv.Perm (Fin 4)) (h2 : (2 : F) = 0) :
    (ρ.permMatrix F).det = 1 := by
  have hneg : (-1 : F) = 1 := by
    have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    exact neg_eq_of_add_eq_zero_left h11
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h
  · simp [h]
  · simp [h, hneg]

theorem exists_permSU {q : ℕ} (hq : 1 ≤ q) (h2 : (2 : F) = 0) :
    ∃ (P : ↥(StatedSU 4 q F)) (σ : Equiv.Perm (Fin 4)),
      (∀ i j : Fin 4, ∃ k : ℕ, (σ ^ k) i = j) ∧
      ∀ a : ↥(torusT F q), ∃ a' : ↥(torusT F q),
        (∀ i, (a' : Fin 4 → Fˣ) (σ i) = (a : Fin 4 → Fˣ) i) ∧
        P * torusDiagSU q hq a * P⁻¹ = torusDiagSU q hq a' := by
  have htrans : ∀ i j : Fin 4, ∃ k : ℕ, (finRotate 4 ^ k) i = j := by
    have key : ∀ i j : Fin 4, ∃ k : Fin 4, (finRotate 4 ^ (k : ℕ)) i = j := by decide
    intro i j
    obtain ⟨k, hk⟩ := key i j
    exact ⟨(k : ℕ), hk⟩
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin 4) F,
      (P : Matrix (Fin 4) (Fin 4) F) = ((finRotate 4)⁻¹).permMatrix F :=
    ⟨Units.mk _ _ (permMatrix_mul_transpose_eq_one ((finRotate 4)⁻¹))
      (permMatrix_transpose_mul_eq_one ((finRotate 4)⁻¹)), rfl⟩
  have hPmem : P ∈ StatedSU 4 q F := by
    unfold StatedSU
    refine Subgroup.subset_closure ?_
    refine ⟨?_, ?_⟩
    · rw [hP, permMatrix_det_eq_one _ h2]
    · rw [hP, permMatrix_map_pow _ hq, permMatrix_transpose_mul_eq_one]
  refine ⟨⟨P, hPmem⟩, finRotate 4, htrans, fun a => ?_⟩
  obtain ⟨ha1, ha2⟩ := mem_torusT_iff.1 a.2
  have hmem : (fun i => (a : Fin 4 → Fˣ) ((finRotate 4)⁻¹ i)) ∈ torusT F q := by
    refine mem_torusT_iff.2 ⟨fun i => ha1 _, ?_⟩
    exact (Equiv.prod_comp (finRotate 4)⁻¹ (fun i => (a : Fin 4 → Fˣ) i)).trans ha2
  refine ⟨⟨_, hmem⟩, fun i => ?_, ?_⟩
  · simp
  · refine mul_inv_eq_of_eq_mul ?_
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, torusDiagSU_coe, hP]
    exact permMatrix_mul_diagonal _ _

end CFSG.LocalAnalysis.RankThreeUC
