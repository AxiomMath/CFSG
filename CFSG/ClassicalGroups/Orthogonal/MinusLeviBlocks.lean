module

public import CFSG.ClassicalGroups.Orthogonal.MinusSplitTorus
public import CFSG.LieType.Universal.Spin.Twisted.ShortAction

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix CFSG.Open
open CFSG.ComponentClassification.UnbalancingLocal.OrthogonalBlocks
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] {b c : K}

theorem coe_minusDiagGL_apply_inl {n r : ℕ} (hr : Odd r) {d : Fin (n - 1) → Kˣ}
    (hd : ∀ j, d j ^ r = 1) (i : Fin (n - 1)) :
    (((minusDiagGL (b := b) (c := c) (n := n) hr d hd :
        StatedOmega (StatedQuadMinus n K b c)) :
        GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K)
      (Sum.inl i) (Sum.inl i) = (d i : K) := by
  rw [coe_minusDiagGL, coe_diagGL, Matrix.diagonal_apply_eq]
  simp [torusEntMinus]

theorem coe_minusDiagGL_zpow_apply_inl {n r : ℕ} (hr : Odd r) {d : Fin (n - 1) → Kˣ}
    (hd : ∀ j, d j ^ r = 1) (k : ℤ) (i : Fin (n - 1)) :
    ((((minusDiagGL (b := b) (c := c) (n := n) hr d hd :
        StatedOmega (StatedQuadMinus n K b c)) ^ k : StatedOmega (StatedQuadMinus n K b c)) :
        GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K)
      (Sum.inl i) (Sum.inl i) = (d i : K) ^ k := by
  rw [Subgroup.coe_zpow, coe_minusDiagGL, ← map_zpow, coe_diagGL, Matrix.diagonal_apply_eq,
    ← map_zpow]
  show ((d ^ k) i : K) = (d i : K) ^ k
  rw [Pi.pow_apply, Units.val_zpow_eq_zpow_val]

theorem minusDiagGL_pow_eq_one {n r : ℕ} (hr : Odd r) {d : Fin (n - 1) → Kˣ}
    (hd : ∀ j, d j ^ r = 1) :
    (minusDiagGL (b := b) (c := c) (n := n) hr d hd) ^ r = 1 := by
  have hdr : d ^ r = 1 := by funext j; exact hd j
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one, coe_minusDiagGL, ← map_pow, hdr, map_one]

theorem minusDiagGL_zpow_eq_one {n r : ℕ} (hr : Odd r) {d : Fin (n - 1) → Kˣ}
    (hd : ∀ j, d j ^ r = 1) {k : ℤ} (hdk : d ^ k = 1) :
    (minusDiagGL (b := b) (c := c) (n := n) hr d hd) ^ k = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_zpow, Subgroup.coe_one, coe_minusDiagGL, ← map_zpow, hdk, map_one]

theorem fromBlocks_mul_comm {l m : Type*} [Fintype l] [Fintype m]
    {A A' : Matrix l l K} {B B' : Matrix m m K} (hA : A * A' = A' * A)
    (hB : B * B' = B' * B) :
    fromBlocks A 0 0 B * fromBlocks A' 0 0 B' = fromBlocks A' 0 0 B' * fromBlocks A 0 0 B := by
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hA, hB]

@[expose] def padGLHom : GL (Fin 2) K →* GL (Fin 3) K :=
  (Units.map (MonoidHom.ofClass
    (reindexAlgEquiv K K (finSumFinEquiv (m := 2) (n := 1))))).comp
    (blockDiagHom (MonoidHom.id (GL (Fin 2) K)) 1)

theorem coe_padGLHom (A : GL (Fin 2) K) :
    (padGLHom A : Matrix (Fin 3) (Fin 3) K) =
      reindex (finSumFinEquiv (m := 2) (n := 1)) (finSumFinEquiv (m := 2) (n := 1))
        (fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0 1) := by
  simp [padGLHom, coe_blockDiagHom, Matrix.coe_reindexAlgEquiv]

theorem det_padGLHom (A : GL (Fin 2) K) :
    (padGLHom A : Matrix (Fin 3) (Fin 3) K).det = (A : Matrix (Fin 2) (Fin 2) K).det := by
  rw [coe_padGLHom, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    mul_one]

theorem padGLHom_eq_one_iff {A : GL (Fin 2) K} : padGLHom A = 1 ↔ A = 1 := by
  constructor
  · intro h
    have h1 : reindex (finSumFinEquiv (m := 2) (n := 1)) (finSumFinEquiv (m := 2) (n := 1))
        (fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0 1) =
        (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [← coe_padGLHom, h, Units.val_one]
    have h2 : fromBlocks (A : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin 2) (Fin 1) K)
        (0 : Matrix (Fin 1) (Fin 2) K) (1 : Matrix (Fin 1) (Fin 1) K) =
        (1 : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) K) := by
      refine (Matrix.reindex (finSumFinEquiv (m := 2) (n := 1))
        (finSumFinEquiv (m := 2) (n := 1))).injective ?_
      simp only [Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      exact h1
    rw [← Matrix.fromBlocks_one] at h2
    exact Units.ext (fromBlocks_inj.1 h2).1
  · rintro rfl
    exact map_one _

theorem padGLHom_injective : Function.Injective (padGLHom (K := K)) := by
  intro A B h
  have h1 : padGLHom (A * B⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [padGLHom_eq_one_iff, mul_inv_eq_one] at h1
  exact h1

theorem diagonal_padGLHom_commute (f : Fin 3 → K) (hf : f 0 = f 1) (A : GL (Fin 2) K) :
    diagonal f * (padGLHom A : Matrix (Fin 3) (Fin 3) K) =
      (padGLHom A : Matrix (Fin 3) (Fin 3) K) * diagonal f := by
  classical
  have hE0 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (0 : Fin 2)) = (0 : Fin 3) := by
    rw [finSumFinEquiv_apply_left]; rfl
  have hE1 : finSumFinEquiv (m := 2) (n := 1) (Sum.inl (1 : Fin 2)) = (1 : Fin 3) := by
    rw [finSumFinEquiv_apply_left]; rfl
  have hE2 : finSumFinEquiv (m := 2) (n := 1) (Sum.inr (0 : Fin 1)) = (2 : Fin 3) := by
    rw [finSumFinEquiv_apply_right]; rfl
  have hcoe : (Sum.elim (fun _ : Fin 2 => f 0) (fun _ : Fin 1 => f 2)) =
      f ∘ finSumFinEquiv (m := 2) (n := 1) := by
    funext x
    rcases x with j | k
    · rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) j with rfl | rfl
      · show f 0 = f (finSumFinEquiv (m := 2) (n := 1) (Sum.inl 0))
        rw [hE0]
      · show f 0 = f (finSumFinEquiv (m := 2) (n := 1) (Sum.inl 1))
        rw [hE1]
        exact hf
    · rw [Subsingleton.elim k 0]
      show f 2 = f (finSumFinEquiv (m := 2) (n := 1) (Sum.inr 0))
      rw [hE2]
  have hdiag : diagonal f = reindex (finSumFinEquiv (m := 2) (n := 1))
      (finSumFinEquiv (m := 2) (n := 1))
      (fromBlocks (diagonal fun _ : Fin 2 => f 0) 0 0 (diagonal fun _ : Fin 1 => f 2)) := by
    rw [Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv,
      hcoe]
    congr 1
    funext i
    simp
  rw [hdiag, coe_padGLHom, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  congr 1
  exact fromBlocks_mul_comm (by ext i j; rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm])
    (by ext i j; rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm])

theorem statedQuadMinus_eq_sum_planeNorm {n : ℕ}
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c v = (∑ i : Fin (n - 1), v (Sum.inl i) * v (Sum.inr (Sum.inl i))) +
      CFSG.LieType.Universal.Spin.Twisted.planeNorm b c
        (fun u => v (Sum.inr (Sum.inr u))) := by
  simp only [StatedQuadMinus, CFSG.LieType.Universal.Spin.Twisted.planeNorm]
  ring

theorem coe_tail_sigma {m : ℕ} (qW : (Fin 2 → K) → K) (g : GL (Fin m) K) :
    ((HypForm.tail m (Fin 2) qW).σ g : Matrix (Fin m ⊕ Fin 2) (Fin m ⊕ Fin 2) K) =
      fromBlocks ((invTranspose g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) 0 0 1 := by
  rw [show (HypForm.tail m (Fin 2) qW).σ =
      blockDiagHom invTranspose (1 : GL (Fin m) K →* GL (Fin 2) K) from rfl, coe_blockDiagHom]
  simp

theorem rho_diagGL {m : ℕ} (qW : (Fin 2 → K) → K) (d : Fin m → Kˣ) :
    (HypForm.tail m (Fin 2) qW).rho (diagGL d) = diagGL (torusEntMinus m K d) := by
  apply Units.ext
  have hσ : ((HypForm.tail m (Fin 2) qW).σ (diagGL d) :
      Matrix (Fin m ⊕ Fin 2) (Fin m ⊕ Fin 2) K) =
      fromBlocks (diagonal fun i => ((d i)⁻¹ : K)) 0 0 1 := by
    rw [show (HypForm.tail m (Fin 2) qW).σ =
        blockDiagHom invTranspose (1 : GL (Fin m) K →* GL (Fin 2) K) from rfl,
      coe_blockDiagHom, coe_invTranspose, ← map_inv, coe_diagGL, Matrix.diagonal_transpose,
      show ((1 : GL (Fin m) K →* GL (Fin 2) K) (diagGL d) : Matrix (Fin 2) (Fin 2) K) = 1 from by
        simp]
    congr 1
    funext i
    simp
  rw [show ((HypForm.tail m (Fin 2) qW).rho (diagGL d) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) =
      fromBlocks ((diagGL d : Matrix (Fin m) (Fin m) K)) 0 0
        ((HypForm.tail m (Fin 2) qW).σ (diagGL d) : Matrix _ _ K) from rfl, hσ, coe_diagGL,
    coe_diagGL]
  ext i j
  rcases i with i | i | u <;> rcases j with j | j | v <;>
    simp [Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply, torusEntMinus]

theorem commute_diagGL_torusEntMinus_rho_padGLHom (qW : (Fin 2 → K) → K) (d : Fin 3 → Kˣ)
    (hd : d 0 = d 1) (A : GL (Fin 2) K) :
    Commute (diagGL (torusEntMinus 3 K d)) ((HypForm.tail 3 (Fin 2) qW).rho (padGLHom A)) := by
  have hmat : (diagGL d : Matrix (Fin 3) (Fin 3) K) *
      (padGLHom A : Matrix (Fin 3) (Fin 3) K) =
      (padGLHom A : Matrix (Fin 3) (Fin 3) K) * diagGL d := by
    rw [coe_diagGL]
    exact diagonal_padGLHom_commute (fun i => (d i : K))
      (by simpa using congrArg (fun u : Kˣ => (u : K)) hd) A
  have hcomm : Commute (diagGL d) (padGLHom A) := Units.ext hmat
  have hmap := hcomm.map (HypForm.tail 3 (Fin 2) qW).rho
  rwa [rho_diagGL] at hmap

@[expose] def planeBlockHom (m : ℕ) : GL (Fin 2) K →* GL (Fin m ⊕ Fin m ⊕ Fin 2) K :=
  blockDiagHom (1 : GL (Fin 2) K →* GL (Fin m) K)
    (blockDiagHom (1 : GL (Fin 2) K →* GL (Fin m) K) (MonoidHom.id (GL (Fin 2) K)))

theorem coe_planeBlockHom {m : ℕ} (Y : GL (Fin 2) K) :
    (planeBlockHom m Y : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) =
      fromBlocks (1 : Matrix (Fin m) (Fin m) K) 0 0
        (fromBlocks (1 : Matrix (Fin m) (Fin m) K) 0 0 (Y : Matrix (Fin 2) (Fin 2) K)) := by
  simp [planeBlockHom, coe_blockDiagHom]

theorem eq_one_of_planeBlockHom_eq_rho {m : ℕ} (qW : (Fin 2 → K) → K) {Y : GL (Fin 2) K}
    {g : GL (Fin m) K} (h : planeBlockHom m Y = (HypForm.tail m (Fin 2) qW).rho g) : Y = 1 := by
  have h' := congrArg (fun x : GL (Fin m ⊕ Fin m ⊕ Fin 2) K =>
    (x : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)) h
  rw [coe_planeBlockHom, HypForm.coe_rho, coe_tail_sigma] at h'
  exact Units.ext ((fromBlocks_inj.1 ((fromBlocks_inj.1 h').2.2.2)).2.2.2)

theorem planeBlockHom_mulVec {m : ℕ} (Y : GL (Fin 2) K) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    (planeBlockHom m Y : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v =
      Sum.elim (v ∘ Sum.inl)
        (Sum.elim (v ∘ Sum.inr ∘ Sum.inl) (Y *ᵥ (v ∘ Sum.inr ∘ Sum.inr))) := by
  rw [coe_planeBlockHom]
  funext x
  rcases x with j | j | u <;>
    simp [Matrix.fromBlocks_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec]

theorem planeBlockHom_commute_rho {m : ℕ} (qW : (Fin 2 → K) → K) (g : GL (Fin m) K)
    (Y : GL (Fin 2) K) :
    Commute ((HypForm.tail m (Fin 2) qW).rho g) (planeBlockHom m Y) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, HypForm.coe_rho, coe_tail_sigma, coe_planeBlockHom]
  exact fromBlocks_mul_comm (by rw [Matrix.mul_one, Matrix.one_mul])
    (fromBlocks_mul_comm (by rw [Matrix.mul_one, Matrix.one_mul])
      (by rw [Matrix.one_mul, Matrix.mul_one]))

theorem planeBlockHom_commute_diagGL {m : ℕ} (d : Fin m → Kˣ) (Y : GL (Fin 2) K) :
    Commute (diagGL (torusEntMinus m K d)) (planeBlockHom m Y) := by
  rw [← rho_diagGL (m := m) (fun _ => 0) d]
  exact planeBlockHom_commute_rho _ _ _

theorem planeBlockHom_injective {m : ℕ} :
    Function.Injective (planeBlockHom (m := m) (K := K)) := by
  intro Y Z h
  have h1 : planeBlockHom (m := m) (Y * Z⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : (Y * Z⁻¹ : GL (Fin 2) K) = 1 := by
    have hY : ∀ u v : Fin 2, ((Y * Z⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) u v =
        (1 : Matrix (Fin 2) (Fin 2) K) u v := by
      intro u v
      have h3 := congrArg (fun g : GL (Fin m ⊕ Fin m ⊕ Fin 2) K =>
        (g : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)) h1
      rw [coe_planeBlockHom, Units.val_one] at h3
      have h4 := congrFun (congrFun h3 (Sum.inr (Sum.inr u))) (Sum.inr (Sum.inr v))
      simpa [Matrix.fromBlocks, Matrix.one_apply] using h4
    exact Units.ext (Matrix.ext hY)
  rwa [mul_inv_eq_one] at h2

theorem orderOf_planeBlockHom {m : ℕ} (Y : GL (Fin 2) K) :
    orderOf (planeBlockHom m Y) = orderOf Y :=
  orderOf_injective (planeBlockHom (m := m)) planeBlockHom_injective Y

theorem planeBlockHom_mulVec_comp_minusFlip {m : ℕ} (i : Fin m) (Y : GL (Fin 2) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    (planeBlockHom m Y : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ
        (v ∘ ⇑(minusFlip m i)) =
      ((planeBlockHom m Y : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v) ∘
        ⇑(minusFlip m i) := by
  rw [planeBlockHom_mulVec, planeBlockHom_mulVec]
  funext x
  rcases x with j | j | u
  · by_cases hj : j = i
    · subst hj
      simp only [Function.comp_apply, minusFlip_apply_inl, Sum.elim_inl, Sum.elim_inr]
    · simp only [Function.comp_apply, minusFlip_apply_inl_of_ne hj, Sum.elim_inl]
  · by_cases hj : j = i
    · subst hj
      simp only [Function.comp_apply, minusFlip_apply_inr, Sum.elim_inl, Sum.elim_inr]
    · simp only [Function.comp_apply, minusFlip_apply_inr_of_ne hj, Sum.elim_inl, Sum.elim_inr]
  · have hfun : (v ∘ ⇑(minusFlip m i)) ∘ Sum.inr ∘ Sum.inr = v ∘ Sum.inr ∘ Sum.inr := by
      funext w
      simp only [Function.comp_apply, minusFlip_apply_inr_inr]
    simp only [hfun, Function.comp_apply, minusFlip_apply_inr_inr, Sum.elim_inr]

theorem planeBlockHom_commute_permGL_minusFlip {m : ℕ} (i : Fin m) (Y : GL (Fin 2) K) :
    Commute (permGL (K := K) (minusFlip m i)) (planeBlockHom m Y) := by
  apply CFSG.SectionRank.ClassicalEven.OrthRot.gl_ext
  intro v
  have hL : (↑(permGL (K := K) (minusFlip m i) * planeBlockHom m Y) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v
      = ((↑(planeBlockHom m Y) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v) ∘
        ⇑(minusFlip m i) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, mulVec_permGL, minusFlip_inv]
  have hR : (↑(planeBlockHom m Y * permGL (K := K) (minusFlip m i)) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v
      = ((↑(planeBlockHom m Y) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *ᵥ v) ∘
        ⇑(minusFlip m i) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, mulVec_permGL, minusFlip_inv,
      planeBlockHom_mulVec_comp_minusFlip]
  rw [hL, hR]

theorem planeBlockHom_isometry {n : ℕ} (Y : GL (Fin 2) K)
    (hY : ∀ z : Fin 2 → K,
      CFSG.LieType.Universal.Spin.Twisted.planeNorm b c (Y *ᵥ z) =
        CFSG.LieType.Universal.Spin.Twisted.planeNorm b c z)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c
        ((planeBlockHom (n - 1) Y :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) *ᵥ v) =
      StatedQuadMinus n K b c v := by
  rw [planeBlockHom_mulVec, statedQuadMinus_eq_sum_planeNorm,
    statedQuadMinus_eq_sum_planeNorm]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
  rw [hY]
  rfl

end CFSG.ClassicalGroups.Orthogonal
