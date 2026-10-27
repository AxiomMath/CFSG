module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112MLocal
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix

section Diag

variable (F : Type) [Field F]

@[expose] noncomputable def t112mDiag : (Fˣ × Fˣ × Fˣ) →* GL (Fin 3) F where
  toFun x :=
    { val := diagonal ![(x.1 : F), (x.2.1 : F), (x.2.2 : F)]
      inv := diagonal ![((x.1⁻¹ : Fˣ) : F), ((x.2.1⁻¹ : Fˣ) : F), ((x.2.2⁻¹ : Fˣ) : F)]
      val_inv := by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        ext i
        fin_cases i <;> simp
      inv_val := by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        ext i
        fin_cases i <;> simp }
  map_one' := by
    apply Units.ext
    show diagonal _ = 1
    rw [← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  map_mul' x y := by
    apply Units.ext
    show diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp

variable {F}

theorem t112mDiag_val (x : Fˣ × Fˣ × Fˣ) :
    ((t112mDiag F x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(x.1 : F), (x.2.1 : F), (x.2.2 : F)] := rfl

theorem t112mDiag_injective : Function.Injective (t112mDiag F) := by
  intro x y h
  have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [t112mDiag_val] at h1
  have e0 := congrFun (congrFun h1 0) 0
  have e1 := congrFun (congrFun h1 1) 1
  have e2 := congrFun (congrFun h1 2) 2
  simp only [diagonal_apply_eq] at e0 e1 e2
  exact Prod.ext (Units.ext e0) (Prod.ext (Units.ext e1) (Units.ext e2))

theorem t112mDiag_mem_SL {x : Fˣ × Fˣ × Fˣ} (h : x.1 * x.2.1 * x.2.2 = 1) :
    t112mDiag F x ∈ CFSG.Open.StatedSL 3 F := by
  apply Subgroup.subset_closure
  show (diagonal ![(x.1 : F), (x.2.1 : F), (x.2.2 : F)]).det = 1
  rw [det_diagonal, Fin.prod_univ_three]
  have := congrArg Units.val h
  simpa using this

theorem t112mDiag_mem_SU {q : ℕ} (hq : q ≠ 0) {x : Fˣ × Fˣ × Fˣ} (h : x.1 * x.2.1 * x.2.2 = 1)
    (h1 : (x.1 : F) ^ q * x.1 = 1) (h2 : (x.2.1 : F) ^ q * x.2.1 = 1)
    (h3 : (x.2.2 : F) ^ q * x.2.2 = 1) :
    t112mDiag F x ∈ CFSG.Open.StatedSU 3 q F := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · show (diagonal ![(x.1 : F), (x.2.1 : F), (x.2.2 : F)]).det = 1
    rw [det_diagonal, Fin.prod_univ_three]
    have := congrArg Units.val h
    simpa using this
  · show ((diagonal ![(x.1 : F), (x.2.1 : F), (x.2.2 : F)]).map (· ^ q))ᵀ *
      diagonal ![(x.1 : F), (x.2.1 : F), (x.2.2 : F)] = 1
    rw [diagonal_map (f := fun y : F => y ^ q) (zero_pow hq), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i
    · simpa using h1
    · simpa using h2
    · simpa using h3

end Diag

section Root

variable (F : Type) [Field F]

theorem t112m_fin_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide

@[expose] noncomputable def t112mRoot : Multiplicative F →* GL (Fin 3) F where
  toFun c := Matrix.GeneralLinearGroup.transvection (0 : Fin 3) 2 t112m_fin_zero_ne_two
    (Multiplicative.toAdd c)
  map_one' := by
    apply Units.ext
    show transvection (0 : Fin 3) 2 (Multiplicative.toAdd (1 : Multiplicative F)) = 1
    rw [toAdd_one, transvection_zero]
  map_mul' c d := by
    apply Units.ext
    show transvection (0 : Fin 3) 2 (Multiplicative.toAdd (c * d)) =
      transvection (0 : Fin 3) 2 (Multiplicative.toAdd c) *
        transvection (0 : Fin 3) 2 (Multiplicative.toAdd d)
    rw [toAdd_mul]
    exact (transvection_mul_transvection_same (0 : Fin 3) 2 t112m_fin_zero_ne_two _ _).symm

variable {F}

theorem t112mRoot_val (c : Multiplicative F) :
    ((t112mRoot F c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      transvection (0 : Fin 3) 2 (Multiplicative.toAdd c) := rfl

theorem t112mRoot_mem_SL (c : Multiplicative F) : t112mRoot F c ∈ CFSG.Open.StatedSL 3 F := by
  apply Subgroup.subset_closure
  show (transvection (0 : Fin 3) 2 (Multiplicative.toAdd c)).det = 1
  exact det_transvection_of_ne _ _ t112m_fin_zero_ne_two _

theorem t112mDiag_mul_root (x : Fˣ × Fˣ × Fˣ) (c : Multiplicative F) :
    t112mDiag F x * t112mRoot F c * (t112mDiag F x)⁻¹ =
      t112mRoot F
        (Multiplicative.ofAdd ((x.1 : F) * Multiplicative.toAdd c * ((x.2.2⁻¹ : Fˣ) : F))) := by
  rw [← map_inv]
  apply Units.ext
  simp only [Units.val_mul, t112mDiag_val, t112mRoot_val, toAdd_ofAdd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

end Root

section Data

variable {F : Type} [Field F]

theorem t112m_mem_normalizer_zpowers {G : Type*} [Group G] {g t : G} (h : g * t = t * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have hc : ∀ k : ℤ, g * t ^ k * g⁻¹ = t ^ k := fun k => by
    rw [(Commute.zpow_right (h : Commute g t) k).eq, mul_inv_cancel_right]
  constructor
  · intro hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    rw [hc k]
    exact Subgroup.zpow_mem_zpowers t k
  · intro hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hv
    have : v = t ^ k := by
      have h1 : g * v * g⁻¹ = g * t ^ k * g⁻¹ := by
        rw [hc k]
        exact hk.symm
      exact mul_left_cancel (mul_right_cancel h1)
    rw [this]
    exact Subgroup.zpow_mem_zpowers t k

theorem t112m_diag_uv {S : Subgroup (GL (Fin 3) F)} {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hu : t112mDiag F (ω, ω, ω) ∈ S) (hv : t112mDiag F (ω, ω ^ 2, 1) ∈ S) :
    (⟨_, hu⟩ : ↥S) ≠ 1 ∧ (⟨_, hu⟩ : ↥S) ^ 3 = 1 ∧ (⟨_, hv⟩ : ↥S) ^ 3 = 1 ∧
      (⟨_, hu⟩ : ↥S) * ⟨_, hv⟩ = ⟨_, hv⟩ * ⟨_, hu⟩ ∧
      (⟨_, hv⟩ : ↥S) ∉ Subgroup.zpowers (⟨_, hu⟩ : ↥S) := by
  have hp3 : ((ω, ω, ω) : Fˣ × Fˣ × Fˣ) ^ 3 = 1 :=
    Prod.ext (by simp [hω3]) (Prod.ext (by simp [hω3]) (by simp [hω3]))
  have hq3 : ((ω, ω ^ 2, 1) : Fˣ × Fˣ × Fˣ) ^ 3 = 1 := by
    refine Prod.ext (by simp [hω3]) (Prod.ext ?_ (by simp))
    show (ω ^ 2) ^ 3 = 1
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : t112mDiag F (ω, ω, ω) = t112mDiag F 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := congrArg Prod.fst (t112mDiag_injective h1)
    exact hω1 h2
  · apply Subtype.ext
    rw [Subgroup.coe_pow, ← map_pow, hp3, map_one, Subgroup.coe_one]
  · apply Subtype.ext
    rw [Subgroup.coe_pow, ← map_pow, hq3, map_one, Subgroup.coe_one]
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, ← map_mul]
    rw [mul_comm]
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow, ← map_zpow] at h1
    have h2 := t112mDiag_injective h1
    have h21 : ω ^ k = ω := by
      have := congrArg Prod.fst h2
      simpa using this
    have h23 : ω ^ k = 1 := by
      have := congrArg (fun x => x.2.2) h2
      simpa using this
    apply hω1
    rw [← h21, h23]

theorem t112m_data_diag_odd {S : Subgroup (GL (Fin 3) F)} {ω : Fˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (h21 : (-1 : F) ≠ 1)
    (hu : t112mDiag F (ω, ω, ω) ∈ S) (hv : t112mDiag F (ω, ω ^ 2, 1) ∈ S)
    (ht : t112mDiag F (-1, -1, 1) ∈ S) :
    ∃ (T : Subgroup ↥S) (u v : ↥S), T ≠ ⊥ ∧ IsPGroup 2 T ∧ u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧
      u * v = v * u ∧ v ∉ Subgroup.zpowers u ∧ u ∈ Subgroup.normalizer (T : Set ↥S) ∧
      v ∈ Subgroup.normalizer (T : Set ↥S) := by
  obtain ⟨hu1, hu3, hv3, huv, hvu⟩ := t112m_diag_uv hω3 hω1 hu hv
  set t : ↥S := ⟨_, ht⟩ with htdef
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : t112mDiag F (-1, -1, 1) = t112mDiag F 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    have h2 := congrArg (fun x => ((x.1 : Fˣ) : F)) (t112mDiag_injective h1)
    simp only [Units.val_neg, Units.val_one, Prod.fst_one] at h2
    exact h21 h2
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    have h2 : ((-1, -1, 1) : Fˣ × Fˣ × Fˣ) ^ 2 = 1 :=
      Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    rw [Subgroup.coe_pow, ← map_pow, h2, map_one, Subgroup.coe_one]
  have hcomm : ∀ x : Fˣ × Fˣ × Fˣ, ∀ hx : t112mDiag F x ∈ S, (⟨_, hx⟩ : ↥S) * t = t * ⟨_, hx⟩ :=
    fun x hx => by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, htdef, ← map_mul]
      rw [mul_comm]
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ht2 ht1
  refine ⟨Subgroup.zpowers t, _, _, ?_, hT2, hu1, hu3, hv3, huv, hvu,
    t112m_mem_normalizer_zpowers (hcomm _ hu), t112m_mem_normalizer_zpowers (hcomm _ hv)⟩
  intro hb
  have h1 : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
  rw [hb, Subgroup.mem_bot] at h1
  exact ht1 h1

theorem t112m_data_diag_two [CharP F 2] {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ (T : Subgroup ↥(CFSG.Open.StatedSL 3 F)) (u v : ↥(CFSG.Open.StatedSL 3 F)), T ≠ ⊥ ∧
      IsPGroup 2 T ∧ u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧ v ∉ Subgroup.zpowers u ∧
      u ∈ Subgroup.normalizer (T : Set ↥(CFSG.Open.StatedSL 3 F)) ∧
      v ∈ Subgroup.normalizer (T : Set ↥(CFSG.Open.StatedSL 3 F)) := by
  set S := CFSG.Open.StatedSL 3 F with hS
  have hu : t112mDiag F (ω, ω, ω) ∈ S :=
    t112mDiag_mem_SL (by rw [← pow_three', hω3])
  have hv : t112mDiag F (ω, ω ^ 2, 1) ∈ S :=
    t112mDiag_mem_SL (by rw [mul_one, ← pow_succ', hω3])
  obtain ⟨hu1, hu3, hv3, huv, hvu⟩ := t112m_diag_uv hω3 hω1 hu hv
  let ρ : Multiplicative F →* ↥S := (t112mRoot F).codRestrict S t112mRoot_mem_SL
  have hρ : ∀ c, ((ρ c : ↥S) : GL (Fin 3) F) = t112mRoot F c := fun c => rfl
  set T : Subgroup ↥S := ρ.range with hT
  have hT1 : T ≠ ⊥ := by
    intro hb
    have h1 : ρ (Multiplicative.ofAdd 1) ∈ T := ⟨_, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    have h2 := congrArg (fun g : ↥S => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2) h1
    simp [hρ, t112mRoot_val, transvection] at h2
  have hT2 : IsPGroup 2 T := by
    rintro ⟨g, c, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
    have : c ^ 2 = 1 := by
      rw [pow_two]
      show Multiplicative.ofAdd (Multiplicative.toAdd c + Multiplicative.toAdd c) = 1
      rw [CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [this, map_one]
  have hnorm : ∀ x : Fˣ × Fˣ × Fˣ, ∀ hx : t112mDiag F x ∈ S, ∀ c,
      (⟨_, hx⟩ : ↥S) * ρ c * (⟨_, hx⟩ : ↥S)⁻¹ ∈ T := by
    intro x hx c
    refine ⟨Multiplicative.ofAdd ((x.1 : F) * Multiplicative.toAdd c * ((x.2.2⁻¹ : Fˣ) : F)), ?_⟩
    apply Subtype.ext
    rw [hρ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (t112mDiag_mul_root x c).symm
  have hN : ∀ x : Fˣ × Fˣ × Fˣ, ∀ hx : t112mDiag F x ∈ S,
      (⟨_, hx⟩ : ↥S) ∈ Subgroup.normalizer (T : Set ↥S) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨c, rfl⟩
      exact hnorm x hx c
    · intro hh
      obtain ⟨c, hc⟩ := hh
      have hx' : t112mDiag F x⁻¹ ∈ S := by rw [map_inv]; exact S.inv_mem hx
      have hinv : (⟨_, hx'⟩ : ↥S) = (⟨_, hx⟩ : ↥S)⁻¹ := Subtype.ext (map_inv _ _)
      have := hnorm x⁻¹ hx' c
      rw [hinv, inv_inv, hc] at this
      simpa [mul_assoc] using this
  exact ⟨T, _, _, hT1, hT2, hu1, hu3, hv3, huv, hvu, hN _ hu, hN _ hv⟩

end Data

end CFSG.HardMathSupport.Solomon.Coordinator
