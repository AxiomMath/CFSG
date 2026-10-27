module

public import CFSG.GH74.Uniqueness.Bender.FrameDefs

public section

namespace CFSG.GH74.Uniqueness.Bender.Frame

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {p f : ℕ} {E : Type} [Field E]

section GroupTheory

variable {G Q : Type*} [Group G] [Group Q]

theorem exists_surjective_map_mk' (N : Subgroup G) [N.Normal] {H K : Subgroup G} (hNK : N ≤ K)
    (ρ : H →* Q) (hρ : Function.Surjective ρ) (hker : ρ.ker = K.subgroupOf H) :
    ∃ π : H.map (QuotientGroup.mk' N) →* Q, Function.Surjective π ∧
      π.ker = (K.map (QuotientGroup.mk' N)).subgroupOf (H.map (QuotientGroup.mk' N)) := by
  set φ : H →* H.map (QuotientGroup.mk' N) := (QuotientGroup.mk' N).subgroupMap H
  have hφs : Function.Surjective φ := MonoidHom.subgroupMap_surjective _ _
  have hφx : ∀ x : H, ((φ x : H.map (QuotientGroup.mk' N)) : G ⧸ N) = ((x : G) : G ⧸ N) :=
    fun _ => rfl
  have hle : φ.ker ≤ ρ.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf]
    apply hNK
    have h1 : ((x : G) : G ⧸ N) = 1 := by
      have h2 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact h2
    exact (QuotientGroup.eq_one_iff _).mp h1
  set π : H.map (QuotientGroup.mk' N) →* Q := φ.liftOfSurjective hφs ⟨ρ, hle⟩
  have hπφ : ∀ x, π (φ x) = ρ x := fun x => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  refine ⟨π, fun y => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hρ y
    exact ⟨φ x, hπφ x⟩
  · ext y
    obtain ⟨x, rfl⟩ := hφs y
    rw [MonoidHom.mem_ker, hπφ, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, hφx]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨k, hk, hkx⟩
      have hkx' : ((k : G) : G ⧸ N) = ((x : G) : G ⧸ N) := hkx
      have h1 : (k : G)⁻¹ * x ∈ N := QuotientGroup.eq.mp hkx'
      have h2 := K.mul_mem hk (hNK h1)
      rwa [mul_inv_cancel_left] at h2

section Involution

variable {F : Subgroup G} {t : G}

theorem zpow_eq_one_or_eq_self (ht2 : t * t = 1) (n : ℤ) : t ^ n = 1 ∨ t ^ n = t := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [_root_.zpow_mul, zpow_two, ht2, _root_.one_zpow]
  · right
    rw [_root_.zpow_add_one, _root_.zpow_mul, zpow_two, ht2, _root_.one_zpow, one_mul]

theorem eq_one_or_eq_of_mem_zpowers (ht2 : t * t = 1) {y : G} (hy : y ∈ Subgroup.zpowers t) :
    y = 1 ∨ y = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact zpow_eq_one_or_eq_self ht2 n

theorem commutator_zpowers_le (ht2 : t * t = 1) (hnorm : ∀ x ∈ F, t * x * t⁻¹ ∈ F) :
    ⁅F, Subgroup.zpowers t⁆ ≤ F := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rcases eq_one_or_eq_of_mem_zpowers ht2 hy with h | h <;> rw [h]
  · rw [commutatorElement_one_right]
    exact F.one_mem
  · rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine F.mul_mem hx ?_
    rw [← mul_assoc]
    exact hnorm _ (F.inv_mem hx)

theorem conj_eq_inv_of_mem_commutator (ht2 : t * t = 1)
    (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hnorm : ∀ x ∈ F, t * x * t⁻¹ ∈ F) {x : G}
    (hx : x ∈ ⁅F, Subgroup.zpowers t⁆) : t * x * t⁻¹ = x⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let S : Subgroup G :=
    { carrier := {x | x ∈ F ∧ t * x * t⁻¹ = x⁻¹}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨F.mul_mem ha hb, ?_⟩
        calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha', hb']
          _ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [hcomm b hb a ha]
      one_mem' := ⟨F.one_mem, by group⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨F.inv_mem ha, ?_⟩
        calc t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
          _ = a⁻¹⁻¹ := by rw [ha'] }
  have hle : ⁅F, Subgroup.zpowers t⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    rcases eq_one_or_eq_of_mem_zpowers ht2 hy with h | h <;> rw [h]
    · rw [commutatorElement_one_right]
      exact S.one_mem
    · refine ⟨commutator_zpowers_le ht2 hnorm
        (Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers _)), ?_⟩
      calc t * ⁅a, t⁆ * t⁻¹ = t * a * t * a⁻¹ * (t⁻¹ * t⁻¹) := by
            rw [commutatorElement_def]; group
        _ = t * a * t * a⁻¹ := by rw [htinv, ht2, mul_one]
        _ = t * a * t⁻¹ * a⁻¹ := by rw [htinv]
        _ = ⁅a, t⁆⁻¹ := by rw [commutatorElement_def]; group
  exact (hle hx).2

theorem card_inf_centralizer_mul_card_commutator (ht2 : t * t = 1)
    (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hnorm : ∀ x ∈ F, t * x * t⁻¹ ∈ F) :
    Nat.card ↥(F ⊓ Subgroup.centralizer {t}) * Nat.card ↥⁅F, Subgroup.zpowers t⁆ =
      Nat.card F := by
  have hmem : ∀ x ∈ F, x * t * x⁻¹ * t⁻¹ ∈ F := fun x hx => by
    rw [mul_assoc, mul_assoc]
    refine F.mul_mem hx ?_
    rw [← mul_assoc]
    exact hnorm _ (F.inv_mem hx)
  let φ : F →* F :=
    { toFun := fun x => ⟨(x : G) * t * (x : G)⁻¹ * t⁻¹, hmem x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have h1 := hcomm _ y.2 _ (hnorm _ (F.inv_mem x.2))
        have h2 := hcomm _ (hnorm _ (F.inv_mem y.2)) _ (hnorm _ (F.inv_mem x.2))
        simp only [Subgroup.coe_mul]
        calc (x : G) * y * t * ((x : G) * y)⁻¹ * t⁻¹ =
            x * (y * ((t * (y : G)⁻¹ * t⁻¹) * (t * (x : G)⁻¹ * t⁻¹))) := by group
          _ = x * (y * ((t * (x : G)⁻¹ * t⁻¹) * (t * (y : G)⁻¹ * t⁻¹))) := by rw [h2]
          _ = x * ((y * (t * (x : G)⁻¹ * t⁻¹)) * (t * (y : G)⁻¹ * t⁻¹)) := by group
          _ = x * (((t * (x : G)⁻¹ * t⁻¹) * y) * (t * (y : G)⁻¹ * t⁻¹)) := by rw [h1]
          _ = x * t * (x : G)⁻¹ * t⁻¹ * (y * t * (y : G)⁻¹ * t⁻¹) := by group) }
  have hker : φ.ker = (F ⊓ Subgroup.centralizer {t}).subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : (x : G) * t * (x : G)⁻¹ * t⁻¹ = 1 := congrArg Subtype.val h
      refine ⟨x.2, ?_⟩
      calc (x : G) * t = ((x : G) * t * (x : G)⁻¹ * t⁻¹) * (t * x) := by group
        _ = t * x := by rw [h', one_mul]
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show (x : G) * t * (x : G)⁻¹ * t⁻¹ = 1
      rw [h]
      group
  have hrange : φ.range.map F.subtype = ⁅F, Subgroup.zpowers t⁆ := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_zpowers t)
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      rcases eq_one_or_eq_of_mem_zpowers ht2 hy with h | h <;> rw [h]
      · rw [commutatorElement_one_right]
        exact Subgroup.one_mem _
      · exact ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  rw [← hrange,
    ← Nat.card_congr (Subgroup.equivMapOfInjective φ.range F.subtype F.subtype_injective).toEquiv,
    h1, mul_comm]

end Involution

end GroupTheory

section Frame

variable (hU : UnitaryFieldData p f E) (v : Fin 3 → (Fin 3 → E))

@[expose] def frameMat : Matrix (Fin 3) (Fin 3) E := Matrix.of fun a b => v b a

@[expose] noncomputable def frameMatStar : Matrix (Fin 3) (Fin 3) E :=
  ((frameMat v).map hU.bar)ᵀ

omit [Field E] in
theorem frameMat_apply (a b : Fin 3) : frameMat v a b = v b a := rfl

theorem frameMatStar_apply (a b : Fin 3) : frameMatStar hU v a b = hU.bar (v a b) := rfl

theorem frameMat_mulVec_single (i : Fin 3) : frameMat v *ᵥ Pi.single i 1 = v i := by
  rw [mulVec_single_one]
  rfl

theorem herm_smul_right (x y : Fin 3 → E) (c : E) : herm hU x (c • y) = c * herm hU x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem herm_smul_left (x y : Fin 3 → E) (c : E) :
    herm hU (c • x) y = hU.bar c * herm hU x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem herm_eq_gramForm (x y : Fin 3 → E) :
    herm hU x y = gramForm hU (1 : Matrix (Fin 3) (Fin 3) E) x y := by
  simp [herm, gramForm_apply, dotProduct]

theorem herm_mulVec_mulVec {g : GL (Fin 3) E} (hg : g ∈ gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))
    (x y : Fin 3 → E) :
    herm hU ((g : Matrix (Fin 3) (Fin 3) E) *ᵥ x) ((g : Matrix (Fin 3) (Fin 3) E) *ᵥ y) =
      herm hU x y := by
  rw [herm_eq_gramForm, herm_eq_gramForm, gramForm_mulVec, (mem_gramSU.mp hg).1]

variable {hU v}

theorem ne_zero_of_norm_eq_one {c : E} (hc : hU.norm c = 1) : c ≠ 0 := by
  rintro rfl
  simp [UnitaryFieldData.norm] at hc

theorem herm_frame_smul (hv : IsOrthonormalFrame hU v) (i j : Fin 3) (c : E) :
    herm hU (v i) (c • v j) = if i = j then c else 0 := by
  rw [herm_smul_right, hv]
  split_ifs <;> simp

theorem frameMatStar_mul_frameMat (hv : IsOrthonormalFrame hU v) :
    frameMatStar hU v * frameMat v = 1 := by
  ext i j
  rw [mul_apply, one_apply, ← hv i j]
  rfl

theorem frameMat_mul_frameMatStar (hv : IsOrthonormalFrame hU v) :
    frameMat v * frameMatStar hU v = 1 :=
  mul_eq_one_comm.mp (frameMatStar_mul_frameMat hv)

theorem frameMatStar_mulVec (hv : IsOrthonormalFrame hU v) (i : Fin 3) :
    frameMatStar hU v *ᵥ v i = Pi.single i 1 := by
  rw [← frameMat_mulVec_single v i, mulVec_mulVec, frameMatStar_mul_frameMat hv, one_mulVec]

theorem frame_ne_zero (hv : IsOrthonormalFrame hU v) (i : Fin 3) : v i ≠ 0 := by
  intro h
  have h1 := hv i i
  rw [ite_eq_left rfl, h] at h1
  simp [herm] at h1

theorem matrix_eq_of_frame (hv : IsOrthonormalFrame hU v) {M N : Matrix (Fin 3) (Fin 3) E}
    (h : ∀ i, M *ᵥ v i = N *ᵥ v i) : M = N := by
  have hMN : M * frameMat v = N * frameMat v := by
    ext a b
    have h1 := congrFun (h b) a
    simp only [mulVec, dotProduct] at h1
    simpa [mul_apply, frameMat_apply] using h1
  calc M = M * (frameMat v * frameMatStar hU v) := by
        rw [frameMat_mul_frameMatStar hv, Matrix.mul_one]
    _ = N * (frameMat v * frameMatStar hU v) := by
        rw [← Matrix.mul_assoc, hMN, Matrix.mul_assoc]
    _ = N := by rw [frameMat_mul_frameMatStar hv, Matrix.mul_one]

theorem GL_eq_of_frame (hv : IsOrthonormalFrame hU v) {g h : GL (Fin 3) E}
    (H : ∀ i, (g : Matrix (Fin 3) (Fin 3) E) *ᵥ v i = (h : Matrix (Fin 3) (Fin 3) E) *ᵥ v i) :
    g = h :=
  Units.ext (matrix_eq_of_frame hv H)

theorem gramSU_eq_of_frame (hv : IsOrthonormalFrame hU v)
    {g h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)}
    (H : ∀ i, ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ v i =
      ((h : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ v i) : g = h :=
  Subtype.ext (GL_eq_of_frame hv H)

theorem inv_mulVec_eq {g : GL (Fin 3) E} {x y : Fin 3 → E} {a : E} (ha : a ≠ 0)
    (h : (g : Matrix (Fin 3) (Fin 3) E) *ᵥ x = a • y) :
    ((g⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ y = a⁻¹ • x := by
  have h2 := congrArg (fun w => ((g⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ w) h
  simp only [mulVec_mulVec, mulVec_smul] at h2
  rw [Units.inv_mul, one_mulVec] at h2
  rw [h2, smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem mulVec_ne_zero (g : GL (Fin 3) E) {x : Fin 3 → E} (hx : x ≠ 0) :
    (g : Matrix (Fin 3) (Fin 3) E) *ᵥ x ≠ 0 := by
  intro h
  apply hx
  have h2 := congrArg (fun w => ((g⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ w) h
  simpa only [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero] using h2

theorem eq_of_smul_frame_eq (hv : IsOrthonormalFrame hU v) {i j : Fin 3} {c d : E} (hc : c ≠ 0)
    (h : c • v i = d • v j) : i = j := by
  by_contra hij
  have h1 := congrArg (herm hU (v i)) h
  rw [herm_frame_smul hv, herm_frame_smul hv, ite_eq_left rfl, ite_eq_right hij] at h1
  exact hc h1

theorem norm_eq_one_of_mulVec (hv : IsOrthonormalFrame hU v) {g : GL (Fin 3) E}
    (hg : g ∈ gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) {i j : Fin 3} {c : E}
    (h : (g : Matrix (Fin 3) (Fin 3) E) *ᵥ v i = c • v j) : hU.norm c = 1 := by
  have h1 := herm_mulVec_mulVec hU hg (v i) (v i)
  rw [h, herm_smul_left, herm_frame_smul hv, hv, ite_eq_left rfl, ite_eq_left rfl] at h1
  rw [UnitaryFieldData.norm, mul_comm]
  exact h1

end Frame

section Monomial

@[expose] def monoMat (σ : Equiv.Perm (Fin 3)) (c : Fin 3 → E) : Matrix (Fin 3) (Fin 3) E :=
  Matrix.of fun a b => if a = σ b then c b else 0

theorem monoMat_mulVec_single (σ : Equiv.Perm (Fin 3)) (c : Fin 3 → E) (i : Fin 3) :
    monoMat σ c *ᵥ Pi.single i 1 = c i • Pi.single (σ i) 1 := by
  rw [mulVec_single_one]
  ext a
  simp [monoMat, Pi.single_apply]

theorem monoMat_eq_submatrix (σ : Equiv.Perm (Fin 3)) (c : Fin 3 → E) :
    monoMat σ c = (diagonal c).submatrix σ.symm id := by
  ext a b
  simp only [monoMat, of_apply, submatrix_apply, id, diagonal_apply, Equiv.symm_apply_eq]
  split_ifs with h
  · rw [h, Equiv.symm_apply_apply]
  · rfl

theorem det_monoMat [CharP E 2] (σ : Equiv.Perm (Fin 3)) (c : Fin 3 → E) :
    (monoMat σ c).det = ∏ i, c i := by
  rw [monoMat_eq_submatrix, det_permute, det_diagonal]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h, CharTwo.neg_eq]

theorem monoMat_unitary (hU : UnitaryFieldData p f E) (σ : Equiv.Perm (Fin 3)) {c : Fin 3 → E}
    (hc : ∀ i, hU.norm (c i) = 1) : ((monoMat σ c).map hU.bar)ᵀ * monoMat σ c = 1 := by
  ext i j
  simp only [mul_apply, transpose_apply, map_apply, monoMat, of_apply, one_apply]
  have h : ∀ a, hU.bar (if a = σ i then c i else 0) * (if a = σ j then c j else 0) =
      if a = σ i then hU.bar (c i) * (if σ i = σ j then c j else 0) else 0 := by
    intro a
    by_cases ha : a = σ i
    · subst ha
      simp
    · simp [ha]
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_ite_eq' Finset.univ (σ i)]
  simp only [Finset.mem_univ, ↓reduceIte, σ.injective.eq_iff]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_comm]
    exact hc i
  · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]

variable {hU : UnitaryFieldData p f E} {v : Fin 3 → (Fin 3 → E)}

variable (hU v) in
@[expose] noncomputable def frameMonoMat (σ : Equiv.Perm (Fin 3)) (c : Fin 3 → E) :
    Matrix (Fin 3) (Fin 3) E :=
  frameMat v * monoMat σ c * frameMatStar hU v

theorem frameMonoMat_mulVec (hv : IsOrthonormalFrame hU v) (σ : Equiv.Perm (Fin 3))
    (c : Fin 3 → E) (i : Fin 3) : frameMonoMat hU v σ c *ᵥ v i = c i • v (σ i) := by
  rw [frameMonoMat, ← mulVec_mulVec, frameMatStar_mulVec hv, ← mulVec_mulVec,
    monoMat_mulVec_single, mulVec_smul, frameMat_mulVec_single]

theorem frameMatStar_map_transpose : ((frameMatStar hU v).map hU.bar)ᵀ = frameMat v := by
  ext a b
  simp [frameMatStar_apply, frameMat_apply, UnitaryFieldData.bar_bar]

theorem frameMonoMat_unitary (hv : IsOrthonormalFrame hU v) (σ : Equiv.Perm (Fin 3))
    {c : Fin 3 → E} (hc : ∀ i, hU.norm (c i) = 1) :
    ((frameMonoMat hU v σ c).map hU.bar)ᵀ * frameMonoMat hU v σ c = 1 := by
  rw [frameMonoMat, Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul,
    frameMatStar_map_transpose]
  change frameMat v * (((monoMat σ c).map hU.bar)ᵀ * frameMatStar hU v) *
    (frameMat v * monoMat σ c * frameMatStar hU v) = 1
  calc _ = frameMat v * (((monoMat σ c).map hU.bar)ᵀ * (frameMatStar hU v * frameMat v) *
        monoMat σ c) * frameMatStar hU v := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [frameMatStar_mul_frameMat hv, Matrix.mul_one, monoMat_unitary hU σ hc, Matrix.mul_one,
          frameMat_mul_frameMatStar hv]

end Monomial

section CharTwo

variable {hU : UnitaryFieldData 2 f E} {v : Fin 3 → (Fin 3 → E)}

theorem det_frameMonoMat (hv : IsOrthonormalFrame hU v) (σ : Equiv.Perm (Fin 3))
    (c : Fin 3 → E) : (frameMonoMat hU v σ c).det = ∏ i, c i := by
  have := hU.charP
  have h1 : (frameMatStar hU v).det * (frameMat v).det = 1 := by
    rw [← det_mul, frameMatStar_mul_frameMat hv, det_one]
  rw [frameMonoMat, det_mul, det_mul, det_monoMat]
  linear_combination (∏ i, c i) * h1

@[expose] noncomputable def frameMonoElt (hv : IsOrthonormalFrame hU v) (σ : Equiv.Perm (Fin 3))
    (c : Fin 3 → E) (hc : ∀ i, hU.norm (c i) = 1) (hprod : ∏ i, c i = 1) :
    gramSU hU (1 : Matrix (Fin 3) (Fin 3) E) :=
  ⟨⟨frameMonoMat hU v σ c, ((frameMonoMat hU v σ c).map hU.bar)ᵀ,
      mul_eq_one_comm.mp (frameMonoMat_unitary hv σ hc), frameMonoMat_unitary hv σ hc⟩,
    mem_gramSU.mpr ⟨by rw [Matrix.mul_one]; exact frameMonoMat_unitary hv σ hc,
      (det_frameMonoMat hv σ c).trans hprod⟩⟩

theorem frameMonoElt_mulVec (hv : IsOrthonormalFrame hU v) (σ : Equiv.Perm (Fin 3))
    (c : Fin 3 → E) (hc : ∀ i, hU.norm (c i) = 1) (hprod : ∏ i, c i = 1) (i : Fin 3) :
    (((frameMonoElt hv σ c hc hprod : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E) *ᵥ v i = c i • v (σ i) :=
  frameMonoMat_mulVec hv σ c i

theorem frameMonoElt_mem_frameMonoSU (hv : IsOrthonormalFrame hU v) (σ : Equiv.Perm (Fin 3))
    (c : Fin 3 → E) (hc : ∀ i, hU.norm (c i) = 1) (hprod : ∏ i, c i = 1) :
    frameMonoElt hv σ c hc hprod ∈ frameMonoSU hU v := by
  refine ⟨fun i => ⟨σ i, c i, frameMonoElt_mulVec hv σ c hc hprod i⟩,
    fun i => ⟨σ.symm i, (c (σ.symm i))⁻¹, ?_⟩⟩
  apply inv_mulVec_eq (ne_zero_of_norm_eq_one (hc _))
  rw [frameMonoElt_mulVec, Equiv.apply_symm_apply]

noncomputable abbrev frameDiagElt (hv : IsOrthonormalFrame hU v) (c : Fin 3 → E)
    (hc : ∀ i, hU.norm (c i) = 1) (hprod : ∏ i, c i = 1) :
    gramSU hU (1 : Matrix (Fin 3) (Fin 3) E) :=
  frameMonoElt hv 1 c hc hprod

theorem frameDiagElt_mulVec (hv : IsOrthonormalFrame hU v) (c : Fin 3 → E)
    (hc : ∀ i, hU.norm (c i) = 1) (hprod : ∏ i, c i = 1) (i : Fin 3) :
    (((frameDiagElt hv c hc hprod : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E) *ᵥ v i = c i • v i :=
  frameMonoMat_mulVec hv 1 c i

theorem frameDiagElt_mem_frameTorusSU (hv : IsOrthonormalFrame hU v) (c : Fin 3 → E)
    (hc : ∀ i, hU.norm (c i) = 1) (hprod : ∏ i, c i = 1) :
    frameDiagElt hv c hc hprod ∈ frameTorusSU hU v :=
  fun i => ⟨c i, ne_zero_of_norm_eq_one (hc i), frameDiagElt_mulVec hv c hc hprod i⟩

end CharTwo

section Eigen

variable {hU : UnitaryFieldData p f E} {v : Fin 3 → (Fin 3 → E)}

variable (hU v) in
@[expose] noncomputable def frameEig (g : Matrix (Fin 3) (Fin 3) E) (i : Fin 3) : E :=
  herm hU (v i) (g *ᵥ v i)

theorem frameEig_eq (hv : IsOrthonormalFrame hU v) {g : Matrix (Fin 3) (Fin 3) E} {i : Fin 3}
    {c : E} (h : g *ᵥ v i = c • v i) : frameEig hU v g i = c := by
  rw [frameEig, h, herm_frame_smul hv, ite_eq_left rfl]

theorem mulVec_frameEig (hv : IsOrthonormalFrame hU v)
    {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hg : g ∈ frameTorusSU hU v) (i : Fin 3) :
    ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ v i =
      frameEig hU v ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i • v i := by
  obtain ⟨c, -, hc⟩ := hg i
  rw [frameEig_eq hv hc, hc]

theorem norm_frameEig (hv : IsOrthonormalFrame hU v)
    {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hg : g ∈ frameTorusSU hU v) (i : Fin 3) :
    hU.norm (frameEig hU v ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i) = 1 :=
  norm_eq_one_of_mulVec hv g.2 (mulVec_frameEig hv hg i)

@[expose] noncomputable def frameEigHom (hv : IsOrthonormalFrame hU v) (i : Fin 3) :
    frameTorusSU hU v →* rootsOfUnity (p ^ f + 1) E where
  toFun g := ⟨Units.mk0 (frameEig hU v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i)
      (ne_zero_of_norm_eq_one (norm_frameEig hv g.2 i)), by
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
      ← hU.norm_eq_pow, norm_frameEig hv g.2 i]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show frameEig hU v 1 i = 1
    exact frameEig_eq hv (by rw [one_mulVec, one_smul])
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0]
    apply frameEig_eq hv
    rw [← mulVec_mulVec, mulVec_frameEig hv h.2, mulVec_smul, mulVec_frameEig hv g.2, smul_smul,
      mul_comm]

theorem coe_frameEigHom (hv : IsOrthonormalFrame hU v) (i : Fin 3) (g : frameTorusSU hU v) :
    ((frameEigHom hv i g : Eˣ) : E) =
      frameEig hU v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) i :=
  rfl

theorem frameEigHom_eq_iff (hv : IsOrthonormalFrame hU v) {i j : Fin 3}
    {g h : frameTorusSU hU v} :
    frameEigHom hv i g = frameEigHom hv j h ↔
      frameEig hU v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) i =
      frameEig hU v (((h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) j := by
  rw [Subtype.ext_iff, Units.ext_iff]
  rfl

theorem frameTorusSU_ext (hv : IsOrthonormalFrame hU v) {g h : frameTorusSU hU v}
    (H : ∀ i, frameEigHom hv i g = frameEigHom hv i h) : g = h := by
  apply Subtype.ext
  apply gramSU_eq_of_frame hv
  intro i
  rw [mulVec_frameEig hv g.2, mulVec_frameEig hv h.2, (frameEigHom_eq_iff hv).mp (H i)]

theorem frameTorusSU_le_frameMonoSU : frameTorusSU hU v ≤ frameMonoSU hU v := by
  intro g hg
  refine ⟨fun i => ?_, fun i => ?_⟩
  · obtain ⟨c, -, hc⟩ := hg i
    exact ⟨i, c, hc⟩
  · obtain ⟨c, hc0, hc⟩ := hg i
    exact ⟨i, c⁻¹, inv_mulVec_eq hc0 hc⟩

theorem conj_mem_frameTorusSU {g h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)}
    (hg : g ∈ frameMonoSU hU v) (hh : h ∈ frameTorusSU hU v) :
    g * h * g⁻¹ ∈ frameTorusSU hU v := by
  intro i
  obtain ⟨j, b, hb⟩ := hg.2 i
  obtain ⟨a, ha0, ha⟩ := hh j
  refine ⟨a, ha0, ?_⟩
  have key : ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ (b • v j) = v i := by
    rw [← hb, mulVec_mulVec, Units.mul_inv, one_mulVec]
  change (((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
    ((h : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
    ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) *ᵥ v i = a • v i
  rw [← mulVec_mulVec, hb, ← mulVec_mulVec, mulVec_smul, ha, smul_comm, mulVec_smul, key]

theorem frameTorusSU_comm (hv : IsOrthonormalFrame hU v)
    {g h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hg : g ∈ frameTorusSU hU v)
    (hh : h ∈ frameTorusSU hU v) : g * h = h * g := by
  apply gramSU_eq_of_frame hv
  intro i
  change (((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
    ((h : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) *ᵥ v i =
    (((h : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
    ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) *ᵥ v i
  rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_frameEig hv hh, mulVec_frameEig hv hg, mulVec_smul,
    mulVec_smul, mulVec_frameEig hv hh, mulVec_frameEig hv hg, smul_smul, smul_smul, mul_comm]

theorem frameTorusSU_pow_mulVec (hv : IsOrthonormalFrame hU v)
    {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hg : g ∈ frameTorusSU hU v) (n : ℕ)
    (i : Fin 3) :
    (((g ^ n : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E) *ᵥ v i =
      (frameEig hU v ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i) ^ n • v i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, mulVec_frameEig hv hg,
      mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

theorem frameTorusSU_pow_eq_one (hv : IsOrthonormalFrame hU v)
    {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hg : g ∈ frameTorusSU hU v) :
    g ^ (p ^ f + 1) = 1 := by
  apply gramSU_eq_of_frame hv
  intro i
  rw [frameTorusSU_pow_mulVec hv hg, ← hU.norm_eq_pow, norm_frameEig hv hg, one_smul]
  simp

theorem scalar_mulVec (c : Eˣ) (x : Fin 3 → E) :
    ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ x =
      (c : E) • x := by
  ext a
  simp [GeneralLinearGroup.coe_scalar, scalar_apply, mulVec_diagonal]

variable (hU v) in
theorem normOneScalars_le_frameTorusSU (m : ℕ) :
    normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) m ≤ frameTorusSU hU v := by
  rintro g ⟨c, -, -, hg⟩ i
  exact ⟨c, c.ne_zero, by rw [hg, scalar_mulVec]⟩

theorem frameEigHom_eq_of_mem_normOneScalars (hv : IsOrthonormalFrame hU v) {m : ℕ}
    {g : frameTorusSU hU v}
    (hg : (g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) ∈
      normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) m) (i j : Fin 3) :
    frameEigHom hv i g = frameEigHom hv j g := by
  obtain ⟨c, -, -, hc⟩ := hg
  have h1 : ∀ k, frameEig hU v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E) k = c := fun k => frameEig_eq hv (by rw [hc, scalar_mulVec])
  rw [frameEigHom_eq_iff, h1, h1]

end Eigen

section LinePerm

variable {hU : UnitaryFieldData p f E} {v : Fin 3 → (Fin 3 → E)}

variable (v) in
@[expose] noncomputable def lineIdx (g : Matrix (Fin 3) (Fin 3) E) (i : Fin 3) : Fin 3 :=
  Classical.epsilon fun j => ∃ c : E, g *ᵥ v i = c • v j

theorem lineIdx_spec {g : Matrix (Fin 3) (Fin 3) E} {i : Fin 3}
    (h : ∃ j, ∃ c : E, g *ᵥ v i = c • v j) : ∃ c : E, g *ᵥ v i = c • v (lineIdx v g i) :=
  Classical.epsilon_spec h

theorem lineIdx_eq (hv : IsOrthonormalFrame hU v) {g : GL (Fin 3) E} {i j : Fin 3} {c : E}
    (h : (g : Matrix (Fin 3) (Fin 3) E) *ᵥ v i = c • v j) :
    lineIdx v (g : Matrix (Fin 3) (Fin 3) E) i = j := by
  obtain ⟨c', hc'⟩ := lineIdx_spec ⟨j, c, h⟩
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact mulVec_ne_zero g (frame_ne_zero hv i) h
  exact (eq_of_smul_frame_eq hv hc (h.symm.trans hc')).symm

theorem lineIdx_one (hv : IsOrthonormalFrame hU v) (i : Fin 3) :
    lineIdx v ((1 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i = i :=
  lineIdx_eq hv (c := 1) (by rw [Units.val_one, one_mulVec, one_smul])

theorem lineIdx_mul (hv : IsOrthonormalFrame hU v) {g h : GL (Fin 3) E}
    (hg : PermutesLines v g) (hh : PermutesLines v h) (i : Fin 3) :
    lineIdx v ((g * h : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i =
      lineIdx v (g : Matrix (Fin 3) (Fin 3) E) (lineIdx v (h : Matrix (Fin 3) (Fin 3) E) i) := by
  obtain ⟨c, hc⟩ := lineIdx_spec (hh i)
  obtain ⟨d, hd⟩ := lineIdx_spec (hg (lineIdx v (h : Matrix (Fin 3) (Fin 3) E) i))
  apply lineIdx_eq hv (c := c * d)
  rw [Units.val_mul, ← mulVec_mulVec, hc, mulVec_smul, hd, smul_smul]

@[expose] noncomputable def linePerm (hv : IsOrthonormalFrame hU v) (g : frameMonoSU hU v) :
    Equiv.Perm (Fin 3) where
  toFun := lineIdx v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
    Matrix (Fin 3) (Fin 3) E)
  invFun := lineIdx v ((((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E)⁻¹ :
    GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)
  left_inv i := by
    rw [← lineIdx_mul hv ((mem_frameMonoSU hU v).mp g.2).2 ((mem_frameMonoSU hU v).mp g.2).1,
      inv_mul_cancel, lineIdx_one hv]
  right_inv i := by
    rw [← lineIdx_mul hv ((mem_frameMonoSU hU v).mp g.2).1 ((mem_frameMonoSU hU v).mp g.2).2,
      mul_inv_cancel, lineIdx_one hv]

@[expose] noncomputable def linePermHom (hv : IsOrthonormalFrame hU v) :
    frameMonoSU hU v →* Equiv.Perm (Fin 3) where
  toFun := linePerm hv
  map_one' := Equiv.ext fun i => lineIdx_one hv i
  map_mul' g h := Equiv.ext fun i => lineIdx_mul hv ((mem_frameMonoSU hU v).mp g.2).1
    ((mem_frameMonoSU hU v).mp h.2).1 i

theorem linePermHom_apply (hv : IsOrthonormalFrame hU v) (g : frameMonoSU hU v) (i : Fin 3) :
    linePermHom hv g i = lineIdx v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i :=
  rfl

theorem ker_linePermHom (hv : IsOrthonormalFrame hU v) :
    (linePermHom hv).ker = (frameTorusSU hU v).subgroupOf (frameMonoSU hU v) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h i
    have hi : lineIdx v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) i = i :=
      congrArg (fun σ : Equiv.Perm (Fin 3) => σ i) h
    obtain ⟨c, hc⟩ := lineIdx_spec (((mem_frameMonoSU hU v).mp g.2).1 i)
    rw [hi] at hc
    refine ⟨c, ?_, hc⟩
    rintro rfl
    rw [zero_smul] at hc
    exact mulVec_ne_zero _ (frame_ne_zero hv i) hc
  · intro h
    refine Equiv.ext fun i => ?_
    obtain ⟨c, -, hc⟩ := h i
    exact lineIdx_eq hv hc

theorem conj_mulVec (hv : IsOrthonormalFrame hU v)
    {g h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hg : g ∈ frameMonoSU hU v)
    (hh : h ∈ frameTorusSU hU v) (l : Fin 3) :
    (((g * h * g⁻¹ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E) *ᵥ v l =
      frameEig hU v ((h : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)
        (lineIdx v ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) l) •
        v l := by
  obtain ⟨b, hb⟩ := lineIdx_spec (((mem_frameMonoSU hU v).mp hg).2 l)
  have key : ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ (b • v (lineIdx v
      ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) l)) = v l := by
    rw [← hb, mulVec_mulVec, Units.mul_inv, one_mulVec]
  change (((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
    ((h : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
    ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) *ᵥ v l = _
  rw [← mulVec_mulVec, hb, ← mulVec_mulVec, mulVec_smul, mulVec_frameEig hv hh, smul_comm,
    mulVec_smul, key]

theorem frameEigHom_conj (hv : IsOrthonormalFrame hU v)
    {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hg : g ∈ frameMonoSU hU v)
    (h : frameTorusSU hU v) (l : Fin 3) :
    frameEigHom hv l ⟨g * h * g⁻¹, conj_mem_frameTorusSU hg h.2⟩ =
      frameEigHom hv
        (lineIdx v ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) l) h :=
  (frameEigHom_eq_iff hv).mpr (frameEig_eq hv (conj_mulVec hv hg h.2 l))

end LinePerm

theorem fin3_cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
  decide

theorem fin3_third : ∀ i j : Fin 3, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j ∧ ∀ l, l = i ∨ l = j ∨ l = k := by
  decide

theorem fin3_cover : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j → ∀ l, l = i ∨ l = j ∨ l = k := by
  decide

theorem prod_fin3_eq {M : Type*} [CommMonoid M] (c : Fin 3 → M) {i j k : Fin 3} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) : ∏ l, c l = c i * c j * c k := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {i, j, k} := by
    ext l
    simpa using fin3_cover i j k hij hki hkj l
  rw [huniv, Finset.prod_insert, Finset.prod_insert, Finset.prod_singleton, mul_assoc]
  all_goals simp [hij, hki.symm, hkj.symm]

section TorusStructure

theorem card_rootsOfUnity_eq (hU : UnitaryFieldData p f E) :
    Nat.card (rootsOfUnity (p ^ f + 1) E) = p ^ f + 1 := by
  rw [← hU.ker_normUnits]
  exact hU.card_ker_normUnits_and_surjective.1

theorem norm_coe_rootsOfUnity (hU : UnitaryFieldData p f E) (x : rootsOfUnity (p ^ f + 1) E) :
    hU.norm ((x : Eˣ) : E) = 1 := by
  rw [hU.norm_eq_pow, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp x.2, Units.val_one]

@[expose] noncomputable def rootsEquiv (hU : UnitaryFieldData p f E) :
    rootsOfUnity (p ^ f + 1) E ≃* Multiplicative (ZMod (p ^ f + 1)) :=
  mulEquivOfCyclicCardEq (by
    rw [card_rootsOfUnity_eq hU, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod])

@[expose] noncomputable def zmodReduce (m d : ℕ) (hd : d ∣ m) :
    Multiplicative (ZMod m) →* Multiplicative (ZMod (m / d)) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (Nat.div_dvd_of_dvd hd) (ZMod (m / d))).toAddMonoidHom

theorem castHom_div_eq_zero_iff {m d : ℕ} [NeZero m] (hd : d ∣ m) (hd0 : 0 < d) (z : ZMod m) :
    ZMod.castHom (Nat.div_dvd_of_dvd hd) (ZMod (m / d)) z = 0 ↔ (d : ZMod m) * z = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  conv_rhs => rw [← ZMod.natCast_zmod_val z, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, hk⟩ := hd
  have hk' : m / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
  have h2 : d * k ∣ d * z.val ↔ k ∣ z.val := Nat.mul_dvd_mul_iff_left hd0
  rw [← hk] at h2
  rw [hk', h2]

theorem zmodReduce_apply {m d : ℕ} (hd : d ∣ m) (y : Multiplicative (ZMod m)) :
    zmodReduce m d hd y = Multiplicative.ofAdd
      (ZMod.castHom (Nat.div_dvd_of_dvd hd) (ZMod (m / d)) (Multiplicative.toAdd y)) :=
  rfl

theorem zmodReduce_eq_one_iff {m d : ℕ} [NeZero m] (hd : d ∣ m) (hd0 : 0 < d)
    (y : Multiplicative (ZMod m)) : zmodReduce m d hd y = 1 ↔ y ^ d = 1 := by
  rw [zmodReduce_apply, ofAdd_eq_one, castHom_div_eq_zero_iff hd hd0, ← nsmul_eq_mul, ← toAdd_pow,
    toAdd_eq_zero]

variable {hU : UnitaryFieldData 2 f E} {v : Fin 3 → (Fin 3 → E)}

theorem prod_frameEig (hv : IsOrthonormalFrame hU v)
    {g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hg : g ∈ frameTorusSU hU v) :
    ∏ i, frameEig hU v ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i = 1 := by
  have h1 : ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
      frameMonoMat hU v 1 (frameEig hU v ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) :=
    matrix_eq_of_frame hv fun i => by
      simp only [mulVec_frameEig hv hg i, frameMonoMat_mulVec hv, Equiv.Perm.one_apply]
  have h2 := (mem_gramSU.mp g.2).2
  rw [h1, det_frameMonoMat hv] at h2
  exact h2

theorem prod_frameEigHom (hv : IsOrthonormalFrame hU v) (x : frameTorusSU hU v) :
    ∏ l, frameEigHom hv l x = 1 := by
  have h := prod_frameEig hv x.2
  rw [Fin.prod_univ_three] at h ⊢
  apply Subtype.ext
  apply Units.ext
  simpa only [Subgroup.coe_mul, Units.val_mul, coe_frameEigHom, OneMemClass.coe_one,
    Units.val_one] using h

@[expose] noncomputable def torusQuotHom (hv : IsOrthonormalFrame hU v) :
    frameTorusSU hU v →* Multiplicative (ZMod (2 ^ f + 1)) ×
      Multiplicative (ZMod ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1))) :=
  ((rootsEquiv hU).toMonoidHom.comp (frameEigHom hv 0 * (frameEigHom hv 1)⁻¹)).prod
    ((zmodReduce _ _ (Nat.gcd_dvd_right 3 (2 ^ f + 1))).comp
      ((rootsEquiv hU).toMonoidHom.comp (frameEigHom hv 1)))

theorem ker_torusQuotHom (hv : IsOrthonormalFrame hU v) :
    (torusQuotHom hv).ker = (normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))
      3).subgroupOf (frameTorusSU hU v) := by
  have hd0 : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  simp only [torusQuotHom, MonoidHom.prod_apply, Prod.mk_eq_one, MonoidHom.comp_apply,
    MonoidHom.mul_apply, MonoidHom.inv_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, mul_inv_eq_one]
  rw [zmodReduce_eq_one_iff _ hd0, ← map_pow, MulEquiv.map_eq_one_iff]
  constructor
  · rintro ⟨h01, hd⟩
    have hc3 : frameEigHom hv 1 g ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := Nat.gcd_dvd_left 3 (2 ^ f + 1)
      calc frameEigHom hv 1 g ^ 3 = (frameEigHom hv 1 g ^ Nat.gcd 3 (2 ^ f + 1)) ^ k := by
            rw [← pow_mul, ← hk]
        _ = 1 := by rw [hd, one_pow]
    have hc3' : (frameEig hU v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) 1) ^ 3 = 1 := by
      have := congrArg (fun x : rootsOfUnity (2 ^ f + 1) E => ((x : Eˣ) : E)) hc3
      simpa only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, coe_frameEigHom,
        OneMemClass.coe_one, Units.val_one] using this
    have h01' := (frameEigHom_eq_iff hv).mp h01
    have hprod := prod_frameEig hv g.2
    rw [Fin.prod_univ_three] at hprod
    refine ⟨(frameEigHom hv 1 g : Eˣ), ?_, ?_, ?_⟩
    · exact norm_coe_rootsOfUnity hU _
    · exact congrArg Subtype.val hc3
    · apply GL_eq_of_frame hv
      intro i
      rw [mulVec_frameEig hv g.2 i, scalar_mulVec, coe_frameEigHom]
      congr 1
      rcases fin3_cases i with rfl | rfl | rfl
      · exact h01'
      · rfl
      · rw [h01'] at hprod
        linear_combination (-(frameEig hU v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
          GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 2)) * hc3' +
          frameEig hU v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
            Matrix (Fin 3) (Fin 3) E) 1 * hprod
  · rintro ⟨c, hcN, hc3, hg⟩
    have h1 : ∀ k, frameEig hU v (((g : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
        GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) k = c :=
      fun k => frameEig_eq hv (by rw [hg, scalar_mulVec])
    refine ⟨(frameEigHom_eq_iff hv).mpr (by rw [h1, h1]), ?_⟩
    apply Subtype.ext
    apply Units.ext
    simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, coe_frameEigHom, h1,
      OneMemClass.coe_one, Units.val_one]
    have hcm : (c : E) ^ (2 ^ f + 1) = 1 := by rw [← hU.norm_eq_pow, hcN]
    have hc3' : (c : E) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    exact pow_gcd_eq_one.mpr ⟨hc3', hcm⟩

theorem torusQuotHom_surjective (hv : IsOrthonormalFrame hU v) :
    Function.Surjective (torusQuotHom hv) := by
  rintro ⟨a, b⟩
  obtain ⟨b0, hb0⟩ := ZMod.castHom_surjective
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 (2 ^ f + 1))) (Multiplicative.toAdd b)
  obtain ⟨c1, hc1⟩ : ∃ c1 : rootsOfUnity (2 ^ f + 1) E,
      c1 = (rootsEquiv hU).symm (Multiplicative.ofAdd b0) := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : rootsOfUnity (2 ^ f + 1) E,
      c0 = (rootsEquiv hU).symm a * c1 := ⟨_, rfl⟩
  let c : Fin 3 → rootsOfUnity (2 ^ f + 1) E := ![c0, c1, (c0 * c1)⁻¹]
  have hcN : ∀ i, hU.norm ((c i : Eˣ) : E) = 1 := fun i => norm_coe_rootsOfUnity hU (c i)
  have hcp : ∏ i, ((c i : Eˣ) : E) = 1 := by
    have h1 : ∏ i, c i = 1 := by
      rw [Fin.prod_univ_three]
      simp [c]
    have h2 := congrArg (fun x : rootsOfUnity (2 ^ f + 1) E => ((x : Eˣ) : E)) h1
    simpa only [SubmonoidClass.coe_finsetProd, Units.coe_prod, OneMemClass.coe_one,
      Units.val_one] using h2
  let g : frameTorusSU hU v := ⟨frameDiagElt hv (fun i => ((c i : Eˣ) : E)) hcN hcp,
    frameDiagElt_mem_frameTorusSU hv _ hcN hcp⟩
  have hg : ∀ i, frameEigHom hv i g = c i := fun i =>
    Subtype.ext (Units.ext (frameEig_eq hv (frameDiagElt_mulVec hv _ hcN hcp i)))
  refine ⟨g, Prod.ext ?_ ?_⟩
  · show rootsEquiv hU (frameEigHom hv 0 g * (frameEigHom hv 1 g)⁻¹) = a
    rw [hg, hg]
    simp [c, hc0]
  · show zmodReduce _ _ (Nat.gcd_dvd_right 3 (2 ^ f + 1))
      (rootsEquiv hU (frameEigHom hv 1 g)) = b
    rw [hg]
    simp only [c, Matrix.cons_val_one, Matrix.cons_val_zero, hc1, MulEquiv.apply_symm_apply]
    rw [zmodReduce_apply, toAdd_ofAdd, hb0, ofAdd_toAdd]

theorem ker_subgroupMap_mk' {G : Type*} [Group G] (N H : Subgroup G) [N.Normal] :
    ((QuotientGroup.mk' N).subgroupMap H).ker = N.subgroupOf H := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff, Subtype.ext_iff]
  rfl

theorem frameTorus_mulEquiv (hv : IsOrthonormalFrame hU v) :
    Nonempty (frameTorus hU v ≃* Multiplicative (ZMod (2 ^ f + 1)) ×
      Multiplicative (ZMod ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)))) := by
  have hker : ((QuotientGroup.mk' (normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))
      3)).subgroupMap (frameTorusSU hU v)).ker = (torusQuotHom hv).ker := by
    rw [ker_torusQuotHom, ker_subgroupMap_mk']
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (normOneScalars hU
    (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3)).subgroupMap (frameTorusSU hU v))
    (MonoidHom.subgroupMap_surjective _ _)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (torusQuotHom_surjective hv)))⟩

theorem card_frameTorus (hv : IsOrthonormalFrame hU v) :
    Nat.card (frameTorus hU v) = (2 ^ f + 1) * ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) := by
  obtain ⟨e⟩ := frameTorus_mulEquiv hv
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_zmod]

theorem linePermHom_surjective (hv : IsOrthonormalFrame hU v) :
    Function.Surjective (linePermHom hv) := by
  intro σ
  have hc : ∀ i : Fin 3, hU.norm ((fun _ => (1 : E)) i) = 1 := fun _ => by
    simp [UnitaryFieldData.norm]
  have hp : ∏ i : Fin 3, (fun _ => (1 : E)) i = 1 := by simp
  refine ⟨⟨frameMonoElt hv σ (fun _ => 1) hc hp, frameMonoElt_mem_frameMonoSU hv σ _ hc hp⟩, ?_⟩
  refine Equiv.ext fun i => ?_
  exact lineIdx_eq hv (frameMonoElt_mulVec hv σ _ hc hp i)

end TorusStructure

theorem frame_group_structure (hU : UnitaryFieldData 2 f E) (hf : 2 ≤ f)
    {v : Fin 3 → (Fin 3 → E)} (hv : IsOrthonormalFrame hU v) :
    frameTorus hU v ≤ frameMono hU v ∧
    (∀ x ∈ frameMono hU v, ∀ y ∈ frameTorus hU v, x * y * x⁻¹ ∈ frameTorus hU v) ∧
    (∀ x ∈ frameTorus hU v, ∀ y ∈ frameTorus hU v, x * y = y * x) ∧
    (∀ x ∈ frameTorus hU v, x ^ (2 ^ f + 1) = 1) ∧
    Nat.card (frameTorus hU v) * Nat.gcd 3 (2 ^ f + 1) = (2 ^ f + 1) ^ 2 ∧
    Nonempty (frameTorus hU v ≃* Multiplicative (ZMod (2 ^ f + 1)) ×
      Multiplicative (ZMod ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)))) ∧
    ∃ π : frameMono hU v →* Equiv.Perm (Fin 3), Function.Surjective π ∧
      π.ker = (frameTorus hU v).subgroupOf (frameMono hU v) := by
  have _ := hf
  refine ⟨Subgroup.map_mono frameTorusSU_le_frameMonoSU, ?_, ?_, ?_, ?_, frameTorus_mulEquiv hv,
    exists_surjective_map_mk' _ (normOneScalars_le_frameTorusSU hU v 3) (linePermHom hv)
      (linePermHom_surjective hv) (ker_linePermHom hv)⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact ⟨g * h * g⁻¹, conj_mem_frameTorusSU hg hh, by simp only [map_mul, map_inv]⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, frameTorusSU_comm hv hg hh]
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, frameTorusSU_pow_eq_one hv hg, map_one]
  · rw [card_frameTorus hv, mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_right 3 _), sq]

theorem frame_involution (hU : UnitaryFieldData 2 f E) (hf : 2 ≤ f)
    {v : Fin 3 → (Fin 3 → E)} (hv : IsOrthonormalFrame hU v)
    {t : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)} (ht : t ∈ frameMono hU v) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) :
    t ∉ frameTorus hU v ∧
    IsCyclic ↥⁅frameTorus hU v, Subgroup.zpowers t⁆ ∧
    Nat.card ↥⁅frameTorus hU v, Subgroup.zpowers t⁆ = 2 ^ f + 1 ∧
    (∀ x ∈ ⁅frameTorus hU v, Subgroup.zpowers t⁆, t * x * t⁻¹ = x⁻¹) ∧
    Nat.card ↥(frameTorus hU v ⊓ Subgroup.centralizer ({t} : Set _)) * Nat.gcd 3 (2 ^ f + 1) =
      2 ^ f + 1 := by
  obtain ⟨-, hnorm, hcomm, hexp, hcard, -, -⟩ := frame_group_structure hU hf hv
  have := hU.finite
  have hnormt : ∀ x ∈ frameTorus hU v, t * x * t⁻¹ ∈ frameTorus hU v :=
    fun x hx => hnorm t ht x hx
  have htF : t ∉ frameTorus hU v := by
    intro htF
    apply ht1
    have h1 := hexp t htF
    have hf1 : 2 ^ f + 1 = 2 * 2 ^ (f - 1) + 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ f)]
    rw [hf1, pow_succ, pow_mul, sq, ht2, one_pow, one_mul] at h1
    exact h1
  have hCle : ⁅frameTorus hU v, Subgroup.zpowers t⁆ ≤ frameTorus hU v :=
    commutator_zpowers_le ht2 hnormt
  obtain ⟨g, hg, hgt⟩ := ht
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = linePermHom hv (⟨g, hg⟩⁻¹ : frameMonoSU hU v) := ⟨_, rfl⟩
  have hσl : ∀ l, σ l = lineIdx v ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E) l := fun l => by rw [hσ]; rfl
  have hgg : g * g ∈ normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3 := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (QuotientGroup.mk' (normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))
        3)) (g * g) = 1 := by
      rw [map_mul, hgt, ht2]
    exact h1
  have hσ2 : σ * σ = 1 := by
    have h1 : (⟨g, hg⟩ : frameMonoSU hU v) * ⟨g, hg⟩ ∈ (linePermHom hv).ker := by
      rw [ker_linePermHom hv, Subgroup.mem_subgroupOf]
      exact normOneScalars_le_frameTorusSU hU v 3 hgg
    rw [hσ, ← map_mul, ← _root_.mul_inv_rev, map_inv, MonoidHom.mem_ker.mp h1, inv_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply htF
    have h2 : (⟨g, hg⟩⁻¹ : frameMonoSU hU v) ∈ (linePermHom hv).ker :=
      MonoidHom.mem_ker.mpr (by rw [← hσ]; exact h1)
    rw [ker_linePermHom hv, Subgroup.mem_subgroupOf] at h2
    have h3 : g⁻¹ ∈ frameTorusSU hU v := h2
    exact ⟨g, by simpa using (frameTorusSU hU v).inv_mem h3, hgt⟩
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    apply hσ1
    refine Equiv.ext fun l => ?_
    by_contra hl
    exact h ⟨l, hl⟩
  obtain ⟨j, hj⟩ : ∃ j, σ i = j := ⟨_, rfl⟩
  have hij : i ≠ j := fun h => hi (hj.trans h.symm)
  have hji : σ j = i := by
    rw [← hj]
    exact congrArg (fun τ : Equiv.Perm (Fin 3) => τ i) hσ2
  obtain ⟨k, hki, hkj, hl⟩ := fin3_third i j hij
  have hσk : σ k = k := by
    rcases hl (σ k) with h | h | h
    · exact absurd (σ.injective (h.trans hji.symm)) hkj
    · exact absurd (σ.injective (h.trans hj.symm)) hki
    · exact h
  have hcommT : ∀ h : frameTorusSU hU v,
      ⁅(h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)), g⁆ ∈ frameTorusSU hU v := by
    intro h
    have e : ⁅(h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)), g⁆ =
        (h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) *
          (g * (h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem h.2 (conj_mem_frameTorusSU hg (inv_mem h.2))
  have hcommEig : ∀ (h : frameTorusSU hU v) (l : Fin 3),
      frameEigHom hv l ⟨⁅(h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)), g⁆, hcommT h⟩ =
        frameEigHom hv l h * (frameEigHom hv (σ l) h)⁻¹ := by
    intro h l
    have e : (⟨⁅(h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)), g⁆, hcommT h⟩ :
        frameTorusSU hU v) = h * ⟨g * (h : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))⁻¹ * g⁻¹,
          conj_mem_frameTorusSU hg (inv_mem h.2)⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [commutatorElement_def]
      group
    rw [e, map_mul, hσl, ← map_inv]
    congr 1
    exact frameEigHom_conj hv hg h⁻¹ l
  have hprod : ∀ x : frameTorusSU hU v,
      frameEigHom hv i x * frameEigHom hv j x * frameEigHom hv k x = 1 := by
    intro x
    rw [← prod_fin3_eq (fun l => frameEigHom hv l x) hij hki hkj]
    exact prod_frameEigHom hv x
  set Z := normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3
  obtain ⟨R, hR⟩ : ∃ R : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)),
      R = ((frameEigHom hv k).ker).map ((QuotientGroup.mk' Z).comp (frameTorusSU hU v).subtype) :=
    ⟨_, rfl⟩
  have hCR : ⁅frameTorus hU v, Subgroup.zpowers t⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rcases eq_one_or_eq_of_mem_zpowers ht2 hy with hy1 | hy1 <;> rw [hy1]
    · rw [commutatorElement_one_right]
      exact R.one_mem
    · obtain ⟨h, hh, rfl⟩ := hx
      rw [hR]
      refine ⟨⟨⁅h, g⁆, hcommT ⟨h, hh⟩⟩, MonoidHom.mem_ker.mpr ?_, ?_⟩
      · rw [hcommEig ⟨h, hh⟩ k, hσk, mul_inv_cancel]
      · show (QuotientGroup.mk' Z) ⁅h, g⁆ = ⁅(QuotientGroup.mk' Z) h, t⁆
        rw [map_commutatorElement, hgt]
  have hRcard : Nat.card R ≤ 2 ^ f + 1 := by
    rw [hR]
    calc Nat.card ↥(((frameEigHom hv k).ker).map
          ((QuotientGroup.mk' Z).comp (frameTorusSU hU v).subtype)) ≤
          Nat.card (frameEigHom hv k).ker :=
          Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
      _ ≤ Nat.card (rootsOfUnity (2 ^ f + 1) E) := by
          refine Nat.card_le_card_of_injective (fun x => frameEigHom hv i x) fun x x' hxx' => ?_
          have hxk : frameEigHom hv k (x : frameTorusSU hU v) = 1 := MonoidHom.mem_ker.mp x.2
          have hx'k : frameEigHom hv k (x' : frameTorusSU hU v) = 1 := MonoidHom.mem_ker.mp x'.2
          have hxx'' : frameEigHom hv i (x : frameTorusSU hU v) = frameEigHom hv i x' := hxx'
          apply Subtype.ext
          apply frameTorusSU_ext hv
          intro l
          rcases hl l with h | h | h <;> rw [h]
          · exact hxx''
          · have p1 := hprod x
            have p2 := hprod x'
            rw [hxk, mul_one, hxx''] at p1
            rw [hx'k, mul_one] at p2
            exact mul_left_cancel (p1.trans p2.symm)
          · rw [hxk, hx'k]
      _ = 2 ^ f + 1 := card_rootsOfUnity_eq hU
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity (2 ^ f + 1) E)
  have hζord : orderOf ζ = 2 ^ f + 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, card_rootsOfUnity_eq hU]
  let c : Fin 3 → rootsOfUnity (2 ^ f + 1) E := fun l =>
    if l = i then ζ else if l = k then ζ⁻¹ else 1
  have hci : c i = ζ := by simp [c]
  have hcj : c j = 1 := by simp [c, hij.symm, hkj.symm]
  have hck : c k = ζ⁻¹ := by simp [c, hki]
  have hcN : ∀ l, hU.norm ((c l : Eˣ) : E) = 1 := fun l => norm_coe_rootsOfUnity hU (c l)
  have hcp : ∏ l, ((c l : Eˣ) : E) = 1 := by
    have h1 : ∏ l, c l = 1 := by
      rw [prod_fin3_eq c hij hki hkj, hci, hcj, hck, mul_one, mul_inv_cancel]
    have h2 := congrArg (fun x : rootsOfUnity (2 ^ f + 1) E => ((x : Eˣ) : E)) h1
    simpa only [SubmonoidClass.coe_finsetProd, Units.coe_prod, OneMemClass.coe_one,
      Units.val_one] using h2
  let h₀ : frameTorusSU hU v := ⟨frameDiagElt hv (fun l => ((c l : Eˣ) : E)) hcN hcp,
    frameDiagElt_mem_frameTorusSU hv _ hcN hcp⟩
  have hh₀ : ∀ l, frameEigHom hv l h₀ = c l := fun l =>
    Subtype.ext (Units.ext (frameEig_eq hv (frameDiagElt_mulVec hv _ hcN hcp l)))
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : frameTorusSU hU v,
      x₀ = ⟨⁅(h₀ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)), g⁆, hcommT h₀⟩ := ⟨_, rfl⟩
  have hx₀i : frameEigHom hv i x₀ = ζ := by
    rw [hx₀, hcommEig, hj, hh₀, hh₀, hci, hcj, inv_one, mul_one]
  have hx₀k : frameEigHom hv k x₀ = 1 := by
    rw [hx₀, hcommEig, hσk, mul_inv_cancel]
  obtain ⟨y, hy⟩ : ∃ y, y = ⁅(QuotientGroup.mk' Z) (h₀ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)),
      t⁆ := ⟨_, rfl⟩
  have hyC : y ∈ ⁅frameTorus hU v, Subgroup.zpowers t⁆ := by
    rw [hy]
    exact Subgroup.commutator_mem_commutator ⟨(h₀ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)),
      h₀.2, rfl⟩ (Subgroup.mem_zpowers t)
  have hyx : y = (QuotientGroup.mk' Z) (x₀ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) := by
    rw [hy, ← hgt, hx₀]
    exact (map_commutatorElement _ _ _).symm
  have hy_dvd : ∀ n : ℕ, y ^ n = 1 → 2 ^ f + 1 ∣ n := by
    intro n hn
    rw [hyx, ← map_pow] at hn
    have hZn : ((x₀ ^ n : frameTorusSU hU v) : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      exact hn
    have h2 := frameEigHom_eq_of_mem_normOneScalars hv hZn i k
    rw [map_pow, map_pow, hx₀i, hx₀k, one_pow] at h2
    rw [← hζord]
    exact orderOf_dvd_of_pow_eq_one h2
  have hy_ord : orderOf y = 2 ^ f + 1 :=
    Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hexp y (hCle hyC)))
      (hy_dvd _ (pow_orderOf_eq_one y))
  have hCcard : Nat.card ↥⁅frameTorus hU v, Subgroup.zpowers t⁆ = 2 ^ f + 1 := by
    apply le_antisymm
    · exact (Subgroup.card_le_of_le hCR).trans hRcard
    · calc 2 ^ f + 1 = orderOf (⟨y, hyC⟩ : ↥⁅frameTorus hU v, Subgroup.zpowers t⁆) := by
            rw [Subgroup.orderOf_mk, hy_ord]
        _ ≤ Nat.card ↥⁅frameTorus hU v, Subgroup.zpowers t⁆ := orderOf_le_card
  refine ⟨htF, isCyclic_of_orderOf_eq_card (⟨y, hyC⟩ : ↥⁅frameTorus hU v, Subgroup.zpowers t⁆)
    (by rw [Subgroup.orderOf_mk, hy_ord, hCcard]), hCcard,
    fun x hx => conj_eq_inv_of_mem_commutator ht2 hcomm hnormt hx, ?_⟩
  have h1 := card_inf_centralizer_mul_card_commutator ht2 hcomm hnormt
  rw [hCcard] at h1
  have hm : 0 < 2 ^ f + 1 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hm
  calc Nat.card ↥(frameTorus hU v ⊓ Subgroup.centralizer {t}) * Nat.gcd 3 (2 ^ f + 1) *
        (2 ^ f + 1) = Nat.card (frameTorus hU v) * Nat.gcd 3 (2 ^ f + 1) := by
        rw [← h1]
        ring
    _ = (2 ^ f + 1) * (2 ^ f + 1) := by rw [hcard, sq]

end CFSG.GH74.Uniqueness.Bender.Frame
