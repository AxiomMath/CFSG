module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraph

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup)
open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical (radicalGroup
  radicalGroup_le mem_radicalGroup mem_radicalW radicalMatrix radicalMatrix_mulVec_single
  radicalMatrix_zero onesVec onesVec_apply radicalMatrix_mul radicalMatrix_mul_self
  mem_radicalGroup_of_dotProduct onesVec_dotProduct_onesVec dotProduct_self_eq_sq
  conj_radicalMatrix onesVec_dotProduct_mulVec_of_mem radicalGL card_radicalGroup)
open CFSG.ComponentClassification.OutcomeLocal (conj_mem_radicalGroup)
open scoped commutatorElement

theorem card_dvd_card_perfectCore_of_mulEquiv {P Γ : Type*} [Group P] [Group Γ] [Finite P]
    {H : Subgroup P} {O M : Subgroup Γ} (E : H ≃* O) (hMO : M ≤ O) (hM : ⁅M, M⁆ = M) :
    Nat.card M ∣ Nat.card (perfectCore H) := by
  set φ : M →* P := H.subtype.comp (E.symm.toMonoidHom.comp (Subgroup.inclusion hMO)) with hφ
  have hφinj : Function.Injective φ :=
    H.subtype_injective.comp (E.symm.injective.comp (Subgroup.inclusion_injective hMO))
  have hTH : φ.range ≤ H := by
    rintro _ ⟨m, rfl⟩
    exact (E.symm (Subgroup.inclusion hMO m)).2
  have hMp : Group.IsPerfect M := Subgroup.isPerfect_iff.mpr hM
  have hTp : Group.IsPerfect φ.range :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hle := le_perfectCore_of_perfect hTH (Subgroup.isPerfect_iff.mp hTp)
  rw [Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
  exact Subgroup.card_dvd_of_le hle

section Radical

variable {F : Type} [Field F] [CharP F 2] {n : ℕ}

theorem card_radicalGroup_mul_dvd_of_le [Finite F] (hn : Even n) (i : Fin n)
    {M H : Subgroup (GL (Fin n) F)} (hRM : radicalGroup (K := F) i ≤ M)
    (hMO : M ≤ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) F)) (hHM : H ≤ M)
    (hHe : ∀ h ∈ H, ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single i 1 =
      Pi.single i 1) :
    Nat.card (radicalGroup (K := F) i) * Nat.card H ∣ Nat.card M := by
  set R₀ := radicalGroup (K := F) i with hR₀
  set R := R₀.subgroupOf M with hR
  have hRn : R.Normal := ⟨fun x hx g => by
    rw [hR, mem_subgroupOf] at hx ⊢
    exact conj_mem_radicalGroup hn (hMO g.2) hx⟩
  let π : H →* M ⧸ R := (QuotientGroup.mk' R).comp (Subgroup.inclusion hHM)
  have hπ : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgR : Subgroup.inclusion hHM g ∈ R := (QuotientGroup.eq_one_iff _).1 hg
    rw [hR, mem_subgroupOf] at hgR
    obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).1 hgR
    have he := hHe g g.2
    change ((Subgroup.inclusion hHM g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ _ = _ at he
    rw [hc, radicalMatrix_mulVec_single hv c] at he
    have hvc : v + c • onesVec = 0 := by
      have h1 : Pi.single i 1 + (v + c • onesVec) = Pi.single i (1 : F) + 0 := by
        rw [add_zero, ← add_assoc]
        exact he
      exact add_left_cancel h1
    have hvi : v i = 0 := (mem_radicalW.1 hv).2
    have hc0 : c = 0 := by
      have h1 := congrFun hvc i
      simp only [Pi.add_apply, Pi.smul_apply, onesVec_apply, smul_eq_mul, mul_one, hvi,
        zero_add, Pi.zero_apply] at h1
      exact h1
    have hv0 : v = 0 := by
      rw [hc0, zero_smul, add_zero] at hvc
      exact hvc
    have h1 : ((Subgroup.inclusion hHM g : M) : GL (Fin n) F) = 1 := by
      apply Units.ext
      rw [hc, hv0, hc0, radicalMatrix_zero, Units.val_one]
    exact Subtype.ext h1
  have h1 : Nat.card H ∣ Nat.card (M ⧸ R) := Subgroup.card_dvd_of_injective π hπ
  have h2 : Nat.card M = Nat.card (M ⧸ R) * Nat.card R :=
    R.card_eq_card_quotient_mul_card_subgroup
  have h3 : Nat.card R = Nat.card R₀ := Nat.card_congr (subgroupOfEquivOfLe hRM).toEquiv
  rw [h2, h3, mul_comm (Nat.card (M ⧸ R))]
  exact Nat.mul_dvd_mul_left _ h1

end Radical

section Transv

variable {F : Type} [Field F] {m : ℕ}

@[expose] def dotTransvMatrix (u : Fin m → F) (a : F) : Matrix (Fin m) (Fin m) F :=
  1 + a • vecMulVec u u

theorem dotTransvMatrix_mulVec (u : Fin m → F) (a : F) (x : Fin m → F) :
    dotTransvMatrix u a *ᵥ x = x + (a * (u ⬝ᵥ x)) • u := by
  simp only [dotTransvMatrix, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]

theorem dotTransvMatrix_mul_self [CharP F 2] {u : Fin m → F} (hu : u ⬝ᵥ u = 0) (a : F) :
    dotTransvMatrix u a * dotTransvMatrix u a = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, dotTransvMatrix_mulVec, dotTransvMatrix_mulVec, one_mulVec]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hu, mul_zero, add_zero]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem dotTransvMatrix_transpose (u : Fin m → F) (a : F) :
    (dotTransvMatrix u a)ᵀ = dotTransvMatrix u a := by
  simp only [dotTransvMatrix, transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]

@[expose] def dotTransvGL [CharP F 2] {u : Fin m → F} (hu : u ⬝ᵥ u = 0) (a : F) : GL (Fin m) F :=
  ⟨dotTransvMatrix u a, dotTransvMatrix u a, dotTransvMatrix_mul_self hu a,
    dotTransvMatrix_mul_self hu a⟩

theorem coe_dotTransvGL [CharP F 2] {u : Fin m → F} (hu : u ⬝ᵥ u = 0) (a : F) :
    (dotTransvGL hu a : Matrix (Fin m) (Fin m) F) = dotTransvMatrix u a :=
  rfl

theorem dotTransvGL_mem [CharP F 2] {u : Fin m → F} (hu : u ⬝ᵥ u = 0) (a : F) :
    dotTransvGL hu a ∈ matrixIsometryGroup (1 : Matrix (Fin m) (Fin m) F) := by
  rw [mem_matrixIsometryGroup, Matrix.mul_one, coe_dotTransvGL, dotTransvMatrix_transpose,
    dotTransvMatrix_mul_self hu]

theorem coe_extendOneGL_dotTransvGL [CharP F 2] {u : Fin m → F} (hu : u ⬝ᵥ u = 0) (a : F) :
    (extendOneGL m F (dotTransvGL hu a) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      dotTransvMatrix (Fin.snoc (α := fun _ => F) u 0) a := by
  rw [coe_extendOneGL, coe_dotTransvGL]
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [dotTransvMatrix, vecMulVec_apply]
    | cast j =>
      simp [dotTransvMatrix, vecMulVec_apply, (Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp [dotTransvMatrix, vecMulVec_apply, (Fin.castSucc_lt_last i).ne]
    | cast j => simp [dotTransvMatrix, vecMulVec_apply, Matrix.one_apply]

end Transv

section Commutator

variable {F : Type} [Field F] [CharP F 2] {n : ℕ}

theorem commutator_radicalMatrix (hn : Even n) {x : Fin n → F} (hx : onesVec ⬝ᵥ x = 0)
    {g s : GL (Fin n) F} (hg : (g : Matrix (Fin n) (Fin n) F) = radicalMatrix x 0)
    (hs : s ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) F)) :
    ((⁅g, s⁆ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      radicalMatrix (x + (s : Matrix (Fin n) (Fin n) F) *ᵥ x)
        (x ⬝ᵥ ((s : Matrix (Fin n) (Fin n) F) *ᵥ x)) := by
  have hgg : g⁻¹ = g := by
    have h1 : g * g = 1 := Units.ext (by
      rw [Units.val_mul, hg, radicalMatrix_mul_self hn hx, Units.val_one])
    exact inv_eq_of_mul_eq_one_right h1
  have hsx : onesVec ⬝ᵥ ((s : Matrix (Fin n) (Fin n) F) *ᵥ x) = 0 := by
    rw [onesVec_dotProduct_mulVec_of_mem hs, hx]
  rw [commutatorElement_def, hgg, Units.val_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Matrix.mul_assoc (s : Matrix (Fin n) (Fin n) F), hg,
    conj_radicalMatrix hs x 0, radicalMatrix_mul 0 0 (onesVec_dotProduct_onesVec hn) hx hsx,
    zero_add, zero_add]

theorem commutator_radicalMatrix_dotTransv (hn : Even n) {x : Fin n → F} (hx : onesVec ⬝ᵥ x = 0)
    {u : Fin n → F} (a : F) {g s : GL (Fin n) F}
    (hg : (g : Matrix (Fin n) (Fin n) F) = radicalMatrix x 0)
    (hs : (s : Matrix (Fin n) (Fin n) F) = dotTransvMatrix u a)
    (hsO : s ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) F)) :
    ((⁅g, s⁆ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      radicalMatrix ((a * (u ⬝ᵥ x)) • u) (a * (u ⬝ᵥ x) ^ 2) := by
  rw [commutator_radicalMatrix hn hx hg hsO, hs, dotTransvMatrix_mulVec]
  have hxx : x ⬝ᵥ x = 0 := by rw [dotProduct_self_eq_sq, hx, zero_pow two_ne_zero]
  have h2 : x + x = 0 := funext fun j => by
    rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]
  congr 1
  · rw [← add_assoc, h2, zero_add]
  · rw [dotProduct_add, dotProduct_smul, hxx, zero_add, smul_eq_mul, dotProduct_comm x u]
    ring

end Commutator

section Four

variable {F : Type} [Field F] [Finite F] [CharP F 2]

variable (F) in
@[expose] noncomputable def isometryThreeImage : Subgroup (GL (Fin (3 + 1)) F) :=
  ((extendOneGL 3 F).comp (matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) F)).subtype).range

theorem isPerfect_matrixIsometryGroup_three (hF : Nat.card F = 2 ^ 2) :
    Group.IsPerfect (matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) F)) := by
  have h3 : (3 : ℕ) = 2 * 1 + 1 := rfl
  obtain ⟨e⟩ := CFSG.ComponentClassification.OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_isAlt (k := F) (n := 3))
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_nondegenerate h3)
    (CFSG.ComponentClassification.OutcomeLocal.finrank_dotForm_ker h3)
  have := CFSG.SeitzReduction.LinearOuter.isPerfect_statedSp_of_card (r := 1) (by norm_num) hF
    (Or.inl le_rfl)
  set E := (CFSG.ComponentClassification.OutcomeLocal.oneRestrictEquiv (k := F) h3).trans e
  exact Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) (MulEquiv.surjective _)

theorem commutator_isometryThreeImage (hF : Nat.card F = 2 ^ 2) :
    ⁅isometryThreeImage F, isometryThreeImage F⁆ = isometryThreeImage F := by
  have := isPerfect_matrixIsometryGroup_three hF
  set φ := (extendOneGL 3 F).comp (matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) F)).subtype
  have hp : Group.IsPerfect φ.range :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  exact Subgroup.isPerfect_iff.mp hp

omit [Finite F] [CharP F 2] in
theorem exists_ne_zero_ne_one_of_two_lt_card (hF : 2 < Nat.card F) : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hinj : Function.Injective (fun x : F => decide (x = 0)) := by
    intro x y hxy
    by_cases hx : x = 0
    · have hy : y = 0 := by simpa [hx] using hxy.symm
      rw [hx, hy]
    · have hy : y ≠ 0 := by simpa [hx] using hxy.symm
      rw [h x hx, h y hy]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem commutator_radicalGroup_sup (hF : Nat.card F = 2 ^ 2) :
    ⁅radicalGroup (K := F) (Fin.last 3) ⊔ isometryThreeImage F,
        radicalGroup (K := F) (Fin.last 3) ⊔ isometryThreeImage F⁆ =
      radicalGroup (K := F) (Fin.last 3) ⊔ isometryThreeImage F := by
  set R₀ := radicalGroup (K := F) (Fin.last 3) with hR₀
  set S := isometryThreeImage F with hS
  set M := R₀ ⊔ S with hM
  set N := ⁅M, M⁆ with hN
  have hev : Even (3 + 1) := ⟨2, rfl⟩
  have hdd : (onesVec : Fin (3 + 1) → F) ⬝ᵥ onesVec = 0 := onesVec_dotProduct_onesVec hev
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hadd : ∀ a : F, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  let Q : (Fin (3 + 1) → F) → F → Prop := fun v c =>
    ∃ g ∈ N, (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) = radicalMatrix v c
  have hQmul : ∀ {v v' : Fin (3 + 1) → F} {c c' : F}, onesVec ⬝ᵥ v = 0 →
      onesVec ⬝ᵥ v' = 0 → Q v c → Q v' c' → Q (v + v') (c + c' + v ⬝ᵥ v') := by
    rintro v v' c c' hv hv' ⟨g, hg, hgv⟩ ⟨g', hg', hgv'⟩
    exact ⟨g * g', N.mul_mem hg hg', by
      rw [Units.val_mul, hgv, hgv', radicalMatrix_mul c c' hdd hv hv']⟩
  have hQeq : ∀ {v v' : Fin (3 + 1) → F} {c c' : F}, v = v' → c = c' → Q v c → Q v' c' := by
    rintro v v' c c' rfl rfl h
    exact h
  set x₀ : Fin (3 + 1) → F := ![1, 0, 0, 1] with hx₀
  set u₁ : Fin (3 + 1) → F := ![1, 1, 0, 0] with hu₁
  set u₂ : Fin (3 + 1) → F := ![1, 0, 1, 0] with hu₂
  have hdx : ∀ μ : F, onesVec ⬝ᵥ (μ • x₀) = 0 := fun μ => by
    rw [dotProduct_smul]
    simp [hx₀, dotProduct, Fin.sum_univ_succ, onesVec, hadd]
  have hdu₁ : ∀ α : F, onesVec ⬝ᵥ (α • u₁) = 0 := fun α => by
    rw [dotProduct_smul]
    simp [hu₁, dotProduct, Fin.sum_univ_succ, onesVec, hadd]
  have hdu₂ : ∀ α : F, onesVec ⬝ᵥ (α • u₂) = 0 := fun α => by
    rw [dotProduct_smul]
    simp [hu₂, dotProduct, Fin.sum_univ_succ, onesVec, hadd]
  have hd0 : (onesVec : Fin (3 + 1) → F) ⬝ᵥ 0 = 0 := dotProduct_zero _
  have hu₁u₁ : u₁ ⬝ᵥ u₁ = 0 := by simp [hu₁, dotProduct, Fin.sum_univ_succ, hadd]
  have hu₁u₂ : u₁ ⬝ᵥ u₂ = 1 := by simp [hu₁, hu₂, dotProduct, Fin.sum_univ_succ]
  have hu₁x : u₁ ⬝ᵥ x₀ = 1 := by simp [hu₁, hx₀, dotProduct, Fin.sum_univ_succ]
  have hu₂x : u₂ ⬝ᵥ x₀ = 1 := by simp [hu₂, hx₀, dotProduct, Fin.sum_univ_succ]
  have hu₁' : (![1, 1, 0] : Fin 3 → F) ⬝ᵥ ![1, 1, 0] = 0 := by
    simp [dotProduct, Fin.sum_univ_succ, hadd]
  have hu₂' : (![1, 0, 1] : Fin 3 → F) ⬝ᵥ ![1, 0, 1] = 0 := by
    simp [dotProduct, Fin.sum_univ_succ, hadd]
  have hsn₁ : (Fin.snoc (α := fun _ => F) ![1, 1, 0] 0 : Fin (3 + 1) → F) = u₁ := by
    funext i
    fin_cases i <;> rfl
  have hsn₂ : (Fin.snoc (α := fun _ => F) ![1, 0, 1] 0 : Fin (3 + 1) → F) = u₂ := by
    funext i
    fin_cases i <;> rfl
  have hK1 : ∀ {u' : Fin 3 → F} (hu' : u' ⬝ᵥ u' = 0) {u : Fin (3 + 1) → F},
      (Fin.snoc (α := fun _ => F) u' 0 : Fin (3 + 1) → F) = u → u ⬝ᵥ x₀ = 1 →
        ∀ a μ : F, Q ((a * μ) • u) (a * μ ^ 2) := by
    intro u' hu' u hsn hux a μ
    have hgM : radicalGL hev (hdx μ) 0 ∈ M :=
      le_sup_left (a := R₀) (mem_radicalGroup_of_dotProduct hev (hdx μ) rfl)
    have hsM : extendOneGL 3 F (dotTransvGL hu' a) ∈ M :=
      le_sup_right (a := R₀) ⟨⟨dotTransvGL hu' a, dotTransvGL_mem hu' a⟩, rfl⟩
    refine ⟨⁅radicalGL hev (hdx μ) 0, extendOneGL 3 F (dotTransvGL hu' a)⁆,
      commutator_mem_commutator hgM hsM, ?_⟩
    rw [commutator_radicalMatrix_dotTransv hev (hdx μ) a rfl
      ((coe_extendOneGL_dotTransvGL hu' a).trans (by rw [hsn]))
      (extendOneGL_mem (dotTransvGL_mem hu' a)),
      dotProduct_smul, hux, smul_eq_mul, mul_one]
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_of_two_lt_card (F := F) (by rw [hF]; norm_num)
  have h1ω : (1 : F) + ω ≠ 0 := fun h => by
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    exact hω1 h.symm
  have hK3 : ∀ c : F, Q 0 c := by
    intro c
    set l := c / (1 + ω) with hl
    have hA : Q (l • u₁) l :=
      hQeq (by rw [mul_one]) (by rw [one_pow, mul_one]) (hK1 hu₁' hsn₁ hu₁x l 1)
    have hB : Q (l • u₁) (l * ω) :=
      hQeq (by rw [div_mul_cancel₀ _ hω0]) (by field_simp) (hK1 hu₁' hsn₁ hu₁x (l / ω) ω)
    refine hQeq ?_ ?_ (hQmul (hdu₁ l) (hdu₁ l) hA hB)
    · funext i
      rw [Pi.add_apply, hadd, Pi.zero_apply]
    · rw [smul_dotProduct, dotProduct_smul, hu₁u₁, smul_zero, smul_zero, add_zero, hl]
      field_simp
  have hK4 : ∀ {u' : Fin 3 → F} (hu' : u' ⬝ᵥ u' = 0) {u : Fin (3 + 1) → F},
      (Fin.snoc (α := fun _ => F) u' 0 : Fin (3 + 1) → F) = u → u ⬝ᵥ x₀ = 1 →
        (∀ α : F, onesVec ⬝ᵥ (α • u) = 0) → ∀ α c : F, Q (α • u) c := by
    intro u' hu' u hsn hux hdu α c
    have hA : Q (α • u) α :=
      hQeq (by rw [mul_one]) (by rw [one_pow, mul_one]) (hK1 hu' hsn hux α 1)
    refine hQeq ?_ ?_ (hQmul (hdu α) hd0 hA (hK3 (c + α)))
    · rw [add_zero]
    · rw [dotProduct_zero, add_zero, add_comm c α, ← add_assoc, hadd, zero_add]
  have hK5 : ∀ v : Fin (3 + 1) → F, onesVec ⬝ᵥ v = 0 → v (Fin.last 3) = 0 → ∀ c : F, Q v c := by
    intro v hv hv3 c
    have hdecomp : v = v 1 • u₁ + v 2 • u₂ := by
      have h0 : v 0 + v 1 + v 2 + v 3 = 0 := by
        simpa [dotProduct, Fin.sum_univ_succ, onesVec, add_assoc] using hv
      have h3' : v 3 = 0 := hv3
      funext i
      fin_cases i
      · simp [hu₁, hu₂]
        linear_combination h0 - h3' - (v 1 + v 2) * h2
      · simp [hu₁, hu₂]
      · simp [hu₁, hu₂]
      · simpa [hu₁, hu₂] using h3'
    have hA := hK4 hu₁' hsn₁ hu₁x hdu₁ (v 1) 0
    have hB := hK4 hu₂' hsn₂ hu₂x hdu₂ (v 2) (c + v 1 * v 2)
    refine hQeq hdecomp.symm ?_ (hQmul (hdu₁ (v 1)) (hdu₂ (v 2)) hA hB)
    simp only [smul_dotProduct, dotProduct_smul, hu₁u₂, smul_eq_mul, mul_one]
    linear_combination (v 1 * v 2) * h2
  have hRN : R₀ ≤ N := by
    intro g hg
    obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hev).1 hg
    obtain ⟨g', hg'N, hg'⟩ := hK5 v (mem_radicalW.1 hv).1 (mem_radicalW.1 hv).2 c
    have hgg : g = g' := Units.ext (hc.trans hg'.symm)
    rw [hgg]
    exact hg'N
  have hSN : S ≤ N := by
    have hSS : ⁅S, S⁆ = S := commutator_isometryThreeImage hF
    rw [← hSS]
    exact Subgroup.commutator_mono le_sup_right le_sup_right
  refine le_antisymm ?_ (sup_le hRN hSN)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)

omit [Finite F] in
theorem radicalGroup_sup_le :
    radicalGroup (K := F) (Fin.last 3) ⊔ isometryThreeImage F ≤
      matrixIsometryGroup (1 : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) := by
  refine sup_le (radicalGroup_le ⟨2, rfl⟩ _) ?_
  rintro _ ⟨g, rfl⟩
  exact extendOneGL_mem g.2

theorem two_pow_dvd_card_radicalGroup_sup (hF : Nat.card F = 2 ^ 2) :
    2 ^ 8 ∣ Nat.card (radicalGroup (K := F) (Fin.last 3) ⊔ isometryThreeImage F :
      Subgroup (GL (Fin (3 + 1)) F)) := by
  have hev : Even (3 + 1) := ⟨2, rfl⟩
  have hdvd := card_radicalGroup_mul_dvd_of_le hev (Fin.last 3)
    (M := radicalGroup (K := F) (Fin.last 3) ⊔ isometryThreeImage F) (H := isometryThreeImage F)
    le_sup_left radicalGroup_sup_le le_sup_right (by
      rintro _ ⟨g, rfl⟩
      exact extendOneGL_mulVec_single_last _)
  have hinj : Function.Injective ((extendOneGL 3 F).comp
      (matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) F)).subtype) :=
    extendOneGL_injective.comp Subtype.val_injective
  have hS : Nat.card (isometryThreeImage F) =
      Nat.card (CFSG.Assembly.LowTwoRank.StatedSp 1 F) := by
    rw [← card_matrixIsometryGroup_one_of_odd (F := F) (n := 3) (r := 1) rfl]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [card_radicalGroup hev, hS, SymplecticFlag.card_statedSp, hF] at hdvd
  refine dvd_trans ?_ hdvd
  decide

theorem graphInvolutionExclusion_four_two {K F : Type} [Field K] [Finite K] [Field F]
    (hK : Nat.card K = 2) (hF : Nat.card F = 4) : GraphInvolutionExclusion 4 K F := by
  have hF' : Nat.card F = 2 ^ 2 := hF
  have : Finite F := finite_of_card_eq_two_pow hF'
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF'
  intro A hθ h1 h2
  obtain ⟨C, hC, hcard, hcore⟩ :=
    card_fixedSubgroup_graph_eq (by norm_num : 1 ≤ 2) hF' (by norm_num) A hθ
  rcases hC with hC1 | ⟨r, hr, hJ⟩
  · obtain ⟨E⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv
      (by norm_num : 1 ≤ 2) hF' (by norm_num) C (Or.inl hC1)
    have hMO : radicalGroup (K := F) (Fin.last 3) ⊔ isometryThreeImage F ≤
        matrixIsometryGroup (C : Matrix (Fin 4) (Fin 4) F) := by
      rw [hC1]
      exact radicalGroup_sup_le
    have hM := card_dvd_card_perfectCore_of_mulEquiv E hMO (commutator_radicalGroup_sup hF')
    rw [hcore] at h2
    have h3 := ((two_pow_dvd_card_radicalGroup_sup hF').trans hM).trans h2
    have h4 : Nat.card (projectiveSL 4 K) ∣ Nat.card (SpecialLinearGroup (Fin 4) K) :=
      Subgroup.card_quotient_dvd_card _
    rw [card_SL_eq (by norm_num), hK] at h4
    have h5 := h3.trans h4
    revert h5
    decide
  · rw [hcard, hJ, card_matrixIsometryGroup_blockSwapJ hr] at h1
    exact not_card_statedSp_dvd_two_mul_card_mulAut (K := K) (f := 1) (r := r) (by norm_num)
      (by norm_num) (by omega) (by omega) (by rw [hK]; rfl) (by rw [hF]; rfl) h1

end Four

theorem graphInvolutionExclusion {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) {K F : Type} [Field K]
    [Finite K] [Field F] (hK : Nat.card K = 2 ^ f) (hF : Nat.card F = 2 ^ (2 * f)) :
    GraphInvolutionExclusion n K F := by
  by_cases h4 : n = 4 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h4
    exact graphInvolutionExclusion_four_two (by rw [hK]; rfl) (by rw [hF]; rfl)
  · exact graphInvolutionExclusion_of_ne_four hf hn (by omega) hK hF

end CFSG.SeitzReduction.LinearPilot
