module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoDecomp
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.CorootCoordinates
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KF4.A2Frame

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

theorem commute_of_orth_diff {α β : V4} (hα : IsRoot Tag.F4 α) (hβ : IsRoot Tag.F4 β)
    (hlen : ipF4 α α ≠ ipF4 β β) (horth : ipF4 α β = 0) (R : Type) [CommRing R] :
    ∀ x ∈ rootSubgroup Tag.F4 R α, ∀ y ∈ rootSubgroup Tag.F4 R β, Commute x y := by
  have hne : α ≠ β := fun h => hlen (by rw [h])
  have hne' : α ≠ -β := fun h => hlen (by rw [h, ipF4_neg_neg])
  refine commute_of_forall_not_isRoot hα hβ hne hne' (fun a b ha hb hroot => ?_) R
  rcases exponent_pair_cases noG2_F4 hα hβ hne hne' ha hb hroot with
    ⟨rfl, rfl⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
  · have h4 := iform_self_cases noG2_F4 hroot
    have hαc := iform_self_cases noG2_F4 hα
    have hβc := iform_self_cases noG2_F4 hβ
    rw [iform_F4] at h4 hαc hβc
    simp only [one_smul, iform_F4, ipF4_add_left, ipF4_add_right] at h4
    rw [ipF4_comm β α, horth] at h4
    omega
  · rw [iform_F4, horth] at h
    omega
  · rw [iform_F4, horth] at h
    omega

theorem rootSpan_commute_of_orth_diff {S₁ S₂ : Set V4} (h₁ : ∀ γ ∈ S₁, IsRoot Tag.F4 γ)
    (h₂ : ∀ γ ∈ S₂, IsRoot Tag.F4 γ)
    (hlen : ∀ α ∈ S₁, ∀ β ∈ S₂, ipF4 α α ≠ ipF4 β β)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, ipF4 α β = 0) (R : Type) [CommRing R] :
    ∀ x ∈ rootSpan Tag.F4 R S₁, ∀ y ∈ rootSpan Tag.F4 R S₂, Commute x y := by
  have step1 : ∀ α ∈ S₁, ∀ c : R, rootSpan Tag.F4 R S₂ ≤
      Subgroup.centralizer ({pinnedX Tag.F4 R α c} : Set _) := by
    intro α hα c
    refine iSup₂_le fun β hβ => ?_
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_orth_diff (h₁ α hα) (h₂ β hβ) (hlen α hα β hβ) (horth α hα β hβ) R
      (pinnedX Tag.F4 R α c) (Subgroup.subset_closure ⟨c, rfl⟩) z hz).symm.eq
  have key : rootSpan Tag.F4 R S₁ ≤ Subgroup.centralizer (rootSpan Tag.F4 R S₂ : Set _) := by
    refine iSup₂_le fun α hα => ?_
    rw [rootSubgroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    show pinnedX Tag.F4 R α c ∈ Subgroup.centralizer (rootSpan Tag.F4 R S₂ : Set _)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := step1 α hα c hy
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  intro x hx y hy
  have := key hx
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this y hy).symm

section Chars

variable {L : Type} [Field L]

theorem rootChar_zsmul (b : Fin Tag.F4.rank → Lˣ) (n : ℤ) (v : V4) :
    rootChar b (n • v) = rootChar b v ^ n := by
  have h := map_zpow (rootCharHom b) (Multiplicative.ofAdd v) n
  rw [← ofAdd_zsmul] at h
  exact h

theorem rootChar_neg' (b : Fin Tag.F4.rank → Lˣ) (v : V4) :
    rootChar b (-v) = (rootChar b v)⁻¹ := by
  have h := rootChar_zsmul b (-1) v
  rwa [neg_one_smul, zpow_neg_one] at h

theorem rootChar_closure (b : Fin Tag.F4.rank → Lˣ) {T : Set V4}
    (h : ∀ t ∈ T, rootChar b t = 1) : ∀ v ∈ AddSubgroup.closure T, rootChar b v = 1 := by
  intro v hv
  induction hv using AddSubgroup.closure_induction with
  | mem x hx => exact h x hx
  | zero => exact rootChar_zero b
  | add x y _ _ hx hy => rw [rootChar_add, hx, hy, one_mul]
  | neg x _ hx => rw [rootChar_neg', hx, inv_one]

@[expose] def diagSL3 (l : Fin 3 → Lˣ) (hl : l 0 * l 1 * l 2 = 1) : SL(3, L) :=
  ⟨Matrix.diagonal fun i => (l i : L), by
    rw [Matrix.det_diagonal, Fin.prod_univ_three, ← Units.val_mul, ← Units.val_mul, hl,
      Units.val_one]⟩

theorem coe_diagSL3 (l : Fin 3 → Lˣ) (hl : l 0 * l 1 * l 2 = 1) :
    ((diagSL3 l hl : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (l i : L) :=
  rfl

theorem diagSL3_mul_transvection (l : Fin 3 → Lˣ) (hl : l 0 * l 1 * l 2 = 1) {x y : Fin 3}
    (hxy : x ≠ y) (t : L) :
    diagSL3 l hl * Matrix.SpecialLinearGroup.transvection hxy t =
      Matrix.SpecialLinearGroup.transvection hxy ((l x : L) * t * ((l y)⁻¹ : Lˣ)) *
        diagSL3 l hl := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    coe_diagSL3]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  by_cases h : x = i ∧ y = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.one_apply, hxy]
  · rw [if_neg h, if_neg h]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply]
    · simp [Matrix.one_apply, hij]

theorem diagSL3_cube (κ : Fin 3 → Lˣ) (hκ : κ 0 * κ 1 * κ 2 = 1) (l : Fin 3 → Lˣ)
    (hl : l 0 * l 1 * l 2 = 1) (hlκ : ∀ i, l i = κ i ^ 3) :
    diagSL3 l hl = diagSL3 κ hκ ^ 3 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL3, coe_diagSL3, Matrix.diagonal_pow]
  congr 1
  funext i
  simp [hlκ i]

end Chars

section FrameChars

variable {L : Type} [Field L]

@[expose] def lab1 (σ : Fin 3 → Fin 3 → V4) (κ : ℤ) (v : V4) : ℤ := ipF4 v (σ 0 1) / κ

@[expose] def lab2 (σ : Fin 3 → Fin 3 → V4) (κ : ℤ) (v : V4) : ℤ := ipF4 v (σ 1 2) / κ

theorem exists_param_of_diag {ψ : SL(3, L) →* ModGL Tag.F4 L} {σ : Fin 3 → Fin 3 → V4}
    (hψ : IsA2Frame ψ σ) (l : Fin 3 → Lˣ) (hl : l 0 * l 1 * l 2 = 1) :
    ∃ b : Fin Tag.F4.rank → Lˣ, ψ (diagSL3 l hl) = rootDiagUnit Tag.F4 b :=
  exists_rootDiagUnit_eq_of_mem_torusGroup
    (hψ.diag _ fun i j hij => by simp [coe_diagSL3, Matrix.diagonal_apply_ne _ hij])

theorem char_frame_root {ψ : SL(3, L) →* ModGL Tag.F4 L} {σ : Fin 3 → Fin 3 → V4}
    (hψ : IsA2Frame ψ σ) {l : Fin 3 → Lˣ} {hl : l 0 * l 1 * l 2 = 1}
    {b : Fin Tag.F4.rank → Lˣ} (hb : ψ (diagSL3 l hl) = rootDiagUnit Tag.F4 b) {x y : Fin 3}
    (hxy : x ≠ y) : rootChar b (σ x y) = l x * (l y)⁻¹ := by
  obtain ⟨ε, hε⟩ := hψ.transv x y hxy
  have hroot := hψ.isRoot x y hxy
  have h1 : rootDiagUnit Tag.F4 b * ψ (Matrix.SpecialLinearGroup.transvection hxy (1 : L)) =
      ψ (Matrix.SpecialLinearGroup.transvection hxy ((l x : L) * 1 * ((l y)⁻¹ : Lˣ))) *
        rootDiagUnit Tag.F4 b := by
    rw [← hb, ← map_mul, ← map_mul, diagSL3_mul_transvection]
  rw [hε, hε] at h1
  have h2 := rootDiagUnit_conj_pinnedX b hroot ((ε : L) * 1)
  have h3 : rootDiagUnit Tag.F4 b * pinnedX Tag.F4 L (σ x y) ((ε : L) * 1) =
      pinnedX Tag.F4 L (σ x y) ((rootChar b (σ x y) : L) * ((ε : L) * 1)) *
        rootDiagUnit Tag.F4 b := by
    rw [← h2]
    group
  rw [h3] at h1
  have h4 := pinnedX_injective Tag.F4 L (σ x y) (mul_right_cancel h1)
  have h5 : (rootChar b (σ x y) : L) * (ε : L) = (ε : L) * ((l x : L) * ((l y)⁻¹ : Lˣ)) := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using h4
  have h6 : (rootChar b (σ x y) : L) = (l x : L) * ((l y)⁻¹ : Lˣ) :=
    mul_right_cancel₀ (Units.ne_zero ε) (by rw [h5]; ring)
  exact Units.ext (by rw [h6]; simp)

theorem char_orth_root {ψ : SL(3, L) →* ModGL Tag.F4 L} {σ : Fin 3 → Fin 3 → V4}
    (hψ : IsA2Frame ψ σ) {l : Fin 3 → Lˣ} {hl : l 0 * l 1 * l 2 = 1}
    {b : Fin Tag.F4.rank → Lˣ} (hb : ψ (diagSL3 l hl) = rootDiagUnit Tag.F4 b) {t : V4}
    (ht : IsRoot Tag.F4 t)
    (hcomm : ∀ x y : Fin 3, x ≠ y → ∀ c c' : L,
      Commute (pinnedX Tag.F4 L t c) (pinnedX Tag.F4 L (σ x y) c')) : rootChar b t = 1 := by
  have hmem : ψ (diagSL3 l hl) ∈ rootSpan Tag.F4 L {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} := by
    rw [← hψ.range]
    exact ⟨_, rfl⟩
  have hle : rootSpan Tag.F4 L {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} ≤
      Subgroup.centralizer ({pinnedX Tag.F4 L t 1} : Set _) := by
    refine iSup₂_le fun r hr => ?_
    obtain ⟨i, j, hij, rfl⟩ := hr
    rw [rootSubgroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c', rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm i j hij 1 c').symm.eq
  have hc := hle hmem
  rw [Subgroup.mem_centralizer_singleton_iff, hb] at hc
  have h2 := rootDiagUnit_conj_pinnedX b ht (1 : L)
  have h3 : rootDiagUnit Tag.F4 b * pinnedX Tag.F4 L t 1 * (rootDiagUnit Tag.F4 b)⁻¹ =
      pinnedX Tag.F4 L t 1 := by
    rw [hc]; group
  rw [h3] at h2
  have h4 := pinnedX_injective Tag.F4 L t h2
  exact Units.ext (by simpa using h4.symm)

theorem cube_identity_add {G : Type*} [AddCommGroup G] (a b c : G) (h : a + b + c = 0)
    (A B : ℤ) :
    (2 * A + B) • (a - b) + (A + 2 * B) • (b - c) = (3 : ℕ) • ((A + B) • a + B • b) := by
  have hc : c = -(a + b) := by
    have := congrArg (fun x => x - (a + b)) h
    simp at this
    abel_nf at this ⊢
    simpa using this
  subst hc
  module

theorem cube_identity (l0 l1 l2 : Lˣ) (h : l0 * l1 * l2 = 1) (A B : ℤ) :
    (l0 * l1⁻¹) ^ (2 * A + B) * (l1 * l2⁻¹) ^ (A + 2 * B) = (l0 ^ (A + B) * l1 ^ B) ^ 3 := by
  have h' : Additive.ofMul l0 + Additive.ofMul l1 + Additive.ofMul l2 = 0 := by
    have := congrArg Additive.ofMul h
    simpa [ofMul_mul] using this
  have := cube_identity_add (Additive.ofMul l0) (Additive.ofMul l1) (Additive.ofMul l2) h' A B
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv, ofMul_pow, ← sub_eq_add_neg]
  simpa using this

theorem rootChar_pow (a : Fin Tag.F4.rank → Lˣ) (n : ℕ) (v : V4) :
    rootChar (a ^ n) v = rootChar a v ^ n := by
  simp only [rootChar, Pi.pow_apply, Finset.prod_pow]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem frame_diag_chars_cube {ψ : SL(3, L) →* ModGL Tag.F4 L} {σ : Fin 3 → Fin 3 → V4}
    {κ : ℤ} (hψ : IsA2Frame ψ σ) {T : Set V4} (hT : ∀ t ∈ T, IsRoot Tag.F4 t)
    (hcomm : ∀ t ∈ T, ∀ x y : Fin 3, x ≠ y → ∀ c c' : L,
      Commute (pinnedX Tag.F4 L t c) (pinnedX Tag.F4 L (σ x y) c'))
    (hdec : ∀ v : V4, ∃ t ∈ AddSubgroup.closure T, (3 : ℤ) • v =
      (2 * lab1 σ κ v + lab2 σ κ v) • σ 0 1 + (lab1 σ κ v + 2 * lab2 σ κ v) • σ 1 2 + t)
    {l : Fin 3 → Lˣ} {hl : l 0 * l 1 * l 2 = 1} {b : Fin Tag.F4.rank → Lˣ}
    (hb : ψ (diagSL3 l hl) = rootDiagUnit Tag.F4 b) (v : V4) :
    rootChar b v ^ 3 = (l 0 ^ (lab1 σ κ v + lab2 σ κ v) * l 1 ^ lab2 σ κ v) ^ 3 := by
  obtain ⟨t, htm, hv⟩ := hdec v
  have hTc : ∀ t ∈ T, rootChar b t = 1 := fun t ht =>
    char_orth_root hψ hb (hT t ht) (hcomm t ht)
  have ht1 := rootChar_closure b hTc t htm
  have h3 : rootChar b ((3 : ℤ) • v) = rootChar b v ^ 3 := by
    rw [rootChar_zsmul]
    norm_num
  rw [← h3, hv, rootChar_add, rootChar_add, rootChar_zsmul, rootChar_zsmul, ht1, mul_one,
    char_frame_root hψ hb (by decide : (0 : Fin 3) ≠ 1),
    char_frame_root hψ hb (by decide : (1 : Fin 3) ≠ 2)]
  exact cube_identity (l 0) (l 1) (l 2) hl _ _

theorem exists_cube_root [IsAlgClosed L] (u : Lˣ) : ∃ w : Lˣ, w ^ 3 = u := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) (by norm_num : 0 < 3)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hz
    exact u.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

theorem frame_diag_chars [IsAlgClosed L] {ψ : SL(3, L) →* ModGL Tag.F4 L}
    {σ : Fin 3 → Fin 3 → V4} {κ : ℤ} (hψ : IsA2Frame ψ σ) {T : Set V4}
    (hT : ∀ t ∈ T, IsRoot Tag.F4 t)
    (hcomm : ∀ t ∈ T, ∀ x y : Fin 3, x ≠ y → ∀ c c' : L,
      Commute (pinnedX Tag.F4 L t c) (pinnedX Tag.F4 L (σ x y) c'))
    (hdec : ∀ v : V4, ∃ t ∈ AddSubgroup.closure T, (3 : ℤ) • v =
      (2 * lab1 σ κ v + lab2 σ κ v) • σ 0 1 + (lab1 σ κ v + 2 * lab2 σ κ v) • σ 1 2 + t)
    {l : Fin 3 → Lˣ} {hl : l 0 * l 1 * l 2 = 1} {b : Fin Tag.F4.rank → Lˣ}
    (hb : ψ (diagSL3 l hl) = rootDiagUnit Tag.F4 b) (v : V4) :
    rootChar b v = l 0 ^ (lab1 σ κ v + lab2 σ κ v) * l 1 ^ lab2 σ κ v := by
  choose w hw using fun u : Lˣ => exists_cube_root (L := L) u
  set κ' : Fin 3 → Lˣ := ![w (l 0), w (l 1), (w (l 0) * w (l 1))⁻¹] with hκ'
  have hκ'1 : κ' 0 * κ' 1 * κ' 2 = 1 := by
    simp [hκ']
  have hκ'cube : ∀ i, l i = κ' i ^ 3 := by
    intro i
    fin_cases i
    · simp [hκ', hw]
    · simp [hκ', hw]
    · have hl2 : l 2 = (l 0 * l 1)⁻¹ := eq_inv_of_mul_eq_one_right hl
      change l 2 = ((w (l 0) * w (l 1))⁻¹) ^ 3
      rw [hl2, inv_pow, mul_pow, hw, hw]
  obtain ⟨bκ, hbκ⟩ := exists_param_of_diag hψ κ' hκ'1
  have hdiag : diagSL3 l hl = diagSL3 κ' hκ'1 ^ 3 := diagSL3_cube κ' hκ'1 l hl hκ'cube
  have hbb : b = bκ ^ 3 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (K := L) (τ := Tag.F4)
    rw [← hb, hdiag, map_pow, hbκ]
    exact (map_pow (rootDiagUnitHom Tag.F4 L) bκ 3).symm
  have hcube := frame_diag_chars_cube hψ hT hcomm hdec hbκ v
  have key : ∀ (u : Lˣ) (e : ℤ), (u ^ e) ^ 3 = (u ^ 3) ^ e := by
    intro u e
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  rw [hbb, rootChar_pow, hcube, mul_pow, key, key, ← hκ'cube 0, ← hκ'cube 1]

end FrameChars

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

