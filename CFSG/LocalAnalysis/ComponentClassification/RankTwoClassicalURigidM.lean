module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidComm
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUSetup

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {K : Type} [Field K] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem stdHermForm_eq_hform {n : ℕ} (x y : Fin n → K) :
    stdHermForm h n x y = hform h.bar x y := by
  rw [stdHermForm_eq_gramForm, gramForm_apply, one_mulVec]
  rfl

theorem exists_isHypTransport_col [Finite K] [CharP K 2] (hε : 1 ≤ ε)
    {u : Fin (2 * 1 + ε) → K} (hu : u ≠ 0) (huu : hform h.bar u u = 0) :
    ∃ R : Matrix (Fin (2 * 1 + ε)) (HypIndex 1 ε) K, IsHypTransport h R ∧
      R *ᵥ Pi.single hE 1 = u := by
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport h (r := 1) (ε := ε)
  set u₀ := R₀ *ᵥ (Pi.single hE 1 : HypIndex 1 ε → K) with hu₀def
  have hu₀ : u₀ ≠ 0 := by
    intro h0
    have := congrArg (transportInv h R₀ *ᵥ ·) h0
    simp only [hu₀def, mulVec_mulVec, transportInv_mul hR₀, one_mulVec, mulVec_zero] at this
    have h1 := congrFun this hE
    simp at h1
  have hu₀u₀ : hform h.bar u₀ u₀ = 0 := by
    rw [← stdHermForm_eq_hform, hu₀def, stdHermForm_transport hR₀, hypForm_apply]
    simp [Fintype.sum_sum_type, Pi.single_apply, hypPartner]
  obtain ⟨g, hg⟩ := exists_statedSU_mulVec_eq h (n := 2 * 1 + ε) (by omega) hu₀ hu₀u₀ hu huu
  refine ⟨(g : GL (Fin (2 * 1 + ε)) K).val * R₀, ?_, ?_⟩
  · have hgu := adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply g.2
    show (((g : GL (Fin (2 * 1 + ε)) K).val * R₀).map h.bar)ᵀ *
      ((g : GL (Fin (2 * 1 + ε)) K).val * R₀) = hypGram 1 ε K
    rw [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ R₀]
    change (R₀.map h.bar)ᵀ * (adjM h.bar (g : GL (Fin (2 * 1 + ε)) K).val *
      (g : GL (Fin (2 * 1 + ε)) K).val * R₀) = _
    rw [hgu, Matrix.one_mul]
    exact hR₀
  · rw [← mulVec_mulVec]
    exact hg

section Transported

variable [CharP K 2] {R : Matrix (Fin (2 * 1 + ε)) (HypIndex 1 ε) K} (hR : IsHypTransport h R)

noncomputable abbrev stabU : Subgroup (StatedSU (2 * 1 + ε) (2 ^ f) K) :=
  (stabE h).map (hypTransport h hR).toMonoidHom

noncomputable abbrev eichU : Subgroup (StatedSU (2 * 1 + ε) (2 ^ f) K) :=
  (eichSub h).map (hypTransport h hR).toMonoidHom

theorem commutator_stabU (hf : 2 ≤ f) (hε : 2 ≤ ε) : ⁅stabU h hR, stabU h hR⁆ = stabU h hR := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  rw [stabU, ← Subgroup.map_commutator]
  exact Subgroup.map_mono (stabE_le_commutator h hf hε)

theorem isPGroup_eichU : IsPGroup 2 (eichU h hR) := (isPGroup_eichSub h).map _

omit [CharP K 2] in
theorem mulVec_of_mem_stabU {g : StatedSU (2 * 1 + ε) (2 ^ f) K} (hg : g ∈ stabU h hR) :
    (g : GL (Fin (2 * 1 + ε)) K).val *ᵥ (R *ᵥ Pi.single hE 1) = R *ᵥ Pi.single hE 1 := by
  obtain ⟨g', hg', rfl⟩ := hg
  have h1 := (mem_stabE h).mp hg'
  change (R * ((g' : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) *
    transportInv h R) *ᵥ (R *ᵥ Pi.single hE 1) = _
  rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, transportInv_mul hR, Matrix.mul_one,
    ← mulVec_mulVec, h1]

omit [CharP K 2] in
theorem mem_stabU_of {g : StatedSU (2 * 1 + ε) (2 ^ f) K}
    (hg : (g : GL (Fin (2 * 1 + ε)) K).val *ᵥ (R *ᵥ Pi.single hE 1) = R *ᵥ Pi.single hE 1) :
    g ∈ stabU h hR := by
  refine ⟨(hypTransport h hR).symm g, (mem_stabE h).mpr ?_, MulEquiv.apply_symm_apply _ _⟩
  rw [coe_hypTransport_symm, ← mulVec_mulVec, ← mulVec_mulVec, hg, mulVec_mulVec,
    transportInv_mul hR, one_mulVec]

omit [CharP K 2] in
theorem transport_single :
    R * (Matrix.single hE hF (1 : K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) *
      transportInv h R =
      vecMulVec (R *ᵥ Pi.single hE 1) (h.bar ∘ (R *ᵥ Pi.single hE 1)) := by
  ext i j
  simp [mul_apply, transportInv, hypGram_apply, Matrix.single, vecMulVec_apply,
    Fintype.sum_sum_type, transpose_apply, map_apply, hypPartner]

theorem eq_of_commute_eichU {Z : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K}
    (hZ : ∀ g ∈ eichU h hR, Z * (g : GL (Fin (2 * 1 + ε)) K).val =
      (g : GL (Fin (2 * 1 + ε)) K).val * Z) :
    ∃ μ β : K, Z = μ • 1 + β • vecMulVec (R *ᵥ Pi.single hE 1)
      (h.bar ∘ (R *ᵥ Pi.single hE 1)) := by
  obtain ⟨μ, β, hμβ⟩ := eq_of_commute_eichM h (Z := transportInv h R * Z * R) fun a c hc => by
    have hc' := hZ _ ⟨eich h hc, eich_mem_eichSub h hc, rfl⟩
    change Z * (R * eichM h.bar a c * transportInv h R) =
      (R * eichM h.bar a c * transportInv h R) * Z at hc'
    calc transportInv h R * Z * R * eichM h.bar a c
        = transportInv h R * (Z * (R * eichM h.bar a c * transportInv h R)) * R := by
          simp only [Matrix.mul_assoc, transportInv_mul hR, Matrix.mul_one]
      _ = transportInv h R * ((R * eichM h.bar a c * transportInv h R) * Z) * R := by rw [hc']
      _ = eichM h.bar a c * (transportInv h R * Z * R) := by
          simp only [← Matrix.mul_assoc, transportInv_mul hR, Matrix.one_mul]
  refine ⟨μ, β, ?_⟩
  rw [← transport_transportInv hR Z, hμβ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    mul_transportInv hR, transport_single h]

omit [CharP K 2] in
include hR in
theorem transport_col_ne_zero : R *ᵥ (Pi.single hE 1 : HypIndex 1 ε → K) ≠ 0 := by
  intro h0
  have := congrArg (transportInv h R *ᵥ ·) h0
  simp only [mulVec_mulVec, transportInv_mul hR, one_mulVec, mulVec_zero] at this
  have h1 := congrFun this hE
  simp at h1

omit [CharP K 2] in
include hR in
theorem transport_col_isotropic :
    hform h.bar (R *ᵥ (Pi.single hE 1 : HypIndex 1 ε → K))
      (R *ᵥ (Pi.single hE 1 : HypIndex 1 ε → K)) = 0 := by
  rw [← stdHermForm_eq_hform, stdHermForm_transport hR, hypForm_apply]
  simp [Fintype.sum_sum_type, Pi.single_apply, hypPartner]

theorem exists_mem_eichU_ne_one : ∃ g ∈ eichU h hR, g ≠ 1 := by
  have hc : (1 : K) + h.bar 1 = ∑ k, h.bar ((0 : Fin ε → K) k) * (0 : Fin ε → K) k := by
    simp [CharTwo.add_self_eq_zero]
  refine ⟨_, ⟨eich h hc, eich_mem_eichSub h hc, rfl⟩, fun h1 => ?_⟩
  have h2 := congrArg (fun g : StatedSU (2 * 1 + ε) (2 ^ f) K =>
    transportInv h R * ((g : GL (Fin (2 * 1 + ε)) K) :
      Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) * R) h1
  simp only [MulEquiv.coe_toMonoidHom, coe_hypTransport, OneMemClass.coe_one, Units.val_one,
    Matrix.mul_one, transportInv_mul hR, transportInv_transport hR] at h2
  have h3 := congrFun (congrFun h2 hE) hF
  simp [coe_eich, eichM] at h3

end Transported

theorem mulVec_eq_of_commute_of_pow [CharP K 2] {n : ℕ} {g : Matrix (Fin n) (Fin n) K}
    {u : Fin n → K} (hu : u ≠ 0)
    (hg : g * vecMulVec u (h.bar ∘ u) = vecMulVec u (h.bar ∘ u) * g) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g *ᵥ u = u := by
  rw [mul_vecMulVec, vecMulVec_mul] at hg
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu (funext hc)
  have hwj : (h.bar ∘ u) j ≠ 0 := by simpa using hj
  set ν := ((h.bar ∘ u) ᵥ* g) j / (h.bar ∘ u) j with hν
  have hgu : g *ᵥ u = ν • u := by
    ext i
    have := congrFun (congrFun hg i) j
    simp only [vecMulVec_apply] at this
    rw [Pi.smul_apply, smul_eq_mul, hν]
    field_simp
    linear_combination this
  have hpow : ∀ m : ℕ, (g ^ m) *ᵥ u = ν ^ m • u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mulVec_mulVec, hgu, mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have h1 := hpow (2 ^ k)
  rw [hk, one_mulVec] at h1
  have hνk : ν ^ 2 ^ k = 1 := by
    have := congrFun h1 j
    rw [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_right₀ hj).mp this.symm
  have h2 : (ν - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, hνk, one_pow, sub_self]
  have h3 : ν = 1 := sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h2)
  rw [hgu, h3, one_smul]

section Transvection

variable {n : ℕ}

theorem exists_transvection_eq [CharP K 2] {M : GL (Fin n) K} (hMH : M ∈ StatedSU n (2 ^ f) K)
    (hM2 : orderOf M = 2) (hr : ((M : Matrix (Fin n) (Fin n) K) - 1).rank = 1) :
    ∃ (u : Fin n → K) (c : K), u ≠ 0 ∧ c ≠ 0 ∧ h.bar c = c ∧ hform h.bar u u = 0 ∧
      (M : Matrix (Fin n) (Fin n) K) - 1 = c • vecMulVec u (h.bar ∘ u) := by
  have hMu := adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply hMH
  have hMM : (M : Matrix (Fin n) (Fin n) K) * M = 1 := by
    rw [← Units.val_mul, ← sq, ← hM2, pow_orderOf_eq_one, Units.val_one]
  have hMadj : adjM h.bar (M : Matrix (Fin n) (Fin n) K) = M := by
    calc adjM h.bar (M : Matrix (Fin n) (Fin n) K) =
        adjM h.bar (M : Matrix (Fin n) (Fin n) K) * (M * M) := by rw [hMM, mul_one]
      _ = M := by rw [← mul_assoc, hMu, one_mul]
  have hNh : adjM h.bar ((M : Matrix (Fin n) (Fin n) K) - 1) =
      (M : Matrix (Fin n) (Fin n) K) - 1 := by
    rw [adjM_sub, hMadj, adjM_one]
  obtain ⟨u, c, hu, hc0, hcσ, huu, huc⟩ := exists_hermitian_rank_one h.bar_bar hNh
    (sub_one_mul_self_eq_zero hM2) hr
  refine ⟨u, c, hu, hc0, hcσ, huu, ?_⟩
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [huc, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul, hform]

variable {u : Fin n → K} {c : K}

theorem vecMulVec_mul_self (huu : hform h.bar u u = 0) :
    vecMulVec u (h.bar ∘ u) * vecMulVec u (h.bar ∘ u) = 0 := by
  rw [vecMulVec_mul_vecMulVec]
  have : (h.bar ∘ u) ⬝ᵥ u = 0 := huu
  rw [this, zero_smul]
  ext i j
  simp [vecMulVec_apply]

theorem commute_vecMulVec_of_mulVec {g : GL (Fin n) K} (hg : g ∈ StatedSU n (2 ^ f) K)
    (hgu : (g : Matrix (Fin n) (Fin n) K) *ᵥ u = u) :
    (g : Matrix (Fin n) (Fin n) K) * vecMulVec u (h.bar ∘ u) =
      vecMulVec u (h.bar ∘ u) * g := by
  have hgu' := adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply hg
  have hadj : adjM h.bar (g : Matrix (Fin n) (Fin n) K) *ᵥ u = u := by
    conv_lhs => rw [← hgu]
    rw [mulVec_mulVec, hgu', one_mulVec]
  rw [mul_vecMulVec, hgu, vecMulVec_mul]
  congr 1
  funext j
  have := congrFun hadj j
  simp only [adjM, mulVec, dotProduct, transpose_apply, map_apply] at this
  simp only [vecMul, dotProduct, Function.comp]
  rw [← this, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.bar_bar, mul_comm]

end Transvection

section Sylow

variable [Finite K] [CharP K 2] {R : Matrix (Fin (2 * 1 + ε)) (HypIndex 1 ε) K}
  (hR : IsHypTransport h R)

omit [Finite K] in
theorem eq_one_of_smul_one_pow {n : ℕ} {μ : K} {k : ℕ}
    (hk : (μ • (1 : Matrix (Fin n) (Fin n) K)) ^ 2 ^ k = 1) (hn : 1 ≤ n) : μ = 1 := by
  rw [smul_pow, one_pow] at hk
  have h1 := congrFun (congrFun hk ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h1
  have h2 : (μ - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h1, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h2)

theorem exists_sylow_le_stabU :
    ∃ S : Sylow 2 (StatedSU (2 * 1 + ε) (2 ^ f) K), eichU h hR ≤ S ∧
      (S : Subgroup (StatedSU (2 * 1 + ε) (2 ^ f) K)) ≤ stabU h hR := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (isPGroup_eichU h hR).exists_le_sylow
  refine ⟨S, hS, ?_⟩
  set u := R *ᵥ (Pi.single hE 1 : HypIndex 1 ε → K) with hu_def
  have hu0 := transport_col_ne_zero h hR
  obtain ⟨g₀, hg₀, hg₀1⟩ := exists_mem_eichU_ne_one h hR
  have : Nontrivial S := ⟨⟨⟨g₀, hS hg₀⟩, 1, fun h' => hg₀1 (congrArg Subtype.val h')⟩⟩
  have hSp : IsPGroup 2 S := S.isPGroup'
  have := hSp.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center S)
  set Zm : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K :=
    (((z : S) : StatedSU (2 * 1 + ε) (2 ^ f) K) : GL (Fin (2 * 1 + ε)) K).val with hZm
  have hzc : ∀ g : S, ((g : StatedSU (2 * 1 + ε) (2 ^ f) K) : GL (Fin (2 * 1 + ε)) K).val * Zm =
      Zm * ((g : StatedSU (2 * 1 + ε) (2 ^ f) K) : GL (Fin (2 * 1 + ε)) K).val := by
    intro g
    have := (Subgroup.mem_center_iff.mp z.2) g
    have := congrArg (fun x : S => (((x : StatedSU (2 * 1 + ε) (2 ^ f) K) :
      GL (Fin (2 * 1 + ε)) K) : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K)) this
    simpa only [Subgroup.coe_mul, Units.val_mul] using this
  obtain ⟨μ, β, hzμβ⟩ := eq_of_commute_eichU h hR (Z := Zm) fun g hg => (hzc ⟨g, hS hg⟩).symm
  have hβ : β ≠ 0 := by
    intro hβ0
    rw [hβ0, zero_smul, add_zero] at hzμβ
    obtain ⟨k, hk⟩ := hSp (z : S)
    have hk' : Zm ^ 2 ^ k = 1 := by
      have := congrArg (fun x : S => (((x : StatedSU (2 * 1 + ε) (2 ^ f) K) :
        GL (Fin (2 * 1 + ε)) K) : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K)) hk
      simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] using this
    rw [hzμβ] at hk'
    have hμ1 := eq_one_of_smul_one_pow hk' (by omega)
    apply hz1
    refine Subtype.ext (Subtype.ext (Subtype.ext (Units.ext ?_)))
    show Zm = 1
    rw [hzμβ, hμ1, one_smul]
  intro s hs
  refine mem_stabU_of h hR ?_
  have hsz := hzc ⟨s, hs⟩
  rw [hzμβ] at hsz
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, add_right_inj] at hsz
  have hsW := smul_right_injective _ hβ hsz
  obtain ⟨k, hk⟩ := hSp ⟨s, hs⟩
  have hk' : ((s : GL (Fin (2 * 1 + ε)) K) : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) ^
      2 ^ k = 1 := by
    have := congrArg (fun x : S => (((x : StatedSU (2 * 1 + ε) (2 ^ f) K) :
      GL (Fin (2 * 1 + ε)) K) : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K)) hk
    simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] using this
  exact mulVec_eq_of_commute_of_pow h hu0 hsW hk'

end Sylow

section OneAdd

variable {n : ℕ} {u : Fin n → K}

omit [Field K] in
theorem eq_zero_of_smul_one_add_smul [Field K] {W : Matrix (Fin n) (Fin n) K} (hW : W ≠ 0)
    (hW2 : W * W = 0) {x y : K} (hxy : x • (1 : Matrix (Fin n) (Fin n) K) + y • W = 0) :
    x = 0 ∧ y = 0 := by
  have h1 := congrArg (· * W) hxy
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hW2, smul_zero, add_zero,
    Matrix.zero_mul] at h1
  have hx : x = 0 := (smul_eq_zero.mp h1).resolve_right hW
  rw [hx, zero_smul, zero_add] at hxy
  exact ⟨hx, (smul_eq_zero.mp hxy).resolve_right hW⟩

theorem adjM_vecMulVec : adjM h.bar (vecMulVec u (h.bar ∘ u)) = vecMulVec u (h.bar ∘ u) := by
  ext i j
  simp [adjM, vecMulVec_apply, h.bar_bar, mul_comm]

theorem exists_one_add_mem [CharP K 2] (huu : hform h.bar u u = 0) {b : K} (hb : h.bar b = b) :
    ∃ N : StatedSU n (2 ^ f) K,
      (N : GL (Fin n) K).val = 1 + b • vecMulVec u (h.bar ∘ u) := by
  refine exists_statedSU_eq (q := 2 ^ f) ?_ ?_
  · rw [← vecMulVec_smul, vecMulVec_eq (Fin 1), det_one_add_replicateCol_mul_replicateRow,
      smul_dotProduct, smul_eq_mul]
    have : (h.bar ∘ u) ⬝ᵥ u = hform h.bar u u := rfl
    rw [this, huu, mul_zero, add_zero]
  · have hmap : ((1 : Matrix (Fin n) (Fin n) K) + b • vecMulVec u (h.bar ∘ u)).map (· ^ 2 ^ f) =
        ((1 : Matrix (Fin n) (Fin n) K) + b • vecMulVec u (h.bar ∘ u)).map h.bar :=
      congrArg _ (funext fun x => (h.bar_apply x).symm)
    rw [hmap]
    change adjM h.bar (1 + b • vecMulVec u (h.bar ∘ u)) * _ = 1
    rw [adjM_add, adjM_one, adjM_smul, hb, adjM_vecMulVec, add_mul, one_mul, mul_add, mul_one,
      smul_mul_smul_comm, vecMulVec_mul_self h huu, smul_zero, add_zero, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]

end OneAdd

section Lift

variable [CharP K 2] {n : ℕ}

theorem commute_of_mk_eq (hn : 1 ≤ n) {z s : StatedSU n (2 ^ f) K} {k : ℕ} (hs : s ^ 2 ^ k = 1)
    (hzs : (QuotientGroup.mk (s * z) : StatedProj (StatedSU n (2 ^ f) K)) =
      QuotientGroup.mk (z * s)) : z * s = s * z := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hzs
  obtain ⟨c, hc⟩ := hzs
  have h1 : ((z : GL (Fin n) K) * s) = (s * z) * Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    calc ((z : GL (Fin n) K) * s) = ((z * s : StatedSU n (2 ^ f) K) : GL (Fin n) K) := rfl
      _ = (((s * z) * ((s * z)⁻¹ * (z * s)) : StatedSU n (2 ^ f) K) : GL (Fin n) K) := by
          rw [mul_inv_cancel_left]
      _ = ((s * z : StatedSU n (2 ^ f) K) : GL (Fin n) K) *
          (((s * z)⁻¹ * (z * s) : StatedSU n (2 ^ f) K) : GL (Fin n) K) := rfl
      _ = (s * z) * Matrix.GeneralLinearGroup.scalar (Fin n) c := by rw [hc]; rfl
  have h2 : (z : GL (Fin n) K) * s * (z : GL (Fin n) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) c * s := by
    rw [h1, ← Matrix.GeneralLinearGroup.scalar_commute c, ← mul_assoc, mul_inv_cancel_right]
  have h3 := congrArg (· ^ 2 ^ k) h2
  simp only [conj_pow] at h3
  have hs' : ((s : GL (Fin n) K)) ^ 2 ^ k = 1 := by
    rw [← Subgroup.coe_pow, hs, Subgroup.coe_one]
  rw [hs', mul_one, mul_inv_cancel, (Commute.mul_pow
    (Matrix.GeneralLinearGroup.scalar_commute c (s : GL (Fin n) K)) _), hs', mul_one,
    ← map_pow] at h3
  have h4 : (c : K) ^ 2 ^ k = 1 := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h3
    simp [Matrix.diagonal_pow] at this
    exact this.symm
  have h5 : (c : K) = 1 := by
    have h6 : ((c : K) - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h4, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h6)
  have hc1 : c = 1 := Units.ext h5
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, hc1, map_one, mul_one]

theorem exists_one_add_of_mk_commute [Finite K] {R : Matrix (Fin (2 * 1 + ε)) (HypIndex 1 ε) K}
    (hR : IsHypTransport h R) {S : Subgroup (StatedSU (2 * 1 + ε) (2 ^ f) K)}
    (hS : eichU h hR ≤ S) (hS2 : IsPGroup 2 S) {z : StatedSU (2 * 1 + ε) (2 ^ f) K}
    (hz : ∀ s ∈ S, (QuotientGroup.mk (s * z) : StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K)) =
      QuotientGroup.mk (z * s)) :
    ∃ b : K, h.bar b = b ∧ ∃ N : StatedSU (2 * 1 + ε) (2 ^ f) K,
      (N : GL (Fin (2 * 1 + ε)) K).val = 1 + b • vecMulVec (R *ᵥ Pi.single hE 1)
        (h.bar ∘ (R *ᵥ Pi.single hE 1)) ∧
      (QuotientGroup.mk N : StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K)) = QuotientGroup.mk z := by
  set u := R *ᵥ (Pi.single hE 1 : HypIndex 1 ε → K) with hu_def
  set W := vecMulVec u (h.bar ∘ u) with hW_def
  have huu : hform h.bar u u = 0 := transport_col_isotropic h hR
  have hu0 : u ≠ 0 := transport_col_ne_zero h hR
  have hW2 : W * W = 0 := vecMulVec_mul_self h huu
  have hW0 : W ≠ 0 := by
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hu0 (funext hc)
    intro h0
    have := congrFun (congrFun h0 j) j
    simp only [hW_def, vecMulVec_apply, Function.comp, Matrix.zero_apply, mul_eq_zero,
      map_eq_zero] at this
    rcases this with h1 | h1 <;> exact hj h1
  have hcomm : ∀ s ∈ S, z * s = s * z := fun s hs => by
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    exact commute_of_mk_eq (by omega) (k := k)
      (by simpa using congrArg Subtype.val hk) (hz s hs)
  obtain ⟨μ, β, hzμβ⟩ := eq_of_commute_eichU h hR
    (Z := ((z : GL (Fin (2 * 1 + ε)) K) : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K))
    fun g hg => by
      have := congrArg (fun x : StatedSU (2 * 1 + ε) (2 ^ f) K =>
        ((x : GL (Fin (2 * 1 + ε)) K) : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K))
        (hcomm g (hS hg))
      simpa only [Subgroup.coe_mul, Units.val_mul] using this
  set Zm := ((z : GL (Fin (2 * 1 + ε)) K) : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K)
    with hZm
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hzμβ
    have h1 : Zm * Zm = 0 := by rw [hzμβ, smul_mul_smul_comm, hW2, smul_zero]
    have h2 : Zm * Zm * (((z⁻¹ * z⁻¹ : StatedSU (2 * 1 + ε) (2 ^ f) K) : GL (Fin (2 * 1 + ε)) K) :
        Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) = 1 := by
      rw [hZm, ← Units.val_mul, ← Units.val_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
      simp
    rw [h1, Matrix.zero_mul] at h2
    have h3 := congrFun (congrFun h2 ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at h3
  have hu := adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply z.2
  rw [← hZm, hzμβ, adjM_add, adjM_smul, adjM_smul, adjM_one, adjM_vecMulVec] at hu
  have hlin : (h.bar μ * μ - 1) • (1 : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) +
      (h.bar μ * β + h.bar β * μ) • W = 0 := by
    have e : (h.bar μ • (1 : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) + h.bar β • W) *
        (μ • 1 + β • W) = (h.bar μ * μ) • 1 + (h.bar μ * β + h.bar β * μ) • W := by
      simp only [Matrix.add_mul, Matrix.mul_add, smul_mul_smul_comm, Matrix.one_mul,
        Matrix.mul_one, hW2, smul_zero, add_zero]
      module
    rw [e] at hu
    have h0 := sub_eq_zero.mpr hu
    rw [← h0]
    module
  obtain ⟨-, hlin2⟩ := eq_zero_of_smul_one_add_smul hW0 hW2 hlin
  have hσμ0 : h.bar μ ≠ 0 := (map_ne_zero _).mpr hμ0
  set b := β / μ with hb_def
  have hb : h.bar b = b := by
    rw [hb_def, map_div₀, div_eq_div_iff hσμ0 hμ0]
    have := eq_of_add_eq_zero_two hlin2
    linear_combination -this
  obtain ⟨N, hN⟩ := exists_one_add_mem h huu hb
  refine ⟨b, hb, N, hN, ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  refine ⟨Units.mk0 μ hμ0, ?_⟩
  rw [eq_comm, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, hN, Matrix.GeneralLinearGroup.coe_scalar]
  change Zm = _
  rw [hzμβ, Units.val_mk0, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.add_mul,
    Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hb_def,
    div_mul_cancel₀ _ hμ0]

end Lift

end CFSG.ComponentClassification.RankTwoClassical.URigid
