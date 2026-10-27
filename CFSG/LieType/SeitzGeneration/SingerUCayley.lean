module

public import CFSG.LieType.SeitzGeneration.OutdiagHeisGen

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Fin.NatCast

section Companion

variable {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem thmU_finRotate_eq_add_one (k : Fin p) : finRotate p k = k + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := NeZero.pos p; omega⟩
  exact finRotate_succ_apply k

theorem thmU_val_add_one (k : Fin p) :
    ((k + 1 : Fin p) : ℕ) = if (k : ℕ) + 1 = p then 0 else (k : ℕ) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := NeZero.pos p; omega⟩
  rw [Fin.val_add_one]
  by_cases hk : k = Fin.last m
  · have hkm : (k : ℕ) = m := by rw [hk, Fin.val_last]
    simp [hk, hkm]
  · have hkm : (k : ℕ) ≠ m := fun h => hk (Fin.ext (by rw [h, Fin.val_last]))
    have hlt : (k : ℕ) < m := lt_of_le_of_ne (Nat.lt_succ_iff.mp k.isLt) hkm
    simp [hk, hkm]

theorem thmU_add_one_eq_zero_iff (k : Fin p) : k + 1 = 0 ↔ (k : ℕ) = p - 1 := by
  have hv := thmU_val_add_one k
  have hz : ((0 : Fin p) : ℕ) = 0 := Fin.val_zero p
  have hk := k.isLt
  constructor
  · intro h
    have h2 : ((k + 1 : Fin p) : ℕ) = 0 := by rw [h, hz]
    rw [hv] at h2
    split_ifs at h2 with h3 <;> omega
  · intro h
    apply Fin.ext
    rw [hv, hz]
    split_ifs with h3
    · rfl
    · omega

theorem thmU_companionMat_apply (c : K) (i k : Fin p) :
    companionMat p c i k = if i = k + 1 then (if k + 1 = 0 then c else 1) else 0 := by
  have h1 := congrFun (companionMat_mulVec_single p c k) i
  rw [mulVec_single_one, col_apply, Pi.smul_apply, thmU_finRotate_eq_add_one,
    Pi.single_apply, smul_eq_mul] at h1
  rw [h1]
  have hw : (if (k : ℕ) = p - 1 then c else 1) = (if k + 1 = 0 then c else 1) := by
    simp only [thmU_add_one_eq_zero_iff]
  rw [hw]
  split_ifs <;> simp

theorem thmU_companionMat_mulVec (c : K) (w : Fin p → K) (k : Fin p) :
    (companionMat p c *ᵥ w) k = (if k = 0 then c else 1) * w (k - 1) := by
  simp only [mulVec, dotProduct, thmU_companionMat_apply]
  rw [Finset.sum_eq_single (k - 1)]
  · simp [sub_add_cancel]
  · intro l _ hl
    rw [if_neg, zero_mul]
    intro hk
    apply hl
    rw [hk, add_sub_cancel_right]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem thmU_val_sub_natCast (i : Fin p) {j : ℕ} (hj : j < p) :
    ((i - (j : Fin p) : Fin p) : ℕ) = if j ≤ (i : ℕ) then (i : ℕ) - j else (i : ℕ) + p - j := by
  have hj' : ((j : Fin p) : ℕ) = j := by rw [Fin.val_natCast, Nat.mod_eq_of_lt hj]
  have hi := i.isLt
  rw [Fin.val_sub, hj']
  split_ifs with h
  · rw [show p - j + (i : ℕ) = ((i : ℕ) - j) + p by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem thmU_wrap_step (c : K) (i k : Fin p) {j : ℕ} (hj : j < p)
    (h : k + 1 = i - (j : Fin p)) :
    (if j ≤ (i : ℕ) then (1 : K) else c) * (if k + 1 = 0 then c else 1) =
      if j + 1 ≤ (i : ℕ) then 1 else c := by
  have hv := congrArg Fin.val h
  rw [thmU_val_add_one, thmU_val_sub_natCast i hj] at hv
  have hi := i.isLt
  have hk := k.isLt
  simp only [thmU_add_one_eq_zero_iff]
  split_ifs at hv ⊢ <;> first | omega | simp

theorem thmU_companionMat_pow_apply (c : K) (j : ℕ) (hj : j ≤ p) (i k : Fin p) :
    (companionMat p c ^ j) i k =
      if k = i - (j : Fin p) then (if j ≤ (i : ℕ) then (1 : K) else c) else 0 := by
  induction j generalizing k with
  | zero =>
    rw [pow_zero, one_apply]
    simp only [Nat.cast_zero, sub_zero, zero_le, ite_true]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  | succ j ih =>
    have hj' : j ≤ p := by omega
    have hjp : j < p := by omega
    have hkey : (k = i - ((j + 1 : ℕ) : Fin p)) ↔ (k + 1 = i - (j : Fin p)) := by
      rw [Nat.cast_succ, ← sub_sub, eq_sub_iff_add_eq]
    rw [pow_succ, mul_apply, Finset.sum_eq_single (k + 1)]
    · rw [ih hj' (k + 1), thmU_companionMat_apply, if_pos rfl]
      by_cases h : k + 1 = i - (j : Fin p)
      · rw [if_pos h, if_pos (hkey.mpr h), thmU_wrap_step c i k hjp h]
      · rw [if_neg h, if_neg (fun h' => h (hkey.mp h')), zero_mul]
    · intro l _ hl
      rw [thmU_companionMat_apply, if_neg hl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem thmU_companionMat_pow_mulVec_single (c : K) {j : ℕ} (hj : j < p) :
    (companionMat p c ^ j) *ᵥ Pi.single 0 1 = Pi.single (j : Fin p) 1 := by
  funext i
  rw [mulVec_single_one, col_apply, thmU_companionMat_pow_apply c j hj.le i 0]
  have hiff : (0 = i - (j : Fin p)) ↔ (i = (j : Fin p)) := by
    constructor
    · intro h; exact (sub_eq_zero.mp h.symm)
    · intro h; rw [h, sub_self]
  by_cases h : i = (j : Fin p)
  · have hval : (i : ℕ) = j := by rw [h, Fin.val_natCast, Nat.mod_eq_of_lt hj]
    rw [if_pos (hiff.mpr h), if_pos (by omega), Pi.single_apply, if_pos h]
  · rw [Pi.single_apply, if_neg h]
    split_ifs <;> first | rfl | (exfalso; exact h (hiff.mp ‹_›))

theorem thmU_companionMat_mul_diagonal (c : K) (u : Fin p → K) :
    companionMat p c * diagonal u = diagonal (fun i => u (i - 1)) * companionMat p c := by
  ext i k
  rw [mul_diagonal, diagonal_mul, thmU_companionMat_apply]
  by_cases h : i = k + 1
  · subst h
    rw [if_pos rfl, add_sub_cancel_right]
    split_ifs <;> ring
  · rw [if_neg h]
    simp

theorem thmU_companionMat_inv_mul_diagonal (c : K) (hdet : IsUnit (companionMat p c).det)
    (v : Fin p → K) :
    (companionMat p c)⁻¹ * diagonal v = diagonal (fun i => v (i + 1)) * (companionMat p c)⁻¹ := by
  have h1 := thmU_companionMat_mul_diagonal c (fun i => v (i + 1))
  simp only [sub_add_cancel] at h1
  have hC : companionMat p c * (companionMat p c)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hC' : (companionMat p c)⁻¹ * companionMat p c = 1 := nonsing_inv_mul _ hdet
  calc (companionMat p c)⁻¹ * diagonal v
      = (companionMat p c)⁻¹ * (diagonal v * companionMat p c) * (companionMat p c)⁻¹ := by
        simp only [mul_assoc, hC, mul_one]
    _ = (companionMat p c)⁻¹ * (companionMat p c * diagonal (fun i => v (i + 1))) *
          (companionMat p c)⁻¹ := by rw [h1]
    _ = diagonal (fun i => v (i + 1)) * (companionMat p c)⁻¹ := by
        rw [← mul_assoc, hC', one_mul]

theorem thmU_commute_companion_entry (c : K) {g : Matrix (Fin p) (Fin p) K}
    (hg : g * companionMat p c = companionMat p c * g) (i j : Fin p) :
    g i j = if (j : ℕ) ≤ (i : ℕ) then (g *ᵥ Pi.single 0 1) (i - j)
      else c * (g *ᵥ Pi.single 0 1) (i - j) := by
  have hcomm : g * companionMat p c ^ (j : ℕ) = companionMat p c ^ (j : ℕ) * g :=
    (Commute.pow_right (show Commute g (companionMat p c) from hg) (j : ℕ)).eq
  have hpj : (companionMat p c ^ (j : ℕ)) *ᵥ Pi.single 0 1 = Pi.single j 1 := by
    rw [thmU_companionMat_pow_mulVec_single c j.isLt, Fin.cast_val_eq_self]
  have hcol : g *ᵥ Pi.single j 1 = (companionMat p c ^ (j : ℕ)) *ᵥ (g *ᵥ Pi.single 0 1) := by
    rw [← hpj, mulVec_mulVec, mulVec_mulVec, hcomm]
  have hgij : g i j = (g *ᵥ Pi.single j 1) i := by
    rw [mulVec_single_one, col_apply]
  rw [hgij, hcol, mulVec, dotProduct]
  simp only [thmU_companionMat_pow_apply c (j : ℕ) j.isLt.le, Fin.cast_val_eq_self, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> simp

theorem thmU_commute_companion_eq_of_col0 (c : K) {g g' : Matrix (Fin p) (Fin p) K}
    (hg : g * companionMat p c = companionMat p c * g)
    (hg' : g' * companionMat p c = companionMat p c * g')
    (h0 : ∀ i, g i 0 = g' i 0) : g = g' := by
  have hcol : g *ᵥ Pi.single 0 1 = g' *ᵥ Pi.single 0 1 := by
    funext i
    simp only [mulVec_single_one, col_apply]
    exact h0 i
  ext i j
  rw [thmU_commute_companion_entry c hg, thmU_commute_companion_entry c hg', hcol]

theorem thmU_pairing_apply (b : Matrix (Fin p) (Fin p) K) (s : Fin p → K) (m : Fin p) :
    ((b * diagonal s * b) *ᵥ Pi.single 0 1) m =
      ∑ j, b m j * (b *ᵥ Pi.single 0 1) j * s j := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec, dotProduct]
  simp only [mulVec_diagonal]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem thmU_val_sub_le_iff (m j : Fin p) :
    ((m - j : Fin p) : ℕ) ≤ (m : ℕ) ↔ (j : ℕ) ≤ (m : ℕ) := by
  have hj := j.isLt
  rcases le_or_gt (j : ℕ) (m : ℕ) with h | h
  · have hle : j ≤ m := Fin.le_def.mpr h
    rw [Fin.coe_sub_iff_le.mpr hle]
    omega
  · have hlt : m < j := Fin.lt_def.mpr h
    rw [Fin.coe_sub_iff_lt.mpr hlt]
    omega

theorem thmU_pairing_symm (c : K) {b : Matrix (Fin p) (Fin p) K}
    (hb : b * companionMat p c = companionMat p c * b) (m j : Fin p) :
    b m j * (b *ᵥ Pi.single 0 1) j = b m (m - j) * (b *ᵥ Pi.single 0 1) (m - j) := by
  rw [thmU_commute_companion_entry c hb m j, thmU_commute_companion_entry c hb m (m - j),
    sub_sub_cancel]
  have hiff := thmU_val_sub_le_iff m j
  by_cases h : (j : ℕ) ≤ (m : ℕ)
  · rw [if_pos h, if_pos (hiff.mpr h)]
    ring
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
    ring

end Companion

section NormClass

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem thmU_norm_one_facts (h : UnitaryFieldData ℓ f K) {x : K} (hx : h.bar x * x = 1) :
    x ≠ 0 ∧ x ^ (ℓ ^ f + 1) = 1 := by
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, mul_zero] at hx
    exact zero_ne_one hx
  · rw [UnitaryFieldData.bar_apply] at hx
    rw [pow_succ]
    exact hx

theorem thmU_norm_one_pow_mul_pow (h : UnitaryFieldData ℓ f K) {p : ℕ} [hp : Fact p.Prime]
    {c : K} (hcu : h.bar c * c = 1) (hc : ¬ ∃ μ : K, μ ^ p = c) {d : K} (hd : h.bar d * d = 1) :
    ∃ m : ℕ, m < p ∧ ∃ x : K, h.bar x * x = 1 ∧ d = c ^ m * x ^ p := by
  classical
  haveI : Finite K := h.finite
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  let G : Subgroup Kˣ := (powMonoidHom (ℓ ^ f + 1) : Kˣ →* Kˣ).ker
  have hG : ∀ x : K, (hx : h.bar x * x = 1) → Units.mk0 x (thmU_norm_one_facts h hx).1 ∈ G := by
    intro x hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, (thmU_norm_one_facts h hx).2, Units.val_one]
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hz ⟨_, hG c hcu⟩)
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp (hz ⟨_, hG d hd⟩)
  have ha' : (z : Kˣ) ^ a = Units.mk0 c (thmU_norm_one_facts h hcu).1 := by
    have := congrArg (fun u : G => (u : Kˣ)) ha
    simpa using this
  have he' : (z : Kˣ) ^ e = Units.mk0 d (thmU_norm_one_facts h hd).1 := by
    have := congrArg (fun u : G => (u : Kˣ)) he
    simpa using this
  have hnd : ¬ ((p : ℤ) ∣ a) := by
    rintro ⟨s, hs⟩
    apply hc
    refine ⟨((z : Kˣ) ^ s : Kˣ), ?_⟩
    have h1 : ((z : Kˣ) ^ s) ^ p = Units.mk0 c (thmU_norm_one_facts h hcu).1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, ← hs, ha']
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_mk0]
  have hZ : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hnd
  obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = ZMod.val ((e : ZMod p) * (a : ZMod p)⁻¹) := ⟨_, rfl⟩
  have hmv : ((m : ℕ) : ZMod p) = (e : ZMod p) * (a : ZMod p)⁻¹ := by
    rw [hm_def]
    exact ZMod.natCast_zmod_val _
  have hmlt : m < p := by
    rw [hm_def]
    exact ZMod.val_lt _
  have hdvd : (p : ℤ) ∣ e - a * (m : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hmv, sub_eq_zero, ← mul_assoc, mul_comm (a : ZMod p), mul_assoc, mul_inv_cancel₀ hZ,
      mul_one]
  obtain ⟨t, ht⟩ := hdvd
  have he2 : e = a * (m : ℤ) + (p : ℤ) * t := by linarith
  have hze : (z : Kˣ) ^ e = ((z : Kˣ) ^ a) ^ m * (((z ^ t : G) : Kˣ)) ^ p := by
    rw [he2, _root_.zpow_add, _root_.zpow_mul (z : Kˣ) a, zpow_natCast, mul_comm (p : ℤ) t,
      _root_.zpow_mul (z : Kˣ) t, zpow_natCast, Subgroup.coe_zpow]
  refine ⟨m, hmlt, ((z ^ t : G) : Kˣ), ?_, ?_⟩
  · have hu : ((z ^ t : G) : Kˣ) ^ (ℓ ^ f + 1) = 1 := by
      have := (z ^ t : G).2
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
      exact this
    rw [UnitaryFieldData.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
  · have key : Units.mk0 d (thmU_norm_one_facts h hd).1 =
        Units.mk0 c (thmU_norm_one_facts h hcu).1 ^ m * ((z ^ t : G) : Kˣ) ^ p := by
      rw [← he', hze, ha']
    have := congrArg Units.val key
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0,
      Units.val_mk0] at this
    exact this

theorem thmU_unitary_det_class (h : UnitaryFieldData ℓ f K) {p : ℕ} [hp : Fact p.Prime]
    (hodd : Odd p) {c : K} (hcu : h.bar c * c = 1) (hc : ¬ ∃ μ : K, μ ^ p = c)
    {b : Matrix (Fin p) (Fin p) K} (hb : (b.map h.bar)ᵀ * b = 1) :
    ∃ m : ℕ, m < p ∧ ∃ x : K, h.bar x * x = 1 ∧
      (x⁻¹ • ((companionMat p c ^ m)⁻¹ * b)).det = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hdet : h.bar b.det * b.det = 1 := by
    have h1 := congrArg Matrix.det hb
    have h2 : h.bar b.det = (b.map h.bar).det := RingHom.map_det h.bar b
    rw [det_mul, det_transpose, det_one, ← h2] at h1
    exact h1
  obtain ⟨m, hm, x, hx, hdx⟩ := thmU_norm_one_pow_mul_pow h hcu hc hdet
  refine ⟨m, hm, x, hx, ?_⟩
  have hx0 : x ≠ 0 := (thmU_norm_one_facts h hx).1
  have hc0 : c ≠ 0 := (thmU_norm_one_facts h hcu).1
  rw [det_smul, det_mul, det_nonsing_inv, det_pow, det_companionMat hodd, Fintype.card_fin,
    Ring.inverse_eq_inv', hdx]
  rw [inv_pow]
  field_simp

end NormClass

section UnitaryGL

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem thmU_gl_inv_unitary (h : UnitaryFieldData ℓ f K) {p : ℕ} (U : GL (Fin p) K)
    (hU : ((U : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (U : Matrix (Fin p) (Fin p) K) = 1) :
    (((U⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ *
      ((U⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = 1 := by
  have hinv : ((U⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      ((U : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ := by
    rw [GeneralLinearGroup.coe_inv]
    exact Matrix.inv_eq_left_inv hU
  have hstar : ((((U⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)).map h.bar)ᵀ =
      (U : Matrix (Fin p) (Fin p) K) := by
    rw [hinv]
    ext i j
    simp [Matrix.map_apply, UnitaryFieldData.bar_bar]
  rw [hstar, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem thmU_unitary_conj_gl (h : UnitaryFieldData ℓ f K) {p : ℕ} (U g : GL (Fin p) K)
    (hU : ((U : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (U : Matrix (Fin p) (Fin p) K) = 1)
    (hg : ((g : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (g : Matrix (Fin p) (Fin p) K) = 1) :
    (((U * g * U⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ *
      ((U * g * U⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = 1 := by
  have hV := thmU_gl_inv_unitary h U hU
  simp only [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((U : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ (U : Matrix (Fin p) (Fin p) K),
    hU, Matrix.one_mul,
    ← Matrix.mul_assoc ((g : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ (g : Matrix (Fin p) (Fin p) K),
    hg, Matrix.one_mul]
  exact hV

end UnitaryGL

section CompanionExtra

variable {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem thmU_companionMat_pow_p (c : K) :
    companionMat p c ^ p = c • (1 : Matrix (Fin p) (Fin p) K) := by
  ext i k
  have hi := i.isLt
  have hnot : ¬ (p ≤ (i : ℕ)) := by omega
  rw [thmU_companionMat_pow_apply c p le_rfl i k, Fin.natCast_self, sub_zero, if_neg hnot,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : k = i
  · subst h
    simp
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem thmU_companionMat_isUnit_det (hodd : Odd p) {c : K} (hc : c ≠ 0) :
    IsUnit (companionMat p c).det := by
  rw [det_companionMat hodd]
  exact isUnit_iff_ne_zero.mpr hc

theorem thmU_val_sub_one (hp1 : 1 < p) (j : Fin p) :
    ((j - 1 : Fin p) : ℕ) = if (j : ℕ) = 0 then p - 1 else (j : ℕ) - 1 := by
  have h1 : (1 : Fin p) = ((1 : ℕ) : Fin p) := Nat.cast_one.symm
  rw [h1, thmU_val_sub_natCast j hp1]
  have hj := j.isLt
  split_ifs with h2 h3 h3 <;> omega

end CompanionExtra
section Membership

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def thmU_gens (ℓ f : ℕ) (K : Type) [Field K] (p : ℕ) (c : K) : Set (GL (Fin p) K) :=
  {g | g ∈ unitarySU ℓ f K p ∧ ((∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) = diagonal t) ∨
    (g : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g)}

theorem thmU_conj_unitarySU (h : UnitaryFieldData ℓ f K) {p : ℕ} (P : GL (Fin p) K)
    (hPu : ((P : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (P : Matrix (Fin p) (Fin p) K) = 1)
    (g : GL (Fin p) K) (hg : g ∈ unitarySU ℓ f K p) :
    P * g * P⁻¹ ∈ unitarySU ℓ f K p := by
  have hPP : (P : Matrix (Fin p) (Fin p) K) * ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdetPP : (P : Matrix (Fin p) (Fin p) K).det *
      ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).det = 1 := by
    rw [← det_mul, hPP, det_one]
  rw [mem_unitarySU_iff h] at hg ⊢
  refine ⟨?_, thmU_unitary_conj_gl h P g hPu hg.2⟩
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hg.1, mul_one]
  exact hdetPP

theorem thmU_conj_diag_mem (h : UnitaryFieldData ℓ f K) {p : ℕ} (P : GL (Fin p) K)
    (hPu : ((P : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (P : Matrix (Fin p) (Fin p) K) = 1)
    (hPd : ∀ t : Fin p → K, ∃ t' : Fin p → K,
      (P : Matrix (Fin p) (Fin p) K) * diagonal t = diagonal t' * (P : Matrix (Fin p) (Fin p) K))
    (g : GL (Fin p) K) (hg : g ∈ unitarySU ℓ f K p)
    (hgd : ∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) = diagonal t) :
    P * g * P⁻¹ ∈ unitarySU ℓ f K p ∧
      ∃ t : Fin p → K, ((P * g * P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = diagonal t := by
  obtain ⟨t, ht⟩ := hgd
  refine ⟨thmU_conj_unitarySU h P hPu g hg, ?_⟩
  have hPP : (P : Matrix (Fin p) (Fin p) K) * ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨t', ht'⟩ := hPd t
  refine ⟨t', ?_⟩
  rw [Units.val_mul, Units.val_mul, ht, ht', mul_assoc, hPP, mul_one]

theorem thmU_pow_conj_diag_mem (h : UnitaryFieldData ℓ f K) {p : ℕ} (P : GL (Fin p) K)
    (hPu : ((P : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (P : Matrix (Fin p) (Fin p) K) = 1)
    (hPd : ∀ t : Fin p → K, ∃ t' : Fin p → K,
      (P : Matrix (Fin p) (Fin p) K) * diagonal t = diagonal t' * (P : Matrix (Fin p) (Fin p) K))
    (k : ℕ) (g : GL (Fin p) K) (hg : g ∈ unitarySU ℓ f K p)
    (hgd : ∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) = diagonal t) :
    P ^ k * g * (P ^ k)⁻¹ ∈ unitarySU ℓ f K p ∧
      ∃ t : Fin p → K, ((P ^ k * g * (P ^ k)⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
        diagonal t := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, inv_one, mul_one]
    exact ⟨hg, hgd⟩
  | succ k ih =>
    have e : P ^ (k + 1) * g * (P ^ (k + 1))⁻¹ = P * (P ^ k * g * (P ^ k)⁻¹) * P⁻¹ := by
      group
    rw [e]
    exact thmU_conj_diag_mem h P hPu hPd _ ih.1 ih.2

end Membership

section Membership2

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem thmU_mul_unitary_gl (h : UnitaryFieldData ℓ f K) {p : ℕ} (A B : GL (Fin p) K)
    (hA : ((A : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (A : Matrix (Fin p) (Fin p) K) = 1)
    (hB : ((B : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (B : Matrix (Fin p) (Fin p) K) = 1) :
    (((A * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ *
      ((A * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = 1 := by
  simp only [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((A : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ (A : Matrix (Fin p) (Fin p) K),
    hA, Matrix.one_mul, hB]

theorem thmU_pow_unitary_gl (h : UnitaryFieldData ℓ f K) {p : ℕ} (A : GL (Fin p) K)
    (hA : ((A : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (A : Matrix (Fin p) (Fin p) K) = 1)
    (k : ℕ) :
    (((A ^ k : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ *
      ((A ^ k : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact thmU_mul_unitary_gl h _ _ ih hA

theorem thmU_scalar_unitary_gl (h : UnitaryFieldData ℓ f K) {p : ℕ} (y : K)
    (hy : h.bar y * y = 1) :
    ((Matrix.scalar (Fin p) y).map h.bar)ᵀ * Matrix.scalar (Fin p) y = 1 := by
  rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  have hfun : (fun _ : Fin p => h.bar y * y) = fun _ : Fin p => (1 : K) := by
    funext i
    exact hy
  rw [hfun]
  exact Matrix.diagonal_one

end Membership2

section CompanionUnitary

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem thmU_companionMat_unitary (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] {c : K}
    (hc : h.bar c * c = 1) :
    ((companionMat p c).map h.bar)ᵀ * companionMat p c = 1 := by
  ext k l
  rw [mul_apply, one_apply, Finset.sum_eq_single (k + 1)]
  · rw [transpose_apply, map_apply, thmU_companionMat_apply, if_pos rfl, thmU_companionMat_apply]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl]
      split_ifs
      · exact hc
      · simp
    · rw [if_neg (fun h' => hkl (add_right_cancel h')), mul_zero, if_neg hkl]
  · intro i _ hi
    rw [transpose_apply, map_apply, thmU_companionMat_apply, if_neg hi, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem thmU_companion_gl_data (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    {c : K} (hcu : h.bar c * c = 1) (cG : GL (Fin p) K)
    (hcG : (cG : Matrix (Fin p) (Fin p) K) = companionMat p c) :
    ((cG : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (cG : Matrix (Fin p) (Fin p) K) = 1 ∧
    (∀ t : Fin p → K, ∃ t' : Fin p → K,
      (cG : Matrix (Fin p) (Fin p) K) * diagonal t = diagonal t' * (cG : Matrix (Fin p) (Fin p) K)) ∧
    (((cG⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ *
      ((cG⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = 1 ∧
    (∀ t : Fin p → K, ∃ t' : Fin p → K,
      ((cG⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * diagonal t =
        diagonal t' * ((cG⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) := by
  have hU : ((cG : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (cG : Matrix (Fin p) (Fin p) K) = 1 := by
    rw [hcG]
    exact thmU_companionMat_unitary h hcu
  have hdet : IsUnit (companionMat p c).det :=
    thmU_companionMat_isUnit_det hodd (thmU_norm_one_facts h hcu).1
  refine ⟨hU, fun t => ⟨fun i => t (i - 1), ?_⟩, thmU_gl_inv_unitary h cG hU,
    fun t => ⟨fun i => t (i + 1), ?_⟩⟩
  · rw [hcG]
    exact thmU_companionMat_mul_diagonal c t
  · rw [GeneralLinearGroup.coe_inv, hcG]
    exact thmU_companionMat_inv_mul_diagonal c hdet t

end CompanionUnitary

section Decomposition

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem thmU_decomp (h : UnitaryFieldData ℓ f K) {p : ℕ} [hp : Fact p.Prime] (hodd : Odd p)
    {c : K} (hcu : h.bar c * c = 1) (hc : ¬ ∃ μ : K, μ ^ p = c) (cG : GL (Fin p) K)
    (hcG : (cG : Matrix (Fin p) (Fin p) K) = companionMat p c) (b : GL (Fin p) K)
    (hb : ((b : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (b : Matrix (Fin p) (Fin p) K) = 1)
    (hbC : Commute cG b) :
    ∃ (m : ℕ) (σ b₁ : GL (Fin p) K), (∀ g : GL (Fin p) K, σ * g = g * σ) ∧
      b = σ * (cG ^ m * b₁) ∧ b₁ ∈ unitarySU ℓ f K p ∧ Commute cG b₁ := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨m, hm, x, hx, hdet⟩ := thmU_unitary_det_class h hodd hcu hc hb
  have hx0 : x ≠ 0 := (thmU_norm_one_facts h hx).1
  have hcG_u : ((cG : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (cG : Matrix (Fin p) (Fin p) K) = 1 := by
    rw [hcG]
    exact thmU_companionMat_unitary h hcu
  have hPu : (((cG ^ m : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ *
      ((cG ^ m : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = 1 :=
    thmU_pow_unitary_gl h cG hcG_u m
  have hQu := thmU_gl_inv_unitary h (cG ^ m) hPu
  have hσ'val : ((GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) = Matrix.scalar (Fin p) x⁻¹ := by
    rw [GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hσσ' : GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0) *
      GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hcen : ∀ g : GL (Fin p) K, GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0) * g =
      g * GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0) :=
    fun g => (commute_scalar (Units.mk0 x hx0) g).symm.eq
  have hσ'U : (((GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K).map h.bar)ᵀ *
      ((GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) = 1 := by
    rw [hσ'val]
    apply thmU_scalar_unitary_gl h
    have hx' : h.bar x⁻¹ * x⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, hx, inv_one]
    exact hx'
  have hb₁U : (((GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ * ((cG ^ m)⁻¹ * b) :
      GL (Fin p) K) : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ *
      ((GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ * ((cG ^ m)⁻¹ * b) :
        GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = 1 :=
    thmU_mul_unitary_gl h _ _ hσ'U (thmU_mul_unitary_gl h _ _ hQu hb)
  have hb₁val : ((GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ * ((cG ^ m)⁻¹ * b) :
      GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      x⁻¹ • ((companionMat p c ^ m)⁻¹ * (b : Matrix (Fin p) (Fin p) K)) := by
    rw [Units.val_mul, Units.val_mul, hσ'val, GeneralLinearGroup.coe_inv, Units.val_pow_eq_pow_val,
      hcG, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  refine ⟨m, GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0),
    GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ * ((cG ^ m)⁻¹ * b), hcen, ?_, ?_, ?_⟩
  · have hc' := (commute_scalar (Units.mk0 x hx0)⁻¹ (cG ^ m)).eq
    have hcm : GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ *
        (cG ^ m * ((cG ^ m)⁻¹ * b)) = cG ^ m * (GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ *
          ((cG ^ m)⁻¹ * b)) := by
      rw [← mul_assoc, ← hc', mul_assoc]
    calc b = GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0) *
          GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ * b := by rw [hσσ', one_mul]
      _ = GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0) *
          (GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ *
            (cG ^ m * ((cG ^ m)⁻¹ * b))) := by rw [mul_inv_cancel_left, mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0) *
          (cG ^ m * (GeneralLinearGroup.scalar (Fin p) (Units.mk0 x hx0)⁻¹ *
            ((cG ^ m)⁻¹ * b))) := by rw [hcm]
  · refine (mem_unitarySU_iff h).mpr ⟨?_, hb₁U⟩
    rw [hb₁val]
    exact hdet
  · exact (commute_scalar _ cG).mul_right (((Commute.refl cG).pow_right m).inv_right.mul_right hbC)

end Decomposition

section Main2

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem thmU_sq_conj_mem (h : UnitaryFieldData ℓ f K) {p : ℕ} [hp : Fact p.Prime] (hodd : Odd p)
    {c : K} (hcu : h.bar c * c = 1) (hc : ¬ ∃ μ : K, μ ^ p = c)
    (H : Subgroup (GL (Fin p) K))
    (hT : ∀ g ∈ unitarySU ℓ f K p,
      (∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) = diagonal t) → g ∈ H)
    (hL : ∀ g ∈ unitarySU ℓ f K p,
      (g : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g ∈ H)
    (cG : GL (Fin p) K) (hcG : (cG : Matrix (Fin p) (Fin p) K) = companionMat p c)
    (b : GL (Fin p) K)
    (hb : ((b : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (b : Matrix (Fin p) (Fin p) K) = 1)
    (hbC : (b : Matrix (Fin p) (Fin p) K) * companionMat p c =
      companionMat p c * (b : Matrix (Fin p) (Fin p) K))
    (s : GL (Fin p) K) (hs : s ∈ unitarySU ℓ f K p)
    (hsd : ∃ t : Fin p → K, (s : Matrix (Fin p) (Fin p) K) = diagonal t)
    (z : GL (Fin p) K) (hz : z ∈ unitarySU ℓ f K p)
    (hzd : ∃ t : Fin p → K, (z : Matrix (Fin p) (Fin p) K) = diagonal t) :
    (b * s * b)⁻¹ * z * (b * s * b) ∈ H ∧ (b * s * b) * z * (b * s * b)⁻¹ ∈ H := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨hU, hPd, hUi, hPdi⟩ := thmU_companion_gl_data h hodd hcu cG hcG
  have hbCG : Commute cG b := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hcG]
    exact hbC.symm
  obtain ⟨m, σ, b₁, hcen, hb_eq, hb₁U, hcb₁⟩ := thmU_decomp h hodd hcu hc cG hcG b hb hbCG
  have hb₁C : (b₁ : Matrix (Fin p) (Fin p) K) * companionMat p c =
      companionMat p c * (b₁ : Matrix (Fin p) (Fin p) K) := by
    rw [← hcG]
    exact (congrArg Units.val hcb₁.eq).symm
  have hb₁H : b₁ ∈ H := hL b₁ hb₁U hb₁C
  set P : GL (Fin p) K := cG ^ m with hP
  have hPb₁ : Commute P b₁ := hcb₁.pow_left m
  have hPsP : P⁻¹ * s * P ∈ H := by
    have hm := thmU_pow_conj_diag_mem h (cG⁻¹) hUi hPdi m s hs hsd
    rw [inv_pow, inv_inv] at hm
    exact hT _ hm.1 hm.2
  have hPsP' : P * s * P⁻¹ ∈ H := by
    have hm := thmU_pow_conj_diag_mem h cG hU hPd m s hs hsd
    exact hT _ hm.1 hm.2
  have hPP : P * P = cG ^ (m + m) := by rw [hP, ← pow_add]
  have hP2z : (P * P)⁻¹ * z * (P * P) ∈ H := by
    have hm := thmU_pow_conj_diag_mem h (cG⁻¹) hUi hPdi (m + m) z hz hzd
    rw [inv_pow, inv_inv] at hm
    rw [hPP]
    exact hT _ hm.1 hm.2
  have hP2z' : (P * P) * z * (P * P)⁻¹ ∈ H := by
    have hm := thmU_pow_conj_diag_mem h cG hU hPd (m + m) z hz hzd
    rw [hPP]
    exact hT _ hm.1 hm.2
  set h₀ : GL (Fin p) K := b₁ * (P⁻¹ * s * P) * b₁ with hh₀
  have hh₀H : h₀ ∈ H := H.mul_mem (H.mul_mem hb₁H hPsP) hb₁H
  have hcomm2 : (P * P) * b₁ = b₁ * (P * P) := (hPb₁.mul_left hPb₁).eq
  have hcomm2' : (P * P)⁻¹ * b₁ = b₁ * (P * P)⁻¹ := ((hPb₁.mul_left hPb₁).inv_left).eq
  have hZc : ∀ g : GL (Fin p) K, (σ * σ) * g = g * (σ * σ) := fun g => by
    rw [mul_assoc, hcen g, ← mul_assoc σ g σ, hcen g, mul_assoc]
  have hy : b * s * b = (σ * σ) * ((P * P) * h₀) := by
    have hb' : b = σ * (P * b₁) := by rw [hb_eq]
    have hcs : σ * (P * b₁ * s) = (P * b₁ * s) * σ := hcen _
    calc b * s * b = σ * (P * b₁ * s * σ) * (P * b₁) := by
          rw [hb']
          group
      _ = σ * (σ * (P * b₁ * s)) * (P * b₁) := by rw [hcs]
      _ = (σ * σ) * (P * b₁ * s * (P * b₁)) := by group
      _ = (σ * σ) * ((P * P) * h₀) := by
          rw [hh₀]
          congr 1
          have e : (P * P) * (b₁ * (P⁻¹ * s * P) * b₁) = P * b₁ * s * (P * b₁) := by
            calc (P * P) * (b₁ * (P⁻¹ * s * P) * b₁) = P * (P * b₁) * (P⁻¹ * s * P) * b₁ := by
                  group
              _ = P * (b₁ * P) * (P⁻¹ * s * P) * b₁ := by rw [hPb₁.eq]
              _ = P * b₁ * s * (P * b₁) := by group
          exact e.symm
  set Z : GL (Fin p) K := σ * σ with hZdef
  have hZg : ∀ g : GL (Fin p) K, Z⁻¹ * g * Z = g := fun g => by
    rw [mul_assoc, ← hZc g, ← mul_assoc, inv_mul_cancel, one_mul]
  have hZg' : ∀ g : GL (Fin p) K, Z * g * Z⁻¹ = g := fun g => by
    rw [hZc g, mul_assoc, mul_inv_cancel, mul_one]
  have hconj1 : ∀ (y g : GL (Fin p) K), (Z * y)⁻¹ * g * (Z * y) = y⁻¹ * g * y := fun y g => by
    calc (Z * y)⁻¹ * g * (Z * y) = y⁻¹ * (Z⁻¹ * g * Z) * y := by group
      _ = y⁻¹ * g * y := by rw [hZg]
  have hconj2 : ∀ (y g : GL (Fin p) K), (Z * y) * g * (Z * y)⁻¹ = y * g * y⁻¹ := fun y g => by
    calc (Z * y) * g * (Z * y)⁻¹ = Z * (y * g * y⁻¹) * Z⁻¹ := by group
      _ = y * g * y⁻¹ := hZg' _
  have hh₁ : (P * P) * h₀ * (P * P)⁻¹ = b₁ * (P * s * P⁻¹) * b₁ := by
    have hcomm2 : (P * P) * b₁ = b₁ * (P * P) := (hPb₁.mul_left hPb₁).eq
    have hcomm2' : (P * P)⁻¹ * b₁ = b₁ * (P * P)⁻¹ := ((hPb₁.mul_left hPb₁).inv_left).eq
    rw [hh₀]
    calc (P * P) * (b₁ * (P⁻¹ * s * P) * b₁) * (P * P)⁻¹
        = ((P * P) * b₁) * ((P⁻¹ * s * P) * b₁ * (P * P)⁻¹) := by group
      _ = (b₁ * (P * P)) * ((P⁻¹ * s * P) * b₁ * (P * P)⁻¹) := by rw [hcomm2]
      _ = b₁ * (P * s * P) * (b₁ * (P * P)⁻¹) := by group
      _ = b₁ * (P * s * P) * ((P * P)⁻¹ * b₁) := by rw [hcomm2']
      _ = b₁ * (P * s * P * (P * P)⁻¹) * b₁ := by group
      _ = b₁ * (P * s * P⁻¹) * b₁ := by group
  have hh₁H : (P * P) * h₀ * (P * P)⁻¹ ∈ H := by
    rw [hh₁]
    exact H.mul_mem (H.mul_mem hb₁H hPsP') hb₁H
  have hy1 : (b * s * b)⁻¹ * z * (b * s * b) = h₀⁻¹ * ((P * P)⁻¹ * z * (P * P)) * h₀ := by
    rw [hy, hconj1]
    group
  have hy2 : (b * s * b) * z * (b * s * b)⁻¹ = ((P * P) * h₀ * (P * P)⁻¹) *
      ((P * P) * z * (P * P)⁻¹) * ((P * P) * h₀ * (P * P)⁻¹)⁻¹ := by
    rw [hy, hconj2]
    group
  rw [hy1, hy2]
  exact ⟨H.mul_mem (H.mul_mem (H.inv_mem hh₀H) hP2z) hh₀H,
    H.mul_mem (H.mul_mem hh₁H hP2z') (H.inv_mem hh₁H)⟩

end Main2

section Closure

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem thmU_gens_conj_mem (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p) {c : K}
    (hcu : h.bar c * c = 1) (cG : GL (Fin p) K)
    (hcG : (cG : Matrix (Fin p) (Fin p) K) = companionMat p c)
    (x : GL (Fin p) K) (hx : x ∈ thmU_gens ℓ f K p c) : cG * x * cG⁻¹ ∈ thmU_gens ℓ f K p c := by
  simp only [thmU_gens, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨hxU, hxd⟩ := hx
  obtain ⟨hU, hPd, -, -⟩ := thmU_companion_gl_data h hodd hcu cG hcG
  rcases hxd with hdiag | hcomm
  · obtain ⟨hmem, hdiag'⟩ := thmU_conj_diag_mem h cG hU hPd x hxU hdiag
    exact ⟨hmem, Or.inl hdiag'⟩
  · have hcomm' : cG * x = x * cG := by
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, hcG]
      exact hcomm.symm
    have hfix : cG * x * cG⁻¹ = x := by
      rw [hcomm', mul_assoc, mul_inv_cancel, mul_one]
    rw [hfix]
    exact ⟨hxU, Or.inr hcomm⟩

theorem thmU_closure_conj_stable (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    {c : K} (hcu : h.bar c * c = 1) (cG : GL (Fin p) K)
    (hcG : (cG : Matrix (Fin p) (Fin p) K) = companionMat p c) :
    ∀ g ∈ Subgroup.closure (thmU_gens ℓ f K p c),
      cG * g * cG⁻¹ ∈ Subgroup.closure (thmU_gens ℓ f K p c) := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (thmU_gens_conj_mem h hodd hcu cG hcG x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show cG * (x * y) * cG⁻¹ = (cG * x * cG⁻¹) * (cG * y * cG⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show cG * x⁻¹ * cG⁻¹ = (cG * x * cG⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

end Closure

section CayleyMain

variable {ℓ f : ℕ} {K : Type} [Field K]

noncomputable def thmU_cayleyQ (p : ℕ) (c d : K) : Matrix (Fin p) (Fin p) K :=
  ∑ i ∈ Finset.range p, ((-d) ^ (p - 1 - i)) • (companionMat p c) ^ i

noncomputable def thmU_cayleyMat (h : UnitaryFieldData ℓ f K) (p : ℕ) (c ε : K) :
    Matrix (Fin p) (Fin p) K :=
  (1 + ε • companionMat p c) * (1 + h.bar ε • (companionMat p c)⁻¹)⁻¹

variable {p : ℕ} [NeZero p]

theorem thmU_cayleyQ_mul_add (hodd : Odd p) (c d : K) :
    thmU_cayleyQ p c d * (companionMat p c + d • (1 : Matrix (Fin p) (Fin p) K)) =
      (c + d ^ p) • (1 : Matrix (Fin p) (Fin p) K) := by
  have hcomm : Commute (companionMat p c) ((-d) • (1 : Matrix (Fin p) (Fin p) K)) :=
    (Commute.one_right _).smul_right _
  have key := hcomm.geom_sum₂_mul p
  have e1 : ∑ i ∈ Finset.range p, companionMat p c ^ i * ((-d) • (1 : Matrix (Fin p) (Fin p) K)) ^
      (p - 1 - i) = thmU_cayleyQ p c d := by
    unfold thmU_cayleyQ
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, one_pow, Matrix.mul_smul, Matrix.mul_one]
  have e2 : companionMat p c - (-d) • (1 : Matrix (Fin p) (Fin p) K) =
      companionMat p c + d • (1 : Matrix (Fin p) (Fin p) K) := by
    rw [neg_smul, sub_neg_eq_add]
  have e3 : companionMat p c ^ p - ((-d) • (1 : Matrix (Fin p) (Fin p) K)) ^ p =
      (c + d ^ p) • (1 : Matrix (Fin p) (Fin p) K) := by
    rw [thmU_companionMat_pow_p, smul_pow, one_pow, Odd.neg_pow hodd]
    module
  rw [e1, e2, e3] at key
  exact key

theorem thmU_cayleyQ_commute (c d : K) :
    Commute (thmU_cayleyQ p c d) (companionMat p c) := by
  unfold thmU_cayleyQ
  exact Commute.sum_left _ _ _ fun i _ => (Commute.pow_left (Commute.refl (companionMat p c)) i).smul_left _

end CayleyMain

section CayleyAlgebra

variable {ℓ f : ℕ} {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem thmU_cayley_eq (h : UnitaryFieldData ℓ f K) (ε : K) (hodd : Odd p) {c : K} (hc : c ≠ 0)
    (hE : c + h.bar ε ^ p ≠ 0) :
    thmU_cayleyMat h p c ε = (c + h.bar ε ^ p)⁻¹ •
      ((1 + ε • companionMat p c) * (thmU_cayleyQ p c (h.bar ε) * companionMat p c)) := by
  have hdetC := thmU_companionMat_isUnit_det hodd hc
  have hY : (1 + h.bar ε • (companionMat p c)⁻¹) =
      (companionMat p c)⁻¹ * (companionMat p c + h.bar ε • 1) := by
    rw [Matrix.mul_add, nonsing_inv_mul _ hdetC, Matrix.mul_smul, Matrix.mul_one]
  have hMinv : (companionMat p c + h.bar ε • 1)⁻¹ =
      (c + h.bar ε ^ p)⁻¹ • thmU_cayleyQ p c (h.bar ε) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, thmU_cayleyQ_mul_add hodd c (h.bar ε), smul_smul, inv_mul_cancel₀ hE,
      one_smul]
  unfold thmU_cayleyMat
  rw [hY, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hdetC, hMinv, Matrix.smul_mul,
    Matrix.mul_smul]

theorem thmU_cayleyQ_mul_add' (hodd : Odd p) (c d : K) :
    (companionMat p c + d • (1 : Matrix (Fin p) (Fin p) K)) * thmU_cayleyQ p c d =
      (c + d ^ p) • (1 : Matrix (Fin p) (Fin p) K) := by
  have hcomm : Commute (companionMat p c + d • (1 : Matrix (Fin p) (Fin p) K))
      (thmU_cayleyQ p c d) :=
    Commute.add_left (thmU_cayleyQ_commute c d).symm (Commute.smul_left (Commute.one_left _) d)
  rw [hcomm.eq, thmU_cayleyQ_mul_add hodd c d]

theorem thmU_cayley_star_rel (h : UnitaryFieldData ℓ f K) (ε : K) (hodd : Odd p) {c : K}
    (hc : c ≠ 0) (hE : c + h.bar ε ^ p ≠ 0) :
    (companionMat p c + h.bar ε • (1 : Matrix (Fin p) (Fin p) K)) *
      thmU_cayleyMat h p c ε = companionMat p c + ε • companionMat p c ^ 2 := by
  rw [thmU_cayley_eq h ε hodd hc hE]
  have hMC : Commute (companionMat p c + h.bar ε • (1 : Matrix (Fin p) (Fin p) K))
      (companionMat p c) :=
    Commute.add_left (Commute.refl _) ((Commute.one_left _).smul_left _)
  have hMX : Commute (companionMat p c + h.bar ε • (1 : Matrix (Fin p) (Fin p) K))
      (1 + ε • companionMat p c) :=
    Commute.add_right (Commute.one_right _) (hMC.smul_right ε)
  have hMQ := thmU_cayleyQ_mul_add' hodd c (h.bar ε)
  have key : (companionMat p c + h.bar ε • (1 : Matrix (Fin p) (Fin p) K)) *
      ((1 + ε • companionMat p c) * (thmU_cayleyQ p c (h.bar ε) * companionMat p c)) =
      (1 + ε • companionMat p c) * ((companionMat p c + h.bar ε • (1 : Matrix (Fin p) (Fin p) K)) *
        thmU_cayleyQ p c (h.bar ε) * companionMat p c) := by
    rw [← Matrix.mul_assoc _ (1 + ε • companionMat p c) _, hMX.eq]
    simp only [Matrix.mul_assoc]
  rw [Matrix.mul_smul, key, hMQ, Matrix.smul_mul, one_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hE, one_smul, Matrix.add_mul, one_mul, Matrix.smul_mul, sq]

theorem thmU_cayley_commute (h : UnitaryFieldData ℓ f K) (ε : K) (hodd : Odd p) {c : K}
    (hc : c ≠ 0) (hE : c + h.bar ε ^ p ≠ 0) :
    Commute (companionMat p c) (thmU_cayleyMat h p c ε) := by
  rw [thmU_cayley_eq h ε hodd hc hE]
  refine Commute.smul_right ?_ _
  have hCX : Commute (companionMat p c) (1 + ε • companionMat p c) :=
    Commute.add_right (Commute.one_right _) ((Commute.refl _).smul_right ε)
  have hCQ : Commute (companionMat p c) (thmU_cayleyQ p c (h.bar ε)) :=
    (thmU_cayleyQ_commute c (h.bar ε)).symm
  exact hCX.mul_right (hCQ.mul_right (Commute.refl _))

end CayleyAlgebra

section CayleyUnitary

variable {ℓ f : ℕ} {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem thmU_add_pow_ne (h : UnitaryFieldData ℓ f K) {c : K} (hodd : Odd p)
    (hc : ¬ ∃ μ : K, μ ^ p = c) (ε : K) : c + h.bar ε ^ p ≠ 0 := by
  intro h0
  apply hc
  refine ⟨-h.bar ε, ?_⟩
  rw [Odd.neg_pow hodd]
  linear_combination -h0

end CayleyUnitary

section CayleyCoord

variable {ℓ f : ℕ} {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem thmU_cayley_unitary (h : UnitaryFieldData ℓ f K) (ε : K) (hodd : Odd p) {c : K}
    (hcu : h.bar c * c = 1) (hc : c ≠ 0) (hE : c + h.bar ε ^ p ≠ 0) :
    ((thmU_cayleyMat h p c ε).map h.bar)ᵀ * thmU_cayleyMat h p c ε = 1 := by
  have hdetC := thmU_companionMat_isUnit_det hodd hc
  have hCu := thmU_companionMat_unitary (p := p) h hcu
  have hstarC : ((companionMat p c).map h.bar)ᵀ = (companionMat p c)⁻¹ :=
    (Matrix.inv_eq_left_inv hCu).symm
  have hstarCinv : (((companionMat p c)⁻¹).map h.bar)ᵀ = companionMat p c := by
    have h1 : (((companionMat p c)⁻¹).map h.bar)ᵀ * ((companionMat p c).map h.bar)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul, mul_nonsing_inv _ hdetC,
        Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]
    rw [hstarC] at h1
    have h2 := Matrix.inv_eq_left_inv h1
    rw [nonsing_inv_nonsing_inv _ hdetC] at h2
    exact h2.symm
  have hstarX : ((1 + ε • companionMat p c).map h.bar)ᵀ =
      1 + h.bar ε • (companionMat p c)⁻¹ := by
    rw [← hstarC]
    ext i j
    by_cases hij : j = i
    · subst hij
      simp [apply_ite h.bar, Matrix.map_apply, Matrix.transpose_apply, Matrix.one_apply]
    · simp [apply_ite h.bar, Matrix.map_apply, Matrix.transpose_apply, Matrix.one_apply, hij,
        Ne.symm hij]
  have hstarY : ((1 + h.bar ε • (companionMat p c)⁻¹).map h.bar)ᵀ =
      1 + ε • companionMat p c := by
    conv_rhs => rw [← hstarCinv]
    ext i j
    by_cases hij : j = i
    · subst hij
      simp [apply_ite h.bar, Matrix.map_apply, Matrix.transpose_apply, Matrix.one_apply,
        UnitaryFieldData.bar_bar]
    · simp [apply_ite h.bar, Matrix.map_apply, Matrix.transpose_apply, Matrix.one_apply, hij,
        Ne.symm hij, UnitaryFieldData.bar_bar]
  have hMQ := thmU_cayleyQ_mul_add' hodd c (h.bar ε)
  have hMu : IsUnit (companionMat p c + h.bar ε • (1 : Matrix (Fin p) (Fin p) K)) := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr
      (Matrix.isUnit_det_of_right_inverse (B := (c + h.bar ε ^ p)⁻¹ •
        thmU_cayleyQ p c (h.bar ε)) ?_)
    rw [Matrix.mul_smul, hMQ, smul_smul, inv_mul_cancel₀ hE, one_smul]
  have hY : (1 + h.bar ε • (companionMat p c)⁻¹) =
      (companionMat p c)⁻¹ * (companionMat p c + h.bar ε • 1) := by
    rw [Matrix.mul_add, nonsing_inv_mul _ hdetC, Matrix.mul_smul, Matrix.mul_one]
  have hCiU : IsUnit (companionMat p c)⁻¹ :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ hdetC)
  have hYU : IsUnit (1 + h.bar ε • (companionMat p c)⁻¹) := by
    rw [hY]
    exact hCiU.mul hMu
  have hYY : (1 + h.bar ε • (companionMat p c)⁻¹) * (1 + h.bar ε • (companionMat p c)⁻¹)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hYU)
  have hXY : Commute (1 + ε • companionMat p c) (1 + h.bar ε • (companionMat p c)⁻¹) := by
    have hCCi : Commute (companionMat p c) (companionMat p c)⁻¹ := by
      unfold Commute SemiconjBy
      rw [mul_nonsing_inv _ hdetC, nonsing_inv_mul _ hdetC]
    have hCY : Commute (companionMat p c) (1 + h.bar ε • (companionMat p c)⁻¹) :=
      Commute.add_right (Commute.one_right _) (hCCi.smul_right _)
    exact Commute.add_left (Commute.one_left _) (hCY.smul_left ε)
  have e1 : ((1 + h.bar ε • (companionMat p c)⁻¹)⁻¹.map h.bar)ᵀ *
      ((1 + h.bar ε • (companionMat p c)⁻¹).map h.bar)ᵀ = 1 := by
    rw [← transpose_mul, ← Matrix.map_mul, hYY, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      transpose_one]
  rw [hstarY] at e1
  unfold thmU_cayleyMat
  rw [Matrix.map_mul, transpose_mul, hstarX]
  calc ((1 + h.bar ε • (companionMat p c)⁻¹)⁻¹.map h.bar)ᵀ * (1 + h.bar ε • (companionMat p c)⁻¹) *
        ((1 + ε • companionMat p c) * (1 + h.bar ε • (companionMat p c)⁻¹)⁻¹)
      = ((1 + h.bar ε • (companionMat p c)⁻¹)⁻¹.map h.bar)ᵀ *
          ((1 + h.bar ε • (companionMat p c)⁻¹) * (1 + ε • companionMat p c)) *
          (1 + h.bar ε • (companionMat p c)⁻¹)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = ((1 + h.bar ε • (companionMat p c)⁻¹)⁻¹.map h.bar)ᵀ *
          ((1 + ε • companionMat p c) * (1 + h.bar ε • (companionMat p c)⁻¹)) *
          (1 + h.bar ε • (companionMat p c)⁻¹)⁻¹ := by rw [hXY.eq]
    _ = (((1 + h.bar ε • (companionMat p c)⁻¹)⁻¹.map h.bar)ᵀ * (1 + ε • companionMat p c)) *
          ((1 + h.bar ε • (companionMat p c)⁻¹) * (1 + h.bar ε • (companionMat p c)⁻¹)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e1, hYY, Matrix.one_mul]

end CayleyCoord

section CayleyColumn

variable {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem thmU_cayleyQ_mulVec_zero (c d : K) (j : Fin p) :
    (thmU_cayleyQ p c d *ᵥ Pi.single 0 1) j = (-d) ^ (p - 1 - (j : ℕ)) := by
  rw [mulVec_single_one, col_apply]
  unfold thmU_cayleyQ
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hj := j.isLt
  rw [Finset.sum_eq_single (j : ℕ)]
  · rw [thmU_companionMat_pow_apply c (j : ℕ) (by omega) j 0, Fin.cast_val_eq_self, sub_self,
      if_pos rfl, if_pos (le_refl _), mul_one]
  · intro i hi hne
    have hi' : i < p := Finset.mem_range.mp hi
    rw [thmU_companionMat_pow_apply c i hi'.le j 0, if_neg, mul_zero]
    intro h0
    apply hne
    have h1 := congrArg Fin.val (sub_eq_zero.mp h0.symm)
    rw [Fin.val_natCast, Nat.mod_eq_of_lt hi'] at h1
    exact h1.symm
  · intro h'
    exact absurd (Finset.mem_range.mpr hj) h'

theorem thmU_cayley_mulVec_apply (ε c d : K) (j : Fin p) :
    (((1 + ε • companionMat p c) * thmU_cayleyQ p c d) *ᵥ Pi.single 0 1) j =
      (-d) ^ (p - 1 - (j : ℕ)) +
        ε * ((if j = 0 then c else 1) * (-d) ^ (p - 1 - ((j - 1 : Fin p) : ℕ))) := by
  rw [← mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, thmU_companionMat_mulVec,
    thmU_cayleyQ_mulVec_zero, thmU_cayleyQ_mulVec_zero]

end CayleyColumn

section CayleyFormula

variable {ℓ f : ℕ} {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem thmU_cayleyMat_apply_zero (h : UnitaryFieldData ℓ f K) (hodd : Odd p) (hp3 : 3 ≤ p)
    {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0) (k : Fin p) :
    thmU_cayleyMat h p c ε k 0 =
      if (k : ℕ) = 0 then c * (1 - h.bar ε * ε) / (h.bar ε ^ p + c)
      else if (k : ℕ) = 1 then (h.bar ε ^ (p - 1) + c * ε) / (h.bar ε ^ p + c)
      else (-1) ^ ((k : ℕ) - 1) * h.bar ε ^ (p - (k : ℕ)) * (1 - h.bar ε * ε) / (h.bar ε ^ p + c) := by
  have hp1 : 1 < p := by omega
  have hE' : c + h.bar ε ^ p ≠ 0 := by rw [add_comm]; exact hE
  have hCX : Commute (companionMat p c) (1 + ε • companionMat p c) :=
    Commute.add_right (Commute.one_right _) ((Commute.refl _).smul_right ε)
  have hCQ : Commute (companionMat p c) (thmU_cayleyQ p c (h.bar ε)) :=
    (thmU_cayleyQ_commute c (h.bar ε)).symm
  have hsw : (1 + ε • companionMat p c) * (thmU_cayleyQ p c (h.bar ε) * companionMat p c) =
      companionMat p c * ((1 + ε • companionMat p c) * thmU_cayleyQ p c (h.bar ε)) := by
    rw [(thmU_cayleyQ_commute c (h.bar ε)).eq, ← Matrix.mul_assoc, ← hCX.eq, Matrix.mul_assoc]
  have hcol : ∀ (A : Matrix (Fin p) (Fin p) K) (i : Fin p), A i 0 = (A *ᵥ Pi.single 0 1) i := by
    intro A i
    rw [mulVec_single_one, col_apply]
  rw [thmU_cayley_eq h ε hodd hc hE', hsw, Matrix.smul_apply, smul_eq_mul,
    hcol (companionMat p c * ((1 + ε • companionMat p c) * thmU_cayleyQ p c (h.bar ε))) k,
    ← mulVec_mulVec, thmU_companionMat_mulVec, thmU_cayley_mulVec_apply]
  obtain ⟨r, hr⟩ := hodd
  have hevenp : Even (p - 1) := ⟨r, by omega⟩
  have hkv := k.isLt
  by_cases h0 : (k : ℕ) = 0
  · have hkF : k = 0 := Fin.ext (by rw [h0, Fin.val_zero])
    have e1 : ((k - 1 : Fin p) : ℕ) = p - 1 := by
      rw [thmU_val_sub_one hp1, if_pos h0]
    have e2 : (((k - 1) - 1 : Fin p) : ℕ) = p - 1 - 1 := by
      rw [thmU_val_sub_one hp1, e1, if_neg (by omega)]
    have hkne1 : (k - 1 : Fin p) ≠ 0 := fun h' => by
      have := congrArg Fin.val h'
      rw [e1, Fin.val_zero] at this
      omega
    rw [if_pos hkF, if_neg hkne1, e1, e2, if_pos h0, show p - 1 - (p - 1) = 0 by omega,
      show p - 1 - (p - 1 - 1) = 1 by omega, pow_zero, pow_one, add_comm (h.bar ε ^ p) c]
    ring
  · by_cases h1 : (k : ℕ) = 1
    · have hk0' : (k : ℕ) ≠ 0 := by omega
      have hkne0 : k ≠ 0 := fun h' => hk0' (by rw [h', Fin.val_zero])
      have e1 : ((k - 1 : Fin p) : ℕ) = 0 := by
        rw [thmU_val_sub_one hp1, if_neg hk0', h1]
      have e2 : (((k - 1) - 1 : Fin p) : ℕ) = p - 1 := by
        rw [thmU_val_sub_one hp1, e1, if_pos rfl]
      have hk1F : k - 1 = 0 := Fin.ext (by rw [e1, Fin.val_zero])
      rw [if_neg hkne0, if_pos hk1F, e1, e2, if_neg h0, if_pos h1, Nat.sub_zero,
        Nat.sub_self, pow_zero, mul_one, one_mul, hevenp.neg_pow, add_comm (h.bar ε ^ p) c]
      ring
    · have hkne0 : k ≠ 0 := fun h' => h0 (by rw [h', Fin.val_zero])
      have e1 : ((k - 1 : Fin p) : ℕ) = (k : ℕ) - 1 := by
        rw [thmU_val_sub_one hp1, if_neg h0]
      have hk1ne : (k - 1 : Fin p) ≠ 0 := fun h' => by
        have := congrArg Fin.val h'
        rw [e1, Fin.val_zero] at this
        omega
      have e2 : (((k - 1) - 1 : Fin p) : ℕ) = (k : ℕ) - 2 := by
        rw [thmU_val_sub_one hp1, e1, if_neg (by omega), show (k : ℕ) - 1 - 1 = (k : ℕ) - 2 by omega]
      rw [if_neg hkne0, if_neg hk1ne, e1, e2, if_neg h0, if_neg h1]
      have hk2 : 2 ≤ (k : ℕ) := by omega
      have hexp1 : p - 1 - ((k : ℕ) - 1) = p - (k : ℕ) := by omega
      have hexp2 : p - 1 - ((k : ℕ) - 2) = (p - (k : ℕ)) + 1 := by omega
      have hsgn : (-1 : K) ^ (p - (k : ℕ)) = (-1 : K) ^ ((k : ℕ) - 1) := by
        rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := (k : ℕ) - 1)]
        congr 1
        omega
      rw [hexp1, hexp2, pow_succ, neg_pow (h.bar ε) (p - (k : ℕ)), hsgn, add_comm (h.bar ε ^ p) c]
      ring

end CayleyFormula

end CFSG.LieType.SeitzGeneration

end
