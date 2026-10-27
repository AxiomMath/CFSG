module

public import CFSG.LargeExtraspecial.DWInsData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses

public noncomputable section

namespace CFSG.LargeExtraspecial.DW.Insp

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem eWords_letters : eWords.all (lettersOK 17) = true := by decide

theorem bwWords_letters : (bwEntries.map fun e => e.2.2.1).all (lettersOK 17) = true := by
  decide

theorem invWords_letters : ((invData.map fun d => d.1) ++ invData.map fun d => d.2.1).all
    (lettersOK 17) = true := by
  decide

theorem rep_powArr {t : Array ℕ} {g : Equiv.Perm (Fin 360)} (h : Rep 360 t g) :
    ∀ k, Rep 360 (powArr t k) (g ^ k)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [pow_succ']
    exact rep_compA h (rep_powArr h k)

@[expose] def omegaPerm (w : List ℤ) : Equiv.Perm (Fin 360) := permOfArr 360 (omegaW w)

@[expose] def aPerm (i : ℕ) : Equiv.Perm (Fin 360) := permOfArr 360 (aArr i)

@[expose] def termPerm (t : List ℕ) : Equiv.Perm (Fin 360) := (t.map aPerm).prod

theorem aPerm_spec (i : ℕ) :
    Rep 360 (aArr i) (aPerm i) ∧ aPerm i ∈ omegaT :=
  omegaW_spec (letters_of_all eWords_letters i)

theorem termArr_nil : termArr [] = idA 360 := by
  simp only [termArr, List.foldr_nil]

theorem termArr_cons (i : ℕ) (t : List ℕ) : termArr (i :: t) = compA 360 (aArr i) (termArr t) := by
  simp only [termArr, List.foldr_cons]

theorem termPerm_nil : termPerm [] = 1 := by
  rw [termPerm, List.map_nil, List.prod_nil]

theorem termPerm_cons (i : ℕ) (t : List ℕ) : termPerm (i :: t) = aPerm i * termPerm t := by
  rw [termPerm, List.map_cons, List.prod_cons, termPerm]

theorem rep_termArr :
    ∀ t : List ℕ, Rep 360 (termArr t) (termPerm t)
  | [] => by
    rw [termArr_nil, termPerm_nil]
    exact rep_idA
  | i :: t => by
    rw [termArr_cons, termPerm_cons]
    exact rep_compA (aPerm_spec i).1 (rep_termArr t)

theorem termPerm_append (t u : List ℕ) : termPerm (t ++ u) = termPerm t * termPerm u := by
  rw [termPerm, List.map_append, List.prod_append, termPerm, termPerm]

theorem termPerm_mem : ∀ t : List ℕ, termPerm t ∈ omegaT
  | [] => by
    rw [termPerm_nil]
    exact omegaT.one_mem
  | i :: t => by
    rw [termPerm_cons]
    exact omegaT.mul_mem (aPerm_spec i).2 (termPerm_mem t)

theorem omegaPerm_spec {w : List ℤ}
    (hw : lettersOK 17 w = true) : Rep 360 (omegaW w) (omegaPerm w) ∧ omegaPerm w ∈ omegaT :=
  omegaW_spec hw

theorem dw27_parts (h : dw27Check = true) :
    relCheck = true ∧ eCheck = true ∧ bwCheck = true ∧ invCheck = true := by
  simpa only [dw27Check, Bool.and_eq_true, and_assoc] using h

theorem rho_cube (h : dw27Check = true) : gen 8 ^ 3 = 1 := by
  have h1 := (dw27_parts h).1
  simp only [relCheck, Bool.and_eq_true] at h1
  exact eq_of_eqA (rep_powArr (rep_gen (by norm_num)) 3) rep_idA h1.1.1

theorem tau_sq (h : dw27Check = true) : gen 9 * gen 9 = 1 := by
  have h1 := (dw27_parts h).1
  simp only [relCheck, Bool.and_eq_true] at h1
  exact eq_of_eqA (rep_compA (rep_gen (by norm_num)) (rep_gen (by norm_num))) rep_idA h1.1.2

theorem tau_rho (h : dw27Check = true) :
    gen 9 * gen 8 = gen 8 ^ 2 * gen 9 := by
  have h1 := (dw27_parts h).1
  simp only [relCheck, Bool.and_eq_true] at h1
  exact eq_of_eqA (rep_compA (rep_gen (by norm_num)) (rep_gen (by norm_num)))
    (rep_compA (rep_powArr (rep_gen (by norm_num)) 2) (rep_gen (by norm_num))) h1.2

theorem eCheck_parts (h : dw27Check = true) :
    (∀ i < 4, eqA 360 (powArr (aArr i) 3) (idA 360) = true ∧
      ∀ j < 4, commArr (aArr i) (aArr j) = true) ∧
    eqA 360 (termArr [0, 1, 2]) (idA 360) = false ∧
    commArr genArrs[9]! (aArr 0) = true ∧ commArr genArrs[9]! (aArr 1) = true := by
  have h1 := (dw27_parts h).2.1
  simp only [eCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h1
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩

theorem aPerm_cube (h : dw27Check = true) {i : ℕ} (hi : i < 4) :
    aPerm i ^ 3 = 1 :=
  eq_of_eqA (rep_powArr (aPerm_spec i).1 3) rep_idA ((eCheck_parts h).1 i hi).1

theorem eq_of_commArr {t u : Array ℕ} {g k : Equiv.Perm (Fin 360)}
    (ht : Rep 360 t g) (hu : Rep 360 u k) (hc : commArr t u = true) : g * k = k * g :=
  eq_of_eqA (rep_compA ht hu) (rep_compA hu ht) hc

theorem aPerm_comm (h : dw27Check = true) {i j : ℕ} (hi : i < 4)
    (hj : j < 4) : aPerm i * aPerm j = aPerm j * aPerm i :=
  eq_of_commArr (aPerm_spec i).1 (aPerm_spec j).1 (((eCheck_parts h).1 i hi).2 j hj)

theorem termPerm_ne_one (h : dw27Check = true) :
    termPerm [0, 1, 2] ≠ 1 := by
  intro h1
  have h2 := (eCheck_parts h).2.1
  rw [(eqA_iff (rep_termArr [0, 1, 2]) rep_idA).2 h1] at h2
  exact absurd h2 (by decide)

theorem tau_comm_aPerm (h : dw27Check = true) {i : ℕ}
    (hi : i < 2) : gen 9 * aPerm i = aPerm i * gen 9 := by
  interval_cases i
  · exact eq_of_commArr (rep_gen (by norm_num)) (aPerm_spec 0).1 (eCheck_parts h).2.2.1
  · exact eq_of_commArr (rep_gen (by norm_num)) (aPerm_spec 1).1 (eCheck_parts h).2.2.2

theorem bw_entry (h : dw27Check = true)
    {e : List ℕ × ℕ × List ℤ × ℕ × ℕ} (he : e ∈ bwEntries) :
    omegaPerm e.2.2.1 * gen 8 ^ e.2.1 * termPerm e.1 =
      termPerm (repTerms.getD e.2.2.2.1 []) ^ e.2.2.2.2 * (omegaPerm e.2.2.1 * gen 8 ^ e.2.1) := by
  have h1 := (dw27_parts h).2.2.1
  simp only [bwCheck, List.all_eq_true] at h1
  have hw : lettersOK 17 e.2.2.1 = true :=
    List.all_eq_true.1 bwWords_letters _ (List.mem_map.2 ⟨e, he, rfl⟩)
  have hc : Rep 360 (bwConj e.2.1 e.2.2.1) (omegaPerm e.2.2.1 * gen 8 ^ e.2.1) :=
    rep_compA (omegaPerm_spec hw).1 (rep_powArr (rep_gen (by norm_num)) _)
  exact eq_of_eqA (rep_compA hc (rep_termArr _))
    (rep_compA (rep_powArr (rep_termArr _) _) hc) (h1 e he)

theorem inv_entry (h : dw27Check = true) {i : ℕ} (hi : i < 3) :
    omegaPerm (invData.getD i ([], [], 0)).1 * omegaPerm (invData.getD i ([], [], 0)).2.1 =
        termPerm (repTerms.getD (invData.getD i ([], [], 0)).2.2 []) *
          omegaPerm (invData.getD i ([], [], 0)).1 ∧
      mainPerm i * (omegaPerm (invData.getD i ([], [], 0)).2.1 *
        (mainPerm i * omegaPerm (invData.getD i ([], [], 0)).2.1)) = 1 := by
  have h1 := (dw27_parts h).2.2.2
  simp only [invCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h1
  have hlen : i < invData.length := by simp [invData]; omega
  have hmem : invData.getD i ([], [], 0) ∈ invData := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  have hg : lettersOK 17 (invData.getD i ([], [], 0)).1 = true :=
    List.all_eq_true.1 invWords_letters _
      (List.mem_append_left _ (List.mem_map.2 ⟨_, hmem, rfl⟩))
  have hu : lettersOK 17 (invData.getD i ([], [], 0)).2.1 = true :=
    List.all_eq_true.1 invWords_letters _
      (List.mem_append_right _ (List.mem_map.2 ⟨_, hmem, rfl⟩))
  have hx := (mainPerm_spec (show i < 5 by omega)).1
  refine ⟨eq_of_eqA (rep_compA (omegaPerm_spec hg).1 (omegaPerm_spec hu).1)
    (rep_compA (rep_termArr _) (omegaPerm_spec hg).1) (h1 i hi).1, ?_⟩
  exact eq_of_eqA (rep_compA hx (rep_compA (omegaPerm_spec hu).1
    (rep_compA hx (omegaPerm_spec hu).1))) rep_idA (h1 i hi).2


theorem aPerm_eq_one {i : ℕ} (hi : 4 ≤ i) : aPerm i = 1 := by
  have e : aArr i = idA 360 := by
    rw [aArr, List.getD_eq_default _ _ (by simp [eWords]; omega)]
    rfl
  rw [aPerm, e]
  exact permOfArr_eq_of_rep rep_idA

theorem aPerm_cube' (h : dw27Check = true) (i : ℕ) :
    aPerm i ^ 3 = 1 := by
  by_cases hi : i < 4
  · exact aPerm_cube h hi
  · rw [aPerm_eq_one (by omega), one_pow]

theorem aPerm_comm' (h : dw27Check = true) (i j : ℕ) :
    aPerm i * aPerm j = aPerm j * aPerm i := by
  by_cases hi : i < 4
  · by_cases hj : j < 4
    · exact aPerm_comm h hi hj
    · rw [aPerm_eq_one (by omega : 4 ≤ j), mul_one, one_mul]
  · rw [aPerm_eq_one (by omega : 4 ≤ i), mul_one, one_mul]

theorem aPerm_comm_termPerm (h : dw27Check = true) (i : ℕ) :
    ∀ t : List ℕ, aPerm i * termPerm t = termPerm t * aPerm i
  | [] => by rw [termPerm_nil, mul_one, one_mul]
  | j :: t => by
    rw [termPerm_cons, ← mul_assoc, aPerm_comm' h i j, mul_assoc, aPerm_comm_termPerm h i t,
      mul_assoc]

theorem termPerm_comm (h : dw27Check = true) :
    ∀ t u : List ℕ, termPerm t * termPerm u = termPerm u * termPerm t
  | [], u => by rw [termPerm_nil, mul_one, one_mul]
  | i :: t, u => by
    rw [termPerm_cons, mul_assoc, termPerm_comm h t u, ← mul_assoc, aPerm_comm_termPerm h i u,
      mul_assoc]

theorem termPerm_cube (h : dw27Check = true) :
    ∀ t : List ℕ, termPerm t ^ 3 = 1
  | [] => by rw [termPerm_nil, one_pow]
  | i :: t => by
    rw [termPerm_cons, (Commute.mul_pow (aPerm_comm_termPerm h i t) 3), aPerm_cube' h,
      termPerm_cube h t, one_mul]

theorem pow_mod_three {G : Type*} [Monoid G] {x : G} (hx : x ^ 3 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one]

theorem tau_rho_pow (h : dw27Check = true) :
    ∀ k : ℕ, gen 9 * gen 8 ^ k = gen 8 ^ (2 * k) * gen 9
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, ← mul_assoc, tau_rho_pow h k, mul_assoc, tau_rho h, ← mul_assoc, ← pow_add]
    ring_nf

@[expose] def InCoset (x : Equiv.Perm (Fin 360)) : Prop :=
  ∃ ω ∈ omegaT, ∃ k < 3, ∃ j < 2, x = ω * gen 8 ^ k * gen 9 ^ j

theorem inCoset_mul_rho (h : dw27Check = true)
    {x : Equiv.Perm (Fin 360)} (hx : InCoset x) : InCoset (x * gen 8) := by
  obtain ⟨ω, hω, k, hk, j, hj, rfl⟩ := hx
  interval_cases j
  · refine ⟨ω, hω, (k + 1) % 3, Nat.mod_lt _ (by norm_num), 0, by norm_num, ?_⟩
    try simp only [pow_zero, mul_one]
    rw [← pow_mod_three (rho_cube h) (k + 1), mul_assoc, ← pow_succ]
  · refine ⟨ω, hω, (k + 2) % 3, Nat.mod_lt _ (by norm_num), 1, by norm_num, ?_⟩
    try simp only [pow_one]
    rw [← pow_mod_three (rho_cube h) (k + 2), mul_assoc (ω * gen 8 ^ k), tau_rho h,
      ← mul_assoc, mul_assoc ω, ← pow_add]

theorem inCoset_mul_tau (h : dw27Check = true)
    {x : Equiv.Perm (Fin 360)} (hx : InCoset x) : InCoset (x * gen 9) := by
  obtain ⟨ω, hω, k, hk, j, hj, rfl⟩ := hx
  interval_cases j
  · refine ⟨ω, hω, k, hk, 1, by norm_num, ?_⟩
    simp only [pow_zero, mul_one, pow_one]
  · refine ⟨ω, hω, k, hk, 0, by norm_num, ?_⟩
    simp only [pow_one, pow_zero, mul_one]
    rw [mul_assoc, tau_sq h, mul_one]

theorem inCoset_mul_omega {x y : Equiv.Perm (Fin 360)}
    (hx : InCoset x) (hy : y ∈ omegaT) : InCoset (x * y) := by
  obtain ⟨ω, hω, k, hk, j, hj, rfl⟩ := hx
  have hσ : gen 8 ^ k * gen 9 ^ j ∈ autT :=
    autT.mul_mem (autT.pow_mem (gen_mem_autT (by norm_num)) k)
      (autT.pow_mem (gen_mem_autT (by norm_num)) j)
  refine ⟨ω * (gen 8 ^ k * gen 9 ^ j * y * (gen 8 ^ k * gen 9 ^ j)⁻¹),
    omegaT.mul_mem hω ((conj_mem_omegaT hσ).1 hy), k, hk, j, hj, ?_⟩
  group

theorem autT_decomp (h : dw27Check = true)
    {a : Equiv.Perm (Fin 360)} (ha : a ∈ autT) : InCoset a := by
  rw [autT_eq] at ha
  induction ha using Subgroup.closure_induction_right with
  | one => exact ⟨1, omegaT.one_mem, 0, by norm_num, 0, by norm_num, by simp⟩
  | mul_right x _ y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    by_cases h8 : i < 8
    · exact inCoset_mul_omega ih (gen_mem_omegaT h8)
    · by_cases h9 : i = 8
      · subst h9
        exact inCoset_mul_rho h ih
      · rw [show i = 9 by omega]
        exact inCoset_mul_tau h ih
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    by_cases h8 : i < 8
    · exact inCoset_mul_omega ih (omegaT.inv_mem (gen_mem_omegaT h8))
    · by_cases h9 : i = 8
      · subst h9
        have e : (gen 8)⁻¹ = gen 8 * gen 8 := by
          rw [inv_eq_iff_mul_eq_one, ← pow_three, rho_cube h]
        rw [e, ← mul_assoc]
        exact inCoset_mul_rho h (inCoset_mul_rho h ih)
      · rw [show i = 9 by omega]
        have e : (gen 9)⁻¹ = gen 9 := inv_eq_of_mul_eq_one_right (tau_sq h)
        rw [e]
        exact inCoset_mul_tau h ih

theorem sq_mem_coset (h : dw27Check = true)
    {a : Equiv.Perm (Fin 360)} (ha : a ∈ autT) :
    ∃ ω ∈ omegaT, ∃ m < 3, a ^ 2 = ω * gen 8 ^ m := by
  obtain ⟨ω, hω, k, hk, j, hj, rfl⟩ := autT_decomp h ha
  have hσ : gen 8 ^ k * gen 9 ^ j ∈ autT :=
    autT.mul_mem (autT.pow_mem (gen_mem_autT (by norm_num)) k)
      (autT.pow_mem (gen_mem_autT (by norm_num)) j)
  have hc := (conj_mem_omegaT hσ).1 hω
  have e : (ω * gen 8 ^ k * gen 9 ^ j) ^ 2 =
      ω * (gen 8 ^ k * gen 9 ^ j * ω * (gen 8 ^ k * gen 9 ^ j)⁻¹) *
        (gen 8 ^ k * gen 9 ^ j) ^ 2 := by
    rw [mul_assoc ω]
    generalize gen 8 ^ k * gen 9 ^ j = σ
    rw [pow_two, pow_two]
    group
  interval_cases j
  · refine ⟨_, omegaT.mul_mem hω hc, (2 * k) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [e, pow_zero, mul_one, ← pow_mul, mul_comm k 2, pow_mod_three (rho_cube h) (2 * k)]
  · refine ⟨_, omegaT.mul_mem hω hc, 0, by norm_num, ?_⟩
    have e2 : (gen 8 ^ k * gen 9 ^ 1) ^ 2 = 1 := by
      rw [pow_one, pow_two, mul_assoc, ← mul_assoc (gen 9), tau_rho_pow h k, mul_assoc,
        tau_sq h, mul_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, rho_cube h, one_pow]
    rw [e, e2, mul_one, pow_zero, mul_one]

theorem exists_conj_mem_sylowT_two {x : Equiv.Perm (Fin 360)}
    (hx : x ∈ autT) (hx2 : orderOf x = 2) : ∃ a ∈ autT, a * x * a⁻¹ ∈ sylowT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x' : autT := ⟨x, hx⟩
  have hX : IsPGroup 2 (Subgroup.zpowers x') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2, pow_one])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq autT sylowA Q
  have h1 : x' ∈ (Q : Subgroup autT) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, coe_sylowA,
    Subgroup.mem_subgroupOf] at h1
  refine ⟨(g⁻¹ : autT), (g⁻¹ : autT).2, ?_⟩
  simpa using h1

theorem exists_conj_mainPerm {x : Equiv.Perm (Fin 360)}
    (hx : x ∈ omegaT) (hx2 : orderOf x = 2) :
    ∃ c ∈ autT, ∃ i < 3, x = c * mainPerm i * c⁻¹ := by
  obtain ⟨a, ha, has⟩ := exists_conj_mem_sylowT_two (omegaT_le_autT hx) hx2
  have hax2 : orderOf (a * x * a⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx2]
  obtain ⟨j, hj, c, hc, hrep⟩ := exists_rep_of_involution has hax2
  have hcA : c ∈ autT := sylowT_le_autT hc
  have hmem : repPerm j ∈ omegaT := by
    have h1 : a * x * a⁻¹ ∈ omegaT := (conj_mem_omegaT ha).1 hx
    rw [hrep] at h1
    have h2 := (conj_mem_omegaT (autT.inv_mem hcA)).1 h1
    simpa [mul_assoc] using h2
  have ht := (repPerm_mem_omegaT_iff hj).1 hmem
  refine ⟨a⁻¹ * c * conjPerm j, autT.mul_mem (autT.mul_mem (autT.inv_mem ha) hcA)
    (conjPerm_spec hj).2, repTypes.getD j 0, ht, ?_⟩
  have e := conj_mainPerm hj
  calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
    _ = a⁻¹ * (c * repPerm j * c⁻¹) * a := by rw [hrep]
    _ = a⁻¹ * (c * (conjPerm j * mainPerm (repTypes.getD j 0) * (conjPerm j)⁻¹) * c⁻¹) * a := by
        rw [e]
    _ = a⁻¹ * c * conjPerm j * mainPerm (repTypes.getD j 0) * (a⁻¹ * c * conjPerm j)⁻¹ := by
        group

end CFSG.LargeExtraspecial.DW.Insp
