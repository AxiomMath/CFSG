module

public import CFSG.LieType.Chevalley.E6EvenInvolution
public import CFSG.LieType.Chevalley.E6GraphLeviUnitary

public noncomputable section

namespace CFSG.LieType.Chevalley.E6EvenInvolution

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphLevi
  CFSG.LieType.Chevalley.E6GraphHighestRoot

variable {K : Type} [Field K]

@[expose] def pairU (σ : K →+* K) {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l) (c : K) :
    SpecialLinearGroup (Fin 6) K :=
  SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hkl (σ c)

theorem coe_pairU (σ : K →+* K) {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (c : K) :
    (pairU σ hij hkl c : Matrix (Fin 6) (Fin 6) K) = 1 + (single i j c + single k l (σ c)) := by
  rw [pairU, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, single_mul_single_of_ne (h := hjk), add_zero]
  abel

theorem pairU_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) {i j k l : Fin 6}
    (hij : i ≠ j) (hkl : k ≠ l) (hk : Fin.rev j = k) (hl : Fin.rev i = l) (hjk : j ≠ k)
    (hli : l ≠ i) (c : K) : pairU σ hij hkl c ∈ unitarySL σ := by
  subst hk hl
  change unitaryTwist σ (pairU σ hij hkl c) = pairU σ hij hkl c
  have e1 : unitaryTwist σ (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hkl (σ c) := by
    rw [unitaryTwist, MonoidHom.comp_apply, map_transvection, graphSL_transvection h2]
  have e2 : unitaryTwist σ (SpecialLinearGroup.transvection hkl (σ c)) =
      SpecialLinearGroup.transvection hij c := by
    rw [unitaryTwist, MonoidHom.comp_apply, map_transvection, graphSL_transvection h2, hσσ]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.transvection_coe, Fin.rev_rev]
  rw [pairU, map_mul, e1, e2]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  simp [single_mul_single_of_ne, hli, hjk]
  abel

theorem pairU_sq (h2 : (2 : K) = 0) (σ : K →+* K) {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (c : K) : pairU σ hij hkl c * pairU σ hij hkl c = 1 :=
  sq_eq_one_of_coe h2 (coe_pairU σ hij hkl hjk c) (by
    simp [Matrix.add_mul, Matrix.mul_add, single_mul_single_of_ne, hij.symm, hjk, hli, hkl.symm])

theorem pow_four_eq_one {G : Type*} [Group G] {s : G} (h : s * s = 1) : s ^ 4 = 1 := by
  calc s ^ 4 = (s * s) ^ 2 := by rw [← sq, ← pow_mul]
    _ = 1 := by rw [h, one_pow]

theorem comm_of_realize_comm
    (h2 : (2 : K) = 0) {B S : SpecialLinearGroup (Fin 6) K}
    (hS : S ^ 4 = 1) (h : realize h2 B * realize h2 S = realize h2 S * realize h2 B) :
    B * S = S * B := by
  obtain ⟨z, hz⟩ : ∃ z, z = B * S * B⁻¹ * S⁻¹ := ⟨_, rfl⟩
  have hzk : z ∈ (realize h2).ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  obtain ⟨l, -, hl⟩ := (mem_ker_realize h2 z).1 hzk
  have hzS : Commute z S := by
    change z * S = S * z
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hl]
    exact (Matrix.scalar_commute l (fun _ => Commute.all _ _) _).eq
  have hBS : B * S * B⁻¹ = z * S := by rw [hz]; group
  have h4 : z ^ 4 = 1 := by
    have e : (B * S * B⁻¹) ^ 4 = 1 := by rw [conj_pow, hS, mul_one, mul_inv_cancel]
    rwa [hBS, hzS.mul_pow, hS, mul_one] at e
  have hz1 : z = 1 := by
    rw [show z = z ^ 4 * (z ^ 3)⁻¹ by group, h4, pow_three_eq_one_of_mem_ker h2 hzk, inv_one,
      one_mul]
  calc B * S = B * S * B⁻¹ * S⁻¹ * (S * B) := by group
    _ = S * B := by rw [← hz, hz1, one_mul]

theorem unitary_entry {σ : K →+* K} {B : SpecialLinearGroup (Fin 6) K} (hB : B ∈ unitarySL σ)
    (x y : Fin 6) :
    ∑ v : Fin 6, σ ((B : Matrix (Fin 6) (Fin 6) K) (Fin.rev v) x) *
      (B : Matrix (Fin 6) (Fin 6) K) v y = antiId K x y := by
  have h := congrFun (congrFun (mem_unitarySL_iff.1 hB) x) y
  rw [Matrix.mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev v)]
  · simp [antiId, Matrix.transpose_apply, Matrix.map_apply]
  · intro u _ hu
    have : v ≠ Fin.rev u := fun h => hu (by rw [h, Fin.rev_rev])
    simp [antiId, this]
  · simp

theorem rev_vals : Fin.rev (0 : Fin 6) = 5 ∧ Fin.rev (1 : Fin 6) = 4 ∧ Fin.rev (2 : Fin 6) = 3 ∧
    Fin.rev (3 : Fin 6) = 2 ∧ Fin.rev (4 : Fin 6) = 1 ∧ Fin.rev (5 : Fin 6) = 0 := by decide

theorem antiId_apply (x y : Fin 6) : antiId K x y = if y = Fin.rev x then 1 else 0 := rfl

abbrev nT1 : Matrix (Fin 6) (Fin 6) K := E K 2 3

theorem unitary_coeffs_T1 {σ : K →+* K} {B : SpecialLinearGroup (Fin 6) K}
    (hB : B ∈ unitarySL σ) {a b : K}
    (hBN : (B : Matrix (Fin 6) (Fin 6) K) = a • 1 + b • nT1) :
    σ a * a = 1 ∧ σ a * b + σ b * a = 0 := by
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := rev_vals
  have e1 := unitary_entry hB 0 5
  have e2 := unitary_entry hB 3 3
  simp only [Fin.sum_univ_six, r0, r1, r2, r3, r4, r5, hBN, antiId_apply, nT1, E,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply] at e1 e2
  simp at e1 e2
  exact ⟨e1, by linear_combination e2⟩

theorem unitary_coeffs_23 {σ : K →+* K} {B : SpecialLinearGroup (Fin 6) K}
    (hB : B ∈ unitarySL σ) {a b : K} {N : Matrix (Fin 6) (Fin 6) K}
    (hN : N = nMat2 K ∨ N = nMat3 K)
    (hBN : (B : Matrix (Fin 6) (Fin 6) K) = a • 1 + b • N) :
    σ a * a = 1 ∧ σ a * b + σ b * a = 0 := by
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := rev_vals
  have e1 := unitary_entry hB 0 5
  have e2 := unitary_entry hB 1 5
  rcases hN with rfl | rfl <;>
  · simp only [Fin.sum_univ_six, r0, r1, r2, r3, r4, r5, hBN, antiId_apply, nMat2, nMat3, E,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply] at e1 e2
    simp at e1 e2
    exact ⟨e1, by linear_combination e2⟩

theorem eq_one_or_eq_of_commutantU
    (h2 : (2 : K) = 0) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2) {R : SpecialLinearGroup (Fin 6) K} {N : Matrix (Fin 6) (Fin 6) K}
    (hR : (R : Matrix (Fin 6) (Fin 6) K) = 1 + N)
    (S : List (SpecialLinearGroup (Fin 6) K)) (hSu : ∀ s ∈ S, s ∈ unitarySL σ)
    (hSR : ∀ s ∈ S, s * R = R * s) (hS4 : ∀ s ∈ S, s ^ 4 = 1)
    (hcomm : ∀ B : SpecialLinearGroup (Fin 6) K, (∀ s ∈ S, B * s = s * B) →
      ∃ a b : K, (B : Matrix (Fin 6) (Fin 6) K) = a • 1 + b • N)
    (hunit : ∀ B ∈ unitarySL σ, ∀ a b : K, (B : Matrix (Fin 6) (Fin 6) K) = a • 1 + b • N →
      σ a * a = 1 ∧ σ a * b + σ b * a = 0)
    {w : ModGL TwistTag.E6.tag K} (hw : w ∈ (unitarySL σ).map (realize h2))
    (hc : ∀ c ∈ (unitarySL σ).map (realize h2), c * realize h2 R = realize h2 R * c →
      w * c = c * w) :
    w = 1 ∨ w = realize h2 R := by
  obtain ⟨B, hBu, rfl⟩ := hw
  have hBS : ∀ s ∈ S, B * s = s * B := fun s hs => comm_of_realize_comm h2 (hS4 s hs) (by
    refine hc _ ⟨s, hSu s hs, rfl⟩ ?_
    rw [← map_mul, ← map_mul, hSR s hs])
  obtain ⟨a, b, hab⟩ := hcomm B hBS
  obtain ⟨h1, h0⟩ := hunit B hBu a b hab
  have ha0 : a ≠ 0 := fun h => by rw [h, mul_zero] at h1; exact zero_ne_one h1
  have ha3 : a ^ 3 = 1 := by rw [← h1, hσ]; ring
  have hσσa : σ (σ a) = a := by
    rw [hσ, hσ, ← pow_mul]
    calc a ^ (2 * 2) = a ^ 3 * a := by ring
      _ = a := by rw [ha3, one_mul]
  set c := b * σ a with hc_def
  have hcσ : σ c = c := by
    have e : σ c = σ b * a := by rw [hc_def, map_mul, hσσa]
    rw [e, hc_def]
    linear_combination h0 - (σ a * b) * h2
  have hc01 : c = 0 ∨ c = 1 := by
    rw [hσ] at hcσ
    have : c * (c - 1) = 0 := by linear_combination hcσ
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have hσa0 : σ a ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
  rcases hc01 with h | h
  ·
    left
    have hb : b = 0 := by
      rcases mul_eq_zero.1 (show b * σ a = 0 from h) with h' | h'
      · exact h'
      · exact absurd h' hσa0
    rw [← MonoidHom.mem_ker, mem_ker_realize]
    exact ⟨a, ha3, by rw [hab, hb, zero_smul, add_zero, Matrix.smul_one_eq_diagonal]; rfl⟩
  ·
    right
    have hb : b = a := by
      calc b = b * σ a * a := by rw [mul_assoc, h1, mul_one]
        _ = a := by rw [show b * σ a = 1 from h, one_mul]
    have hk : B * R⁻¹ ∈ (realize h2).ker := by
      rw [mem_ker_realize]
      refine ⟨a, ha3, ?_⟩
      have hRR : (R : Matrix (Fin 6) (Fin 6) K) * ((R⁻¹ : SpecialLinearGroup (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [Matrix.SpecialLinearGroup.coe_mul, hab, hb, ← smul_add, ← hR, Matrix.smul_mul, hRR,
        Matrix.smul_one_eq_diagonal]
      rfl
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
    exact hk

theorem comm_smul_add {B X Y : Matrix (Fin 6) (Fin 6) K} (a : K) (hX : B * X = X * B)
    (hY : B * Y = Y * B) : B * (a • X + Y) = (a • X + Y) * B := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hX, hY]

theorem comm_of_pair (h2 : (2 : K) = 0) {σ : K →+* K} {t : K} (ht : t + σ t = 1)
    {B : Matrix (Fin 6) (Fin 6) K} {i j k l : Fin 6}
    (h1 : B * (single i j 1 + single k l 1) = (single i j 1 + single k l 1) * B)
    (h1' : B * (single i j t + single k l (σ t)) = (single i j t + single k l (σ t)) * B) :
    B * single i j 1 = single i j 1 * B ∧ B * single k l 1 = single k l 1 * B := by
  have htt : t + t = 0 := by linear_combination t * h2
  have h11 : (1 : K) + 1 = 0 := by linear_combination h2
  have e : single k l (1 : K) =
      t • (single i j 1 + single k l 1) + (single i j t + single k l (σ t)) := by
    rw [smul_add, Matrix.smul_single, Matrix.smul_single, smul_eq_mul, mul_one,
      show single i j t + single k l t + (single i j t + single k l (σ t)) =
        single i j (t + t) + single k l (t + σ t) by rw [single_add, single_add]; abel, htt, ht,
      single_zero, zero_add]
  have hk : B * single k l 1 = single k l 1 * B := by rw [e]; exact comm_smul_add t h1 h1'
  have e' : single i j (1 : K) = (1 : K) • (single i j 1 + single k l 1) + single k l 1 := by
    rw [one_smul, add_assoc, ← single_add, h11, single_zero, add_zero]
  exact ⟨by rw [e']; exact comm_smul_add 1 h1 hk, hk⟩

theorem comm_of_pair' (h2 : (2 : K) = 0) {σ : K →+* K} {t : K} (ht : t + σ t = 1)
    {B X Y : Matrix (Fin 6) (Fin 6) K} (h1 : B * (X + Y) = (X + Y) * B)
    (h1' : B * (t • X + σ t • Y) = (t • X + σ t • Y) * B) :
    B * X = X * B ∧ B * Y = Y * B := by
  have e : Y = t • (X + Y) + (t • X + σ t • Y) := by
    rw [smul_add, add_add_add_comm, ← add_smul, ← add_smul,
      show t + t = 0 by linear_combination t * h2, ht, zero_smul, one_smul, zero_add]
  have hY : B * Y = Y * B := by rw [e]; exact comm_smul_add t h1 h1'
  have e' : X = (1 : K) • (X + Y) + Y := by
    rw [one_smul, add_assoc, ← two_smul K Y, h2, zero_smul, add_zero]
  exact ⟨by rw [e']; exact comm_smul_add 1 h1 hY, hY⟩

theorem transvection_mem_unitarySL (h2 : (2 : K) = 0) {σ : K →+* K} {i j : Fin 6} (hij : i ≠ j)
    (hj : Fin.rev j = i) {c : K} (hc : σ c = c) :
    SpecialLinearGroup.transvection hij c ∈ unitarySL σ := by
  change unitaryTwist σ (SpecialLinearGroup.transvection hij c) =
    SpecialLinearGroup.transvection hij c
  rw [unitaryTwist, MonoidHom.comp_apply, map_transvection, hc, graphSL_transvection h2]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.transvection_coe]
  rw [hj, show Fin.rev i = j by rw [← hj, Fin.rev_rev]]

theorem pow_four_eq_one_of_coe (h2 : (2 : K) = 0) {S : SpecialLinearGroup (Fin 6) K}
    {M : Matrix (Fin 6) (Fin 6) K} (hS : (S : Matrix (Fin 6) (Fin 6) K) = 1 + M)
    (hM : M * M * (M * M) = 0) : S ^ 4 = 1 := by
  have h1 : ((S * S : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 + M * M := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hS, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, ← add_assoc, add_assoc 1 M M,
      ← two_smul K M, h2, zero_smul, add_zero]
  exact (show S ^ 4 = (S * S) * (S * S) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]).trans
    (sq_eq_one_of_coe h2 h1 hM)

abbrev u01 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 0) (j := 1) (k := 4) (l := 5) (by decide) (by decide) c

theorem coe_u01 (σ : K →+* K) (c : K) :
    ((u01 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 0 1 c + single 4 5 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u01_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u01 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

theorem u01_sq (h2 : (2 : K) = 0) (σ : K →+* K) (c : K) : u01 σ c * u01 σ c = 1 :=
  pairU_sq h2 σ _ _ (by decide) (by decide) c

abbrev u10 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 1) (j := 0) (k := 5) (l := 4) (by decide) (by decide) c

theorem coe_u10 (σ : K →+* K) (c : K) :
    ((u10 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 1 0 c + single 5 4 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u10_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u10 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

theorem u10_sq (h2 : (2 : K) = 0) (σ : K →+* K) (c : K) : u10 σ c * u10 σ c = 1 :=
  pairU_sq h2 σ _ _ (by decide) (by decide) c

abbrev u24 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 2) (j := 4) (k := 1) (l := 3) (by decide) (by decide) c

theorem coe_u24 (σ : K →+* K) (c : K) :
    ((u24 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 2 4 c + single 1 3 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u24_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u24 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

theorem u24_sq (h2 : (2 : K) = 0) (σ : K →+* K) (c : K) : u24 σ c * u24 σ c = 1 :=
  pairU_sq h2 σ _ _ (by decide) (by decide) c

abbrev u50 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 5) (j := 0) (k := 5) (l := 0) (by decide) (by decide) c

theorem coe_u50 (σ : K →+* K) (c : K) :
    ((u50 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 5 0 c + single 5 0 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u50_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u50 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

theorem u50_sq (h2 : (2 : K) = 0) (σ : K →+* K) (c : K) : u50 σ c * u50 σ c = 1 :=
  pairU_sq h2 σ _ _ (by decide) (by decide) c

abbrev u04 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 0) (j := 4) (k := 1) (l := 5) (by decide) (by decide) c

theorem coe_u04 (σ : K →+* K) (c : K) :
    ((u04 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 0 4 c + single 1 5 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u04_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u04 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

theorem u04_sq (h2 : (2 : K) = 0) (σ : K →+* K) (c : K) : u04 σ c * u04 σ c = 1 :=
  pairU_sq h2 σ _ _ (by decide) (by decide) c

abbrev u40 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 4) (j := 0) (k := 5) (l := 1) (by decide) (by decide) c

theorem coe_u40 (σ : K →+* K) (c : K) :
    ((u40 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 4 0 c + single 5 1 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u40_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u40 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

theorem u40_sq (h2 : (2 : K) = 0) (σ : K →+* K) (c : K) : u40 σ c * u40 σ c = 1 :=
  pairU_sq h2 σ _ _ (by decide) (by decide) c

abbrev u02 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 0) (j := 2) (k := 3) (l := 5) (by decide) (by decide) c

theorem coe_u02 (σ : K →+* K) (c : K) :
    ((u02 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 0 2 c + single 3 5 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u02_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u02 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

theorem u02_sq (h2 : (2 : K) = 0) (σ : K →+* K) (c : K) : u02 σ c * u02 σ c = 1 :=
  pairU_sq h2 σ _ _ (by decide) (by decide) c

abbrev u03 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 0) (j := 3) (k := 2) (l := 5) (by decide) (by decide) c

theorem coe_u03 (σ : K →+* K) (c : K) :
    ((u03 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 0 3 c + single 2 5 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u03_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u03 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

theorem u03_sq (h2 : (2 : K) = 0) (σ : K →+* K) (c : K) : u03 σ c * u03 σ c = 1 :=
  pairU_sq h2 σ _ _ (by decide) (by decide) c

abbrev u13 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 1) (j := 3) (k := 2) (l := 4) (by decide) (by decide) c

theorem coe_u13 (σ : K →+* K) (c : K) :
    ((u13 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 1 3 c + single 2 4 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u13_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u13 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

abbrev u20 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 2) (j := 0) (k := 5) (l := 3) (by decide) (by decide) c

theorem coe_u20 (σ : K →+* K) (c : K) :
    ((u20 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 2 0 c + single 5 3 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u20_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u20 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

abbrev u31 (σ : K →+* K) (c : K) : SpecialLinearGroup (Fin 6) K :=
  pairU σ (i := 3) (j := 1) (k := 4) (l := 2) (by decide) (by decide) c

theorem coe_u31 (σ : K →+* K) (c : K) :
    ((u31 σ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (single 3 1 c + single 4 2 (σ c)) :=
  coe_pairU σ _ _ (by decide) c

theorem u31_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    u31 σ c ∈ unitarySL σ :=
  pairU_mem h2 hσσ _ _ (by decide) (by decide) (by decide) (by decide) c

@[expose] def slT1 : SpecialLinearGroup (Fin 6) K := trv (a := 2) (b := 3) (by decide)

theorem coe_slT1 : ((slT1 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
    1 + nT1 :=
  coe_trv (a := 2) (b := 3) (by decide)

theorem nT1_sq : (nT1 : Matrix (Fin 6) (Fin 6) K) * nT1 = 0 := by
  simp [nT1, E]

theorem slT1_mem (h2 : (2 : K) = 0) (σ : K →+* K) : slT1 ∈ unitarySL σ :=
  transvection_mem_unitarySL (i := 2) (j := 3) h2 (by decide) (by decide) (map_one σ)

@[expose] def gensU1 (σ : K →+* K) (t₀ : K) : List (SpecialLinearGroup (Fin 6) K) :=
  [slT1, u01 σ 1, u01 σ t₀, u10 σ 1, u10 σ t₀, u24 σ 1, u24 σ t₀, u50 σ t₀]

theorem gensU1_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (t₀ : K) :
    ∀ s ∈ gensU1 σ t₀, s ∈ unitarySL σ := by
  simp only [gensU1, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [slT1_mem h2 σ, u01_mem h2 hσσ 1, u01_mem h2 hσσ t₀, u10_mem h2 hσσ 1,
    u10_mem h2 hσσ t₀, u24_mem h2 hσσ 1, u24_mem h2 hσσ t₀, u50_mem h2 hσσ t₀]

theorem gensU1_comm (σ : K →+* K) (t₀ : K) : ∀ s ∈ gensU1 σ t₀, s * slT1 = slT1 * s := by
  have hc : ∀ {s : SpecialLinearGroup (Fin 6) K} {M : Matrix (Fin 6) (Fin 6) K},
      (s : Matrix (Fin 6) (Fin 6) K) = 1 + M → M * nT1 = nT1 * M → s * slT1 = slT1 * s :=
    fun hs h => comm_of_coe hs coe_slT1 h
  simp only [gensU1, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · rfl
  · exact hc (coe_u01 σ 1) (by simp [nT1, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u01 σ t₀) (by simp [nT1, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u10 σ 1) (by simp [nT1, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u10 σ t₀) (by simp [nT1, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u24 σ 1) (by simp [nT1, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u24 σ t₀) (by simp [nT1, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u50 σ t₀) (by simp [nT1, E, Matrix.add_mul, Matrix.mul_add])

theorem gensU1_pow (h2 : (2 : K) = 0) (σ : K →+* K) (t₀ : K) :
    ∀ s ∈ gensU1 σ t₀, s ^ 4 = 1 := by
  simp only [gensU1, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [pow_four_eq_one (sq_eq_one_of_coe h2 coe_slT1 nT1_sq),
    pow_four_eq_one (u01_sq h2 σ 1), pow_four_eq_one (u01_sq h2 σ t₀),
    pow_four_eq_one (u10_sq h2 σ 1), pow_four_eq_one (u10_sq h2 σ t₀),
    pow_four_eq_one (u24_sq h2 σ 1), pow_four_eq_one (u24_sq h2 σ t₀),
    pow_four_eq_one (u50_sq h2 σ t₀)]

theorem commutantU1 {R : Type*} [CommRing R] {B : Matrix (Fin 6) (Fin 6) R}
    (h0 : B * E R 2 3 = E R 2 3 * B)
    (h1 : B * E R 0 1 = E R 0 1 * B)
    (h2 : B * E R 1 0 = E R 1 0 * B)
    (h3 : B * E R 4 5 = E R 4 5 * B)
    (h4 : B * E R 2 4 = E R 2 4 * B)
    (h5 : B * E R 5 0 = E R 5 0 * B) :
    B = B 2 2 • (1 : Matrix (Fin 6) (Fin 6) R) + B 2 3 • E R 2 3 := by
  have f20 : B 2 0 = 0 := col_eq_zero h1 (i := 2) (by decide)
  have f21 : B 2 1 = 0 := col_eq_zero h2 (i := 2) (by decide)
  have f24 : B 2 4 = 0 := col_eq_zero h3 (i := 2) (by decide)
  have f25 : B 2 5 = 0 := col_eq_zero h5 (i := 2) (by decide)
  have f32 : B 3 2 = 0 := col_eq_zero h0 (i := 3) (by decide)
  have f33 : B 3 3 = B 2 2 := (diag_eq h0).symm
  have f30 : B 3 0 = 0 := row_eq_zero h0 (j := 0) (by decide)
  have f31 : B 3 1 = 0 := row_eq_zero h0 (j := 1) (by decide)
  have f34 : B 3 4 = 0 := row_eq_zero h0 (j := 4) (by decide)
  have f35 : B 3 5 = 0 := row_eq_zero h0 (j := 5) (by decide)
  have f02 : B 0 2 = 0 := col_eq_zero h0 (i := 0) (by decide)
  have f03 : B 0 3 = 0 := row_eq_zero h2 (j := 3) (by decide)
  have f00 : B 0 0 = B 2 2 := (diag_eq h5).symm |>.trans (diag_eq h3).symm
      |>.trans (diag_eq h4).symm
  have f01 : B 0 1 = 0 := col_eq_zero h2 (i := 0) (by decide)
  have f04 : B 0 4 = 0 := row_eq_zero h2 (j := 4) (by decide)
  have f05 : B 0 5 = 0 := row_eq_zero h2 (j := 5) (by decide)
  have f12 : B 1 2 = 0 := col_eq_zero h0 (i := 1) (by decide)
  have f13 : B 1 3 = 0 := row_eq_zero h1 (j := 3) (by decide)
  have f10 : B 1 0 = 0 := col_eq_zero h1 (i := 1) (by decide)
  have f11 : B 1 1 = B 2 2 := (diag_eq h1).symm |>.trans (diag_eq h5).symm
      |>.trans (diag_eq h3).symm |>.trans (diag_eq h4).symm
  have f14 : B 1 4 = 0 := row_eq_zero h1 (j := 4) (by decide)
  have f15 : B 1 5 = 0 := row_eq_zero h1 (j := 5) (by decide)
  have f42 : B 4 2 = 0 := col_eq_zero h0 (i := 4) (by decide)
  have f43 : B 4 3 = 0 := row_eq_zero h4 (j := 3) (by decide)
  have f40 : B 4 0 = 0 := col_eq_zero h1 (i := 4) (by decide)
  have f41 : B 4 1 = 0 := col_eq_zero h2 (i := 4) (by decide)
  have f44 : B 4 4 = B 2 2 := (diag_eq h4).symm
  have f45 : B 4 5 = 0 := row_eq_zero h4 (j := 5) (by decide)
  have f52 : B 5 2 = 0 := col_eq_zero h0 (i := 5) (by decide)
  have f53 : B 5 3 = 0 := row_eq_zero h3 (j := 3) (by decide)
  have f50 : B 5 0 = 0 := col_eq_zero h1 (i := 5) (by decide)
  have f51 : B 5 1 = 0 := col_eq_zero h2 (i := 5) (by decide)
  have f54 : B 5 4 = 0 := col_eq_zero h3 (i := 5) (by decide)
  have f55 : B 5 5 = B 2 2 := (diag_eq h3).symm |>.trans (diag_eq h4).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, f00, f01, f02, f03, f04, f05, f10, f11, f12, f13,
      f14, f15, f20, f21, f24, f25, f30, f31, f32, f33, f34, f35, f40, f41, f42, f43, f44, f45,
      f50, f51, f52, f53, f54, f55]

theorem gensU1_commutant (h2 : (2 : K) = 0) {σ : K →+* K} {t₀ : K} (ht₀ : t₀ + σ t₀ = 1)
    (B : SpecialLinearGroup (Fin 6) K) (hB : ∀ s ∈ gensU1 σ t₀, B * s = s * B) :
    (B : Matrix (Fin 6) (Fin 6) K) = B 2 2 • (1 : Matrix (Fin 6) (Fin 6) K) + B 2 3 • nT1 := by
  have c0 := comm_of_comm_one_add coe_slT1 (hB _ (by simp [gensU1]))
  have c1 := comm_of_comm_one_add (coe_u01 σ 1) (hB _ (by simp [gensU1]))
  have c2 := comm_of_comm_one_add (coe_u01 σ t₀) (hB _ (by simp [gensU1]))
  have c3 := comm_of_comm_one_add (coe_u10 σ 1) (hB _ (by simp [gensU1]))
  have c4 := comm_of_comm_one_add (coe_u10 σ t₀) (hB _ (by simp [gensU1]))
  have c5 := comm_of_comm_one_add (coe_u24 σ 1) (hB _ (by simp [gensU1]))
  have c6 := comm_of_comm_one_add (coe_u24 σ t₀) (hB _ (by simp [gensU1]))
  have c7 := comm_of_comm_one_add (coe_u50 σ t₀) (hB _ (by simp [gensU1]))
  rw [map_one] at c1 c3 c5
  rw [← single_add, ht₀] at c7
  exact commutantU1 c0 (comm_of_pair h2 ht₀ c1 c2).1 (comm_of_pair h2 ht₀ c3 c4).1
    (comm_of_pair h2 ht₀ c1 c2).2 (comm_of_pair h2 ht₀ c5 c6).1 c7

@[expose] def gensU2 (σ : K →+* K) (t₀ : K) : List (SpecialLinearGroup (Fin 6) K) :=
  [u04 σ 1, u40 σ 1, u02 σ 1, u02 σ t₀, u03 σ 1, u03 σ t₀, u01 σ 1, u01 σ t₀]

theorem gensU2_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (t₀ : K) :
    ∀ s ∈ gensU2 σ t₀, s ∈ unitarySL σ := by
  simp only [gensU2, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [u04_mem h2 hσσ 1, u40_mem h2 hσσ 1, u02_mem h2 hσσ 1, u02_mem h2 hσσ t₀,
    u03_mem h2 hσσ 1, u03_mem h2 hσσ t₀, u01_mem h2 hσσ 1, u01_mem h2 hσσ t₀]

theorem gensU2_comm (σ : K →+* K) (t₀ : K) : ∀ s ∈ gensU2 σ t₀, s * sl2 = sl2 * s := by
  have hc : ∀ {s : SpecialLinearGroup (Fin 6) K} {M : Matrix (Fin 6) (Fin 6) K},
      (s : Matrix (Fin 6) (Fin 6) K) = 1 + M → M * nMat2 K = nMat2 K * M → s * sl2 = sl2 * s :=
    fun hs h => comm_of_coe hs coe_sl2 h
  simp only [gensU2, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact hc (coe_u04 σ 1) (by simp [nMat2, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u40 σ 1) (by simp [nMat2, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u02 σ 1) (by simp [nMat2, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u02 σ t₀) (by simp [nMat2, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u03 σ 1) (by simp [nMat2, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u03 σ t₀) (by simp [nMat2, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u01 σ 1) (by simp [nMat2, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u01 σ t₀) (by simp [nMat2, E, Matrix.add_mul, Matrix.mul_add])

theorem gensU2_pow (h2 : (2 : K) = 0) (σ : K →+* K) (t₀ : K) :
    ∀ s ∈ gensU2 σ t₀, s ^ 4 = 1 := by
  simp only [gensU2, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [pow_four_eq_one (u04_sq h2 σ 1), pow_four_eq_one (u40_sq h2 σ 1),
    pow_four_eq_one (u02_sq h2 σ 1), pow_four_eq_one (u02_sq h2 σ t₀),
    pow_four_eq_one (u03_sq h2 σ 1), pow_four_eq_one (u03_sq h2 σ t₀),
    pow_four_eq_one (u01_sq h2 σ 1), pow_four_eq_one (u01_sq h2 σ t₀)]

theorem gensU2_commutant (h2 : (2 : K) = 0) {σ : K →+* K} {t₀ : K} (ht₀ : t₀ + σ t₀ = 1)
    (B : SpecialLinearGroup (Fin 6) K) (hB : ∀ s ∈ gensU2 σ t₀, B * s = s * B) :
    (B : Matrix (Fin 6) (Fin 6) K) = B 0 0 • (1 : Matrix (Fin 6) (Fin 6) K) + B 0 1 • nMat2 K := by
  have c0 := comm_of_comm_one_add (coe_u04 σ 1) (hB _ (by simp [gensU2]))
  have c1 := comm_of_comm_one_add (coe_u40 σ 1) (hB _ (by simp [gensU2]))
  have c2 := comm_of_comm_one_add (coe_u02 σ 1) (hB _ (by simp [gensU2]))
  have c3 := comm_of_comm_one_add (coe_u02 σ t₀) (hB _ (by simp [gensU2]))
  have c4 := comm_of_comm_one_add (coe_u03 σ 1) (hB _ (by simp [gensU2]))
  have c5 := comm_of_comm_one_add (coe_u03 σ t₀) (hB _ (by simp [gensU2]))
  have c6 := comm_of_comm_one_add (coe_u01 σ 1) (hB _ (by simp [gensU2]))
  have c7 := comm_of_comm_one_add (coe_u01 σ t₀) (hB _ (by simp [gensU2]))
  rw [map_one] at c0 c1 c2 c4 c6
  exact commutant2 c0 c1 (comm_of_pair h2 ht₀ c2 c3).1 (comm_of_pair h2 ht₀ c4 c5).1
    (comm_of_pair h2 ht₀ c6 c7).1

abbrev upP : Matrix (Fin 6) (Fin 6) K := E K 0 2 + E K 1 3

abbrev upQ : Matrix (Fin 6) (Fin 6) K := E K 2 4 + E K 3 5

abbrev upD : Matrix (Fin 6) (Fin 6) K := E K 0 4 + E K 1 5

abbrev loP : Matrix (Fin 6) (Fin 6) K := E K 2 0 + E K 3 1

abbrev loQ : Matrix (Fin 6) (Fin 6) K := E K 4 2 + E K 5 3

abbrev loD : Matrix (Fin 6) (Fin 6) K := E K 4 0 + E K 5 1

@[expose] def xPlus (σ : K →+* K) (t₀ c : K) : SpecialLinearGroup (Fin 6) K :=
  u02 σ c * u13 σ c * u04 σ (t₀ * (c * σ c))

@[expose] def xMinus (σ : K →+* K) (t₀ c : K) : SpecialLinearGroup (Fin 6) K :=
  u20 σ c * u31 σ c * u40 σ (t₀ * (c * σ c))

theorem coe_xPlus (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) {t₀ : K}
    (ht₀ : t₀ + σ t₀ = 1) (c : K) :
    ((xPlus σ t₀ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (c • upP + σ c • upQ + σ (t₀ * (c * σ c)) • upD) := by
  have he : c * σ c + t₀ * (c * σ c) = σ (t₀ * (c * σ c)) := by
    rw [map_mul, map_mul, hσσ]
    linear_combination (-(c * σ c)) * ht₀ + (c * σ c * t₀) * h2
  rw [xPlus, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_u02,
    coe_u13, coe_u04]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  simp only [single_mul_single_same, single_mul_single_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, add_zero, Matrix.zero_mul]
  simp only [upP, upQ, upD, E, smul_add, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [← he, single_add, single_add]
  abel

theorem coe_xMinus (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) {t₀ : K}
    (ht₀ : t₀ + σ t₀ = 1) (c : K) :
    ((xMinus σ t₀ c : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (c • loP + σ c • loQ + (t₀ * (c * σ c)) • loD) := by
  have he : σ c * c + σ (t₀ * (c * σ c)) = t₀ * (c * σ c) := by
    rw [map_mul, map_mul, hσσ]
    linear_combination (-(σ c * c)) * ht₀ + (σ c * c * σ t₀) * h2
  rw [xMinus, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_u20,
    coe_u31, coe_u40]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  simp only [single_mul_single_same, single_mul_single_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, add_zero, Matrix.zero_mul]
  simp only [loP, loQ, loD, E, smul_add, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [show single (5 : Fin 6) (1 : Fin 6) (t₀ * (c * σ c)) =
    single 5 1 (σ c * c) + single 5 1 (σ (t₀ * (c * σ c))) by rw [← single_add, he]]
  abel

theorem xPlus_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (t₀ c : K) :
    xPlus σ t₀ c ∈ unitarySL σ :=
  mul_mem (mul_mem (u02_mem h2 hσσ c) (u13_mem h2 hσσ c)) (u04_mem h2 hσσ _)

theorem xMinus_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (t₀ c : K) :
    xMinus σ t₀ c ∈ unitarySL σ :=
  mul_mem (mul_mem (u20_mem h2 hσσ c) (u31_mem h2 hσσ c)) (u40_mem h2 hσσ _)

@[expose] def gensU3 (σ : K →+* K) (t₀ : K) : List (SpecialLinearGroup (Fin 6) K) :=
  [u04 σ 1, u40 σ 1, xPlus σ t₀ 1, xPlus σ t₀ t₀, xMinus σ t₀ 1, xMinus σ t₀ t₀, u01 σ 1,
    u01 σ t₀]

theorem gensU3_mem (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (t₀ : K) :
    ∀ s ∈ gensU3 σ t₀, s ∈ unitarySL σ := by
  simp only [gensU3, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [u04_mem h2 hσσ 1, u40_mem h2 hσσ 1, xPlus_mem h2 hσσ t₀ 1, xPlus_mem h2 hσσ t₀ t₀,
    xMinus_mem h2 hσσ t₀ 1, xMinus_mem h2 hσσ t₀ t₀, u01_mem h2 hσσ 1, u01_mem h2 hσσ t₀]

theorem upP_comm : (upP : Matrix (Fin 6) (Fin 6) K) * nMat3 K = nMat3 K * upP := by
  simp [nMat3, E, Matrix.add_mul, Matrix.mul_add]

theorem upQ_comm : (upQ : Matrix (Fin 6) (Fin 6) K) * nMat3 K = nMat3 K * upQ := by
  simp [nMat3, E, Matrix.add_mul, Matrix.mul_add]

theorem upD_comm : (upD : Matrix (Fin 6) (Fin 6) K) * nMat3 K = nMat3 K * upD := by
  simp [nMat3, E, Matrix.add_mul, Matrix.mul_add]

theorem loP_comm : (loP : Matrix (Fin 6) (Fin 6) K) * nMat3 K = nMat3 K * loP := by
  simp [nMat3, E, Matrix.add_mul, Matrix.mul_add]

theorem loQ_comm : (loQ : Matrix (Fin 6) (Fin 6) K) * nMat3 K = nMat3 K * loQ := by
  simp [nMat3, E, Matrix.add_mul, Matrix.mul_add]

theorem loD_comm : (loD : Matrix (Fin 6) (Fin 6) K) * nMat3 K = nMat3 K * loD := by
  simp [nMat3, E, Matrix.add_mul, Matrix.mul_add]

theorem comm_three {X Y Z N : Matrix (Fin 6) (Fin 6) K} (a b d : K) (hX : X * N = N * X)
    (hY : Y * N = N * Y) (hZ : Z * N = N * Z) :
    (a • X + b • Y + d • Z) * N = N * (a • X + b • Y + d • Z) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hX, hY, hZ]

theorem gensU3_comm (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) {t₀ : K}
    (ht₀ : t₀ + σ t₀ = 1) : ∀ s ∈ gensU3 σ t₀, s * sl3 = sl3 * s := by
  have hc : ∀ {s : SpecialLinearGroup (Fin 6) K} {M : Matrix (Fin 6) (Fin 6) K},
      (s : Matrix (Fin 6) (Fin 6) K) = 1 + M → M * nMat3 K = nMat3 K * M → s * sl3 = sl3 * s :=
    fun hs h => comm_of_coe hs coe_sl3 h
  simp only [gensU3, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact hc (coe_u04 σ 1) (by simp [nMat3, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u40 σ 1) (by simp [nMat3, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_xPlus h2 hσσ ht₀ 1) (comm_three _ _ _ upP_comm upQ_comm upD_comm)
  · exact hc (coe_xPlus h2 hσσ ht₀ t₀) (comm_three _ _ _ upP_comm upQ_comm upD_comm)
  · exact hc (coe_xMinus h2 hσσ ht₀ 1) (comm_three _ _ _ loP_comm loQ_comm loD_comm)
  · exact hc (coe_xMinus h2 hσσ ht₀ t₀) (comm_three _ _ _ loP_comm loQ_comm loD_comm)
  · exact hc (coe_u01 σ 1) (by simp [nMat3, E, Matrix.add_mul, Matrix.mul_add])
  · exact hc (coe_u01 σ t₀) (by simp [nMat3, E, Matrix.add_mul, Matrix.mul_add])

theorem upMM (a b d : K) :
    (a • upP + b • upQ + d • upD : Matrix (Fin 6) (Fin 6) K) * (a • upP + b • upQ + d • upD) =
      (a * b) • upD := by
  simp only [upP, upQ, upD, E, smul_add, Matrix.smul_single, smul_eq_mul, mul_one,
    Matrix.add_mul, Matrix.mul_add]
  simp only [single_mul_single_same, single_mul_single_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, add_zero, zero_add]

theorem loMM (a b d : K) :
    (a • loP + b • loQ + d • loD : Matrix (Fin 6) (Fin 6) K) * (a • loP + b • loQ + d • loD) =
      (b * a) • loD := by
  simp only [loP, loQ, loD, E, smul_add, Matrix.smul_single, smul_eq_mul, mul_one,
    Matrix.add_mul, Matrix.mul_add]
  simp only [single_mul_single_same, single_mul_single_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true, add_zero, zero_add]

theorem upD_sq (a : K) : (a • upD : Matrix (Fin 6) (Fin 6) K) * (a • upD) = 0 := by
  simp [upD, E, Matrix.add_mul, Matrix.mul_add]

theorem loD_sq (a : K) : (a • loD : Matrix (Fin 6) (Fin 6) K) * (a • loD) = 0 := by
  simp [loD, E, Matrix.add_mul, Matrix.mul_add]

theorem gensU3_pow (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) {t₀ : K}
    (ht₀ : t₀ + σ t₀ = 1) : ∀ s ∈ gensU3 σ t₀, s ^ 4 = 1 := by
  simp only [gensU3, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact pow_four_eq_one (u04_sq h2 σ 1)
  · exact pow_four_eq_one (u40_sq h2 σ 1)
  · exact pow_four_eq_one_of_coe h2 (coe_xPlus h2 hσσ ht₀ 1) (by rw [upMM, upD_sq])
  · exact pow_four_eq_one_of_coe h2 (coe_xPlus h2 hσσ ht₀ t₀) (by rw [upMM, upD_sq])
  · exact pow_four_eq_one_of_coe h2 (coe_xMinus h2 hσσ ht₀ 1) (by rw [loMM, loD_sq])
  · exact pow_four_eq_one_of_coe h2 (coe_xMinus h2 hσσ ht₀ t₀) (by rw [loMM, loD_sq])
  · exact pow_four_eq_one (u01_sq h2 σ 1)
  · exact pow_four_eq_one (u01_sq h2 σ t₀)

theorem comm_of_three {B X Y Z : Matrix (Fin 6) (Fin 6) K} {a b d : K}
    (h : B * (a • X + b • Y + d • Z) = (a • X + b • Y + d • Z) * B) (hZ : B * Z = Z * B) :
    B * (a • X + b • Y) = (a • X + b • Y) * B := by
  have e : a • X + b • Y = (1 : K) • (a • X + b • Y + d • Z) + (-d) • Z := by
    rw [one_smul, neg_smul, add_neg_cancel_right]
  rw [e]
  exact comm_smul_add _ h (by rw [Matrix.mul_smul, Matrix.smul_mul, hZ])

theorem gensU3_commutant (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) {t₀ : K}
    (ht₀ : t₀ + σ t₀ = 1)
    (B : SpecialLinearGroup (Fin 6) K) (hB : ∀ s ∈ gensU3 σ t₀, B * s = s * B) :
    (B : Matrix (Fin 6) (Fin 6) K) = B 0 0 • (1 : Matrix (Fin 6) (Fin 6) K) + B 0 1 • nMat3 K := by
  have c0 := comm_of_comm_one_add (coe_u04 σ 1) (hB _ (by simp [gensU3]))
  have c1 := comm_of_comm_one_add (coe_u40 σ 1) (hB _ (by simp [gensU3]))
  have c2 := comm_of_comm_one_add (coe_xPlus h2 hσσ ht₀ 1) (hB _ (by simp [gensU3]))
  have c3 := comm_of_comm_one_add (coe_xPlus h2 hσσ ht₀ t₀) (hB _ (by simp [gensU3]))
  have c4 := comm_of_comm_one_add (coe_xMinus h2 hσσ ht₀ 1) (hB _ (by simp [gensU3]))
  have c5 := comm_of_comm_one_add (coe_xMinus h2 hσσ ht₀ t₀) (hB _ (by simp [gensU3]))
  have c6 := comm_of_comm_one_add (coe_u01 σ 1) (hB _ (by simp [gensU3]))
  have c7 := comm_of_comm_one_add (coe_u01 σ t₀) (hB _ (by simp [gensU3]))
  rw [map_one] at c0 c1 c6
  have hD : (B : Matrix (Fin 6) (Fin 6) K) * upD = upD * (B : Matrix (Fin 6) (Fin 6) K) := c0
  have hD' : (B : Matrix (Fin 6) (Fin 6) K) * loD = loD * (B : Matrix (Fin 6) (Fin 6) K) := c1
  have p1 := comm_of_three c2 hD
  have p2 := comm_of_three c3 hD
  have q1 := comm_of_three c4 hD'
  have q2 := comm_of_three c5 hD'
  rw [map_one, one_smul, one_smul] at p1 q1
  exact commutant3 (comm_of_pair' h2 ht₀ p1 p2).1 (comm_of_pair' h2 ht₀ q1 q2).1 hD
    (comm_of_pair h2 ht₀ c6 c7).1

theorem realize_slT1
    (h2 : (2 : K) = 0) :
    realize h2 slT1 = pinnedX TwistTag.E6.tag K (Pi.single (e6Idx 3) 1) 1 :=
  realize_trv h2 2

theorem eq_one_or_eq_slT1
    (h2 : (2 : K) = 0) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2)
    (hσσ : ∀ c, σ (σ c) = c) {t₀ : K} (ht₀ : t₀ + σ t₀ = 1) {w : ModGL TwistTag.E6.tag K}
    (hw : w ∈ (unitarySL σ).map (realize h2))
    (hc : ∀ c ∈ (unitarySL σ).map (realize h2), c * realize h2 slT1 = realize h2 slT1 * c →
      w * c = c * w) :
    w = 1 ∨ w = realize h2 slT1 :=
  eq_one_or_eq_of_commutantU h2 hσ coe_slT1 (gensU1 σ t₀) (gensU1_mem h2 hσσ t₀)
    (gensU1_comm σ t₀) (gensU1_pow h2 σ t₀) (fun B hB => ⟨_, _, gensU1_commutant h2 ht₀ B hB⟩)
    (fun _ hB _ _ hab => unitary_coeffs_T1 hB hab) hw hc

theorem eq_one_or_eq_sl2
    (h2 : (2 : K) = 0) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2)
    (hσσ : ∀ c, σ (σ c) = c) {t₀ : K} (ht₀ : t₀ + σ t₀ = 1) {w : ModGL TwistTag.E6.tag K}
    (hw : w ∈ (unitarySL σ).map (realize h2))
    (hc : ∀ c ∈ (unitarySL σ).map (realize h2), c * realize h2 sl2 = realize h2 sl2 * c →
      w * c = c * w) :
    w = 1 ∨ w = realize h2 sl2 :=
  eq_one_or_eq_of_commutantU h2 hσ coe_sl2 (gensU2 σ t₀) (gensU2_mem h2 hσσ t₀)
    (gensU2_comm σ t₀) (gensU2_pow h2 σ t₀) (fun B hB => ⟨_, _, gensU2_commutant h2 ht₀ B hB⟩)
    (fun _ hB _ _ hab => unitary_coeffs_23 hB (Or.inl rfl) hab) hw hc

theorem eq_one_or_eq_sl3
    (h2 : (2 : K) = 0) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2)
    (hσσ : ∀ c, σ (σ c) = c) {t₀ : K} (ht₀ : t₀ + σ t₀ = 1) {w : ModGL TwistTag.E6.tag K}
    (hw : w ∈ (unitarySL σ).map (realize h2))
    (hc : ∀ c ∈ (unitarySL σ).map (realize h2), c * realize h2 sl3 = realize h2 sl3 * c →
      w * c = c * w) :
    w = 1 ∨ w = realize h2 sl3 :=
  eq_one_or_eq_of_commutantU h2 hσ coe_sl3 (gensU3 σ t₀) (gensU3_mem h2 hσσ t₀)
    (gensU3_comm h2 hσσ ht₀) (gensU3_pow h2 hσσ ht₀)
    (fun B hB => ⟨_, _, gensU3_commutant h2 hσσ ht₀ B hB⟩)
    (fun _ hB _ _ hab => unitary_coeffs_23 hB (Or.inr rfl) hab) hw hc

end CFSG.LieType.Chevalley.E6EvenInvolution
