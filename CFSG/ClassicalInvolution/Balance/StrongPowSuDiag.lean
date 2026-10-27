module

public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearDiag
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutInvolution

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (coordSet mem_coordSet exists_third
  mapGL coe_mapGL coe_mapGL_inv exists_pair_same)
open CFSG.ClassicalInvolution.RouteD.Gaps (diagGL exists_diagGL_of_offdiag_zero coe_diagGL)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

omit [Finite K] [CharP K p] in
theorem unitaryFieldData_of_card (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    UnitaryFieldData p f K := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  exact ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩

theorem bar_eq_unitaryInvolution (h : UnitaryFieldData p f K) (c : K) :
    h.bar c = unitaryInvolution K p f c := by
  rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]

theorem mem_SUid_of_mem_gramSU (hK : Nat.card K = (p ^ f) ^ 2) (h : UnitaryFieldData p f K)
    {M : GL (Fin n) K} (hM : M ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU h
      (1 : Matrix (Fin n) (Fin n) K)) : M ∈ SUid (unitaryInvolution K p f) n := by
  have : M ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K n := by
    rw [CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU h]
    exact hM
  rw [SUid_eq_statedSU hK n]
  exact this

theorem exists_torEl (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {c : K}
    (hc : unitaryInvolution K p f c * c = 1) {i j : Fin n} (hij : i ≠ j) :
    ∃ t : Su K p f n, ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (unitLambdaDiag c i j) := by
  have h := unitaryFieldData_of_card hK hq
  have hc' : h.bar c * c = 1 := by rw [bar_eq_unitaryInvolution]; exact hc
  obtain ⟨M, hM, hMmem⟩ := unitLambdaDiag_mem h hc' hij
  exact ⟨⟨M, mem_SUid_of_mem_gramSU hK h hMmem⟩, hM⟩

theorem exists_swapEl (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {i j : Fin n}
    (hij : i ≠ j) :
    ∃ w : Su K p f n, ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      unitSignedSwapMatrix i j := by
  have h := unitaryFieldData_of_card hK hq
  obtain ⟨M, hM, hMmem⟩ := unitSignedSwapMatrix_mem h hij
  exact ⟨⟨M, mem_SUid_of_mem_gramSU hK h hMmem⟩, hM⟩

theorem torEl_mem {J : Finset (Fin n)} {t : Su K p f n} {c : K} {i j : Fin n} (hi : i ∈ J)
    (hj : j ∈ J)
    (ht : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal (unitLambdaDiag c i j)) :
    t ∈ coordBlockSU K p f J := by
  rw [mem_coordBlockSU_iff]
  intro r s hrs
  rw [ht, diagonal_apply]
  by_cases hrs' : r = s
  · subst hrs'
    have hr : r ∉ J := by rcases hrs with h | h <;> exact h
    have h1 : r ≠ i := fun h => hr (h ▸ hi)
    have h2 : r ≠ j := fun h => hr (h ▸ hj)
    simp [unitLambdaDiag, h1, h2]
  · simp [hrs']

omit [Finite K] in
theorem unitSignedSwapMatrix_apply'' (i j : Fin n) (a b : Fin n) :
    (unitSignedSwapMatrix i j : Matrix (Fin n) (Fin n) K) a b =
      if Equiv.swap i j a = b then (if a = i then -1 else 1) else 0 := by
  rw [unitSignedSwapMatrix, Matrix.diagonal_mul]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem swapEl_mem {J : Finset (Fin n)} {w : Su K p f n} {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J)
    (hw : ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = unitSignedSwapMatrix i j) :
    w ∈ coordBlockSU K p f J := by
  rw [mem_coordBlockSU_iff]
  intro r s hrs
  rw [hw, unitSignedSwapMatrix_apply'']
  by_cases hr : r = i ∨ r = j
  · have hrJ : r ∈ J := by rcases hr with rfl | rfl <;> assumption
    have hsJ : s ∉ J := by rcases hrs with h | h; exact absurd hrJ h; exact h
    have hsw : Equiv.swap i j r ∈ J := by
      rcases hr with rfl | rfl
      · simpa using hj
      · simpa using hi
    have hne : Equiv.swap i j r ≠ s := fun h => hsJ (h ▸ hsw)
    have hrs' : r ≠ s := fun h => hsJ (h ▸ hrJ)
    simp [hne, hrs']
  · push Not at hr
    rw [Equiv.swap_apply_of_ne_of_ne hr.1 hr.2]
    simp [hr.1]


omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem diag_entry_eq {g : Matrix (Fin n) (Fin n) K} {φ : K ≃+* K} {d : Fin n → K}
    (h : g * φ.mapMatrix (diagonal d) = diagonal d * g) {i k : Fin n} (hk : g k i ≠ 0) :
    d k = φ (d i) := by
  have h1 := congrFun (congrFun h k) i
  rw [RingEquiv.mapMatrix_apply, Matrix.diagonal_map (map_zero φ), Matrix.mul_diagonal,
    Matrix.diagonal_mul] at h1
  exact mul_left_cancel₀ hk (by rw [mul_comm (g k i) (d k)]; exact h1.symm)

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem exists_entry_ne_zero (g : GL (Fin n) K) (i : Fin n) :
    ∃ k, (g : Matrix (Fin n) (Fin n) K) k i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := congrFun (congrFun (Units.inv_mul g) i) i
  rw [Matrix.mul_apply] at h1
  simp [hcon] at h1

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem comm_of_fixed {g : GL (Fin n) K} {φ : K ≃+* K} {x y : Matrix (Fin n) (Fin n) K}
    (h : y = (g : Matrix (Fin n) (Fin n) K) * φ.mapMatrix x *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    (g : Matrix (Fin n) (Fin n) K) * φ.mapMatrix x = y * g := by
  have hgi : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul g
  rw [h, Matrix.mul_assoc, hgi, Matrix.mul_one]

theorem fixes_normOne_of_comm_torus (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) {g : GL (Fin n) K} {ψ : K ≃+* K}
    (h : ∀ (t : Su K p f n) (c : K) (i j : Fin n), i ≠ j → unitaryInvolution K p f c * c = 1 →
      ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal (unitLambdaDiag c i j) →
      (g : Matrix (Fin n) (Fin n) K) * ψ.mapMatrix ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g) :
    ∀ a : K, unitaryInvolution K p f a * a = 1 → ψ a = a := by
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1, map_one]
  have hn0 : 0 < n := by omega
  set i₀ : Fin n := ⟨0, hn0⟩ with hi₀
  obtain ⟨k₀, hk₀⟩ := exists_entry_ne_zero g i₀
  have hkk : k₀ = i₀ := by
    by_contra hne
    obtain ⟨j, hj1, hj2⟩ := exists_third hn i₀ k₀
    obtain ⟨t, ht⟩ := exists_torEl hK hq ha (i := i₀) (j := j) hj1.symm
    have e := h t a i₀ j hj1.symm ha ht
    rw [ht] at e
    have := diag_entry_eq e hk₀
    have h1 : unitLambdaDiag a i₀ j k₀ = 1 := by simp [unitLambdaDiag, hne, hj2.symm]
    have h2 : unitLambdaDiag a i₀ j i₀ = a := by simp [unitLambdaDiag]
    rw [h1, h2] at this
    exact ha1 (ψ.injective (by rw [map_one]; exact this.symm))
  rw [hkk] at hk₀
  obtain ⟨j, hj1, -⟩ := exists_third hn i₀ i₀
  obtain ⟨t, ht⟩ := exists_torEl hK hq ha (i := i₀) (j := j) hj1.symm
  have e := h t a i₀ j hj1.symm ha ht
  rw [ht] at e
  have := diag_entry_eq e hk₀
  have h2 : unitLambdaDiag a i₀ j i₀ = a := by simp [unitLambdaDiag]
  rw [h2] at this
  exact this.symm

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem phi_eq_or_inv {g : GL (Fin n) K} {φ : K ≃+* K} {a : K} (ha1 : a ≠ 1) {i j : Fin n}
    (hij : i ≠ j)
    (h : (g : Matrix (Fin n) (Fin n) K) * φ.mapMatrix (diagonal (unitLambdaDiag a i j)) =
      diagonal (unitLambdaDiag a i j) * g) : φ a = a ∨ φ a = a⁻¹ := by
  obtain ⟨k, hk⟩ := exists_entry_ne_zero g i
  have := diag_entry_eq h hk
  have h2 : unitLambdaDiag a i j i = a := by simp [unitLambdaDiag]
  rw [h2] at this
  by_cases hki : k = i
  · left
    rw [hki, h2] at this
    exact this.symm
  · by_cases hkj : k = j
    · right
      have h3 : unitLambdaDiag a i j k = a⁻¹ := by
        rw [hkj]
        simp [unitLambdaDiag, hij.symm]
      rw [h3] at this
      exact this.symm
    · exfalso
      have h3 : unitLambdaDiag a i j k = 1 := by simp [unitLambdaDiag, hki, hkj]
      rw [h3] at this
      exact ha1 (φ.injective (by rw [map_one]; exact this.symm))


theorem iterate_form (α : Su K p f n →* Su K p f n) (g : GL (Fin n) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f n, ((α x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) *
        φ.mapMatrix ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (k : ℕ) :
    ∃ (g' : GL (Fin n) K) (ψ : K ≃+* K), (∀ c, ψ c = φ^[k] c) ∧ ∀ x : Su K p f n,
      (((α^[k] x : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (g' : Matrix (Fin n) (Fin n) K) *
          ψ.mapMatrix ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((g'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  induction k with
  | zero => exact ⟨1, RingEquiv.refl K, fun c => rfl, fun x => by simp⟩
  | succ k ih =>
    obtain ⟨g', ψ, hψ, hx⟩ := ih
    have hmm : ∀ M : Matrix (Fin n) (Fin n) K,
        (ψ.trans φ).mapMatrix M = φ.mapMatrix (ψ.mapMatrix M) := fun M => by ext i j; rfl
    refine ⟨g * mapGL φ g', ψ.trans φ, fun c => ?_, fun x => ?_⟩
    · rw [Function.iterate_succ_apply']
      show φ (ψ c) = φ (φ^[k] c)
      rw [hψ]
    · rw [Function.iterate_succ_apply', hα, hx, hmm]
      simp only [Units.val_mul, _root_.mul_inv_rev, map_mul, coe_mapGL, coe_mapGL_inv,
        Matrix.mul_assoc]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem iterate_phi_odd {φ : K ≃+* K} {a : K} (h : φ a = a⁻¹) (r : ℕ) :
    φ^[2 * r + 1] a = a⁻¹ ∧ φ^[2 * r] a = a := by
  induction r with
  | zero => exact ⟨h, rfl⟩
  | succ r ih =>
    have e1 : 2 * (r + 1) = (2 * r + 1) + 1 := by ring
    have h1 : φ^[2 * (r + 1)] a = a := by
      rw [e1, Function.iterate_succ_apply', ih.1, map_inv₀, h, inv_inv]
    refine ⟨?_, h1⟩
    rw [Function.iterate_succ_apply', h1, h]

theorem ringEquiv_eq_refl_of_fix (hK : Nat.card K = (p ^ f) ^ 2) (φ : K ≃+* K)
    (hφ : ∀ a : K, unitaryInvolution K p f a * a = 1 → φ a = a) (c : K) : φ c = c := by
  obtain ⟨ζ, hζ, hord⟩ := CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq hK
  have hζφ : φ (ζ : K) = ζ := hφ ζ hζ
  let L : Subfield K := φ.toRingHom.eqLocusField (RingHom.id K)
  have hLmem : ∀ x, x ∈ L ↔ φ x = x := fun x => Iff.rfl
  have hcardK : Nat.card K = Nat.card L ^ Module.finrank L K := Module.natCard_eq_pow_finrank
  have hpow : ∀ k : ℕ, ((ζ : K) ^ k) ∈ L := fun k => by
    rw [hLmem, map_pow, hζφ]
  have hinj : Function.Injective
      (fun k : Fin (p ^ f + 1) => (⟨(ζ : K) ^ (k : ℕ), hpow k⟩ : L)) := by
    intro a b hab
    have h1 : (ζ : K) ^ (a : ℕ) = (ζ : K) ^ (b : ℕ) := congrArg Subtype.val hab
    have h2 : ζ ^ (a : ℕ) = ζ ^ (b : ℕ) := Units.ext h1
    have := pow_injOn_Iio_orderOf (x := ζ) (by rw [hord]; exact a.2) (by rw [hord]; exact b.2) h2
    exact Fin.ext this
  have hLge : p ^ f + 1 ≤ Nat.card L := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hfr : Module.finrank L K = 1 := by
    by_contra h
    have hpos : 0 < Module.finrank L K := Module.finrank_pos
    have h2 : 2 ≤ Module.finrank L K := by omega
    have h3 : Nat.card L ^ 2 ≤ Nat.card L ^ Module.finrank L K :=
      Nat.pow_le_pow_right (by omega) h2
    rw [← hcardK, hK] at h3
    have h4 : (p ^ f + 1) ^ 2 ≤ Nat.card L ^ 2 := Nat.pow_le_pow_left hLge 2
    have h5 : (p ^ f) ^ 2 < (p ^ f + 1) ^ 2 :=
      Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by norm_num)
    omega
  have hLtop : L = ⊤ := by
    rw [hfr, pow_one] at hcardK
    have h1 : Nat.card L.toAddSubgroup = Nat.card K := hcardK.symm
    have := AddSubgroup.eq_top_of_card_eq _ h1
    ext x
    simp only [Subfield.mem_top, iff_true]
    have hx : x ∈ L.toAddSubgroup := by rw [this]; trivial
    exact hx
  exact (hLmem c).mp (by rw [hLtop]; trivial)

theorem phi_fix (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hn : 3 ≤ n)
    (α : Su K p f n →* Su K p f n) (g : GL (Fin n) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f n, ((α x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) *
        φ.mapMatrix ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {J : Finset (Fin n)} (hJ : 2 ≤ J.card) (hfixJ : ∀ s ∈ coordBlockSU K p f J, α s = s)
    (hpow : ∃ m : ℕ, Odd m ∧ ∀ x, α^[m] x = x) : ∀ c, φ c = c := by
  have hμ : ∀ a : K, unitaryInvolution K p f a * a = 1 → φ a = a := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1, map_one]
    have hJ' : 1 < J.card := by omega
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hJ'
    obtain ⟨t, ht⟩ := exists_torEl hK hq ha hij
    have htJ : t ∈ coordBlockSU K p f J := torEl_mem hi hj ht
    have e : (g : Matrix (Fin n) (Fin n) K) *
        φ.mapMatrix ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g := by
      apply comm_of_fixed
      have := hα t
      rwa [hfixJ t htJ] at this
    rw [ht] at e
    rcases phi_eq_or_inv ha1 hij e with h | h
    · exact h
    · obtain ⟨m, hm, hαm⟩ := hpow
      obtain ⟨g', ψ, hψ, hx⟩ := iterate_form α g φ hα m
      obtain ⟨r, rfl⟩ := hm
      have hψa : ψ a = a⁻¹ := by rw [hψ]; exact (iterate_phi_odd h r).1
      have hcomm : ∀ (t : Su K p f n) (c : K) (i j : Fin n), i ≠ j →
          unitaryInvolution K p f c * c = 1 →
          ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal (unitLambdaDiag c i j) →
          (g' : Matrix (Fin n) (Fin n) K) *
            ψ.mapMatrix ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
              ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g' := by
        intro t c i j _ _ _
        apply comm_of_fixed
        have := hx t
        rwa [hαm t] at this
      have h3 := fixes_normOne_of_comm_torus hK hq hn hcomm a ha
      rw [h, ← hψa, h3]
  exact ringEquiv_eq_refl_of_fix hK φ hμ


omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem mapMatrix_eq_self {φ : K ≃+* K} (hφ : ∀ c, φ c = c) (M : Matrix (Fin n) (Fin n) K) :
    φ.mapMatrix M = M := by
  ext i j
  exact hφ _

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem offdiag_zero_of_comm_torus {g : Matrix (Fin n) (Fin n) K} {a : K} (ha1 : a ≠ 1)
    (hainv : a⁻¹ ≠ a) {i j : Fin n} (hij : i ≠ j)
    (e : g * diagonal (unitLambdaDiag a i j) = diagonal (unitLambdaDiag a i j) * g) {l : Fin n}
    (hl : l ≠ i) : g i l = 0 ∧ g l i = 0 := by
  have e1 := congrFun (congrFun e i) l
  have e2 := congrFun (congrFun e l) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e1 e2
  have hdi : unitLambdaDiag a i j i = a := by simp [unitLambdaDiag]
  have hdl : unitLambdaDiag a i j l ≠ a := by
    by_cases hlj : l = j
    · subst hlj
      have : unitLambdaDiag a i l l = a⁻¹ := by simp [unitLambdaDiag, hl]
      rw [this]
      exact hainv
    · have : unitLambdaDiag a i j l = 1 := by simp [unitLambdaDiag, hl, hlj]
      rw [this]
      exact fun h => ha1 h.symm
  rw [hdi] at e1 e2
  refine ⟨?_, ?_⟩
  · have : g i l * (unitLambdaDiag a i j l - a) = 0 := by linear_combination e1
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hdl)
  · have : g l i * (a - unitLambdaDiag a i j l) = 0 := by linear_combination e2
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hdl))

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem diag_eq_of_comm_swap {g : Matrix (Fin n) (Fin n) K} {i j : Fin n}
    (e : g * unitSignedSwapMatrix i j = unitSignedSwapMatrix i j * g) : g i i = g j j := by
  have h := congrFun (congrFun e i) j
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  have hw : (unitSignedSwapMatrix i j : Matrix (Fin n) (Fin n) K) i j = -1 := by
    simp [unitSignedSwapMatrix_apply'']
  have hL : ∑ r, g i r * (unitSignedSwapMatrix i j : Matrix (Fin n) (Fin n) K) r j =
      g i i * (unitSignedSwapMatrix i j : Matrix (Fin n) (Fin n) K) i j := by
    refine Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun r _ hr => ?_
    rw [unitSignedSwapMatrix_apply'']
    have : Equiv.swap i j r ≠ j := fun h' => hr (by
      have := (Equiv.swap i j).injective (h'.trans (Equiv.swap_apply_left i j).symm)
      exact this)
    simp [this]
  have hR : ∑ r, (unitSignedSwapMatrix i j : Matrix (Fin n) (Fin n) K) i r * g r j =
      (unitSignedSwapMatrix i j : Matrix (Fin n) (Fin n) K) i j * g j j := by
    refine Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun r _ hr => ?_
    rw [unitSignedSwapMatrix_apply'']
    have : j ≠ r := fun h' => hr h'.symm
    simp [this]
  rw [hL, hR, hw] at h
  linear_combination -h

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem exists_partner_of_card {σ : Fin n → Bool} {i : Fin n}
    (h : 2 ≤ (coordSet σ (σ i)).card) : ∃ j, j ≠ i ∧ σ j = σ i := by
  have h' : 1 < (coordSet σ (σ i)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h'
  by_cases hai : a = i
  · exact ⟨b, fun h => hab (hai.trans h.symm), (mem_coordSet.mp hb)⟩
  · exact ⟨a, hai, (mem_coordSet.mp ha)⟩


theorem diag_of_fixes_blocks_su (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) (σ : Fin n → Bool) (α : Su K p f n →* Su K p f n) (g : GL (Fin n) K)
    (φ : K ≃+* K)
    (hα : ∀ x : Su K p f n, ((α x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) *
        φ.mapMatrix ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hfix : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSU K p f (coordSet σ b), α s = s)
    (hpow : ∃ m : ℕ, Odd m ∧ ∀ x, α^[m] x = x) :
    (∀ c, φ c = c) ∧ ∃ u : Fin n → Kˣ, g = diagGL u ∧ ∀ i j, σ i = σ j → u i = u j := by
  have h := unitaryFieldData_of_card hK hq
  obtain ⟨i₀, j₀, hij₀, hσ₀⟩ := exists_pair_same hn σ
  have hcard₀ : 2 ≤ (coordSet σ (σ i₀)).card :=
    Finset.one_lt_card.mpr ⟨i₀, mem_coordSet.mpr rfl, j₀, mem_coordSet.mpr hσ₀.symm, hij₀⟩
  have hφ : ∀ c, φ c = c := phi_fix hK hq hn α g φ hα hcard₀ (hfix _ hcard₀) hpow
  have hcomm : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSU K p f (coordSet σ b),
      (g : Matrix (Fin n) (Fin n) K) * ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g := by
    intro b hb s hs
    have e := comm_of_fixed (g := g) (φ := φ) (x := ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (y := ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (by
        have := hα s
        rwa [hfix b hb s hs] at this)
    rwa [mapMatrix_eq_self hφ] at e
  obtain ⟨a, ha1, hainv⟩ := CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.exists_normOne_ne h hp2
  set c : K := ((a : Kˣ) : K) with hc
  have hcN : unitaryInvolution K p f c * c = 1 := (CFSG.LieType.Steinberg.mem_normOne _).1 a.2
  have hc1 : c ≠ 1 := ha1
  have hcinv : c⁻¹ ≠ c := by
    simpa [hc, Units.val_inv_eq_inv_val] using hainv
  have hblock : ∀ i : Fin n, 2 ≤ (coordSet σ (σ i)).card → ∀ l : Fin n, l ≠ i →
      (g : Matrix (Fin n) (Fin n) K) i l = 0 ∧ (g : Matrix (Fin n) (Fin n) K) l i = 0 := by
    intro i hi l hl
    obtain ⟨j, hji, hσj⟩ := exists_partner_of_card hi
    obtain ⟨t, ht⟩ := exists_torEl hK hq hcN (i := i) (j := j) hji.symm
    have htJ : t ∈ coordBlockSU K p f (coordSet σ (σ i)) :=
      torEl_mem (mem_coordSet.mpr rfl) (mem_coordSet.mpr hσj) ht
    have e := hcomm _ hi t htJ
    rw [ht] at e
    exact offdiag_zero_of_comm_torus hc1 hcinv hji.symm e hl
  have hoff : ∀ k l : Fin n, k ≠ l → (g : Matrix (Fin n) (Fin n) K) k l = 0 := by
    intro k l hkl
    by_cases hk : 2 ≤ (coordSet σ (σ k)).card
    · exact (hblock k hk l hkl.symm).1
    · by_cases hl : 2 ≤ (coordSet σ (σ l)).card
      · exact (hblock l hl k hkl).2
      · exfalso
        push Not at hk hl
        have hk1 : (coordSet σ (σ k)).card ≤ 1 := by omega
        have hl1 : (coordSet σ (σ l)).card ≤ 1 := by omega
        have hσ : σ k ≠ σ l := fun heq => by
          have := Finset.card_le_one.mp hk1 k (mem_coordSet.mpr rfl) l (mem_coordSet.mpr heq.symm)
          exact hkl this
        obtain ⟨t, htk, htl⟩ := exists_third hn k l
        have hcases : σ t = σ k ∨ σ t = σ l := by
          cases hk' : σ k <;> cases hl' : σ l <;> cases ht' : σ t <;> simp_all
        rcases hcases with h1 | h1
        · exact htk (Finset.card_le_one.mp hk1 t (mem_coordSet.mpr h1) k (mem_coordSet.mpr rfl))
        · exact htl (Finset.card_le_one.mp hl1 t (mem_coordSet.mpr h1) l (mem_coordSet.mpr rfl))
  obtain ⟨u, hu⟩ := exists_diagGL_of_offdiag_zero g hoff
  refine ⟨hφ, u, hu, fun i j hσ => ?_⟩
  by_cases hij : i = j
  · rw [hij]
  · have hcard : 2 ≤ (coordSet σ (σ i)).card :=
      Finset.one_lt_card.mpr ⟨i, mem_coordSet.mpr rfl, j, mem_coordSet.mpr hσ.symm, hij⟩
    obtain ⟨w, hw⟩ := exists_swapEl hK hq hij
    have hwJ : w ∈ coordBlockSU K p f (coordSet σ (σ i)) :=
      swapEl_mem (mem_coordSet.mpr rfl) (mem_coordSet.mpr hσ.symm) hw
    have e := hcomm _ hcard w hwJ
    rw [hw] at e
    have h1 := diag_eq_of_comm_swap e
    rw [hu, coe_diagGL, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h1
    exact Units.ext h1

end CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
