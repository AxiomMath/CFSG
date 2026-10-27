module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.TwoTorusField
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.SL2Odd

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

section Noncomm

variable {K : Type} [Field K]

theorem mkPSL_noncomm (h2 : (2 : K) ≠ 0) {E D : Matrix (Fin 2) (Fin 2) K}
    {A B : SpecialLinearGroup (Fin 2) K} (hAE : (A : Matrix (Fin 2) (Fin 2) K) * E = E * A)
    (hAs : ¬ ∃ e : K, (A : Matrix (Fin 2) (Fin 2) K) = e • (1 : Matrix (Fin 2) (Fin 2) K))
    {a b : K} (hb : b ≠ 0)
    (hBab : (B : Matrix (Fin 2) (Fin 2) K) = a • (1 : Matrix (Fin 2) (Fin 2) K) + b • D)
    (hB2 : ¬ ∃ e : K, (B : Matrix (Fin 2) (Fin 2) K) * B = e • (1 : Matrix (Fin 2) (Fin 2) K))
    (hDE : D * E ≠ E * D) :
    mkPSL K A * mkPSL K B ≠ mkPSL K B * mkPSL K A := by
  intro h
  have h' : mkPSL K (A * B) = mkPSL K (B * A) := by rw [map_mul, map_mul, h]
  rw [mkPSL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h'
  have hz := h'
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
  obtain ⟨r, hr, hzr⟩ := hz
  rw [Fintype.card_fin] at hr
  have hBA : (B : Matrix (Fin 2) (Fin 2) K) * A = r • ((A : Matrix (Fin 2) (Fin 2) K) * B) := by
    have h1 : (A * B) * ((A * B)⁻¹ * (B * A)) = B * A := by group
    have h2' : ((A * B * ((A * B)⁻¹ * (B * A)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = ((B * A : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by rw [h1]
    rw [Matrix.SpecialLinearGroup.coe_mul (A * B), ← hzr, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one] at h2'
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h2'
    rw [← h2']
  have hr' : r = 1 ∨ r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hr' with rfl | rfl
  ·
    rw [one_smul] at hBA
    have hcom : Commute (A : Matrix (Fin 2) (Fin 2) K) B := hBA.symm
    obtain ⟨a', b', hEab⟩ := comm_eq_smul_add hAs (by rw [← hAE])
    have hD : D = b⁻¹ • ((B : Matrix (Fin 2) (Fin 2) K) - a • (1 : Matrix (Fin 2) (Fin 2) K)) := by
      rw [hBab]
      simp [smul_smul, hb]
    apply hDE
    have h1 : Commute (A : Matrix (Fin 2) (Fin 2) K)
        ((B : Matrix (Fin 2) (Fin 2) K) - a • (1 : Matrix (Fin 2) (Fin 2) K)) :=
      hcom.sub_right ((Commute.one_right _).smul_right a)
    have hED : Commute E D := by
      rw [hEab, hD]
      exact (((Commute.one_left _).smul_left a').add_left (h1.smul_left b')).smul_right b⁻¹
    exact hED.symm
  ·
    exfalso
    apply hB2
    have hinv : ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hinv' : (A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h1 : ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((B : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K)) =
        -(B : Matrix (Fin 2) (Fin 2) K) := by
      rw [hBA, neg_smul, one_smul, Matrix.mul_neg, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have h2' : (B : Matrix (Fin 2) (Fin 2) K).trace = 0 := by
      have h3 : Matrix.trace (((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          ((B : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K))) = (B : Matrix (Fin 2) (Fin 2) K).trace := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc, hinv', Matrix.mul_one]
      rw [h1, Matrix.trace_neg] at h3
      have : (2 : K) * (B : Matrix (Fin 2) (Fin 2) K).trace = 0 := by linear_combination -h3
      exact (mul_eq_zero.1 this).resolve_left h2
    refine ⟨-1, ?_⟩
    have := mat2_mul_self (B : Matrix (Fin 2) (Fin 2) K)
    rw [h2', zero_smul, Matrix.SpecialLinearGroup.det_coe, one_smul, zero_sub] at this
    rw [this, neg_one_smul]

end Noncomm

section Helpers

theorem dihedral_comm {G : Type*} [Group G] {z : ℕ} (e : G ≃* DihedralGroup z) {x y : G}
    (hx : x * x ≠ 1) (hy : y * y ≠ 1) : x * y = y * x := by
  have key : ∀ g : G, g * g ≠ 1 → ∃ i, e g = DihedralGroup.r i := by
    intro g hg
    cases h : e g with
    | r i => exact ⟨i, rfl⟩
    | sr i =>
      exfalso
      apply hg
      apply e.injective
      rw [map_mul, h, DihedralGroup.sr_mul_self, map_one]
  obtain ⟨i, hi⟩ := key x hx
  obtain ⟨j, hj⟩ := key y hy
  apply e.injective
  rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]

variable {K : Type} [Field K]

theorem pow_two_mul_eq_one_of_center {A : SpecialLinearGroup (Fin 2) K} {k : ℕ}
    (h : A ^ k ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K)) : A ^ (2 * k) = 1 := by
  rw [mul_comm, pow_mul, sq]
  exact center_sq_eq_one h

theorem sq_scalar_of_pow_two_center {A : SpecialLinearGroup (Fin 2) K}
    (h : A ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K)) :
    ∃ e : K, (A : Matrix (Fin 2) (Fin 2) K) * A = e • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, -, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [← pow_two, ← Matrix.SpecialLinearGroup.coe_pow, ← hr, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem pow_four_of_sq_scalar {A : SpecialLinearGroup (Fin 2) K} {e : K}
    (h : (A : Matrix (Fin 2) (Fin 2) K) * A = e • (1 : Matrix (Fin 2) (Fin 2) K)) :
    A ^ 4 = 1 := by
  have hdet : e ^ 2 = 1 := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe] at this
    simpa [Matrix.det_smul] using this.symm
  apply Subtype.ext
  show ((A ^ 4 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two, Matrix.SpecialLinearGroup.coe_mul,
    pow_two, Matrix.SpecialLinearGroup.coe_mul, h, smul_mul_smul_comm, one_mul, ← pow_two, hdet,
    one_smul]

theorem card_le_four_mul_of_trace_sq [Finite K] (T : Subgroup (SpecialLinearGroup (Fin 2) K))
    (htr : ∀ s : K, ∀ A ∈ T, (A : Matrix (Fin 2) (Fin 2) K).trace = s → ∀ A' ∈ T,
      (A' : Matrix (Fin 2) (Fin 2) K).trace = s →
      A' = A ∨ (A' : Matrix (Fin 2) (Fin 2) K) = s • (1 : Matrix (Fin 2) (Fin 2) K) - A)
    (K₀ : Subfield K) (hK₀ : ∀ A ∈ T, (A : Matrix (Fin 2) (Fin 2) K).trace ^ 2 ∈ K₀) :
    Nat.card T ≤ 4 * Nat.card K₀ := by
  classical
  have : Fintype T := Fintype.ofFinite T
  have : Fintype K₀ := Fintype.ofFinite K₀
  let f : T → K₀ := fun A => ⟨(A : Matrix (Fin 2) (Fin 2) K).trace ^ 2, hK₀ A A.2⟩
  have hfib : ∀ u ∈ (Finset.univ : Finset T).image f,
      (Finset.univ.filter (fun A : T => f A = u)).card ≤ 4 := by
    intro u hu
    obtain ⟨A₀, -, rfl⟩ := Finset.mem_image.1 hu
    set s₀ := (A₀ : Matrix (Fin 2) (Fin 2) K).trace with hs₀
    obtain ⟨A₁, hA₁⟩ : ∃ A₁ : T, ∀ A : T, (A : Matrix (Fin 2) (Fin 2) K).trace = -s₀ →
        ((A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          ((A₁ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∨
        ((A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          (-s₀) • (1 : Matrix (Fin 2) (Fin 2) K) -
            ((A₁ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      by_cases hex : ∃ A₁ : T, (A₁ : Matrix (Fin 2) (Fin 2) K).trace = -s₀
      · obtain ⟨A₁, hA₁⟩ := hex
        refine ⟨A₁, fun A hA => ?_⟩
        rcases htr (-s₀) A₁ A₁.2 hA₁ A A.2 hA with h | h
        · left; rw [h]
        · right; exact h
      · simp only [not_exists] at hex
        exact ⟨A₀, fun A hA => absurd hA (hex A)⟩
    let S4 : Finset (Matrix (Fin 2) (Fin 2) K) :=
      {((A₀ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
       s₀ • (1 : Matrix (Fin 2) (Fin 2) K) -
         ((A₀ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
       ((A₁ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
       (-s₀) • (1 : Matrix (Fin 2) (Fin 2) K) -
         ((A₁ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}
    have hinj : Function.Injective (fun A : T =>
        ((A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
      intro A B h
      exact Subtype.ext (Subtype.ext h)
    have hsub : (Finset.univ.filter (fun A : T => f A = f A₀)).image
        (fun A : T => ((A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) ⊆ S4 := by
      intro M hM
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hM
      have hA' : (A : Matrix (Fin 2) (Fin 2) K).trace ^ 2 = s₀ ^ 2 := by
        have := congrArg Subtype.val (Finset.mem_filter.1 hA).2
        simpa [f, hs₀] using this
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hA' with h | h
      · rcases htr s₀ A₀ A₀.2 rfl A A.2 h with h' | h'
        · simp [S4, h']
        · simp [S4, h']
      · rcases hA₁ A h with h' | h'
        · simp [S4, h']
        · simp [S4, h']
    calc (Finset.univ.filter (fun A : T => f A = f A₀)).card
        = ((Finset.univ.filter (fun A : T => f A = f A₀)).image
          (fun A : T => ((A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ S4.card := Finset.card_le_card hsub
      _ ≤ 4 := Finset.card_le_four
  have h1 := Finset.card_le_mul_card_image (Finset.univ : Finset T) 4 hfib
  have h2 : ((Finset.univ : Finset T).image f).card ≤ Nat.card K₀ := by
    rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  exact h1.trans (Nat.mul_le_mul_left _ h2)

end Helpers

theorem num_aux (x N q : ℕ) (h1 : x ^ 2 ≤ q) (h2 : q + 1 ≤ N) (h3 : N ≤ 4 * x)
    (h4 : 27 ≤ q) : False := by
  have h7 : 7 ≤ x := by omega
  nlinarith

section Assembly

open CFSG.Glauberman.Dickson

variable {K : Type} [Field K] [Finite K]

theorem subfield_alternative_false {p m f : ℕ} [Fact p.Prime] (hm0 : 0 < m) (hp2 : p ≠ 2)
    (hF : Nat.card K = p ^ f) (hf : 2 * m ≤ f) (hK27 : 27 ≤ Nat.card K)
    (T : Subgroup (SpecialLinearGroup (Fin 2) K)) (M : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hTM : T ≤ M) (hTcard : Nat.card K + 1 ≤ Nat.card T)
    (hTtr : ∀ s : K, ∀ A ∈ T, (A : Matrix (Fin 2) (Fin 2) K).trace = s → ∀ A' ∈ T,
      (A' : Matrix (Fin 2) (Fin 2) K).trace = s →
      A' = A ∨ (A' : Matrix (Fin 2) (Fin 2) K) = s • (1 : Matrix (Fin 2) (Fin 2) K) - A)
    (h2 : (2 : K) ≠ 0)
    (W : SubfieldConjugacyWitness p m (M.map (mkPSL K))) : False := by
  have h2K : (2 : K) ∈ W.K := by simp
  have hK0 : ∀ A ∈ T, (A : Matrix (Fin 2) (Fin 2) K).trace ^ 2 ∈ W.K := by
    intro A hA
    by_cases hs : (A : Matrix (Fin 2) (Fin 2) K).trace = 0
    · rw [hs]; simp
    set s := (A : Matrix (Fin 2) (Fin 2) K).trace with hsdef
    have hmem : mkPSL K A ∈ M.map (mkPSL K) := Subgroup.mem_map_of_mem _ (hTM hA)
    have h := normalizedTrace_mem_subfield (M.map (mkPSL K)) W ⟨mkPSL K A, hmem⟩
      ⟨mkPSL K A, hmem⟩ A A rfl rfl hs hs
    have htr2 : Matrix.trace ((A * A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        s * s - 2 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, mat2_mul_self, Matrix.SpecialLinearGroup.det_coe,
        one_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
      simp [hsdef]
    rw [htr2] at h
    have e1 : (s * s - 2) / (s * s) = 1 - 2 / s ^ 2 := by field_simp
    rw [e1] at h
    have h3 : 2 / s ^ 2 ∈ W.K := by
      have := W.K.sub_mem W.K.one_mem h
      simpa using this
    have h4 : s ^ 2 / 2 ∈ W.K := by
      have := W.K.inv_mem h3
      rwa [inv_div] at this
    have h5 := W.K.mul_mem h4 h2K
    rwa [div_mul_cancel₀ _ h2] at h5
  have hcount := card_le_four_mul_of_trace_sq T hTtr W.K hK0
  rw [W.card_eq] at hcount
  have hpm : 3 ≤ p ^ m := by
    have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    exact hp3.trans (Nat.le_self_pow hm0.ne' p)
  have hsq : (p ^ m) ^ 2 ≤ p ^ f := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  rw [hF] at hK27 hTcard
  exact num_aux (p ^ m) (Nat.card T) (p ^ f) hsq (by omega) hcount (by omega)

theorem eq_top_of_torus_pair {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK27 : 27 ≤ Nat.card K) {E D : Matrix (Fin 2) (Fin 2) K}
    (M T : Subgroup (SpecialLinearGroup (Fin 2) K)) (hTM : T ≤ M)
    (hTE : ∀ A ∈ T, (A : Matrix (Fin 2) (Fin 2) K) * E = E * A) (hTcyc : IsCyclic T)
    (hTcard : Nat.card K + 1 ≤ Nat.card T) (hTp : ∀ A ∈ T, A ^ p = 1 → A = 1)
    (hTtr : ∀ s : K, ∀ A ∈ T, (A : Matrix (Fin 2) (Fin 2) K).trace = s → ∀ A' ∈ T,
      (A' : Matrix (Fin 2) (Fin 2) K).trace = s →
      A' = A ∨ (A' : Matrix (Fin 2) (Fin 2) K) = s • (1 : Matrix (Fin 2) (Fin 2) K) - A)
    {B : SpecialLinearGroup (Fin 2) K} (hBM : B ∈ M) {a b : K} (hb : b ≠ 0)
    (hBab : (B : Matrix (Fin 2) (Fin 2) K) = a • (1 : Matrix (Fin 2) (Fin 2) K) + b • D)
    (hB2 : ¬ ∃ e : K, (B : Matrix (Fin 2) (Fin 2) K) * B = e • (1 : Matrix (Fin 2) (Fin 2) K))
    (hDE : D * E ≠ E * D) : M = ⊤ := by
  classical
  have hpr : ringChar K = p := ringChar.eq K p
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [hpr]; exact hp2)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  set A : SpecialLinearGroup (Fin 2) K := (g : SpecialLinearGroup (Fin 2) K) with hAdef
  have hAT : A ∈ T := g.2
  have hAM : A ∈ M := hTM hAT
  set N := Nat.card T with hNdef
  have hN28 : 28 ≤ N := by omega
  have hord : orderOf A = N := by
    rw [hAdef, Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hApow : ∀ k, A ^ k = 1 → N ∣ k := fun k hk => hord ▸ orderOf_dvd_of_pow_eq_one hk
  have hAsq : ¬ ∃ e : K, (A : Matrix (Fin 2) (Fin 2) K) * A = e • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rintro ⟨e, he⟩
    have := Nat.le_of_dvd (by norm_num) (hApow 4 (pow_four_of_sq_scalar he))
    omega
  have hAs : ¬ ∃ e : K, (A : Matrix (Fin 2) (Fin 2) K) = e • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rintro ⟨e, he⟩
    apply hAsq
    refine ⟨e * e, ?_⟩
    rw [he, smul_mul_smul_comm, one_mul]
  have hpN : ¬ p ∣ N := by
    intro hdvd
    have : Fintype T := Fintype.ofFinite T
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := T) p (by
      rw [← Nat.card_eq_fintype_card]; exact hdvd)
    have h1 : (x : SpecialLinearGroup (Fin 2) K) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]; rfl
    have h2' := hTp x x.2 h1
    have : x = 1 := Subtype.ext h2'
    rw [this, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  have hbigk : ∀ k, 0 < k → (mkPSL K A) ^ k = 1 → N ≤ 2 * k := by
    intro k hk hpk
    have := hApow (2 * k) (pow_two_mul_eq_one_of_center (mkPSL_pow_eq_one_iff.1 hpk))
    exact Nat.le_of_dvd (by omega) this
  let H : Subgroup (PSL2MatrixGroup K) := M.map (mkPSL K)
  let x : H := ⟨mkPSL K A, Subgroup.mem_map_of_mem _ hAM⟩
  let y : H := ⟨mkPSL K B, Subgroup.mem_map_of_mem _ hBM⟩
  have hxy : x * y ≠ y * x := fun h =>
    mkPSL_noncomm h2 (hTE A hAT) hAs hb hBab hB2 hDE (congrArg Subtype.val h)
  have hxk : ∀ k, 0 < k → x ^ k = 1 → N ≤ 2 * k := fun k hk h =>
    hbigk k hk (by simpa [x] using congrArg Subtype.val h)
  have hx2 : x * x ≠ 1 := fun h => by
    have := hxk 2 (by norm_num) (by rw [pow_two]; exact h)
    omega
  have hy2 : y * y ≠ 1 := fun h => by
    apply hB2
    apply sq_scalar_of_pow_two_center
    rw [← mkPSL_pow_eq_one_iff, pow_two]
    simpa [y] using congrArg Subtype.val h
  have hxe : ∀ {X : Type} [Group X] (e : H ≃* X) (k : ℕ), 0 < k → (e x) ^ k = 1 → N ≤ 2 * k :=
    fun e k hk h => hxk k hk (e.injective (by rw [map_pow, h, map_one]))
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hFf⟩ := FiniteField.card K p
  have hF : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hFf
  have hf0 : 0 < (f : ℕ) := f.pos
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield (p := p)
      (f := (f : ℕ)) hF H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m', t, -, ht, N', C, hN', hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩ | ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩
  · exact absurd (hEl.toIsMulCommutative.is_comm.comm x y) hxy
  · have : IsCyclic H := hcyc
    exact absurd (IsCyclic.isMulCommutative.is_comm.comm x y) hxy
  · exact absurd (dihedral_comm e hx2 hy2) hxy
  ·
    exfalso
    have hord4 : ∀ σ : alternatingGroup (Fin 4), σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by decide
    rcases hord4 (e x) with h | h
    · have := hxe e 2 (by norm_num) h; omega
    · have := hxe e 3 (by norm_num) h; omega
  ·
    exfalso
    have hord4 : ∀ σ : Equiv.Perm (Fin 4), σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by decide
    rcases hord4 (e x) with h | h | h
    · have := hxe e 2 (by norm_num) h; omega
    · have := hxe e 3 (by norm_num) h; omega
    · have := hxe e 4 (by norm_num) h; omega
  ·
    exfalso
    rcases CFSG.RankThree.PartOne.SEITZ2.alternating_five_orders (e x) with h | h | h
    · have := hxe e 2 (by norm_num) h; omega
    · have := hxe e 3 (by norm_num) h; omega
    · have := hxe e 5 (by norm_num) h; omega
  ·
    exfalso
    have hcomp : N'.IsComplement' C := by
      have := hN'
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
    have hHcard : Nat.card N' * Nat.card C = Nat.card H := hcomp.card_mul_card
    have hxN : x ^ N = 1 := by
      apply Subtype.ext
      show (mkPSL K A) ^ N = 1
      rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
    have hodN : orderOf x ∣ N := orderOf_dvd_of_pow_eq_one hxN
    have hcop : Nat.Coprime (orderOf x) p := by
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
      exact fun h => hpN (h.trans hodN)
    have hodH : orderOf x ∣ Nat.card H := orderOf_dvd_natCard x
    rw [← hHcard, hNcard, hCcard] at hodH
    have hodt : orderOf x ∣ t := by
      have hc : Nat.Coprime (orderOf x) (p ^ m') := hcop.pow_right m'
      exact hc.dvd_of_dvd_mul_left hodH
    have hodd : Odd (p ^ (f : ℕ)) := (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
    have hg2 : Nat.gcd (p ^ (f : ℕ) - 1) 2 = 2 := by
      apply Nat.gcd_eq_right
      obtain ⟨c, hc⟩ := hodd
      exact ⟨c, by omega⟩
    rw [hg2] at ht
    have hle : orderOf x ≤ (p ^ (f : ℕ) - 1) / 2 :=
      Nat.le_of_dvd (by
        have : 2 ≤ p ^ (f : ℕ) - 1 := by omega
        exact Nat.div_pos this (by norm_num)) (hodt.trans ht)
    have := hxk (orderOf x) (orderOf_pos x) (pow_orderOf_eq_one x)
    omega
  ·
    by_cases hmf' : m = (f : ℕ)
    · have e2 : GaloisField p m ≃+* K := by
        have := Fintype.ofFinite (GaloisField p m)
        exact FiniteField.ringEquivOfCardEq (by
          rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF, GaloisField.card p m hm0,
            hmf'])
      have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup K) := by
        rw [Nat.card_congr eP.toEquiv]
        exact Nat.card_congr (h826_pslEquiv e2).toEquiv
      exact eq_top_of_map_mkPSL_eq_top h2 (Subgroup.eq_top_of_card_eq H hcardH)
    · exfalso
      obtain ⟨c, hc⟩ := hmf
      have hc2 : 2 ≤ c := by
        rcases Nat.lt_or_ge c 2 with h | h
        · interval_cases c
          · omega
          · omega
        · exact h
      exact subfield_alternative_false (Nat.pos_of_ne_zero hm0) hp2 hF (by nlinarith) hK27 T M hTM
        hTcard hTtr h2 W
  ·
    exfalso
    have := Nat.le_of_dvd hf0 hmf
    exact subfield_alternative_false (Nat.pos_of_ne_zero hm0) hp2 hF this hK27 T M hTM hTcard hTtr
      h2 W

theorem closure_centralizers_eq_top (hK : ringChar K ≠ 2) (h27 : 27 ≤ Nat.card K)
    {E₁ D : GL (Fin 2) K}
    (hE : ∀ a : K, ((E₁ : Matrix (Fin 2) (Fin 2) K).charpoly).eval a ≠ 0)
    (hD2 : ∃ c : K, (D : Matrix (Fin 2) (Fin 2) K) ^ 2 = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hDs : ¬ ∃ c : K, (D : Matrix (Fin 2) (Fin 2) K) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hDE : (D : Matrix (Fin 2) (Fin 2) K) * E₁ ≠ E₁ * D) :
    Subgroup.closure ({B : SpecialLinearGroup (Fin 2) K |
        (E₁ : Matrix (Fin 2) (Fin 2) K) * B = B * E₁} ∪
      {B : SpecialLinearGroup (Fin 2) K |
        (D : Matrix (Fin 2) (Fin 2) K) * B = B * D}) = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hpP : (ringChar K).Prime := by
    have := CharP.char_is_prime K (ringChar K)
    exact this
  have : Fact (ringChar K).Prime := ⟨hpP⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨T, hTE, hTcyc, hTcard, hTp, hTtr⟩ := exists_torus (p := ringChar K) hE
  obtain ⟨c, hc⟩ := hD2
  have hD : (D : Matrix (Fin 2) (Fin 2) K) * D = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← pow_two, hc]
  obtain ⟨htr, hdet⟩ := trace_det_of_sq_scalar hD hDs
  have hdet0 : (D : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit).ne_zero
  have hc0 : c ≠ 0 := by
    intro h
    apply hdet0
    rw [hdet, h, neg_zero]
  obtain ⟨B, hBcomm, a, b, ha, hb, hBab⟩ :=
    exists_sl2_comm_aff h2 (by omega) hc0 htr hdet
  have hB2 := not_sq_scalar (D := (D : Matrix (Fin 2) (Fin 2) K)) (c := c) h2 ha hb hD hDs
  rw [← hBab] at hB2
  refine eq_top_of_torus_pair (E := (E₁ : Matrix (Fin 2) (Fin 2) K))
    (D := (D : Matrix (Fin 2) (Fin 2) K)) (by exact hK) h27 _ T ?_ hTE
    hTcyc hTcard hTp hTtr (B := B) ?_ hb hBab hB2 hDE
  · intro A hA
    exact Subgroup.subset_closure (Or.inl (hTE A hA).symm)
  · exact Subgroup.subset_closure (Or.inr hBcomm.symm)

end Assembly

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
