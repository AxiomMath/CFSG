module

public import Certificates.Data.Kernel.Misc.A7Cnt
public import CFSG.Certificates.Kernel.Misc.A7NatSound
public import CFSG.Certificates.Kernel.BalanceSC.Parts
public import Certificates.Data.A7Fano

public section

namespace CFSG.KC.A7Cnt

open Equiv Finset CFSG.KD.A7Cnt CFSG.KD.A7Nat CFSG.KC.LQT.P CFSG.KC.Ord CFSG.KC.A7Nat
open scoped Pointwise

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem oneC_eq : oneC = code (1 : Perm (Fin 7)) := by
  rw [← code_one]
  decide +kernel

theorem beq_one (σ : Perm (Fin 7)) : Nat.beq (code σ) oneC = true ↔ σ = 1 := by
  rw [oneC_eq, beq_code h7]

theorem sq_code (σ : Perm (Fin 7)) : sqK (code σ) = code (σ ^ 2) := by
  rw [sqK, code_mul h7, pow_two]

theorem p5_code (σ : Perm (Fin 7)) : p5 (code σ) = code (σ ^ 5) := by
  simp only [p5, letN_eq, sq_code, code_mul h7]
  exact congrArg code (by group)

theorem p7_code (σ : Perm (Fin 7)) : p7 (code σ) = code (σ ^ 7) := by
  simp only [p7, letN_eq, sq_code, code_mul h7]
  exact congrArg code (by group)

theorem p35_code (σ : Perm (Fin 7)) : p35 (code σ) = code (σ ^ 35) := by
  simp only [p35, letN_eq, sq_code, code_mul h7]
  exact congrArg code (by group)

theorem img_fin (σ : Perm (Fin 7)) (i : Fin 7) : img (code σ) i = σ i := img_code h7 σ i

theorem img_lit (σ : Perm (Fin 7)) (a b : ℕ) (ha : a < 7) (hb : b < 7) :
    Nat.beq (img (code σ) a) b = true ↔ σ ⟨a, ha⟩ = ⟨b, hb⟩ := by
  rw [beq_iff, Fin.ext_iff, ← img_fin]

theorem sign_conj' (g y : Perm (Fin 7)) : Perm.sign (g * y * g⁻¹) = Perm.sign y := by
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm (Perm.sign g), mul_assoc,
    Int.units_mul_self, mul_one]

theorem cnt_eq {f : ℕ → Bool} {p : Perm (Fin 7) → Prop} [DecidablePred p]
    (hf : ∀ σ, f (code σ) = true ↔ p σ) : cntP 7 f = (univ.filter p).card := by
  rw [cntP_eq h7]
  exact congrArg card (filter_congr fun σ _ => hf σ)

theorem k1_eq : k1 = (univ.filter fun σ : Perm (Fin 7) =>
    Perm.sign σ = 1 ∧ ((σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5))).card := by
  unfold k1
  refine cnt_eq fun σ => ?_
  rw [andB_iff, orB_iff, andB_iff, andB_iff, img_lit σ 5 5 (by omega) (by omega),
    img_lit σ 6 6 (by omega) (by omega), img_lit σ 5 6 (by omega) (by omega),
    img_lit σ 6 5 (by omega) (by omega), even_code h7, and_comm]
  rfl

theorem k2_eq : k2 = (univ.filter fun σ : Perm (Fin 7) =>
    Perm.sign σ = 1 ∧ ∀ i : Fin 7, ((σ i).val < 4 ↔ i.val < 4)).card := by
  unfold k2
  refine cnt_eq fun σ => ?_
  rw [andB_iff, allN_fin, even_code h7, and_comm]
  refine and_congr_right' (forall_congr' fun i => ?_)
  rw [iffB_iff, blt_iff, blt_iff, img_fin]

theorem k3_eq : k3 = (univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ σ 4 = 4).card := by
  unfold k3
  refine cnt_eq fun σ => ?_
  rw [andB_iff, img_lit σ 4 4 (by omega) (by omega), even_code h7, and_comm]
  rfl

theorem k4_eq : k4 = (univ.filter fun σ : Perm (Fin 7) =>
    Perm.sign σ = 1 ∧ σ 4 = 4 ∧ σ ^ 5 = 1).card := by
  unfold k4
  refine cnt_eq fun σ => ?_
  rw [andB_iff, andB_iff, img_lit σ 4 4 (by omega) (by omega), p5_code, beq_one, even_code h7]
  change σ 4 = 4 ∧ _ ∧ _ ↔ _
  tauto

theorem k5_eq : k5 = (univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ σ ^ 35 = 1).card := by
  unfold k5
  refine cnt_eq fun σ => ?_
  rw [andB_iff, p35_code, beq_one, even_code h7]

theorem k6_eq : k6 = (univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ σ ^ 7 = 1).card := by
  unfold k6
  refine cnt_eq fun σ => ?_
  rw [andB_iff, p7_code, beq_one, even_code h7]

@[expose] def x2 : Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem x2C_eq : x2C = code x2 := by decide +kernel

theorem card_cent_conj (g x : Perm (Fin 7)) :
    (univ.filter fun y : Perm (Fin 7) => Perm.sign y = 1 ∧ g * x * g⁻¹ * y = y * (g * x * g⁻¹)).card =
      (univ.filter fun y : Perm (Fin 7) => Perm.sign y = 1 ∧ x * y = y * x).card := by
  refine card_bij' (fun y _ => g⁻¹ * y * g) (fun y _ => g * y * g⁻¹) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    refine ⟨?_, ?_⟩
    · have := sign_conj' g⁻¹ y
      rw [inv_inv] at this
      rw [this, hy.1]
    · have := congrArg (fun z => g⁻¹ * z * g) hy.2
      simpa [mul_assoc] using this
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    refine ⟨?_, ?_⟩
    · rw [sign_conj', hy.1]
    · have := congrArg (fun z => g * z * g⁻¹) hy.2
      simpa [mul_assoc] using this
  · intro y _
    simp [mul_assoc]
  · intro y _
    simp [mul_assoc]

theorem centK_eq : centK = (univ.filter fun y : Perm (Fin 7) =>
    Perm.sign y = 1 ∧ x2 * y = y * x2).card := by
  unfold centK
  refine cnt_eq fun σ => ?_
  rw [andB_iff, x2C_eq, comm_code h7, even_code h7, and_comm]

theorem cent_card (hi : invK = true) (hc : centK = 24) (x : Perm (Fin 7)) (hx : Perm.sign x = 1)
    (h1 : x ≠ 1) (h2 : x * x = 1) :
    (univ.filter fun y : Perm (Fin 7) => Perm.sign y = 1 ∧ x * y = y * x).card = 24 := by
  have h := (allP_iff invF).1 hi x
  unfold invF at h
  rw [impB_iff, andB_iff, andB_iff, notB_iff, even_code h7, beq_one, code_mul h7, beq_one,
    anyL_iff] at h
  obtain ⟨e, -, he⟩ := h ⟨hx, h1, h2⟩
  rw [andB_iff, letB_eq, andB_iff] at he
  replace he := he.2
  obtain ⟨g, hg⟩ := exists_of_permK he.1
  rw [← hg, x2C_eq, conj_code h7, beq_code h7] at he
  rw [← he.2, card_cent_conj, ← centK_eq, hc]

theorem bitJ_eq (m i : ℕ) : bitJ m i = m.testBit i := bit_eq m i

theorem testBit_imgM (σ : Perm (Fin 7)) (m v : ℕ) :
    (imgM (code σ) m).testBit v = true ↔ ∃ i : Fin 7, m.testBit i = true ∧ (σ i : ℕ) = v := by
  unfold imgM
  change ((Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft 1
    (Bool.rec (motive := fun _ => ℕ) 31 (img (code σ) i) (bitJ m i)))) 7) &&& 127).testBit v = true ↔ _
  rw [Nat.testBit_and, Bool.and_eq_true, testBit_fold,
    show (127 : ℕ) = 2 ^ 7 - 1 from rfl, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨i, hi, hf⟩, hv⟩
    rw [bitJ_eq] at hf
    cases hb : m.testBit i
    · rw [hb] at hf
      exact absurd hf (by change (31 : ℕ) ≠ v; omega)
    · rw [hb] at hf
      refine ⟨⟨i, hi⟩, hb, ?_⟩
      rw [← img_fin]
      exact hf
  · rintro ⟨i, hb, rfl⟩
    refine ⟨⟨i, i.isLt, ?_⟩, (σ i).isLt⟩
    rw [bitJ_eq, hb]
    exact img_fin σ i

open CFSG.KC.BalanceSC in
theorem imgM_fmask (σ : Perm (Fin 7)) (L : Finset (Fin 7)) :
    imgM (code σ) (fmask L) = fmask (σ • L) := by
  apply Nat.eq_of_testBit_eq
  intro v
  apply Bool.eq_iff_iff.2
  rw [testBit_imgM, testBit_fmask]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [testBit_fmask] at hi
    obtain ⟨x, hx, hxi⟩ := hi
    obtain rfl : x = i := Fin.ext hxi
    exact ⟨σ x, Finset.mem_smul_finset.2 ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
    exact ⟨x, (testBit_fmask L x).2 ⟨x, hx, rfl⟩, rfl⟩

open CFSG.KC.BalanceSC in
theorem presB_iff {P : Finset (Finset (Fin 7))} {M : List ℕ} (hP : P.image fmask = M.toFinset)
    (σ : Perm (Fin 7)) : presB (code σ) M = true ↔ σ • P = P := by
  have hmem : ∀ L, L ∈ P ↔ fmask L ∈ M := fun L => by
    rw [← List.mem_toFinset, ← hP, fmask_injective.mem_finset_image]
  have hM : ∀ m ∈ M, ∃ L ∈ P, fmask L = m := fun m hm => by
    rw [← List.mem_toFinset, ← hP, mem_image] at hm
    exact hm
  unfold presB
  rw [allL_iff]
  constructor
  · intro h
    have hsub : σ • P ⊆ P := by
      intro L' hL'
      obtain ⟨L, hL, rfl⟩ := Finset.mem_smul_finset.1 hL'
      have := h (fmask L) ((hmem L).1 hL)
      rw [letB_eq, memL_iff, imgM_fmask] at this
      exact (hmem _).2 this
    exact eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])
  · intro h m hm
    obtain ⟨L, hL, rfl⟩ := hM m hm
    rw [letB_eq, memL_iff, imgM_fmask, ← hmem]
    exact h ▸ Finset.smul_mem_smul_finset hL

open CFSG.KC.BalanceSC in
theorem f1_img : CFSG.A7Fano.fano1.image fmask = f1L.toFinset := by decide +kernel

open CFSG.KC.BalanceSC in
theorem f2_img : CFSG.A7Fano.fano2.image fmask = f2L.toFinset := by decide +kernel

theorem pres1 (σ : Perm (Fin 7)) : presB (code σ) f1L = true ↔ σ • CFSG.A7Fano.fano1 =
    CFSG.A7Fano.fano1 := presB_iff f1_img σ

theorem pres2 (σ : Perm (Fin 7)) : presB (code σ) f2L = true ↔ σ • CFSG.A7Fano.fano2 =
    CFSG.A7Fano.fano2 := presB_iff f2_img σ

open CFSG.A7Fano

theorem cycC_eq : cycC = code cyc7 := by decide +kernel

theorem dblC_eq : dblC = code dbl7 := by decide +kernel

theorem c1_of (h : c1K = true) (hh : hLK = true) (g : Perm (Fin 7)) (hg : Perm.sign g = 1) :
    g • fano1 = fano1 ∨ g • fano2 = fano2 ∨
      ∃ i : Fin 7, ∃ j : Fin 3, (g * cyc7 ^ (i : ℕ) * dbl7 ^ (j : ℕ)) ^ 5 = 1 ∧
        g * cyc7 ^ (i : ℕ) * dbl7 ^ (j : ℕ) ≠ 1 := by
  have hc := (allP_iff c1F).1 h g
  unfold c1F at hc
  rw [impB_iff, even_code h7, orB_iff, orB_iff, pres1, pres2, anyL_iff] at hc
  rcases hc hg with h1 | h2 | ⟨c, hc, hp⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · right
    right
    unfold hLK at hh
    rw [allL_iff] at hh
    obtain ⟨i, hi⟩ := (anyN_fin _ _).1 (hh c hc)
    obtain ⟨j, hj⟩ := (anyN_fin _ _).1 hi
    rw [beq_iff, cycC_eq, dblC_eq, code_pow h7, code_pow h7, code_mul h7] at hj
    subst hj
    rw [letB_eq, code_mul h7, pent, andB_iff, notB_iff, p5_code, beq_one, beq_one, ← mul_assoc] at hp
    exact ⟨i, j, hp⟩

theorem stK_eq {P : Finset (Finset (Fin 7))} {M : List ℕ} (hP : P.image CFSG.KC.BalanceSC.fmask =
    M.toFinset) : stK M = (stabSet P).card := by
  unfold stK stabSet
  refine cnt_eq fun σ => ?_
  rw [andB_iff, presB_iff hP, even_code h7, and_comm]

theorem rL_eq : List.ofFn (fun i => code (reps1 i)) = rL := by decide +kernel

theorem mem_rL (i : Fin 15) : code (reps1 i) ∈ rL := by
  rw [← rL_eq, List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem reps_of (h : repK = true) : (∀ i, Perm.sign (reps1 i) = 1) ∧
    (∀ i j, i ≠ j → ((reps1 i)⁻¹ * reps1 j) • fano1 ≠ fano1) := by
  unfold repK at h
  rw [andB_iff, andB_iff, allL_iff, allL_iff] at h
  obtain ⟨he, hnd, hp⟩ := h
  refine ⟨fun i => (even_code h7 _).1 (he _ (mem_rL i)), fun i j hij => ?_⟩
  have hinj := List.nodup_ofFn.1 (rL_eq ▸ nodupL_iff rL hnd)
  have hne : code (reps1 i) ≠ code (reps1 j) := fun e => hij (hinj e)
  have := (allL_iff _ _).1 (hp _ (mem_rL i)) _ (mem_rL j)
  rw [impB_iff, notB_iff, beq_iff, notB_iff, code_inv h7, code_mul h7, pres1] at this
  exact this hne

theorem countP_ofFn {m : ℕ} (f : Fin m → ℕ) (p : ℕ → Bool) :
    (List.ofFn f).countP p = (univ.filter fun i => p (f i) = true).card := by
  rw [List.ofFn_eq_map, List.countP_map, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
  congr 1
  ext i
  simp

theorem reps1_zero : code (reps1 0) = oneC := by decide +kernel

theorem fix_of (hr : repK = true) (h : fxK = true) (j : Fin 15) (hj : j ≠ 0) :
    fixCount fano1 reps1 j ≤ 3 := by
  unfold fxK at h
  rw [andB_iff, allL_iff, allL_iff] at h
  obtain ⟨hw, ht⟩ := h
  have hne : code (reps1 j) ≠ oneC := by
    unfold repK at hr
    rw [andB_iff, andB_iff] at hr
    have hinj := List.nodup_ofFn.1 (rL_eq ▸ nodupL_iff rL hr.2.1)
    rw [← reps1_zero]
    exact fun e => hj (hinj e)
  have hk := ht _ (mem_rL j)
  rw [impB_iff, notB_iff, beq_iff] at hk
  have hk := hk hne
  rw [Nat.ble_eq, cntL_eq, ← rL_eq, countP_ofFn] at hk
  refine le_trans ?_ hk
  unfold fixCount
  apply card_le_card
  intro i
  simp only [mem_filter, mem_univ, true_and, notB_iff]
  intro hall hwit
  unfold witB at hwit
  rw [anyL_iff] at hwit
  obtain ⟨w, hwm, hwo⟩ := hwit
  obtain ⟨g, rfl⟩ := exists_of_permK (hw w hwm)
  rw [andB_iff, andB_iff, andB_iff, notB_iff, even_code h7, pres1, cj, cj, code_inv h7,
    code_mul h7, code_mul h7, code_inv h7, code_mul h7, code_mul h7, pres1, pres1] at hwo
  exact hwo.2.2.2 (hall g (by simp [stabSet, hwo.1, hwo.2.1, hwo.2.2.1]))

@[expose] def x3 : Perm (Fin 7) := Equiv.swap 1 0 * Equiv.swap 1 2

theorem x3C_eq : x3C = code x3 := by decide +kernel

theorem x3iC_eq : x3iC = code x3⁻¹ := by decide +kernel

theorem normCount_conj (h σ : Perm (Fin 7)) : normCount (h * σ * h⁻¹) = normCount σ := by
  unfold normCount
  refine card_bij' (fun g _ => h⁻¹ * g * h) (fun g _ => h * g * h⁻¹) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    refine ⟨?_, ?_⟩
    · have := sign_conj' h⁻¹ g
      rw [inv_inv] at this
      rw [this, hg.1]
    · rcases hg.2 with e | e
      · left
        have := congrArg (fun z => h⁻¹ * z * h) e
        simpa [mul_assoc] using this
      · right
        have := congrArg (fun z => h⁻¹ * z * h) e
        simpa [mul_assoc] using this
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    refine ⟨?_, ?_⟩
    · rw [sign_conj', hg.1]
    · rcases hg.2 with e | e
      · left
        have := congrArg (fun z => h * z * h⁻¹) e
        simpa [mul_assoc] using this
      · right
        have := congrArg (fun z => h * z * h⁻¹) e
        simpa [mul_assoc] using this
  · intro g _
    simp [mul_assoc]
  · intro g _
    simp [mul_assoc]

theorem normK_eq : normK = normCount x3 := by
  unfold normK normCount
  refine cnt_eq fun g => ?_
  rw [andB_iff, even_code h7, letB_eq, orB_iff, x3C_eq, x3iC_eq, code_mul h7, code_mul h7,
    code_mul h7, beq_code h7, beq_code h7, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]

theorem norm_of (h : normK = 72) (σ : Perm (Fin 7)) (hσ : σ.cycleType = {3}) :
    normCount σ = 72 := by
  have h3 : x3.cycleType = {3} :=
    Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  obtain ⟨c, hc⟩ := isConj_iff.1 (Perm.isConj_iff_cycleType_eq.2 (h3.trans hσ.symm))
  rw [← hc, normCount_conj, ← normK_eq, h]

end CFSG.KC.A7Cnt

end
