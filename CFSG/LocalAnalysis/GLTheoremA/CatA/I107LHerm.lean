module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LFrob
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107L

open CFSG.Open CFSG.Assembly Matrix

section Herm

variable {K : Type} [Field K]

@[expose] abbrev OffIdx (k : ℕ) : Type := {s : Sym2 (Fin k) // ¬ s.IsDiag}

@[expose] def offEntry {k : ℕ} (f : OffIdx k → K) (i j : Fin k) : K :=
  if h : i = j then 0 else f ⟨s(i, j), by rw [Sym2.mk_isDiag_iff]; exact h⟩

theorem offEntry_comm {k : ℕ} (f : OffIdx k → K) (i j : Fin k) :
    offEntry f i j = offEntry f j i := by
  unfold offEntry
  by_cases h : i = j
  · subst h; rfl
  · rw [dif_neg h, dif_neg (Ne.symm h)]
    exact congrArg f (Subtype.ext Sym2.eq_swap)

theorem offEntry_add {k : ℕ} (f g : OffIdx k → K) (i j : Fin k) :
    offEntry (f + g) i j = offEntry f i j + offEntry g i j := by
  unfold offEntry
  split_ifs <;> simp

theorem offEntry_zero {k : ℕ} (i j : Fin k) : offEntry (0 : OffIdx k → K) i j = 0 := by
  unfold offEntry
  split_ifs <;> simp

@[expose] def hermMat (σ : K →+* K) {k : ℕ} (a : Fin k → K) (f : OffIdx k → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => if i = j then a i else if i < j then offEntry f i j else σ (offEntry f i j)

theorem hermMat_add (σ : K →+* K) {k : ℕ} (a a' : Fin k → K) (f f' : OffIdx k → K) :
    hermMat σ (a + a') (f + f') = hermMat σ a f + hermMat σ a' f' := by
  ext i j
  simp only [hermMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, offEntry_add, map_add]
  split_ifs <;> ring

theorem hermMat_zero (σ : K →+* K) {k : ℕ} : hermMat σ (0 : Fin k → K) (0 : OffIdx k → K) = 0 := by
  ext i j
  simp only [hermMat, Matrix.of_apply, Matrix.zero_apply, offEntry_zero, map_zero, Pi.zero_apply]
  split_ifs <;> simp

theorem hermMat_herm (σ : K →+* K) (hσσ : ∀ x, σ (σ x) = x) {k : ℕ} (a : Fin k → K)
    (ha : ∀ i, σ (a i) = a i) (f : OffIdx k → K) :
    ((hermMat σ a f).map σ)ᵀ = hermMat σ a f := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [hermMat, Matrix.of_apply, if_true, ha]
  · rcases lt_or_gt_of_ne hij with h | h
    · simp only [hermMat, Matrix.of_apply]
      rw [if_neg (Ne.symm hij), if_neg (not_lt.2 h.le), hσσ, if_neg hij, if_pos h]
      exact offEntry_comm f j i
    · simp only [hermMat, Matrix.of_apply]
      rw [if_neg (Ne.symm hij), if_pos h, if_neg hij, if_neg (not_lt.2 h.le), offEntry_comm f j i]

@[expose] def hookU (d k : ℕ) : Matrix (Fin d) (Fin k) K :=
  Matrix.of fun a i => if a.val / 2 = i.val ∧ a.val < 2 * k then 1 else 0

@[expose] def hookR (d k : ℕ) : Matrix (Fin k) (Fin d) K :=
  Matrix.of fun i a => if a.val = 2 * i.val then 1 else 0

theorem hookU_map (σ : K →+* K) (d k : ℕ) : (hookU (K := K) d k).map σ = hookU (K := K) d k := by
  ext a i
  simp only [hookU, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem card_filter_pair {d k : ℕ} (hkd : 2 * k ≤ d) (i : Fin k) :
    (Finset.univ.filter fun a : Fin d => a.val / 2 = i.val ∧ a.val < 2 * k).card = 2 := by
  have hi := i.isLt
  rw [Finset.card_eq_two]
  refine ⟨⟨2 * i.val, by omega⟩, ⟨2 * i.val + 1, by omega⟩, ?_, ?_⟩
  · intro h
    simp [Fin.ext_iff] at h
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega

theorem sum_hookU_mul {d k : ℕ} (h2 : (2 : K) = 0) (hkd : 2 * k ≤ d) (i j : Fin k) :
    ∑ a : Fin d, hookU (K := K) d k a i * hookU (K := K) d k a j = if i = j then 2 else 0 := by
  by_cases hij : i = j
  · subst hij
    have hterm : ∀ a : Fin d, hookU (K := K) d k a i * hookU (K := K) d k a i =
        if a.val / 2 = i.val ∧ a.val < 2 * k then 1 else 0 := by
      intro a
      simp only [hookU, Matrix.of_apply]
      split_ifs <;> simp
    simp only [hterm, if_true]
    rw [Finset.sum_boole, card_filter_pair hkd i]
    norm_num
  · have hterm : ∀ a : Fin d, hookU (K := K) d k a i * hookU (K := K) d k a j = 0 := by
      intro a
      simp only [hookU, Matrix.of_apply]
      split_ifs with h1 h2
      · exfalso
        apply hij
        ext
        omega
      · simp
      · simp
      · simp
    simp [hterm, hij]

theorem hookU_transpose_mul {d k : ℕ} (h2 : (2 : K) = 0) (hkd : 2 * k ≤ d) :
    (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [Matrix.transpose_apply]
  rw [sum_hookU_mul h2 hkd i j]
  split_ifs <;> simp [h2]

theorem hookU_transpose_mulVec_one {d k : ℕ} (h2 : (2 : K) = 0) (hkd : 2 * k ≤ d) :
    (hookU (K := K) d k)ᵀ *ᵥ (fun _ => (1 : K)) = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_one, hookU, Matrix.of_apply,
    Pi.zero_apply]
  rw [Finset.sum_boole, card_filter_pair hkd i]
  simp [h2]

theorem hookR_mul_hookU {d k : ℕ} (hkd : 2 * k ≤ d) :
    hookR (K := K) d k * hookU (K := K) d k = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  rw [Finset.sum_eq_single (⟨2 * i.val, by omega⟩ : Fin d)]
  · simp only [hookR, hookU, Matrix.of_apply, if_true]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : ¬ (2 * i.val / 2 = j.val ∧ 2 * i.val < 2 * k) := fun h => hij (Fin.ext (by omega))
      simp only [hne, if_false, mul_zero]
      simp [hookR, hij]
  · intro b _ hb
    have hb' : ¬ (b.val = 2 * i.val) := fun e => hb (Fin.ext e)
    simp [hookR, hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem herm_eq_zero_of_UHU {d k : ℕ} (hkd : 2 * k ≤ d) (H : Matrix (Fin k) (Fin k) K)
    (hN : hookU (K := K) d k * H * (hookU (K := K) d k)ᵀ = 0) : H = 0 := by
  have hRU := hookR_mul_hookU (K := K) hkd
  have hUR : (hookU (K := K) d k)ᵀ * (hookR (K := K) d k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hRU, Matrix.transpose_one]
  have key : hookR (K := K) d k * (hookU (K := K) d k * H * (hookU (K := K) d k)ᵀ) * (hookR (K := K) d k)ᵀ = H := by
    calc hookR (K := K) d k * (hookU (K := K) d k * H * (hookU (K := K) d k)ᵀ) * (hookR (K := K) d k)ᵀ
        = (hookR (K := K) d k * hookU (K := K) d k) * H * ((hookU (K := K) d k)ᵀ * (hookR (K := K) d k)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [hRU, hUR, Matrix.one_mul, Matrix.mul_one]
  rw [← key, hN]
  simp

@[expose] def diagSub (σ : K →+* K) (k : ℕ) : AddSubgroup (Fin k → K) where
  carrier := {a | ∀ i, σ (a i) = a i}
  add_mem' := fun {a b} ha hb i => by simp only [Pi.add_apply, map_add, ha i, hb i]
  zero_mem' := fun i => by simp
  neg_mem' := fun {a} ha i => by simp only [Pi.neg_apply, map_neg, ha i]

@[expose] abbrev HermPar (σ : K →+* K) (k : ℕ) : Type := ↥(diagSub σ k) × (OffIdx k → K)

@[expose] def hermM (σ : K →+* K) (d k : ℕ) (p : HermPar σ k) : Matrix (Fin d) (Fin d) K :=
  1 + hookU (K := K) d k * hermMat σ (p.1 : Fin k → K) p.2 * (hookU (K := K) d k)ᵀ

theorem hermM_zero (σ : K →+* K) (d k : ℕ) : hermM σ d k 0 = 1 := by
  simp [hermM, hermMat_zero]

theorem hermM_add (σ : K →+* K) {d k : ℕ} (hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0)
    (p q : HermPar σ k) : hermM σ d k (p + q) = hermM σ d k p * hermM σ d k q := by
  have hH : hermMat σ ((p + q).1 : Fin k → K) (p + q).2 =
      hermMat σ (p.1 : Fin k → K) p.2 + hermMat σ (q.1 : Fin k → K) q.2 :=
    hermMat_add σ _ _ _ _
  have hAB : (hookU (K := K) d k * hermMat σ (p.1 : Fin k → K) p.2 * (hookU (K := K) d k)ᵀ) *
      (hookU (K := K) d k * hermMat σ (q.1 : Fin k → K) q.2 * (hookU (K := K) d k)ᵀ) = 0 := by
    calc _ = hookU (K := K) d k * hermMat σ (p.1 : Fin k → K) p.2 *
          ((hookU (K := K) d k)ᵀ * hookU (K := K) d k) * hermMat σ (q.1 : Fin k → K) q.2 *
            (hookU (K := K) d k)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hUU]; simp
  unfold hermM
  rw [hH]
  simp only [Matrix.mul_add, Matrix.add_mul, add_mul, mul_add, one_mul, mul_one, hAB, add_zero]
  abel

@[expose] noncomputable def hermHom (σ : K →+* K) (d k : ℕ)
    (hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0) :
    Multiplicative (HermPar σ k) →* GL (Fin d) K :=
  CFSG.SectionRank.ClassicalOdd.glOfAdd (hermM σ d k) (hermM_zero σ d k) (fun p q => hermM_add σ hUU p q)

theorem hermHom_val (σ : K →+* K) (d k : ℕ) (hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0)
    (x : Multiplicative (HermPar σ k)) :
    ((hermHom σ d k hUU x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = hermM σ d k x.toAdd :=
  CFSG.SectionRank.ClassicalOdd.coe_glOfAdd _ _ _ _

theorem det_one_add_hookU {d k : ℕ} (hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0)
    (H : Matrix (Fin k) (Fin k) K) : (1 + hookU (K := K) d k * H * (hookU (K := K) d k)ᵀ).det = 1 := by
  rw [Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hUU, zero_mul, add_zero, Matrix.det_one]

theorem hookUT_map (σ : K →+* K) (d k : ℕ) :
    ((hookU (K := K) d k)ᵀ).map σ = (hookU (K := K) d k)ᵀ := by
  ext i a
  simp only [Matrix.map_apply, Matrix.transpose_apply, hookU, Matrix.of_apply]
  split_ifs <;> simp

theorem sq_UHU {d k : ℕ} (hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0)
    (H : Matrix (Fin k) (Fin k) K) :
    (hookU (K := K) d k * H * (hookU (K := K) d k)ᵀ) * (hookU (K := K) d k * H * (hookU (K := K) d k)ᵀ) = 0 := by
  calc _ = hookU (K := K) d k * (H * (((hookU (K := K) d k)ᵀ * hookU (K := K) d k) * (H * (hookU (K := K) d k)ᵀ))) := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hUU]; simp

theorem one_add_sq_eq_one {d : ℕ} {N : Matrix (Fin d) (Fin d) K} (h2 : (2 : K) = 0) (hN2 : N * N = 0) :
    (1 + N) * (1 + N) = 1 := by
  have hNN : N + N = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply, ← two_mul, h2, zero_mul]
  calc (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
    _ = 1 := by rw [hNN, hN2]; simp

theorem hermM_unitary (σ : K →+* K) (n : ℕ) (hσ : ∀ x : K, σ x = x ^ 2 ^ n)
    (hσσ : ∀ x : K, σ (σ x) = x) (h2 : (2 : K) = 0) {d k : ℕ}
    (hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0) (p : HermPar σ k) :
    ((hermM σ d k p).map (fun x : K => x ^ 2 ^ n))ᵀ * hermM σ d k p = 1 := by
  have hfun : (fun x : K => x ^ 2 ^ n) = ⇑σ := funext fun x => (hσ x).symm
  rw [hfun]
  have ha : ∀ i, σ ((p.1 : Fin k → K) i) = (p.1 : Fin k → K) i := p.1.2
  have hT : ((hermM σ d k p).map σ)ᵀ = hermM σ d k p := by
    unfold hermM
    rw [Matrix.map_add (f := σ) (hf := map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ),
      Matrix.transpose_add, Matrix.transpose_one,
      Matrix.map_mul, Matrix.map_mul, hookU_map σ, hookUT_map σ, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hermMat_herm σ hσσ _ ha p.2]
    simp only [Matrix.mul_assoc]
  rw [hT]
  unfold hermM
  exact one_add_sq_eq_one h2 (sq_UHU hUU _)


theorem eq_zero_of_hermMat_eq_zero (σ : K →+* K) {k : ℕ} (a : Fin k → K) (f : OffIdx k → K)
    (h : hermMat σ a f = 0) : a = 0 ∧ f = 0 := by
  refine ⟨funext fun i => ?_, funext fun s => ?_⟩
  · have := congrFun (congrFun h i) i
    simpa [hermMat] using this
  · obtain ⟨s, hs⟩ := s
    induction s using Sym2.ind with
    | _ i j =>
      have hij : i ≠ j := fun e => hs (Sym2.mk_isDiag_iff.2 e)
      have hf : f ⟨s(i, j), hs⟩ = offEntry f i j := by
        unfold offEntry
        rw [dif_neg hij]
      rw [hf]
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have := congrFun (congrFun h i) j
        simpa [hermMat, hij, hlt] using this
      · have := congrFun (congrFun h j) i
        have hlt : j < i := hgt
        simpa [hermMat, Ne.symm hij, hlt, offEntry_comm f j i] using this

theorem hermHom_injective (σ : K →+* K) {d k : ℕ} (hkd : 2 * k ≤ d)
    (hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0) :
    Function.Injective (hermHom σ d k hUU) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : hermM σ d k x.toAdd = 1 := by
    rw [← hermHom_val σ d k hUU x, hx, Units.val_one]
  have hN : hookU (K := K) d k * hermMat σ (x.toAdd.1 : Fin k → K) x.toAdd.2 *
      (hookU (K := K) d k)ᵀ = 0 := by
    unfold hermM at h1
    exact add_eq_left.1 h1
  obtain ⟨ha, hf⟩ := eq_zero_of_hermMat_eq_zero σ _ _ (herm_eq_zero_of_UHU hkd _ hN)
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact Prod.ext (Subtype.ext ha) hf

theorem hermHom_mem (σ : K →+* K) (n : ℕ) (hσ : ∀ x : K, σ x = x ^ 2 ^ n)
    (hσσ : ∀ x : K, σ (σ x) = x) (h2 : (2 : K) = 0) {d k : ℕ}
    (hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0) (x : Multiplicative (HermPar σ k)) :
    hermHom σ d k hUU x ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
  unfold LargeEvenSUGroup
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [hermHom_val]
    unfold hermM
    exact det_one_add_hookU hUU _
  · rw [hermHom_val]
    exact hermM_unitary σ n hσ hσσ h2 hUU _

theorem hermHom_fix (σ : K →+* K) {d k : ℕ} (h2 : (2 : K) = 0) (hkd : 2 * k ≤ d)
    (hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0) (x : Multiplicative (HermPar σ k)) :
    ((hermHom σ d k hUU x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (fun _ => (1 : K)) =
      fun _ => 1 := by
  rw [hermHom_val]
  unfold hermM
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hookU_transpose_mulVec_one h2 hkd, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]

theorem add_self_eq_zero_of_two (h2 : (2 : K) = 0) (a : K) : a + a = 0 := by
  rw [← two_mul, h2, zero_mul]

theorem two_mul_choose_two_add (k : ℕ) : 2 * k.choose 2 + k = k ^ 2 := by
  rw [Nat.choose_two_right]
  have hev : 2 * (k * (k - 1) / 2) = k * (k - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)
  rw [hev]
  cases k with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel]
    ring

end Herm

section Count

variable {K : Type} [Field K] [Finite K]

theorem card_hermPar {n : ℕ} (σ : K →+* K) (hσ : ∀ x : K, σ x = x ^ 2 ^ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hF : Nat.card {x : K // x ^ 2 ^ n = x} = 2 ^ n) (k : ℕ) :
    Nat.card (HermPar σ k) = 2 ^ (n * k ^ 2) := by
  classical
  have hF' : Nat.card {x : K // σ x = x} = 2 ^ n := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [hσ]), hF]
  have hdiag : Nat.card ↥(diagSub σ k) = (2 ^ n) ^ k := by
    have e1 : ↥(diagSub σ k) ≃ (Fin k → {x : K // σ x = x}) :=
      (Equiv.subtypeEquivRight (fun a => Iff.rfl)).trans
        (Equiv.subtypePiEquivPi (p := fun _ b => σ b = b))
    rw [Nat.card_congr e1, Nat.card_fun, hF', Nat.card_eq_fintype_card, Fintype.card_fin]
  have hoff : Nat.card (OffIdx k → K) = ((2 ^ n) ^ 2) ^ (k.choose 2) := by
    haveI := Fintype.ofFinite K
    rw [Nat.card_fun, hK, Nat.card_eq_fintype_card (α := OffIdx k), Sym2.card_subtype_not_diag,
      Fintype.card_fin]
  have hexp : (2 ^ n) ^ k * ((2 ^ n) ^ 2) ^ (k.choose 2) = 2 ^ (n * k ^ 2) := by
    rw [← two_mul_choose_two_add k]
    ring
  rw [HermPar, Nat.card_prod, hdiag, hoff, hexp]

end Count

theorem pRank_herm_ge {d k n : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : 2 * k ≤ d) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    n * k ^ 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  haveI : CharP K 2 := charP_two_of_card_sq hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let σ : K →+* K := iterateFrobenius K 2 n
  have hσ : ∀ x : K, σ x = x ^ 2 ^ n := fun x => rfl
  have hσσ : ∀ x : K, σ (σ x) = x := fun x => by rw [hσ, hσ]; exact pow_pow_frob_eq hK x
  have hUU : (hookU (K := K) d k)ᵀ * hookU (K := K) d k = 0 := hookU_transpose_mul h2 hkd
  have hF : Nat.card {x : K // x ^ 2 ^ n = x} = 2 ^ n := card_fixed_frob hn hK
  have hcomm : ∀ a b : Multiplicative (HermPar σ k), a * b = b * a := fun a b => mul_comm a b
  have hpow : ∀ a : Multiplicative (HermPar σ k), a ^ 2 = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    refine Prod.ext (Subtype.ext (funext fun i => ?_)) (funext fun s => ?_)
    · exact add_self_eq_zero_of_two h2 _
    · exact add_self_eq_zero_of_two h2 _
  have hA : Nat.card (Multiplicative (HermPar σ k)) = 2 ^ (n * k ^ 2) := by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact card_hermPar σ hσ hK hF k
  have hv : (fun _ : Fin d => (1 : K)) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  exact CFSG.SectionRank.ClassicalOdd.le_pRank_statedProj (by norm_num) hcomm hpow hA
    (hermHom σ d k hUU) (hermHom_injective σ hkd hUU) (hermHom_mem σ n hσ hσσ h2 hUU) hv
    (hermHom_fix σ h2 hkd hUU)

end CFSG.LocalAnalysis.GLTheoremA.I107L

end
