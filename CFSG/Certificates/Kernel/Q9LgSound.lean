
module

public import Certificates.Data.Kernel.Q9Lg
public import CFSG.Certificates.Kernel.Q9SL2Sound

public section

namespace CFSG.KC.Q9Lg

open CFSG.GH74.GLS.Stage4.Q9 CFSG.GH74.GLS.Stage4.Q9.DFacts CFSG.KC.Q9SL2

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9

theorem getD_histK (L : List ℕ) {n : ℕ} (hn : n < 17) : (histK L).getD n 0 = L.count n := by
  simp [histK, List.getD_eq_getElem?_getD, hn]

theorem count_of_hist {L H : List ℕ} (h : histK L = H) {n : ℕ} (hn : n < 17) :
    L.count n = H.getD n 0 := by
  rw [← h, getD_histK L hn]

theorem pos_of_hist {L H : List ℕ} (h : histK L = H) {o : ℕ} (ho : o ∈ L) (hlt : o < 17) :
    0 < H.getD o 0 := by
  rw [← count_of_hist h hlt]
  exact List.count_pos_iff.mpr ho

theorem ordAuxK_bound (m : ℕ) : ∀ k p n, ordAuxK m k p n = 0 ∨ ordAuxK m k p n < n + k := by
  intro k
  induction k with
  | zero => intro p n; left; simp [ordAuxK]
  | succ k ih =>
    intro p n
    simp only [ordAuxK]
    split
    · right; omega
    · rcases ih (mulK p m) (n + 1) with h | h
      · left; exact h
      · right; omega

theorem ordK_lt (m : ℕ) : ordK m < 17 := by
  rcases ordAuxK_bound m 16 m 1 with h | h <;> rw [ordK] <;> omega

theorem histI_supp : ∀ o < 17, 0 < histI.getD o 0 →
    o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 8 ∨ o = 10 := by
  decide

theorem histO_supp : ∀ o < 17, 0 < histO.getD o 0 → o = 1 ∨ o = 5 ∨ o = 8 := by
  decide

theorem count_double (L : List ℕ) (n : ℕ) :
    (L.map (2 * ·)).count n = if n % 2 = 0 then L.count (n / 2) else 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.count_cons, ih, List.count_cons]
    by_cases h : n % 2 = 0
    · rw [if_pos h, if_pos h]
      by_cases ha : a = n / 2
      · rw [if_pos (by simp; omega), if_pos (by simp [ha])]
      · rw [if_neg (by simp; omega), if_neg (by simp [ha])]
    · rw [if_neg h, if_neg h, if_neg (by simp; omega)]

theorem mem_sl2 (M : SL2) : M ∈ sl2List := by
  have hf : ∀ x : F9, x ∈ f9List := by
    intro x
    rcases x with ⟨a, b⟩
    revert a b
    decide
  have h := M.det_coe
  rw [Matrix.det_fin_two] at h
  simp only [sl2List, List.mem_flatMap, List.mem_filterMap]
  refine ⟨(M : 𝕄) 0 0, hf _, (M : 𝕄) 0 1, hf _, (M : 𝕄) 1 0, hf _, (M : 𝕄) 1 1, hf _, ?_⟩
  split
  · exact congrArg some (Subtype.ext (Matrix.eta_fin_two _).symm)
  · rename_i hne
    exact absurd h hne

theorem enc_mem_codes (M : SL2) : enc M ∈ codes := by
  rw [← sl2_map]
  exact List.mem_map.mpr ⟨M, mem_sl2 M, rfl⟩

theorem card_sl2_count (F : ℕ → ℕ) (n : ℕ) :
    (Finset.univ.filter fun g : SL2 => F (enc g) = n).card = (codes.map F).count n := by
  have hU : (Finset.univ : Finset SL2) = sl2List.toFinset := by
    ext g
    simp [mem_sl2 g]
  have hF : (sl2List.toFinset.filter fun g => F (enc g) = n) =
      (sl2List.filter fun g => decide (F (enc g) = n)).toFinset := by
    ext g
    simp
  rw [hU, hF, card_filter, ← sl2_map, List.map_map, List.count_eq_countP,
    List.countP_map, List.countP_eq_length_filter]
  congr 1

@[expose] def outerL (g : SL2) : Lg := ⟨g, Multiplicative.ofAdd 1⟩

theorem outerL_injective : Function.Injective outerL := fun _ _ h =>
  congrArg SemidirectProduct.left h

theorem parityL_outerL (g : SL2) : parityL (outerL g) = Multiplicative.ofAdd 1 := rfl

theorem parityL_outerL_ne (g : SL2) : parityL (outerL g) ≠ 1 := by
  rw [parityL_outerL]
  decide

theorem lg_cases (l : Lg) : (∃ g, l = innerL g) ∨ ∃ g, l = outerL g := by
  rcases l with ⟨g, a⟩
  obtain ⟨a, rfl⟩ : ∃ a', a = Multiplicative.ofAdd a' := ⟨a.toAdd, rfl⟩
  fin_cases a
  · exact Or.inl ⟨g, rfl⟩
  · exact Or.inr ⟨g, rfl⟩

theorem outerL_sq (g : SL2) : outerL g ^ 2 = innerL (g * sigmaAut g) := by
  rw [pow_two]
  refine SemidirectProduct.ext ?_ ?_
  · change g * sigmaHom (Multiplicative.ofAdd 1) g = g * sigmaAut g
    rw [sigmaHom_ofAdd_one]
  · change Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1
    decide

theorem orderOf_outerL (g : SL2) : orderOf (outerL g) = 2 * orderOf (g * sigmaAut g) := by
  have h2 : 2 ∣ orderOf (outerL g) := by
    have h := orderOf_map_dvd parityL (outerL g)
    have he : orderOf (parityL (outerL g)) = 2 := by
      rw [parityL_outerL]
      exact orderOf_eq_prime (by decide) (by decide)
    rwa [he] at h
  have hsq := orderOf_pow_of_dvd (x := outerL g) two_ne_zero h2
  rw [outerL_sq, orderOf_injective innerL innerL_injective] at hsq
  rw [hsq]
  exact (Nat.mul_div_cancel' h2).symm

theorem orderOf_eq_ordK (M : SL2) (h : ordK (enc M) ≠ 0) : orderOf M = ordK (enc M) := by
  rw [← ordL_innerL] at h ⊢
  rw [← orderOf_injective innerL innerL_injective M]
  exact ordLAux_spec (innerL M) 16 1 (normL (innerL M)) (by rw [normL_eq, pow_one]) le_rfl
    (fun j hj1 hj => by omega) h

theorem ordLAux_ne_zero (l : Lg) : ∀ (k n : ℕ) (p : Lg), p = l ^ n → 1 ≤ n →
    (∃ m, n ≤ m ∧ m < n + k ∧ l ^ m = 1) → ordLAux l k p n ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro n p _ _ ⟨m, h1, h2, _⟩
    omega
  | succ k ih =>
    intro n p hp hn ⟨m, h1, h2, hm⟩
    simp only [ordLAux]
    split_ifs with hp1
    · omega
    · have hmn : m ≠ n := by
        intro e
        apply hp1
        rw [hp, ← e]
        exact hm
      exact ih (n + 1) _ (by rw [normL_eq, hp, pow_succ]) (by omega) ⟨m, by omega, by omega, hm⟩

theorem ordL_eq_orderOf (l : Lg) (h : orderOf l ≤ 16) : ordL l = orderOf l := by
  have hpos : 0 < orderOf l := orderOf_pos l
  have hne : ordL l ≠ 0 := ordLAux_ne_zero l 16 1 (normL l) (by rw [normL_eq, pow_one]) le_rfl
    ⟨orderOf l, by omega, by omega, pow_orderOf_eq_one l⟩
  exact (ordLAux_spec l 16 1 (normL l) (by rw [normL_eq, pow_one]) le_rfl
    (fun j hj1 hj => by omega) hne).symm

theorem outK_enc (g : SL2) : outK (enc g) = enc (g * sigmaAut g) := by
  rw [enc_mul, enc_sigma]
  rfl

theorem ordK_I (hI : chkHistIK = true) (g : SL2) :
    ordK (enc g) = 1 ∨ ordK (enc g) = 2 ∨ ordK (enc g) = 3 ∨ ordK (enc g) = 4 ∨
      ordK (enc g) = 5 ∨ ordK (enc g) = 6 ∨ ordK (enc g) = 8 ∨ ordK (enc g) = 10 := by
  have hmem : ordK (enc g) ∈ codes.map ordK := List.mem_map.mpr ⟨enc g, enc_mem_codes g, rfl⟩
  exact histI_supp _ (ordK_lt _) (pos_of_hist (eq_of_beq hI) hmem (ordK_lt _))

theorem ordK_O (hO : chkHistOK = true) (g : SL2) :
    ordK (outK (enc g)) = 1 ∨ ordK (outK (enc g)) = 5 ∨ ordK (outK (enc g)) = 8 := by
  have hmem : ordK (outK (enc g)) ∈ codes.map fun x => ordK (outK x) :=
    List.mem_map.mpr ⟨enc g, enc_mem_codes g, rfl⟩
  exact histO_supp _ (ordK_lt _) (pos_of_hist (eq_of_beq hO) hmem (ordK_lt _))

theorem orderOf_sq_outer (hO : chkHistOK = true) (g : SL2) :
    orderOf (g * sigmaAut g) = ordK (outK (enc g)) := by
  rw [outK_enc]
  apply orderOf_eq_ordK
  rw [← outK_enc]
  rcases ordK_O hO g with h | h | h <;> omega

theorem ordL_outerL (hO : chkHistOK = true) (g : SL2) :
    ordL (outerL g) = 2 * ordK (outK (enc g)) := by
  have ho := orderOf_sq_outer hO g
  rw [ordL_eq_orderOf _ (by rw [orderOf_outerL, ho]; rcases ordK_O hO g with h | h | h <;> omega),
    orderOf_outerL, ho]

theorem card_split (P : Lg → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun g => P (innerL g)).card +
      (Finset.univ.filter fun g => P (outerL g)).card := by
  have hU : (Finset.univ : Finset Lg) = Finset.univ.image innerL ∪ Finset.univ.image outerL := by
    ext l
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff]
    rcases lg_cases l with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact Or.inl ⟨g, rfl⟩
    · exact Or.inr ⟨g, rfl⟩
  have hD : Disjoint (Finset.univ.image innerL) (Finset.univ.image outerL) := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨g, rfl⟩ := h1
    obtain ⟨g', hg'⟩ := h2
    have h := congrArg parityL hg'
    rw [parityL_innerL] at h
    exact parityL_outerL_ne g' h
  rw [hU, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hD),
    Finset.filter_image, Finset.filter_image, Finset.card_image_of_injective _ innerL_injective,
    Finset.card_image_of_injective _ outerL_injective]

theorem card_ordL_eq (hI : chkHistIK = true) (hO : chkHistOK = true) (n : ℕ) (hn : n < 17) :
    (Finset.univ.filter fun l : Lg => ordL l = n).card =
      histI.getD n 0 + if n % 2 = 0 then histO.getD (n / 2) 0 else 0 := by
  rw [card_split]
  simp only [ordL_innerL, ordL_outerL hO]
  rw [card_sl2_count ordK n, card_sl2_count (fun x => 2 * ordK (outK x)) n,
    count_of_hist (eq_of_beq hI) hn]
  have hm : (codes.map fun x => 2 * ordK (outK x)) =
      (codes.map fun x => ordK (outK x)).map (2 * ·) := by
    rw [List.map_map]
    rfl
  rw [hm, count_double]
  split_ifs
  · rw [count_of_hist (eq_of_beq hO) (by omega)]
  · rfl

theorem ordL_mem_of (hI : chkHistIK = true) (hO : chkHistOK = true) (l : Lg) :
    ordL l ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 16} : Finset ℕ) := by
  rcases lg_cases l with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · rw [ordL_innerL]
    rcases ordK_I hI g with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  · rw [ordL_outerL hO]
    rcases ordK_O hO g with h | h | h <;> rw [h] <;> decide

theorem card_outer_inv_of (hO : chkHistOK = true) :
    (Finset.univ.filter fun l : Lg => parityL l ≠ 1 ∧ l ^ 2 = 1).card = 72 := by
  rw [card_split]
  have h0 : (Finset.univ.filter fun g : SL2 => parityL (innerL g) ≠ 1 ∧ innerL g ^ 2 = 1) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun g _ h => h.1 (parityL_innerL g)
  have h1 : (Finset.univ.filter fun g : SL2 => parityL (outerL g) ≠ 1 ∧ outerL g ^ 2 = 1) =
      Finset.univ.filter fun g : SL2 => ordK (outK (enc g)) = 1 := by
    apply Finset.filter_congr
    intro g _
    rw [outerL_sq, ← orderOf_sq_outer hO, orderOf_eq_one_iff, map_eq_one_iff innerL innerL_injective]
    exact and_iff_right (parityL_outerL_ne g)
  rw [h0, h1, Finset.card_empty, zero_add, card_sl2_count (fun x => ordK (outK x)) 1,
    count_of_hist (eq_of_beq hO) (by norm_num)]
  rfl

theorem no_outer_sq_of (hO : chkHistOK = true) :
    ∀ l : Lg, parityL l ≠ 1 → l ^ 2 ≠ innerL minusOne := by
  intro l hl hsq
  rcases lg_cases l with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact hl (parityL_innerL g)
  · rw [outerL_sq] at hsq
    have h := congrArg orderOf (innerL_injective hsq)
    rw [orderOf_sq_outer hO, orderOf_minusOne] at h
    rcases ordK_O hO g with h' | h' | h' <;> omega

end CFSG.KC.Q9Lg
