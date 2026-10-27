module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux22
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData6
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenNat

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open E8TenTwo

section F4

variable {L : Type} [Field L] [CharP L 2]

theorem two_eq_zero_L : (2 : L) = 0 := CharP.cast_eq_zero L 2

@[expose] def emb (ω : L) (x : ℕ) : L :=
  if x = 1 then 1 else if x = 2 then ω else if x = 3 then ω + 1 else 0

@[simp] theorem emb_zero (ω : L) : emb ω 0 = 0 := by simp [emb]
@[simp] theorem emb_one (ω : L) : emb ω 1 = 1 := by simp [emb]
@[simp] theorem emb_two (ω : L) : emb ω 2 = ω := by simp [emb]
@[simp] theorem emb_three (ω : L) : emb ω 3 = ω + 1 := by simp [emb]

theorem char2_aux {ω : L} (hω : ω ^ 2 + ω + 1 = 0) :
    (2 : L) = 0 ∧ (3 : L) = 1 ∧ (4 : L) = 0 ∧ ω ^ 2 = ω + 1 ∧ ω ^ 3 = 1 := by
  have h2 := two_eq_zero_L (L := L)
  refine ⟨h2, by linear_combination h2, by linear_combination 2 * h2,
    by linear_combination hω - (ω + 1) * h2, ?_⟩
  linear_combination (ω - 1) * hω

theorem emb_xor {ω : L} {x y : ℕ} (hx : x < 4) (hy : y < 4) :
    emb ω (x ^^^ y) = emb ω x + emb ω y := by
  have h2 := two_eq_zero_L (L := L)
  interval_cases x <;> interval_cases y <;> simp [emb] <;> ring_nf <;> simp [h2] <;>
    first | done | ring1 | linear_combination (-1 : L) * h2 | linear_combination (-ω) * h2 |
      linear_combination (1 : L) * h2 | linear_combination ω * h2

theorem emb_f4mulW {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {x : ℕ} (hx : x < 4) :
    emb ω (f4mulW x) = ω * emb ω x := by
  obtain ⟨h2, h3, h4, hω2, hω3⟩ := char2_aux hω
  interval_cases x <;> simp [emb, f4mulW] <;> ring_nf <;> simp [h2, h3, hω2] <;>
    first | done | ring1 | linear_combination (-1 : L) * h2 | linear_combination (-ω) * h2 |
      linear_combination (1 : L) * h2 | linear_combination ω * h2

theorem emb_f4mul {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {sc : ℕ} (hsc : sc = 1 ∨ sc = 2) {y : ℕ}
    (hy : y < 4) : emb ω (f4mul sc y) = emb ω sc * emb ω y := by
  rcases hsc with rfl | rfl
  · simp [f4mul]
  · simp [f4mul]
    exact emb_f4mulW hω hy

theorem emb_f4sq {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {x : ℕ} (hx : x < 4) :
    emb ω (f4sq x) = emb ω x ^ 2 := by
  obtain ⟨h2, h3, h4, hω2, hω3⟩ := char2_aux hω
  interval_cases x <;> simp [emb, f4sq] <;> ring_nf <;> simp [h2, h3, hω2] <;>
    first | done | ring1 | linear_combination (-1 : L) * h2 | linear_combination (-ω) * h2 |
      linear_combination (1 : L) * h2 | linear_combination ω * h2

theorem omega_ne_zero {ω : L} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  rintro rfl
  simp at hω

theorem omega_add_one_ne_zero {ω : L} (hω : ω ^ 2 + ω + 1 = 0) : ω + 1 ≠ 0 := by
  intro h
  have h2 := two_eq_zero_L (L := L)
  have : ω = -1 := by linear_combination h
  rw [this] at hω
  exact one_ne_zero (by linear_combination hω)

theorem emb_eq_zero {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {x : ℕ} (hx : x < 4) (h : emb ω x = 0) :
    x = 0 := by
  interval_cases x
  · rfl
  · simp at h
  · exact absurd (by simpa using h) (omega_ne_zero hω)
  · exact absurd (by simpa using h) (omega_add_one_ne_zero hω)

theorem quad_pow4 {z : L} (hz : z ^ 2 + z + 1 = 0) : z ^ 4 = z := by
  linear_combination z * (z - 1) * hz

theorem emb_pow4 {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {x : ℕ} (hx : x < 4) :
    emb ω x ^ 4 = emb ω x := by
  have h2 := two_eq_zero_L (L := L)
  interval_cases x
  · simp
  · simp
  · simpa using quad_pow4 hω
  · simp only [emb_three]
    exact quad_pow4 (z := ω + 1) (by linear_combination hω + (ω + 1) * h2)

theorem F4_cases {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {c : L} (hc : c ^ 4 = c) :
    ∃ a : ℕ, a < 4 ∧ c = emb ω a := by
  have h2 := two_eq_zero_L (L := L)
  have h0 : c * ((c - 1) * (c ^ 2 + c + 1)) = 0 := by linear_combination hc
  rcases mul_eq_zero.1 h0 with h | h
  · exact ⟨0, by norm_num, by simpa using h⟩
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨1, by norm_num, by simpa using sub_eq_zero.1 h⟩
  · have h3 : (c - ω) * (c - (ω + 1)) = 0 := by
      linear_combination h + hω - (c * (ω + 1) + 1) * h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact ⟨2, by norm_num, by simpa using sub_eq_zero.1 h⟩
    · exact ⟨3, by norm_num, by simpa using sub_eq_zero.1 h⟩

end F4

section Dec

variable {L : Type} [Field L] [CharP L 2]

@[expose] def decvX (ω : L) (Xs : List ℕ) : Fn L :=
  ∑ i ∈ Finset.range 20, (Pi.single (nuW i) (emb ω (Xs.getD i 0)) : Fn L)

theorem decvX_apply_nuW (ω : L) (Xs : List ℕ) {i : ℕ} (hi : i < 20) :
    decvX ω Xs (nuW i) = emb ω (Xs.getD i 0) := by
  unfold decvX
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hj' : j < 20 := Finset.mem_range.1 hj
    have : nuW j ≠ nuW i := fun h =>
      hji (nuW_inj j (List.mem_range.2 hj') i (List.mem_range.2 hi) h)
    simp [Pi.single_apply, Ne.symm this]
  · intro h
    exact absurd (Finset.mem_range.2 hi) h

theorem decvX_apply_out (ω : L) (Xs : List ℕ) {μ : Fin Tag.E8.rank → ℤ} (h : ∀ j < 20, nuW j ≠ μ) :
    decvX ω Xs μ = 0 := by
  unfold decvX
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp [Pi.single_apply, Ne.symm (h j (Finset.mem_range.1 hj))]

theorem decvX_add {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {Xs Ys Zs : List ℕ}
    (h : ∀ i < 20, Zs.getD i 0 = Xs.getD i 0 ^^^ Ys.getD i 0)
    (hX : ∀ i, Xs.getD i 0 < 4) (hY : ∀ i, Ys.getD i 0 < 4) :
    decvX ω Zs = decvX ω Xs + decvX ω Ys := by
  unfold decvX
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Finset.mem_range.1 hi), emb_xor (ω := ω) (hX i) (hY i), Pi.single_add]

theorem decvX_ext (ω : L) {Xs Ys : List ℕ} (h : ∀ i < 20, Xs.getD i 0 = Ys.getD i 0) :
    decvX ω Xs = decvX ω Ys := by
  unfold decvX
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Finset.mem_range.1 hi)]

@[expose] def decv (ω : L) (b : ℕ) : Fn L := decvX ω (expandV b)

theorem decv_xor {ω : L} (hω : ω ^ 2 + ω + 1 = 0) (b b' : ℕ) :
    decv ω (b ^^^ b') = decv ω b + decv ω b' :=
  decvX_add hω (fun i _ => expandV_xor b b' i) (expandV_lt b) (expandV_lt b')

theorem decv_zero {ω : L} (hω : ω ^ 2 + ω + 1 = 0) : decv ω 0 = 0 := by
  have h := decv_xor hω 0 0
  rw [Nat.xor_zero] at h
  simpa using h

theorem decv_apply_nuW (ω : L) {b i : ℕ} (hi : i < 20) :
    decv ω b (nuW i) = emb ω ((expandV b).getD i 0) := decvX_apply_nuW ω _ hi

theorem decv_pair {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {k a : ℕ} (hk : k < 10) (ha : a < 4) :
    decv ω (a <<< (2 * k)) =
      Pi.single (nuW (2 * k)) (emb ω a) + Pi.single (nuW (2 * k + 1)) (emb ω a ^ 2) := by
  have hpair := expandV_pair k hk a ha
  have h1 : 2 * k < 20 := by omega
  have h2 : 2 * k + 1 < 20 := by omega
  have hne : nuW (2 * k) ≠ nuW (2 * k + 1) := fun h => by
    have := nuW_inj _ (List.mem_range.2 h1) _ (List.mem_range.2 h2) h
    omega
  funext μ
  by_cases hμ : ∃ i < 20, nuW i = μ
  · obtain ⟨i, hi, rfl⟩ := hμ
    rw [decv_apply_nuW ω hi, hpair i hi]
    simp only [Pi.add_apply, Pi.single_apply]
    have e1 : nuW i = nuW (2 * k) ↔ i = 2 * k := ⟨fun h => nuW_inj _ (List.mem_range.2 hi) _
      (List.mem_range.2 h1) h, fun h => by rw [h]⟩
    have e2 : nuW i = nuW (2 * k + 1) ↔ i = 2 * k + 1 := ⟨fun h => nuW_inj _ (List.mem_range.2 hi) _
      (List.mem_range.2 h2) h, fun h => by rw [h]⟩
    by_cases c1 : i = 2 * k
    · subst c1
      simp [hne]
    · by_cases c2 : i = 2 * k + 1
      · subst c2
        simp [Ne.symm hne, emb_f4sq hω ha]
      · simp [c1, c2, e1, e2]
  · push Not at hμ
    rw [decv, decvX_apply_out ω _ hμ]
    simp only [Pi.add_apply, Pi.single_apply]
    rw [if_neg (Ne.symm (hμ _ h1)), if_neg (Ne.symm (hμ _ h2))]
    simp

end Dec


set_option linter.unusedSectionVars false

section Factor

variable {L : Type} [Field L] [CharP L 2]

theorem nuW_root {i : ℕ} (hi : i < 20) : nuW i ∈ rootFinset Tag.E8 :=
  mem_rootFinset.2 (mem_mRoots.1 (nuW_data i (List.mem_range.2 hi)).1).1

theorem nuW_deg1 {i : ℕ} (hi : i < 20) : nuW i ∈ deg1Roots :=
  mem_deg1Roots.2 ⟨(mem_mRoots.1 (nuW_data i (List.mem_range.2 hi)).1).1,
    (mem_mRoots.1 (nuW_data i (List.mem_range.2 hi)).1).2.1⟩

theorem aE8_char2 {γ μ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset Tag.E8) (hγ0 : γ 7 = 0)
    (hμ : μ ∈ deg1Roots) :
    (aE8 γ μ : L) = if γ + μ ∈ rootFinset Tag.E8 then 1 else 0 := by
  by_cases h : γ + μ ∈ rootFinset Tag.E8
  · rw [if_pos h]
    have h1 := (adm_aE8 γ hγ hγ0 μ hμ).1 h
    rcases abs_eq (zero_le_one' ℤ) |>.1 h1 with h1 | h1 <;> rw [h1] <;> simp [CharTwo.neg_eq]
  · rw [if_neg h, (adm_aE8 γ hγ hγ0 μ hμ).2 h]
    simp

theorem factor_lemma {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {t q : ℕ} (ht : t < 4) (hq : q < 3)
    {sc : ℕ} (hsc : sc = 1 ∨ sc = 2) {Xs : List ℕ} (hX : ∀ i, Xs.getD i 0 < 4) :
    actOp aE8 (trRoot t q) (emb ω sc) (decvX ω Xs) =
      decvX ω (modelFactor ((triples.getD t []).getD q []) sc Xs) := by
  have hγ := trRoot_P1 t (List.mem_range.2 ht) q (List.mem_range.2 hq)
  have hsrc := trRoot_src t (List.mem_range.2 ht) q (List.mem_range.2 hq)
  have hcl := trRoot_close t (List.mem_range.2 ht) q (List.mem_range.2 hq)
  funext μ
  rw [actOp_eval]
  by_cases hμ : ∃ i < 20, nuW i = μ
  · obtain ⟨i, hi, rfl⟩ := hμ
    rw [decvX_apply_nuW ω Xs hi, decvX_apply_nuW ω (modelFactor _ sc Xs) hi,
      modelFactor_getD _ _ _ hi]
    rcases hsrc i (List.mem_range.2 hi) with ⟨hlt, hadd⟩ | ⟨h20, hnone⟩
    · have hs : (srcT ((triples.getD t []).getD q [])).getD i 20 < 20 := hlt
      have hs' : nuW ((srcT ((triples.getD t []).getD q [])).getD i 20) + trRoot t q = nuW i := hadd
      set s := (srcT ((triples.getD t []).getD q [])).getD i 20 with hsdef
      rw [if_pos hs, emb_xor (hX i) (f4mul_lt sc _ (hX s)), emb_f4mul hω hsc (hX s)]
      have e1 : nuW i - trRoot t q = nuW s := (eq_sub_of_add_eq hs').symm
      rw [e1, decvX_apply_nuW ω Xs hs, aE8_char2 hγ.1 hγ.2 (nuW_deg1 hs),
        if_pos (by rw [add_comm, hs']; exact nuW_root hi)]
      ring
    · have h20' : ¬ (srcT ((triples.getD t []).getD q [])).getD i 20 < 20 := by
        have : (srcT ((triples.getD t []).getD q [])).getD i 20 = 20 := h20
        omega
      rw [if_neg h20', Nat.xor_zero]
      rw [decvX_apply_out ω Xs (μ := nuW i - trRoot t q) (fun j hj h => hnone j (List.mem_range.2 hj)
        (by rw [h]; abel))]
      ring
  · push Not at hμ
    rw [decvX_apply_out ω Xs hμ, decvX_apply_out ω (modelFactor _ sc Xs) hμ, zero_add]
    by_cases h2 : ∃ j < 20, nuW j = μ - trRoot t q
    · obtain ⟨j, hj, hjeq⟩ := h2
      have hjμ : nuW j + trRoot t q = μ := by rw [hjeq]; abel
      by_cases hroot : trRoot t q + nuW j ∈ rootFinset Tag.E8
      · exfalso
        obtain ⟨i, hi, hie⟩ := hcl j (List.mem_range.2 hj) (by rwa [add_comm])
        exact hμ i (List.mem_range.1 hi) (by rw [hie, hjμ])
      · rw [hjeq.symm, aE8_char2 hγ.1 hγ.2 (nuW_deg1 hj), if_neg hroot]
        ring
    · push Not at h2
      rw [decvX_apply_out ω Xs h2]
      ring

end Factor

section Gen

variable {L : Type} [Field L] [CharP L 2]

@[expose] def genOp (ω : L) (g : ℕ) : Fn L →ₗ[L] Fn L :=
  if g < 4 then
    actOp aE8 (trRoot g 0) (emb ω 1) ∘ₗ actOp aE8 (trRoot g 1) (emb ω 1) ∘ₗ
      actOp aE8 (trRoot g 2) (emb ω 2)
  else
    actOp aE8 (trRoot (g % 4) 2) (emb ω 2) ∘ₗ actOp aE8 (trRoot (g % 4) 1) (emb ω 1) ∘ₗ
      actOp aE8 (trRoot (g % 4) 0) (emb ω 1)

theorem genOp_decvX {ω : L} (hω : ω ^ 2 + ω + 1 = 0) {g : ℕ} (hg : g < 8) {Xs : List ℕ}
    (hX : ∀ i, Xs.getD i 0 < 4) : genOp ω g (decvX ω Xs) = decvX ω (modelGen g Xs) := by
  unfold genOp modelGen genFac
  by_cases hg4 : g < 4
  · simp only [if_pos hg4, Nat.mod_eq_of_lt hg4, List.foldr_cons, List.foldr_nil]
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      factor_lemma hω hg4 (by norm_num : 2 < 3) (Or.inr rfl) hX,
      factor_lemma hω hg4 (by norm_num : 1 < 3) (Or.inl rfl)
        (modelFactor_lt _ _ _ hX),
      factor_lemma hω hg4 (by norm_num : 0 < 3) (Or.inl rfl)
        (modelFactor_lt _ _ _ (modelFactor_lt _ _ _ hX))]
  · have hm : g % 4 < 4 := Nat.mod_lt _ (by norm_num)
    simp only [if_neg hg4, List.foldr_cons, List.foldr_nil]
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      factor_lemma hω hm (by norm_num : 0 < 3) (Or.inl rfl) hX,
      factor_lemma hω hm (by norm_num : 1 < 3) (Or.inl rfl)
        (modelFactor_lt _ _ _ hX),
      factor_lemma hω hm (by norm_num : 2 < 3) (Or.inr rfl)
        (modelFactor_lt _ _ _ (modelFactor_lt _ _ _ hX))]

end Gen

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
