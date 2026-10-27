module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCentE
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrameNorm

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native

theorem frameWt_add (u v : FrameVec) :
    frameWt (u + v) = framePop (frameEncode u ^^^ frameEncode v) := by
  rw [frameWt_eq, frameEncode_add]

theorem apply_eq_one_iff (u : FrameVec) (k : Fin 8) :
    u k = 1 ↔ (frameEncode u).testBit k = true := by
  conv_lhs => rw [← frameDecode_frameEncode u]
  rw [frameDecode]
  by_cases h : (frameEncode u).testBit k <;> simp [h]

theorem triple_spec {a b c : ℕ} (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (ha2 : framePop a = 2) (hb2 : framePop b = 2) (hc2 : framePop c = 2)
    (hab : framePop (a ^^^ b) = 2) (hac : framePop (a ^^^ c) = 2) (hbc : framePop (b ^^^ c) = 2)
    (hne : c ≠ a ^^^ b) :
    ∃ k < 8, a.testBit k = true ∧ b.testBit k = true ∧ c.testBit k = true := by
  have h := triple_check
  rw [tripleCheck, List.all_eq_true] at h
  have h1 := h a (List.mem_range.2 ha)
  simp only [ha2, beq_self_eq_true, Bool.not_true, Bool.false_or, List.all_eq_true,
    List.mem_range] at h1
  have h2 := h1 b hb
  simp only [hb2, hab, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    List.all_eq_true, List.mem_range] at h2
  have h3 := h2 c hc
  have hne' : (c != a ^^^ b) = true := bne_iff_ne.2 hne
  simp only [hc2, hac, hbc, hne', beq_self_eq_true, Bool.and_self, Bool.not_true,
    Bool.false_or, List.any_eq_true, List.mem_range, Bool.and_eq_true] at h3
  obtain ⟨k, hk, ⟨h4, h5⟩, h6⟩ := h3
  exact ⟨k, hk, h4, h5, h6⟩

theorem pair2_spec {a b : ℕ} (ha : a < 256) (hb : b < 256) (ha2 : framePop a = 2)
    (hb2 : framePop b = 2) (hab : framePop (a ^^^ b) = 2) {k l : ℕ} (hk : k < 8) (hl : l < 8)
    (h1 : a.testBit k = true) (h2 : b.testBit k = true) (h3 : a.testBit l = true)
    (h4 : b.testBit l = true) : k = l := by
  have h := pair2_check
  rw [pairCheck2, List.all_eq_true] at h
  have h5 := h a (List.mem_range.2 ha)
  simp only [ha2, beq_self_eq_true, Bool.not_true, Bool.false_or, List.all_eq_true,
    List.mem_range] at h5
  have h6 := h5 b hb
  simp only [hb2, hab, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    List.all_eq_true, List.mem_range] at h6
  have h7 := h6 k hk l hl
  simpa [h1, h2, h3, h4] using h7

theorem triple_common {u v t : FrameVec} (hu : frameWt u = 2) (hv : frameWt v = 2)
    (ht : frameWt t = 2) (huv : frameWt (u + v) = 2) (hut : frameWt (u + t) = 2)
    (hvt : frameWt (v + t) = 2) (hne : t ≠ u + v) : ∃ k, u k = 1 ∧ v k = 1 ∧ t k = 1 := by
  rw [frameWt_eq] at hu hv ht
  rw [frameWt_add] at huv hut hvt
  have hne' : frameEncode t ≠ frameEncode u ^^^ frameEncode v := fun h =>
    hne (frameEncode_injective (h.trans (frameEncode_add u v).symm))
  obtain ⟨k, hk, h1, h2, h3⟩ := triple_spec (frameEncode_lt u) (frameEncode_lt v)
    (frameEncode_lt t) hu hv ht huv hut hvt hne'
  exact ⟨⟨k, hk⟩, (apply_eq_one_iff _ _).2 h1, (apply_eq_one_iff _ _).2 h2,
    (apply_eq_one_iff _ _).2 h3⟩

theorem pair_common_unique {u v : FrameVec} (hu : frameWt u = 2) (hv : frameWt v = 2)
    (huv : frameWt (u + v) = 2) {k l : Fin 8} (hk : u k = 1 ∧ v k = 1)
    (hl : u l = 1 ∧ v l = 1) : k = l := by
  rw [frameWt_eq] at hu hv
  rw [frameWt_add] at huv
  exact Fin.ext (pair2_spec (frameEncode_lt u) (frameEncode_lt v) hu hv huv k.2 l.2
    ((apply_eq_one_iff _ _).1 hk.1) ((apply_eq_one_iff _ _).1 hk.2)
    ((apply_eq_one_iff _ _).1 hl.1) ((apply_eq_one_iff _ _).1 hl.2))

theorem frameEncode_frameE (i : Fin 8) : frameEncode (frameE i) = 2 ^ (i : ℕ) := by
  rw [frameE_eq_frameDecode, frameEncode_frameDecode _ (by fin_cases i <;> decide)]

theorem popcount_sub_bit : ∀ n < 256, ∀ c < 8, framePop n = 2 → n.testBit c = true →
    framePop (n ^^^ 2 ^ c) = 1 := by
  decide +kernel

theorem frameVec_add_self (v : FrameVec) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem eq_frameE_of_frameWt_one {w : FrameVec} (h : frameWt w = 1) : ∃ d, w = frameE d := by
  obtain ⟨d, hd⟩ := Finset.card_eq_one.1 h
  refine ⟨d, ?_⟩
  rw [← blockVec_frameSupp w, hd]
  funext j
  simp [blockVec, frameE]

theorem eq_frameE_add {u : FrameVec} (hu : frameWt u = 2) {c : Fin 8} (hc : u c = 1) :
    ∃ d, d ≠ c ∧ u = frameE c + frameE d := by
  have h1 : frameWt (u + frameE c) = 1 := by
    rw [frameWt_add, frameEncode_frameE]
    rw [frameWt_eq] at hu
    exact popcount_sub_bit _ (frameEncode_lt u) _ c.2 hu ((apply_eq_one_iff _ _).1 hc)
  obtain ⟨d, hd⟩ := eq_frameE_of_frameWt_one h1
  have hu' : u = frameE c + frameE d := by
    rw [← hd, add_comm u (frameE c), ← add_assoc, frameVec_add_self, zero_add]
  refine ⟨d, fun hdc => ?_, hu'⟩
  rw [hdc, frameVec_add_self] at hu'
  rw [hu', (frameWt_eq_zero_iff 0).2 rfl] at hu
  exact absurd hu (by norm_num)

theorem frameWt_frameE_add : ∀ i j : Fin 8, i ≠ j → frameWt (frameE i + frameE j) = 2 := by
  decide

theorem frameE_add_mem (i j : Fin 8) : frameE i + frameE j ∈ evenSub := by
  rw [mem_evenSub]
  revert i j
  decide

theorem frameE_inj : ∀ i j : Fin 8, frameE i = frameE j → i = j := by decide

theorem frameE_injective : Function.Injective frameE := fun i j h => frameE_inj i j h

theorem sum_frameE (s : Finset (Fin 8)) : ∑ j ∈ s, frameE j = blockVec s := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, blockVec_empty]
  | insert a s ha ih => rw [Finset.sum_insert ha, ih, blockVec_insert ha]

theorem even_eq_sum {v : FrameVec} (hv : v ∈ evenSub) :
    v = ∑ j ∈ frameSupp v, (frameE 0 + frameE j) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, sum_frameE, blockVec_frameSupp]
  have h : Even (frameSupp v).card := Nat.even_iff.2 ((mem_evenSub_iff_frameWt v).1 hv)
  obtain ⟨k, hk⟩ := h
  rw [hk, add_nsmul, frameVec_add_self, zero_add]

theorem map_sum_evenSub (f : FrameVec → FrameVec)
    (hadd : ∀ v ∈ evenSub, ∀ v' ∈ evenSub, f (v + v') = f v + f v') (h0 : f 0 = 0)
    (w : Fin 8 → FrameVec) (hw : ∀ j, w j ∈ evenSub) (s : Finset (Fin 8)) :
    f (∑ j ∈ s, w j) = ∑ j ∈ s, f (w j) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, h0]
  | insert a s ha ih =>
    have hs : (∑ j ∈ s, w j) ∈ evenSub := AddSubgroup.sum_mem _ fun j _ => hw j
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact hadd _ (hw a) _ hs

theorem frameE_ne12 : ∀ j : Fin 8, frameE 0 + frameE j ≠ frameE 1 + frameE 2 := by decide

theorem exists_perm_of_wt2 (f : FrameVec → FrameVec)
    (hadd : ∀ v ∈ evenSub, ∀ v' ∈ evenSub, f (v + v') = f v + f v')
    (hinj : ∀ v ∈ evenSub, ∀ v' ∈ evenSub, f v = f v' → v = v')
    (hwt : ∀ v ∈ evenSub, frameWt v = 2 → frameWt (f v) = 2) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ v ∈ evenSub, f v = permVec σ v := by
  have h0 : f 0 = 0 := by
    have := hadd 0 (zero_mem _) 0 (zero_mem _)
    rw [add_zero] at this
    exact add_eq_left.1 this.symm
  set u : Fin 8 → FrameVec := fun j => f (frameE 0 + frameE j) with hu
  have hwu : ∀ j, j ≠ 0 → frameWt (u j) = 2 := fun j hj =>
    hwt _ (frameE_add_mem 0 j) (frameWt_frameE_add 0 j (Ne.symm hj))
  have hsum : ∀ i j, u i + u j = f (frameE i + frameE j) := by
    intro i j
    rw [hu, ← hadd _ (frameE_add_mem 0 i) _ (frameE_add_mem 0 j)]
    congr 1
    rw [add_add_add_comm, frameVec_add_self, zero_add]
  have hwuu : ∀ i j, i ≠ j → frameWt (u i + u j) = 2 := fun i j hij => by
    rw [hsum]
    exact hwt _ (frameE_add_mem i j) (frameWt_frameE_add i j hij)
  have hne12 : ∀ j, u j ≠ u 1 + u 2 := by
    intro j h
    rw [hsum] at h
    exact frameE_ne12 j (hinj _ (frameE_add_mem 0 j) _ (frameE_add_mem 1 2) h)
  have h1 := hwu 1 (by decide)
  have h2 := hwu 2 (by decide)
  have h12 := hwuu 1 2 (by decide)
  obtain ⟨c, hc1, hc2, -⟩ := triple_common h1 h2 (hwu 3 (by decide)) h12
    (hwuu 1 3 (by decide)) (hwuu 2 3 (by decide)) (hne12 3)
  have hc : ∀ j, j ≠ 0 → u j c = 1 := by
    intro j hj
    by_cases hj1 : j = 1
    · rw [hj1]; exact hc1
    by_cases hj2 : j = 2
    · rw [hj2]; exact hc2
    obtain ⟨c', h1', h2', h3'⟩ := triple_common h1 h2 (hwu j hj) h12
      (hwuu 1 j (Ne.symm hj1)) (hwuu 2 j (Ne.symm hj2)) (hne12 j)
    rw [pair_common_unique h1 h2 h12 ⟨hc1, hc2⟩ ⟨h1', h2'⟩]
    exact h3'
  choose! d hd using fun j (hj : j ≠ 0) => eq_frameE_add (hwu j hj) (hc j hj)
  set τ : Fin 8 → Fin 8 := fun j => if j = 0 then c else d j with hτdef
  have hτ : Function.Injective τ := by
    intro i j hij
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · rw [hi, hj]
    · simp only [hτdef, hi, hj, ↓reduceIte] at hij
      exact absurd hij.symm (hd j hj).1
    · simp only [hτdef, hi, hj, ↓reduceIte] at hij
      exact absurd hij (hd i hi).1
    · simp only [hτdef, hi, hj, ↓reduceIte] at hij
      have h3 : u i = u j := by rw [(hd i hi).2, (hd j hj).2, hij]
      exact frameE_injective (add_left_cancel
        (hinj _ (frameE_add_mem 0 i) _ (frameE_add_mem 0 j) h3))
  set σ := Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hτ) with hσdef
  have hσ : ∀ j, f (frameE 0 + frameE j) = permVec σ (frameE 0 + frameE j) := by
    intro j
    rw [permVec_add, permVec_frameE, permVec_frameE]
    by_cases hj : j = 0
    · rw [hj, frameVec_add_self, frameVec_add_self, h0]
    · change u j = _
      rw [(hd j hj).2]
      simp [hσdef, hτdef, hj]
  refine ⟨σ, fun v hv => ?_⟩
  rw [even_eq_sum hv, map_sum_evenSub f hadd h0 _ (fun j => frameE_add_mem 0 j),
    map_sum_evenSub (permVec σ) (fun _ _ _ _ => permVec_add _ _ _) rfl _
      (fun j => frameE_add_mem 0 j)]
  exact Finset.sum_congr rfl fun j _ => hσ j

theorem wt2Fix_spec {m : ℕ} (hm : m < 256) (he : framePop m % 2 = 0) (h0 : m ≠ 0) :
    fixCount 240 signArrs[m]! = 60 ↔ framePop m = 2 := by
  have h := wt2Fix_check
  rw [wt2FixCheck, List.all_eq_true] at h
  have h1 := h m (List.mem_range.2 hm)
  have he' : (framePop m % 2 == 0) = true := beq_iff_eq.2 he
  have h0' : (m == 0) = false := beq_eq_false_iff_ne.2 h0
  simp only [he', h0', Bool.not_true, Bool.false_or, beq_iff_eq] at h1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq] at h1
  exact h1

theorem fix_signPerm_iff {v : FrameVec} (hv : v ∈ evenSub) (h0 : v ≠ 0) :
    Fintype.card (Function.fixedPoints (signPerm v)) = 60 ↔ frameWt v = 2 := by
  have hm0 : frameEncode v ≠ 0 := fun h => h0 (frameEncode_injective (h.trans (by decide)))
  rw [card_fixedPoints_of_rep (rep_signArr hv), ← signArrs_encode,
    wt2Fix_spec (frameEncode_lt v) (by simpa using framePop_even hv) hm0, frameWt_eq]

theorem conj_signPerm_mem {w : Equiv.Perm (Fin 240)}
    (hn : w ∈ normalizer (eSub : Set (Equiv.Perm (Fin 240)))) {v : FrameVec} (hv : v ∈ evenSub) :
    ∃ u ∈ evenSub, w * signPerm v * w⁻¹ = signPerm u := by
  obtain ⟨u, hu, he⟩ := mem_eSub.1 ((mem_normalizer_iff.1 hn _).1 (mem_eSub.2 ⟨v, hv, rfl⟩))
  exact ⟨u, hu, he.symm⟩

theorem exists_perm_of_normalizer {w : Equiv.Perm (Fin 240)}
    (hn : w ∈ normalizer (eSub : Set (Equiv.Perm (Fin 240)))) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ v ∈ evenSub, w * signPerm v * w⁻¹ = signPerm (permVec σ v) := by
  classical
  set f : FrameVec → FrameVec := fun v =>
    if hv : v ∈ evenSub then Classical.choose (conj_signPerm_mem hn hv) else 0 with hfdef
  have hf : ∀ v (hv : v ∈ evenSub), f v ∈ evenSub ∧ w * signPerm v * w⁻¹ = signPerm (f v) := by
    intro v hv
    simp only [hfdef, hv, ↓reduceDIte]
    exact Classical.choose_spec (conj_signPerm_mem hn hv)
  have hadd : ∀ v ∈ evenSub, ∀ v' ∈ evenSub, f (v + v') = f v + f v' := by
    intro v hv v' hv'
    refine signPerm_inj (hf _ (add_mem hv hv')).1 (add_mem (hf v hv).1 (hf v' hv').1) ?_
    rw [← (hf _ (add_mem hv hv')).2, signPerm_add (hf v hv).1 (hf v' hv').1, ← (hf v hv).2,
      ← (hf v' hv').2, signPerm_add hv hv']
    group
  have hinj : ∀ v ∈ evenSub, ∀ v' ∈ evenSub, f v = f v' → v = v' := by
    intro v hv v' hv' h
    refine signPerm_inj hv hv' ?_
    have h1 := (hf v hv).2.trans (h ▸ (hf v' hv').2.symm)
    simpa using h1
  have hwt : ∀ v ∈ evenSub, frameWt v = 2 → frameWt (f v) = 2 := by
    intro v hv h2
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [(frameWt_eq_zero_iff 0).2 rfl] at h2
      exact absurd h2 (by norm_num)
    have hfv0 : f v ≠ 0 := by
      intro h
      have h1 := (hf v hv).2
      rw [h, signPerm_zero, mul_inv_eq_one, mul_eq_left] at h1
      exact hv0 (signPerm_inj hv (zero_mem _) (h1.trans signPerm_zero.symm))
    rw [← fix_signPerm_iff (hf v hv).1 hfv0, ← (hf v hv).2, card_fixedPoints_conj,
      fix_signPerm_iff hv hv0]
    exact h2
  obtain ⟨σ, hσ⟩ := exists_perm_of_wt2 f hadd hinj hwt
  exact ⟨σ, fun v hv => by rw [(hf v hv).2, hσ v hv]⟩

theorem permMat_conj_mem (σ : Equiv.Perm (Fin 8)) {g : Equiv.Perm (Fin 240)} (hg : g ∈ eSub) :
    permMat σ * g * (permMat σ)⁻¹ ∈ eSub := by
  obtain ⟨v, hv, rfl⟩ := mem_eSub.1 hg
  rw [permMat_conj_signPerm σ hv]
  exact mem_eSub.2 ⟨_, permVec_mem_evenSub σ hv, rfl⟩

theorem permMat_mem_normalizer (σ : Equiv.Perm (Fin 8)) :
    permMat σ ∈ normalizer (eSub : Set (Equiv.Perm (Fin 240))) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨permMat_conj_mem σ, fun hg => ?_⟩
  have h := permMat_conj_mem σ⁻¹ hg
  rwa [← permMat_inv, inv_inv, show (permMat σ)⁻¹ * (permMat σ * g * (permMat σ)⁻¹) * permMat σ = g
    by group] at h

theorem eSub_le_wE8 : eSub ≤ wE8 := eSub_le_wPlus.trans wPlus_le

theorem permMat_mem_eSub_iff (τ : Equiv.Perm (Fin 8)) : permMat τ ∈ eSub ↔ τ = 1 := by
  refine ⟨fun h => eq_of_permVec_evenSub fun v hv => ?_, fun h => by
    rw [h, permMat_one]; exact one_mem _⟩
  refine signPerm_inj (permVec_mem_evenSub τ hv) hv ?_
  rw [← permMat_conj_signPerm τ hv, eSub_comm h (mem_eSub.2 ⟨v, hv, rfl⟩), mul_inv_cancel_right,
    permVec_one]

theorem exists_decomp {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hn : w ∈ normalizer (eSub : Set (Equiv.Perm (Fin 240)))) :
    ∃ σ : Equiv.Perm (Fin 8), w * (permMat σ)⁻¹ ∈ eSub ∧
      ∀ v ∈ evenSub, w * signPerm v * w⁻¹ = signPerm (permVec σ v) := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_normalizer hn
  refine ⟨σ, centralizer_eSub (mul_mem hw (inv_mem (permMat_mem_wE8 σ))) fun e he => ?_, hσ⟩
  obtain ⟨v, hv, rfl⟩ := mem_eSub.1 he
  have h1 := permMat_conj_signPerm σ⁻¹ hv
  have h2 := hσ _ (permVec_mem_evenSub σ⁻¹ hv)
  rw [permVec_permVec_inv] at h2
  rw [permMat_inv]
  calc w * permMat σ⁻¹ * signPerm v
      = w * (permMat σ⁻¹ * signPerm v * (permMat σ⁻¹)⁻¹) * permMat σ⁻¹ := by group
    _ = w * signPerm (permVec σ⁻¹ v) * w⁻¹ * (w * permMat σ⁻¹) := by rw [h1]; group
    _ = signPerm v * (w * permMat σ⁻¹) := by rw [h2]

theorem decomp_unique {e e' : Equiv.Perm (Fin 240)} (he : e ∈ eSub) (he' : e' ∈ eSub)
    {σ σ' : Equiv.Perm (Fin 8)} (h : e * permMat σ = e' * permMat σ') : e = e' ∧ σ = σ' := by
  have h1 : permMat (σ * σ'⁻¹) ∈ eSub := by
    rw [permMat_mul, ← permMat_inv]
    have : permMat σ * (permMat σ')⁻¹ = e⁻¹ * e' := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h, mul_inv_cancel_right]
    rw [this]
    exact mul_mem (inv_mem he) he'
  have hσ : σ = σ' := mul_inv_eq_one.1 ((permMat_mem_eSub_iff _).1 h1)
  subst hσ
  exact ⟨mul_right_cancel h, rfl⟩

theorem normalizer_eSub_spec {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hn : w ∈ normalizer (eSub : Set (Equiv.Perm (Fin 240)))) :
    ∃ σ : Equiv.Perm (Fin 8), (∀ v ∈ evenSub, w * signPerm v * w⁻¹ = signPerm (permVec σ v)) ∧
      (w ∈ wPlus ↔ σ ∈ alternatingGroup (Fin 8)) := by
  obtain ⟨σ, he, hσ⟩ := exists_decomp hw hn
  refine ⟨σ, hσ, ?_⟩
  have hs : Equiv.Perm.sign (w * (permMat σ)⁻¹) = 1 := (mem_wPlus_iff.1 (eSub_le_wPlus he)).2
  rw [map_mul, map_inv, sign_permMat, mul_inv_eq_one] at hs
  rw [mem_wPlus_iff, Equiv.Perm.mem_alternatingGroup, hs]
  exact and_iff_right hw

theorem card_eSub : Nat.card eSub = 2 ^ 7 := by
  have e : evenSub ≃ eSub :=
    Equiv.ofBijective (fun v => ⟨signPerm v, mem_eSub.2 ⟨v, v.2, rfl⟩⟩)
      ⟨fun v w h => Subtype.ext (signPerm_inj v.2 w.2 (congrArg Subtype.val h)), fun g => by
        obtain ⟨v, hv, h⟩ := mem_eSub.1 g.2
        exact ⟨⟨v, hv⟩, Subtype.ext h⟩⟩
  rw [← Nat.card_congr e, Nat.card_congr evenSubEquiv.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

@[expose] def nDecomp (p : eSub × Equiv.Perm (Fin 8)) :
    (wE8 ⊓ normalizer (eSub : Set (Equiv.Perm (Fin 240))) : Subgroup (Equiv.Perm (Fin 240))) :=
  ⟨p.1 * permMat p.2, mem_inf.2 ⟨mul_mem (eSub_le_wE8 p.1.2) (permMat_mem_wE8 _),
    mul_mem (le_normalizer p.1.2) (permMat_mem_normalizer _)⟩⟩

theorem nDecomp_bijective : Function.Bijective nDecomp := by
  refine ⟨fun p q h => ?_, fun w => ?_⟩
  · have h1 := decomp_unique p.1.2 q.1.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1.1) h1.2
  · obtain ⟨σ, he, -⟩ := exists_decomp (mem_inf.1 w.2).1 (mem_inf.1 w.2).2
    exact ⟨(⟨_, he⟩, σ), Subtype.ext (inv_mul_cancel_right _ _)⟩

theorem card_normalizer_eSub : Nat.card (wE8 ⊓ normalizer (eSub : Set (Equiv.Perm (Fin 240))) :
    Subgroup (Equiv.Perm (Fin 240))) = 2 ^ 7 * 40320 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ nDecomp_bijective), Nat.card_prod, card_eSub,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

@[expose] def nDecompPlus (p : eSub × alternatingGroup (Fin 8)) :
    (wPlus ⊓ normalizer (eSub : Set (Equiv.Perm (Fin 240))) : Subgroup (Equiv.Perm (Fin 240))) :=
  ⟨p.1 * permMat p.2, mem_inf.2 ⟨mul_mem (eSub_le_wPlus p.1.2) ((permMat_mem_wPlus_iff _).2 p.2.2),
    mul_mem (le_normalizer p.1.2) (permMat_mem_normalizer _)⟩⟩

theorem nDecompPlus_bijective : Function.Bijective nDecompPlus := by
  refine ⟨fun p q h => ?_, fun w => ?_⟩
  · have h1 := decomp_unique p.1.2 q.1.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1.1) (Subtype.ext h1.2)
  · have hw := mem_inf.1 w.2
    obtain ⟨σ, he, -⟩ := exists_decomp (wPlus_le hw.1) hw.2
    have hσ : σ ∈ alternatingGroup (Fin 8) := by
      rw [← permMat_mem_wPlus_iff]
      have h1 : permMat σ = (w * (permMat σ)⁻¹)⁻¹ * w := by group
      rw [h1]
      exact mul_mem (inv_mem (eSub_le_wPlus he)) hw.1
    exact ⟨(⟨_, he⟩, ⟨σ, hσ⟩), Subtype.ext (inv_mul_cancel_right _ _)⟩

theorem card_normalizer_eSub_plus : Nat.card (wPlus ⊓
    normalizer (eSub : Set (Equiv.Perm (Fin 240))) : Subgroup (Equiv.Perm (Fin 240))) =
      2 ^ 7 * 20160 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ nDecompPlus_bijective), Nat.card_prod, card_eSub,
    card_alternatingGroup_fin_eight]

end CFSG.EvenSmallLie.OmegaEight.Weyl
