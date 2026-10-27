module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAbelP
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylNormE1

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer

@[expose] def stabVec (v : FrameVec) : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | permVec σ v = v}
  mul_mem' {σ τ} hσ hτ := by
    change permVec (σ * τ) v = v
    rw [permVec_mul, hτ, hσ]
  one_mem' := permVec_one v
  inv_mem' {σ} hσ := by
    change permVec σ⁻¹ v = v
    conv_lhs => rw [← hσ]
    exact permVec_inv_permVec σ v

theorem mem_fixSet_closure (L : List (Equiv.Perm (Fin 8))) {v : FrameVec} :
    v ∈ fixSet (closure {σ | σ ∈ L}) ↔ v ∈ evenSub ∧ ∀ σ ∈ L, permVec σ v = v := by
  refine ⟨fun h => ⟨h.1, fun σ hσ => h.2 σ (subset_closure hσ)⟩, fun h => ⟨h.1, fun σ hσ => ?_⟩⟩
  have hle : closure {σ | σ ∈ L} ≤ stabVec v := (closure_le _).2 fun σ hσ => h.2 σ hσ
  exact hle hσ

theorem vec_mem_fixSet {B : Subgroup (Equiv.Perm (Fin 240))} (hB : B ≤ nSub)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {v : FrameVec} (hv : v ∈ evenSub)
    (hvB : signPerm v ∈ B) : v ∈ fixSet (qOf B hB) := by
  refine ⟨hv, ?_⟩
  rintro σ ⟨x, rfl⟩
  have hc : (x : Equiv.Perm (Fin 240)) * signPerm v * (x : Equiv.Perm (Fin 240))⁻¹ =
      signPerm (permVec ((actOn B hB) x) v) := conj_signPerm_actE ⟨x, hB x.2⟩ hv
  rw [hab _ x.2 _ hvB, mul_inv_cancel_right] at hc
  exact signPerm_inj (permVec_mem_evenSub _ hv) hv hc.symm

theorem signPerm_mem_of_card_eq {B : Subgroup (Equiv.Perm (Fin 240))} (hB : B ≤ nSub)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hc : Nat.card (B ⊓ eSub : Subgroup (Equiv.Perm (Fin 240))) = Nat.card (fixSet (qOf B hB))) :
    ∀ k ∈ fixSet (qOf B hB), signPerm k ∈ B := by
  classical
  set S : Set FrameVec := {k | k ∈ fixSet (qOf B hB) ∧ signPerm k ∈ B} with hSdef
  have hSsub : S ⊆ fixSet (qOf B hB) := fun k hk => hk.1
  have hle : Nat.card (B ⊓ eSub : Subgroup (Equiv.Perm (Fin 240))) ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective (fun e => ⟨Classical.choose (exists_vec_of_mem_inf e),
      vec_mem_fixSet hB hab (Classical.choose_spec (exists_vec_of_mem_inf e)).1 ?_, ?_⟩) ?_
    · rw [(Classical.choose_spec (exists_vec_of_mem_inf e)).2]
      exact (mem_inf.1 e.2).1
    · rw [(Classical.choose_spec (exists_vec_of_mem_inf e)).2]
      exact (mem_inf.1 e.2).1
    · intro e f h
      have h1 := congrArg Subtype.val h
      simp only at h1
      refine Subtype.ext ?_
      rw [← (Classical.choose_spec (exists_vec_of_mem_inf e)).2,
        ← (Classical.choose_spec (exists_vec_of_mem_inf f)).2, h1]
  have heq : S = fixSet (qOf B hB) := by
    refine Set.eq_of_subset_of_ncard_le hSsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← hc]
    exact hle
  intro k hk
  rw [← heq] at hk
  exact hk.2

theorem exists_lift {B : Subgroup (Equiv.Perm (Fin 240))} (hB : B ≤ nSub)
    {g : Equiv.Perm (Fin 8)} (hg : g ∈ qOf B hB)
    (hK : ∀ k ∈ fixSet (qOf B hB), signPerm k ∈ B)
    (hrep : ∀ u ∈ evenSub, ∃ r ∈ liftReps, u + frameDecode r ∈ fixSet (qOf B hB)) :
    ∃ r ∈ liftReps, signPerm (frameDecode r) * permMat g ∈ B := by
  obtain ⟨x, rfl⟩ := hg
  have he := actE_spec ⟨x, hB x.2⟩
  obtain ⟨u, hu, hue⟩ := mem_eSub.1 he
  obtain ⟨r, hr, hk⟩ := hrep u hu
  set g := actE ⟨x, hB x.2⟩
  have hgk : permVec g (u + frameDecode r) = u + frameDecode r := hk.2 g ⟨x, rfl⟩
  have hkE : u + frameDecode r ∈ evenSub := hk.1
  have hrE : frameDecode r ∈ evenSub := by
    have := add_mem hu hkE
    rwa [← add_assoc, frameVec_add_self, zero_add] at this
  have hcomm : permMat g * signPerm (u + frameDecode r) =
      signPerm (u + frameDecode r) * permMat g := by
    have := permMat_conj_signPerm g hkE
    rw [hgk] at this
    calc permMat g * signPerm (u + frameDecode r)
        = (permMat g * signPerm (u + frameDecode r) * (permMat g)⁻¹) * permMat g := by group
      _ = signPerm (u + frameDecode r) * permMat g := by rw [this]
  refine ⟨r, hr, ?_⟩
  have hx : (x : Equiv.Perm (Fin 240)) = signPerm u * permMat g := by
    rw [hue, inv_mul_cancel_right]
  have h1 : signPerm (frameDecode r) * permMat g =
      (x : Equiv.Perm (Fin 240)) * signPerm (u + frameDecode r) := by
    rw [hx, mul_assoc, hcomm, ← mul_assoc, ← signPerm_add hu hkE, ← add_assoc,
      frameVec_add_self, zero_add]
  change signPerm (frameDecode r) * permMat g ∈ B
  rw [h1]
  exact mul_mem x.2 (hK _ hk)

theorem le_of_lifts {B X : Subgroup (Equiv.Perm (Fin 240))} (hB : B ≤ nSub)
    (hBX : B ⊓ eSub ≤ X) (hgen : qOf B hB ≤ qOf (B ⊓ X) (inf_le_left.trans hB)) : B ≤ X := by
  set C := B ⊓ X
  have hCB : C ≤ B := inf_le_left
  have hq : qOf C (hCB.trans hB) = qOf B hB := by
    refine le_antisymm ?_ hgen
    rintro σ ⟨x, rfl⟩
    exact ⟨⟨x, hCB x.2⟩, rfl⟩
  have hinf : (C ⊓ eSub : Subgroup (Equiv.Perm (Fin 240))) = B ⊓ eSub := by
    refine le_antisymm (inf_le_inf_right _ hCB) fun y hy => ?_
    exact mem_inf.2 ⟨mem_inf.2 ⟨(mem_inf.1 hy).1, hBX hy⟩, (mem_inf.1 hy).2⟩
  have hcard : Nat.card B ≤ Nat.card C := by
    rw [card_eq_card_inf_mul_card_qOf C (hCB.trans hB), card_eq_card_inf_mul_card_qOf B hB, hq,
      hinf]
  have := eq_of_le_of_card_ge hCB hcard
  rw [← this]
  exact inf_le_right

theorem qOf_abelian {B : Subgroup (Equiv.Perm (Fin 240))} (hB : B ≤ nSub)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ∀ a ∈ qOf B hB, ∀ b ∈ qOf B hB, a * b = b * a := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hab _ x.2 _ y.2)

@[expose] def pairConst (v : FrameVec) : Prop := v 0 = v 1 ∧ v 2 = v 3 ∧ v 4 = v 5 ∧ v 6 = v 7

instance (v : FrameVec) : Decidable (pairConst v) := by
  unfold pairConst
  infer_instance

theorem permVec_apply_eq {σ : Equiv.Perm (Fin 8)} {v : FrameVec} (h : permVec σ v = v)
    (i : Fin 8) : v (σ.symm i) = v i := congrFun h i

theorem permVec_swap_eq {a b : Fin 8} {v : FrameVec} (h : v a = v b) :
    permVec (Equiv.swap a b) v = v := by
  funext i
  rw [permVec_apply, Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, h]
  · rw [h2, h]
  · rfl

theorem fix_q1Gens_iff (v : FrameVec) :
    (∀ σ ∈ q1Gens, permVec σ v = v) ↔ pairConst v := by
  constructor
  · intro h
    have h0 := permVec_apply_eq (h (Equiv.swap 0 1) (by simp [q1Gens])) (0 : Fin 8)
    have h2 := permVec_apply_eq (h (Equiv.swap 2 3) (by simp [q1Gens])) (2 : Fin 8)
    have h4 := permVec_apply_eq (h (Equiv.swap 4 5) (by simp [q1Gens])) (4 : Fin 8)
    have h6 := permVec_apply_eq (h (Equiv.swap 6 7) (by simp [q1Gens])) (6 : Fin 8)
    simp only [Equiv.symm_swap] at h0 h2 h4 h6
    exact ⟨by simpa using h0.symm, by simpa using h2.symm, by simpa using h4.symm,
      by simpa using h6.symm⟩
  · rintro ⟨h01, h23, h45, h67⟩ σ hσ
    simp only [q1Gens, List.mem_cons, List.mem_nil_iff, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl
    · exact permVec_swap_eq h01
    · exact permVec_swap_eq h23
    · exact permVec_swap_eq h45
    · exact permVec_swap_eq h67

theorem fix_q0Gens_iff (v : FrameVec) :
    (∀ σ ∈ q0Gens, permVec σ v = v) ↔ pairConst v := by
  constructor
  · intro h
    have g1 := h (Equiv.swap 0 1 * Equiv.swap 2 3) (by simp [q0Gens])
    have g2 := h (Equiv.swap 0 1 * Equiv.swap 4 5) (by simp [q0Gens])
    have g3 := h (Equiv.swap 0 1 * Equiv.swap 6 7) (by simp [q0Gens])
    have h0 := permVec_apply_eq g1 (0 : Fin 8)
    have h2 := permVec_apply_eq g1 (2 : Fin 8)
    have h4 := permVec_apply_eq g2 (4 : Fin 8)
    have h6 := permVec_apply_eq g3 (6 : Fin 8)
    have e0 : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3).symm (0 : Fin 8) = (1 : Fin 8) := by
      decide
    have e2 : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3).symm (2 : Fin 8) = (3 : Fin 8) := by
      decide
    have e4 : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 4 5).symm (4 : Fin 8) = (5 : Fin 8) := by
      decide
    have e6 : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 6 7).symm (6 : Fin 8) = (7 : Fin 8) := by
      decide
    rw [e0] at h0
    rw [e2] at h2
    rw [e4] at h4
    rw [e6] at h6
    exact ⟨h0.symm, h2.symm, h4.symm, h6.symm⟩
  · rintro ⟨h01, h23, h45, h67⟩ σ hσ
    simp only [q0Gens, List.mem_cons, List.mem_nil_iff, or_false] at hσ
    rcases hσ with rfl | rfl | rfl
    · rw [permVec_mul, permVec_swap_eq h23, permVec_swap_eq h01]
    · rw [permVec_mul, permVec_swap_eq h45, permVec_swap_eq h01]
    · rw [permVec_mul, permVec_swap_eq h67, permVec_swap_eq h01]

theorem mem_fixSet_q1Sub {v : FrameVec} : v ∈ fixSet q1Sub ↔ v ∈ evenSub ∧ pairConst v := by
  rw [q1Sub, mem_fixSet_closure, fix_q1Gens_iff]

theorem mem_fixSet_q0Sub {v : FrameVec} : v ∈ fixSet q0Sub ↔ v ∈ evenSub ∧ pairConst v := by
  rw [q0Sub, mem_fixSet_closure, fix_q0Gens_iff]

theorem liftReps_spec : ∀ n < 256, framePop n % 2 = 0 →
    ∃ r ∈ liftReps, pairConst (frameDecode n + frameDecode r) := by
  decide +kernel

theorem liftReps_lt : ∀ r ∈ liftReps, r < 256 ∧ framePop r % 2 = 0 := by decide

theorem exists_liftRep {u : FrameVec} (hu : u ∈ evenSub) :
    ∃ r ∈ liftReps, u + frameDecode r ∈ evenSub ∧ pairConst (u + frameDecode r) := by
  obtain ⟨r, hr, hp⟩ := liftReps_spec _ (frameEncode_lt u) (by simpa using framePop_even hu)
  rw [frameDecode_frameEncode] at hp
  exact ⟨r, hr, add_mem hu (decode_mem_evenSub (liftReps_lt r hr).1 (liftReps_lt r hr).2), hp⟩

theorem pairConst_decomp_aux : ∀ a b c d : ZMod 2,
    (fun i => ![a, a, b, b, c, c, d, d] i : FrameVec) =
      (if a = 1 then vec2 0 1 else 0) + (if b = 1 then vec2 2 3 else 0) +
        (if c = 1 then vec2 4 5 else 0) + (if d = 1 then vec2 6 7 else 0) := by
  decide

theorem pairConst_decomp (v : FrameVec) (hv : pairConst v) : v =
    (if v 0 = 1 then vec2 0 1 else 0) + (if v 2 = 1 then vec2 2 3 else 0) +
      (if v 4 = 1 then vec2 4 5 else 0) + (if v 6 = 1 then vec2 6 7 else 0) := by
  obtain ⟨h01, h23, h45, h67⟩ := hv
  rw [← pairConst_decomp_aux]
  funext i
  fin_cases i <;> simp [h01, h23, h45, h67]

@[expose] def kOneSub : Subgroup (Equiv.Perm (Fin 240)) :=
  closure {signPerm (vec2 0 1), signPerm (vec2 2 3), signPerm (vec2 4 5), signPerm (vec2 6 7)}

theorem signPerm_ite_mem {c : Prop} [Decidable c] {i j : Fin 8} (hij : i ≠ j)
    (h : signPerm (vec2 i j) ∈ kOneSub) :
    (if c then vec2 i j else 0) ∈ evenSub ∧ signPerm (if c then vec2 i j else 0) ∈ kOneSub := by
  split_ifs
  · exact ⟨vec2_mem_evenSub i j hij, h⟩
  · exact ⟨zero_mem _, by rw [signPerm_zero]; exact one_mem _⟩

theorem signPerm_mem_kOneSub {v : FrameVec} (hv : pairConst v) : signPerm v ∈ kOneSub := by
  have g01 : signPerm (vec2 0 1) ∈ kOneSub := subset_closure (by simp)
  have g23 : signPerm (vec2 2 3) ∈ kOneSub := subset_closure (by simp)
  have g45 : signPerm (vec2 4 5) ∈ kOneSub := subset_closure (by simp)
  have g67 : signPerm (vec2 6 7) ∈ kOneSub := subset_closure (by simp)
  obtain ⟨a1, a2⟩ := signPerm_ite_mem (c := v 0 = 1) (by decide) g01
  obtain ⟨b1, b2⟩ := signPerm_ite_mem (c := v 2 = 1) (by decide) g23
  obtain ⟨c1, c2⟩ := signPerm_ite_mem (c := v 4 = 1) (by decide) g45
  obtain ⟨d1, d2⟩ := signPerm_ite_mem (c := v 6 = 1) (by decide) g67
  rw [pairConst_decomp v hv, signPerm_add (add_mem (add_mem a1 b1) c1) d1,
    signPerm_add (add_mem a1 b1) c1, signPerm_add a1 b1]
  exact mul_mem (mul_mem (mul_mem a2 b2) c2) d2

theorem signPerm_vec2_67 : signPerm (vec2 6 7) = frameElt (vec2 6 7) := signPerm_pair 6 (by decide)

theorem kOneSub_le_e1Sub : kOneSub ≤ e1Sub := by
  rw [kOneSub, closure_le]
  rintro g (rfl | rfl | rfl | rfl)
  · rw [signPerm_vec2_01]; exact mem_e1Sub.2 ⟨_, rfl⟩
  · rw [signPerm_vec2_23]; exact mem_e1Sub.2 ⟨_, rfl⟩
  · rw [signPerm_vec2_45]; exact mem_e1Sub.2 ⟨_, rfl⟩
  · rw [signPerm_vec2_67]; exact mem_e1Sub.2 ⟨_, rfl⟩

theorem sq_signPerm_permMat {v : FrameVec} (hv : v ∈ evenSub) {σ : Equiv.Perm (Fin 8)}
    (hσ : σ * σ = 1) : (signPerm v * permMat σ) * (signPerm v * permMat σ) =
      signPerm (v + permVec σ v) := by
  rw [signPerm_add hv (permVec_mem_evenSub σ hv), ← permMat_conj_signPerm σ hv]
  have h1 : permMat σ * permMat σ = 1 := by rw [← permMat_mul, hσ, permMat_one]
  calc signPerm v * permMat σ * (signPerm v * permMat σ)
      = signPerm v * (permMat σ * signPerm v * (permMat σ)⁻¹) * (permMat σ * permMat σ) := by
        group
    _ = _ := by rw [h1, mul_one]

theorem signPerm_pair_mem_uPrimeSub (j : Fin 8) (σ : Equiv.Perm (Fin 8)) (hj : j ≠ 0)
    (hσ : σ * σ = 1) (hgen : signPerm (vec2 0 j) * permMat σ ∈ uPrimeSub) {w : FrameVec}
    (hw : vec2 0 1 + (vec2 0 j + permVec σ (vec2 0 j)) = w) : signPerm w ∈ uPrimeSub := by
  have h01 : signPerm (vec2 0 1) ∈ uPrimeSub := subset_closure (Set.mem_insert _ _)
  have hv := vec2_mem_evenSub 0 j (Ne.symm hj)
  have hsq := mul_mem hgen hgen
  rw [sq_signPerm_permMat hv hσ] at hsq
  have := mul_mem h01 hsq
  rwa [← signPerm_add (vec2_mem_evenSub 0 1 (by decide)) (add_mem hv (permVec_mem_evenSub σ hv)),
    hw] at this

theorem kOneSub_le_uPrimeSub : kOneSub ≤ uPrimeSub := by
  rw [kOneSub, closure_le]
  rintro g (rfl | rfl | rfl | rfl)
  · exact subset_closure (Set.mem_insert _ _)
  · exact signPerm_pair_mem_uPrimeSub 2 (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide) (by decide)
      (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (by decide)
  · exact signPerm_pair_mem_uPrimeSub 4 (Equiv.swap 0 1 * Equiv.swap 4 5) (by decide) (by decide)
      (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      (by decide)
  · exact signPerm_pair_mem_uPrimeSub 6 (Equiv.swap 0 1 * Equiv.swap 6 7) (by decide) (by decide)
      (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl)))) (by decide)

theorem closure_comm_of_comm {S : Set (Equiv.Perm (Fin 240))}
    (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a := by
  have h1 : closure S ≤ centralizer S :=
    (closure_le _).2 fun a ha => mem_centralizer_iff.2 fun b hb => h b hb a ha
  have h2 : closure S ≤ centralizer (closure S) :=
    (closure_le _).2 fun a ha => mem_centralizer_iff.2 fun b hb =>
      (mem_centralizer_iff.1 (h1 hb) a ha).symm
  intro a ha b hb
  exact (mem_centralizer_iff.1 (h2 ha) b hb).symm

theorem uPrimeGensArr_get0 : uPrimeGensArr[0]! = signArr (vec2 0 1) := by
  simp only [uPrimeGensArr, List.getElem!_toArray, List.getElem!_cons_zero]

theorem uPrimeGensArr_get1 : uPrimeGensArr[1]! =
    compA 240 (signArr (vec2 0 2)) (permArr (Equiv.swap 0 1 * Equiv.swap 2 3)) := by
  simp only [uPrimeGensArr, List.getElem!_toArray, List.getElem!_cons_succ,
    List.getElem!_cons_zero]

theorem uPrimeGensArr_get2 : uPrimeGensArr[2]! =
    compA 240 (signArr (vec2 0 4)) (permArr (Equiv.swap 0 1 * Equiv.swap 4 5)) := by
  simp only [uPrimeGensArr, List.getElem!_toArray, List.getElem!_cons_succ,
    List.getElem!_cons_zero]

theorem uPrimeGensArr_get3 : uPrimeGensArr[3]! =
    compA 240 (signArr (vec2 0 6)) (permArr (Equiv.swap 0 1 * Equiv.swap 6 7)) := by
  simp only [uPrimeGensArr, List.getElem!_toArray, List.getElem!_cons_succ,
    List.getElem!_cons_zero]

theorem uPrimeGensArr_size : uPrimeGensArr.size = 4 := by
  simp only [uPrimeGensArr, List.size_toArray, List.length_cons, List.length_nil]

theorem rep_uPrimeGen {j : Fin 8} (hj : j ≠ 0) (σ : Equiv.Perm (Fin 8)) :
    Rep 240 (compA 240 (signArr (vec2 0 j)) (permArr σ)) (signPerm (vec2 0 j) * permMat σ) :=
  rep_compA (rep_signArr (vec2_mem_evenSub 0 j (Ne.symm hj))) (rep_permArr σ)

theorem permsA_uPrimeGensArr : permsA 240 uPrimeGensArr = {signPerm (vec2 0 1),
    signPerm (vec2 0 2) * permMat (Equiv.swap 0 1 * Equiv.swap 2 3),
    signPerm (vec2 0 4) * permMat (Equiv.swap 0 1 * Equiv.swap 4 5),
    signPerm (vec2 0 6) * permMat (Equiv.swap 0 1 * Equiv.swap 6 7)} := by
  have e0 : permOfArr 240 uPrimeGensArr[0]! = signPerm (vec2 0 1) := by
    rw [uPrimeGensArr_get0]
    exact permOfArr_eq_of_rep (rep_signArr (vec2_mem_evenSub 0 1 (by decide)))
  have e1 : permOfArr 240 uPrimeGensArr[1]! =
      signPerm (vec2 0 2) * permMat (Equiv.swap 0 1 * Equiv.swap 2 3) := by
    rw [uPrimeGensArr_get1]
    exact permOfArr_eq_of_rep (rep_uPrimeGen (by decide) _)
  have e2 : permOfArr 240 uPrimeGensArr[2]! =
      signPerm (vec2 0 4) * permMat (Equiv.swap 0 1 * Equiv.swap 4 5) := by
    rw [uPrimeGensArr_get2]
    exact permOfArr_eq_of_rep (rep_uPrimeGen (by decide) _)
  have e3 : permOfArr 240 uPrimeGensArr[3]! =
      signPerm (vec2 0 6) * permMat (Equiv.swap 0 1 * Equiv.swap 6 7) := by
    rw [uPrimeGensArr_get3]
    exact permOfArr_eq_of_rep (rep_uPrimeGen (by decide) _)
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, uPrimeGensArr_size]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl e0
    · exact Or.inr (Or.inl e1)
    · exact Or.inr (Or.inr (Or.inl e2))
    · exact Or.inr (Or.inr (Or.inr e3))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩
    · exact ⟨2, by norm_num, e2⟩
    · exact ⟨3, by norm_num, e3⟩

theorem uPrimeSub_eq : uPrimeSub = closure (permsA 240 uPrimeGensArr) := by
  rw [permsA_uPrimeGensArr]
  rfl

theorem rep_uElt {i : ℕ} (hi : i < 128) :
    Rep 240 uPrimeCert.pts[i]! (permOfArr 240 uPrimeCert.pts[i]!) :=
  (rep_permOfArr (u_list_facts.valid i hi)).1

theorem rep_uGen {k : ℕ} (hk : k < 4) :
    Rep 240 uPrimeGensArr[k]! (permOfArr 240 uPrimeGensArr[k]!) :=
  (rep_permOfArr (u_list_facts.gens k hk)).1

theorem rep_uGen_inv {k : ℕ} (hk : k < 4) :
    Rep 240 (invCand 240 uPrimeGensArr[k]!) (permOfArr 240 uPrimeGensArr[k]!)⁻¹ :=
  (rep_permOfArr (u_list_facts.gens k hk)).2

theorem uGen_mem_permsA {k : ℕ} (hk : k < 4) :
    permOfArr 240 uPrimeGensArr[k]! ∈ permsA 240 uPrimeGensArr :=
  ⟨k, show k < uPrimeGensArr.size by rw [uPrimeGensArr_size]; exact hk, rfl⟩

theorem mem_closure_of_uElt : ∀ i < 128, ∀ {X : Equiv.Perm (Fin 240)},
    Rep 240 uPrimeCert.pts[i]! X → X ∈ closure (permsA 240 uPrimeGensArr) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi X hX
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [(isId_iff hX).1 u_list_facts.id0]
      exact one_mem _
    · obtain ⟨k, hk, j, hj, he⟩ := u_list_facts.tree i hi hpos
      have hJ := rep_uElt (hj.trans hi)
      rw [eq_of_eqA hX (rep_compA (rep_uGen hk) hJ) he]
      exact mul_mem (subset_closure (uGen_mem_permsA hk)) (ih j hj (hj.trans hi) hJ)

theorem exists_uElt_of_mem {X : Equiv.Perm (Fin 240)}
    (hX : X ∈ closure (permsA 240 uPrimeGensArr)) :
    ∃ i < 128, Rep 240 uPrimeCert.pts[i]! X := by
  refine closure_induction_left (p := fun Y _ => ∃ i < 128, Rep 240 uPrimeCert.pts[i]! Y)
    ⟨0, by norm_num, ?_⟩ (fun g hg Y _ hY => ?_) (fun g hg Y _ hY => ?_) hX
  · have h0 := rep_uElt (i := 0) (by norm_num)
    rwa [(isId_iff h0).1 u_list_facts.id0] at h0
  · obtain ⟨k, hk, rfl⟩ := hg
    rw [Set.mem_ofPred_eq, uPrimeGensArr_size] at hk
    obtain ⟨i, hi, hYr⟩ := hY
    obtain ⟨j, hj, he⟩ := u_list_facts.closed i hi k hk
    exact ⟨j, hj, rep_of_eqA (rep_compA (rep_uGen hk) hYr) he⟩
  · obtain ⟨k, hk, rfl⟩ := hg
    rw [Set.mem_ofPred_eq, uPrimeGensArr_size] at hk
    obtain ⟨i, hi, hYr⟩ := hY
    obtain ⟨j, hj, he⟩ := u_list_facts.closedInv i hi k hk
    exact ⟨j, hj, rep_of_eqA (rep_compA (rep_uGen_inv hk) hYr) he⟩

theorem card_uPrimeSub : Nat.card uPrimeSub = 2 ^ 7 := by
  rw [uPrimeSub_eq]
  let f : Fin 128 → closure (permsA 240 uPrimeGensArr) := fun i =>
    ⟨permOfArr 240 uPrimeCert.pts[i.val]!, mem_closure_of_uElt i i.2 (rep_uElt i.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => ?_, fun x => ?_⟩
    · by_contra hij
      have hd := u_list_facts.distinct i i.2 j j.2 (fun e => hij (Fin.ext e))
      rw [(eqA_iff (rep_uElt i.2) (rep_uElt j.2)).2 (congrArg Subtype.val h)] at hd
      exact Bool.noConfusion hd
    · obtain ⟨i, hi, hr⟩ := exists_uElt_of_mem x.2
      exact ⟨⟨i, hi⟩, Subtype.ext (permOfArr_eq_of_rep hr)⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem uPrimeCert_size : uPrimeCert.pts.size = 128 := by simp [uPrimeCert]

theorem mem_uPrimeSub_of_memU {x : Array ℕ} {X : Equiv.Perm (Fin 240)} (hx : Rep 240 x X)
    (h : memU x = true) : X ∈ uPrimeSub := by
  rw [memU, List.any_eq_true] at h
  obtain ⟨a, ha, he⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hj' : j < 128 := by simpa [uPrimeCert_size] using hj
  rw [Array.getElem_toList, ← getElem!_pos uPrimeCert.pts j (by rw [uPrimeCert_size]; exact hj')]
    at he
  rw [uPrimeSub_eq]
  exact mem_closure_of_uElt j hj' (rep_of_eqA hx he)

theorem uPrimeSub_comm : ∀ a ∈ uPrimeSub, ∀ b ∈ uPrimeSub, a * b = b * a := by
  rw [uPrimeSub_eq]
  refine closure_comm_of_comm ?_
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  rw [Set.mem_ofPred_eq, uPrimeGensArr_size] at hi hj
  exact (eqA_iff (rep_compA (rep_uGen hi) (rep_uGen hj))
    (rep_compA (rep_uGen hj) (rep_uGen hi))).1 (u_list_facts.comm i hi j hj)

theorem not_sq_uPrimeSub : ∃ u ∈ uPrimeSub, u * u ≠ 1 := by
  refine ⟨signPerm (vec2 0 2) * permMat (Equiv.swap 0 1 * Equiv.swap 2 3),
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)), fun h => ?_⟩
  have h1 := u_list_facts.sq
  rw [uPrimeGensArr_get1, (isId_iff (rep_compA (rep_uPrimeGen (j := 2) (by decide) _)
    (rep_uPrimeGen (j := 2) (by decide) _))).2 h] at h1
  exact absurd h1 (by decide)

theorem rep_liftArr {r : ℕ} (hr : r ∈ liftReps) (σ : Equiv.Perm (Fin 8)) :
    Rep 240 (liftArr r σ) (signPerm (frameDecode r) * permMat σ) := by
  obtain ⟨h1, h2⟩ := liftReps_lt r hr
  rw [liftArr, signArrs_get h1]
  exact rep_compA (rep_signArr (decode_mem_evenSub h1 h2)) (rep_permArr σ)

theorem lift1_mem {B : Subgroup (Equiv.Perm (Fin 240))} (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    {r0 r1 r2 r3 : ℕ} (h0 : r0 ∈ liftReps) (h1 : r1 ∈ liftReps) (h2 : r2 ∈ liftReps)
    (h3 : r3 ∈ liftReps) (b0 : signPerm (frameDecode r0) * permMat (Equiv.swap 0 1) ∈ B)
    (b1 : signPerm (frameDecode r1) * permMat (Equiv.swap 2 3) ∈ B)
    (b2 : signPerm (frameDecode r2) * permMat (Equiv.swap 4 5) ∈ B)
    (b3 : signPerm (frameDecode r3) * permMat (Equiv.swap 6 7) ∈ B) :
    signPerm (frameDecode r0) * permMat (Equiv.swap 0 1) ∈ e1Sub ∧
      signPerm (frameDecode r1) * permMat (Equiv.swap 2 3) ∈ e1Sub ∧
      signPerm (frameDecode r2) * permMat (Equiv.swap 4 5) ∈ e1Sub ∧
      signPerm (frameDecode r3) * permMat (Equiv.swap 6 7) ∈ e1Sub := by
  have c01 := commA'_of_comm (rep_liftArr h0 _) (rep_liftArr h1 _) (hab _ b0 _ b1)
  have c02 := commA'_of_comm (rep_liftArr h0 _) (rep_liftArr h2 _) (hab _ b0 _ b2)
  have c03 := commA'_of_comm (rep_liftArr h0 _) (rep_liftArr h3 _) (hab _ b0 _ b3)
  have c12 := commA'_of_comm (rep_liftArr h1 _) (rep_liftArr h2 _) (hab _ b1 _ b2)
  have c13 := commA'_of_comm (rep_liftArr h1 _) (rep_liftArr h3 _) (hab _ b1 _ b3)
  have c23 := commA'_of_comm (rep_liftArr h2 _) (rep_liftArr h3 _) (hab _ b2 _ b3)
  have h := lift1_check
  rw [lift1Check, List.all_eq_true] at h
  have h' := List.all_eq_true.1 (h r0 h0) r1 h1
  have h'' := List.all_eq_true.1 h' r2 h2
  have hf := List.all_eq_true.1 h'' r3 h3
  simp only [c01, c02, c03, c12, c13, c23, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at hf
  obtain ⟨⟨⟨m0, m1⟩, m2⟩, m3⟩ := hf
  exact ⟨mem_e1Sub_of_memE1 (rep_liftArr h0 _) m0, mem_e1Sub_of_memE1 (rep_liftArr h1 _) m1,
    mem_e1Sub_of_memE1 (rep_liftArr h2 _) m2, mem_e1Sub_of_memE1 (rep_liftArr h3 _) m3⟩

theorem lift0_mem {B : Subgroup (Equiv.Perm (Fin 240))} (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    {r0 r1 r2 : ℕ} (h0 : r0 ∈ liftReps) (h1 : r1 ∈ liftReps) (h2 : r2 ∈ liftReps)
    (b0 : signPerm (frameDecode r0) * permMat (Equiv.swap 0 1 * Equiv.swap 2 3) ∈ B)
    (b1 : signPerm (frameDecode r1) * permMat (Equiv.swap 0 1 * Equiv.swap 4 5) ∈ B)
    (b2 : signPerm (frameDecode r2) * permMat (Equiv.swap 0 1 * Equiv.swap 6 7) ∈ B) :
    (signPerm (frameDecode r0) * permMat (Equiv.swap 0 1 * Equiv.swap 2 3) ∈ e1Sub ∧
      signPerm (frameDecode r1) * permMat (Equiv.swap 0 1 * Equiv.swap 4 5) ∈ e1Sub ∧
      signPerm (frameDecode r2) * permMat (Equiv.swap 0 1 * Equiv.swap 6 7) ∈ e1Sub) ∨
    (signPerm (frameDecode r0) * permMat (Equiv.swap 0 1 * Equiv.swap 2 3) ∈ uPrimeSub ∧
      signPerm (frameDecode r1) * permMat (Equiv.swap 0 1 * Equiv.swap 4 5) ∈ uPrimeSub ∧
      signPerm (frameDecode r2) * permMat (Equiv.swap 0 1 * Equiv.swap 6 7) ∈ uPrimeSub) := by
  have c01 := commA'_of_comm (rep_liftArr h0 _) (rep_liftArr h1 _) (hab _ b0 _ b1)
  have c02 := commA'_of_comm (rep_liftArr h0 _) (rep_liftArr h2 _) (hab _ b0 _ b2)
  have c12 := commA'_of_comm (rep_liftArr h1 _) (rep_liftArr h2 _) (hab _ b1 _ b2)
  have h := lift0_check
  rw [lift0Check, List.all_eq_true] at h
  have h' := List.all_eq_true.1 (h r0 h0) r1 h1
  have hf := List.all_eq_true.1 h' r2 h2
  simp only [c01, c02, c12, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Bool.and_eq_true] at hf
  rcases hf with ⟨⟨m0, m1⟩, m2⟩ | ⟨⟨m0, m1⟩, m2⟩
  · exact Or.inl ⟨mem_e1Sub_of_memE1 (rep_liftArr h0 _) m0,
      mem_e1Sub_of_memE1 (rep_liftArr h1 _) m1, mem_e1Sub_of_memE1 (rep_liftArr h2 _) m2⟩
  · exact Or.inr ⟨mem_uPrimeSub_of_memU (rep_liftArr h0 _) m0,
      mem_uPrimeSub_of_memU (rep_liftArr h1 _) m1, mem_uPrimeSub_of_memU (rep_liftArr h2 _) m2⟩

theorem qOf_le_pSub {B : Subgroup (Equiv.Perm (Fin 240))} (hBT : B ≤ tSub) :
    qOf B (hBT.trans tSub_le_nSub) ≤ pSub := by
  rintro σ ⟨x, rfl⟩
  exact actE_mem_pSub (hBT x.2)

theorem qOf_le_pPlusSub {B : Subgroup (Equiv.Perm (Fin 240))} (hBT : B ≤ tPlusSub) :
    qOf B ((hBT.trans tPlusSub_le_tSub).trans tSub_le_nSub) ≤ pPlusSub := by
  rintro σ ⟨x, rfl⟩
  exact actE_mem_pPlusSub (hBT x.2)

theorem lift_mem_qOf_inf {B X : Subgroup (Equiv.Perm (Fin 240))} (hB : B ≤ nSub) {r : ℕ}
    (hr : r ∈ liftReps) {g : Equiv.Perm (Fin 8)} (hb : signPerm (frameDecode r) * permMat g ∈ B)
    (hx : signPerm (frameDecode r) * permMat g ∈ X) : g ∈ qOf (B ⊓ X) (inf_le_left.trans hB) :=
  ⟨⟨_, mem_inf.2 ⟨hb, hx⟩⟩, actHom_decomp (decode_mem_evenSub (liftReps_lt r hr).1
    (liftReps_lt r hr).2) g _⟩

theorem inf_eSub_le_kOneSub {B : Subgroup (Equiv.Perm (Fin 240))} (hB : B ≤ nSub)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hfix : ∀ v, v ∈ fixSet (qOf B hB) → pairConst v) : B ⊓ eSub ≤ kOneSub := by
  intro e he
  obtain ⟨v, hv, rfl⟩ := mem_eSub.1 (mem_inf.1 he).2
  exact signPerm_mem_kOneSub (hfix v (vec_mem_fixSet hB hab hv (mem_inf.1 he).1))

theorem abelian_t_spec (B : Subgroup (Equiv.Perm (Fin 240))) (hBT : B ≤ tSub)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hcard : 2 ^ 8 ≤ Nat.card B) : B = e1Sub := by
  have hB : B ≤ nSub := hBT.trans tSub_le_nSub
  have h1 := card_eq_card_inf_mul_card_qOf B hB
  have h2 := card_inf_le_fixSet B hB hab
  obtain ⟨h3, h4, -⟩ := fixSet_bound (qOf_le_pSub hBT) (qOf_abelian hB hab)
  have hQpos : 0 < Nat.card (qOf B hB) := Nat.card_pos
  have h2' := Nat.mul_le_mul_right (Nat.card (qOf B hB)) h2
  have h5 : Nat.card (fixSet (qOf B hB)) * Nat.card (qOf B hB) = 256 := by omega
  have hQ : qOf B hB = q1Sub := h4 h5
  have h6 : Nat.card (B ⊓ eSub : Subgroup (Equiv.Perm (Fin 240))) =
      Nat.card (fixSet (qOf B hB)) := Nat.eq_of_mul_eq_mul_right hQpos (by omega)
  have hK := signPerm_mem_of_card_eq hB hab h6
  have hfix : ∀ v, v ∈ fixSet (qOf B hB) → pairConst v := fun v hv => by
    rw [hQ, mem_fixSet_q1Sub] at hv
    exact hv.2
  have hrep : ∀ u ∈ evenSub, ∃ r ∈ liftReps, u + frameDecode r ∈ fixSet (qOf B hB) := by
    intro u hu
    obtain ⟨r, hr, hm, hp⟩ := exists_liftRep hu
    exact ⟨r, hr, by rw [hQ, mem_fixSet_q1Sub]; exact ⟨hm, hp⟩⟩
  have hg : ∀ g ∈ q1Gens, g ∈ qOf B hB := fun g hg => hQ ▸ subset_closure hg
  obtain ⟨r0, hr0, b0⟩ := exists_lift hB (hg (Equiv.swap 0 1) (by simp [q1Gens])) hK hrep
  obtain ⟨r1, hr1, b1⟩ := exists_lift hB (hg (Equiv.swap 2 3) (by simp [q1Gens])) hK hrep
  obtain ⟨r2, hr2, b2⟩ := exists_lift hB (hg (Equiv.swap 4 5) (by simp [q1Gens])) hK hrep
  obtain ⟨r3, hr3, b3⟩ := exists_lift hB (hg (Equiv.swap 6 7) (by simp [q1Gens])) hK hrep
  obtain ⟨x0, x1, x2, x3⟩ := lift1_mem hab hr0 hr1 hr2 hr3 b0 b1 b2 b3
  have hle : B ≤ e1Sub := by
    refine le_of_lifts hB ((inf_eSub_le_kOneSub hB hab hfix).trans kOneSub_le_e1Sub) ?_
    rw [hQ, q1Sub, closure_le]
    intro g hgL
    simp only [q1Gens, Set.mem_ofPred_eq, List.mem_cons, List.mem_nil_iff, or_false] at hgL
    rcases hgL with rfl | rfl | rfl | rfl
    · exact lift_mem_qOf_inf hB hr0 b0 x0
    · exact lift_mem_qOf_inf hB hr1 b1 x1
    · exact lift_mem_qOf_inf hB hr2 b2 x2
    · exact lift_mem_qOf_inf hB hr3 b3 x3
  exact eq_of_le_of_card_ge hle (by rw [card_e1Sub]; exact hcard)

theorem abelian_tPlus_spec (B : Subgroup (Equiv.Perm (Fin 240))) (hBT : B ≤ tPlusSub)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hcard : 2 ^ 7 ≤ Nat.card B) :
    B = eSub ∨ B = e1PlusSub ∨ B = uPrimeSub := by
  have hBT' : B ≤ tSub := hBT.trans tPlusSub_le_tSub
  have hB : B ≤ nSub := hBT'.trans tSub_le_nSub
  have h1 := card_eq_card_inf_mul_card_qOf B hB
  have h2 := card_inf_le_fixSet B hB hab
  obtain ⟨-, -, h4⟩ := fixSet_bound (qOf_le_pSub hBT') (qOf_abelian hB hab)
  obtain ⟨h5, h6⟩ := h4 (qOf_le_pPlusSub hBT)
  have hQpos : 0 < Nat.card (qOf B hB) := Nat.card_pos
  have h2' := Nat.mul_le_mul_right (Nat.card (qOf B hB)) h2
  have h7 : Nat.card (fixSet (qOf B hB)) * Nat.card (qOf B hB) = 128 := by omega
  have h8 : Nat.card (B ⊓ eSub : Subgroup (Equiv.Perm (Fin 240))) =
      Nat.card (fixSet (qOf B hB)) := Nat.eq_of_mul_eq_mul_right hQpos (by omega)
  rcases h6 h7 with hQ | hQ
  · left
    have hc : Nat.card (qOf B hB) = 1 := by rw [hQ]; exact card_bot
    have hinf : B ⊓ eSub = B :=
      eq_of_le_of_card_ge inf_le_left (by rw [h1, hc, mul_one])
    have hle : B ≤ eSub := hinf ▸ inf_le_right
    exact eq_of_le_of_card_ge hle (by rw [card_eSub]; exact hcard)
  · right
    have hK := signPerm_mem_of_card_eq hB hab h8
    have hfix : ∀ v, v ∈ fixSet (qOf B hB) → pairConst v := fun v hv => by
      rw [hQ, mem_fixSet_q0Sub] at hv
      exact hv.2
    have hrep : ∀ u ∈ evenSub, ∃ r ∈ liftReps, u + frameDecode r ∈ fixSet (qOf B hB) := by
      intro u hu
      obtain ⟨r, hr, hm, hp⟩ := exists_liftRep hu
      exact ⟨r, hr, by rw [hQ, mem_fixSet_q0Sub]; exact ⟨hm, hp⟩⟩
    have hg : ∀ g ∈ q0Gens, g ∈ qOf B hB := fun g hg => hQ ▸ subset_closure hg
    obtain ⟨r0, hr0, b0⟩ :=
      exists_lift hB (hg (Equiv.swap 0 1 * Equiv.swap 2 3) (by simp [q0Gens])) hK hrep
    obtain ⟨r1, hr1, b1⟩ :=
      exists_lift hB (hg (Equiv.swap 0 1 * Equiv.swap 4 5) (by simp [q0Gens])) hK hrep
    obtain ⟨r2, hr2, b2⟩ :=
      exists_lift hB (hg (Equiv.swap 0 1 * Equiv.swap 6 7) (by simp [q0Gens])) hK hrep
    have hgen : ∀ {X : Subgroup (Equiv.Perm (Fin 240))},
        signPerm (frameDecode r0) * permMat (Equiv.swap 0 1 * Equiv.swap 2 3) ∈ X →
        signPerm (frameDecode r1) * permMat (Equiv.swap 0 1 * Equiv.swap 4 5) ∈ X →
        signPerm (frameDecode r2) * permMat (Equiv.swap 0 1 * Equiv.swap 6 7) ∈ X →
        qOf B hB ≤ qOf (B ⊓ X) (inf_le_left.trans hB) := by
      intro X x0 x1 x2
      rw [hQ, q0Sub, closure_le]
      intro g hgL
      simp only [q0Gens, Set.mem_ofPred_eq, List.mem_cons, List.mem_nil_iff, or_false] at hgL
      rcases hgL with rfl | rfl | rfl
      · exact lift_mem_qOf_inf hB hr0 b0 x0
      · exact lift_mem_qOf_inf hB hr1 b1 x1
      · exact lift_mem_qOf_inf hB hr2 b2 x2
    rcases lift0_mem hab hr0 hr1 hr2 b0 b1 b2 with ⟨x0, x1, x2⟩ | ⟨x0, x1, x2⟩
    · left
      have hle : B ≤ e1Sub :=
        le_of_lifts hB ((inf_eSub_le_kOneSub hB hab hfix).trans kOneSub_le_e1Sub)
          (hgen x0 x1 x2)
      have hle' : B ≤ e1PlusSub := by
        rw [e1PlusSub_eq]
        exact le_inf hle (hBT.trans tPlusSub_le_wPlus)
      exact eq_of_le_of_card_ge hle' (by rw [card_e1PlusSub]; exact hcard)
    · right
      have hle : B ≤ uPrimeSub :=
        le_of_lifts hB ((inf_eSub_le_kOneSub hB hab hfix).trans kOneSub_le_uPrimeSub)
          (hgen x0 x1 x2)
      exact eq_of_le_of_card_ge hle (by rw [card_uPrimeSub]; exact hcard)

end CFSG.EvenSmallLie.OmegaEight.Weyl
