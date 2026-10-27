module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCoordCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCover
public import CFSG.RankThree.Native.PermEnumeration

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native

theorem getElem!_toArray_map_range {α : Type*} [Inhabited α] (f : ℕ → α) {n m : ℕ} (hm : m < n) :
    ((List.range n).map f).toArray[m]! = f m := by
  rw [getElem!_pos _ m (by simpa using hm)]
  simp

theorem signArrs_get {m : ℕ} (hm : m < 256) : signArrs[m]! = signArr (frameDecode m) :=
  getElem!_toArray_map_range _ hm

theorem frameArrs_get {m : ℕ} (hm : m < 256) : frameArrs[m]! = frameArr (frameDecode m) :=
  getElem!_toArray_map_range _ hm

structure TableFacts (A : Array (Array ℕ)) (p : ℕ → Bool) (sgn : ℕ → ℕ) : Prop where
  inv : ∀ a < 256, p a = true → isInvA 240 A[a]! A[a]! = true
  sift : ∀ a < 256, p a = true → siftW A[a]! = true
  sgn : ∀ a < 256, p a = true → ((240 - fixCount 240 A[a]!) / 2) % 2 = sgn a
  mul : ∀ a < 256, p a = true → ∀ b < 256, p b = true →
    eqA 240 (compA 240 A[a]! A[b]!) A[a ^^^ b]! = true
  inj : ∀ a < 256, p a = true → ∀ b < 256, p b = true → eqA 240 A[a]! A[b]! = true → a = b

theorem tableFacts {A : Array (Array ℕ)} {p : ℕ → Bool} {sgn : ℕ → ℕ}
    (h : tableOK A p sgn = true) : TableFacts A p sgn := by
  simp only [tableOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a ha hp => ?_, fun a ha hp => ?_, fun a ha hp => ?_, fun a ha hpa b hb hpb => ?_,
    fun a ha hpa b hb hpb he => ?_⟩
  · rcases h1 a ha with h | h
    · rw [hp] at h; exact absurd h (by decide)
    · exact h.1.1
  · rcases h1 a ha with h | h
    · rw [hp] at h; exact absurd h (by decide)
    · exact h.1.2
  · rcases h1 a ha with h | h
    · rw [hp] at h; exact absurd h (by decide)
    · exact h.2
  · rcases h2 a ha with h | h
    · rw [hpa] at h; exact absurd h (by decide)
    · rcases h b hb with h' | h'
      · rw [hpb] at h'; exact absurd h' (by decide)
      · exact h'.1
  · rcases h2 a ha with h | h
    · rw [hpa] at h; exact absurd h (by decide)
    · rcases h b hb with h' | h'
      · rw [hpb] at h'; exact absurd h' (by decide)
      · rcases h'.2 with h'' | h''
        · exact h''
        · rw [he] at h''; exact absurd h'' (by decide)

structure CoordFacts : Prop where
  frame : TableFacts frameArrs (fun _ => true) (fun a => framePop a % 2)
  sign : TableFacts signArrs (fun a => framePop a % 2 == 0) (fun _ => 0)
  refl : ∀ i < 8, eqA 240 frameArrs[2 ^ i]! (reflArr (keyPts.getD i 0)) = true
  fz : eqA 240 frameArrs[255]! negArr = true
  sz : eqA 240 signArrs[255]! negArr = true
  pair : ∀ i ∈ [0, 2, 4, 6], eqA 240 signArrs[2 ^ i + 2 ^ (i + 1)]!
    frameArrs[2 ^ i + 2 ^ (i + 1)]! = true
  s0 : eqA 240 (permArr (Equiv.swap 0 1)) s0Arr = true

theorem coord_facts : CoordFacts := by
  have h := coord_check
  simp only [coordCheck, coordCheckWith, Bool.and_eq_true, List.all_eq_true, allLt_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨tableFacts h1, tableFacts h2, h3, h4, h5, h6, h7⟩

theorem eqA_symm {n : ℕ} {t u : Array ℕ} (h : eqA n t u = true) : eqA n u t = true := by
  rw [eqA, allLt_iff] at h ⊢
  intro i hi
  have := h i hi
  rw [beq_iff_eq] at this ⊢
  exact this.symm

theorem mem_wE8_of_siftW {x : Array ℕ} {X : Equiv.Perm (Fin 240)} (hX : Rep 240 x X)
    (h : siftW x = true) : X ∈ wE8 :=
  mem_wE8_of_siftA hX h

theorem frameArrs_encode (v : FrameVec) : frameArrs[frameEncode v]! = frameArr v := by
  rw [frameArrs_get (frameEncode_lt v), frameDecode_frameEncode]

theorem rep_frameArr (v : FrameVec) : Rep 240 (frameArr v) (frameElt v) := by
  have h := coord_facts.frame.inv _ (frameEncode_lt v) rfl
  rw [frameArrs_encode] at h
  exact (isInvA_spec' h).1

theorem frameElt_mul_self (v : FrameVec) : frameElt v * frameElt v = 1 := by
  have h := coord_facts.frame.inv _ (frameEncode_lt v) rfl
  rw [frameArrs_encode] at h
  exact (isInvA_spec' h).2

theorem frameElt_add (v w : FrameVec) : frameElt (v + w) = frameElt v * frameElt w := by
  have h := coord_facts.frame.mul _ (frameEncode_lt v) rfl _ (frameEncode_lt w) rfl
  rw [frameArrs_encode, frameArrs_encode, ← frameEncode_add, frameArrs_encode] at h
  exact (eq_of_eqA (rep_compA (rep_frameArr v) (rep_frameArr w)) (rep_frameArr _) h).symm

theorem frameElt_injective : Function.Injective frameElt := by
  intro v w h
  have he : eqA 240 frameArrs[frameEncode v]! frameArrs[frameEncode w]! = true := by
    rw [frameArrs_encode, frameArrs_encode]
    exact (eqA_iff (rep_frameArr v) (rep_frameArr w)).2 h
  exact frameEncode_injective
    (coord_facts.frame.inj _ (frameEncode_lt v) rfl _ (frameEncode_lt w) rfl he)

theorem frameElt_zero : frameElt 0 = 1 := by
  have h := frameElt_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem frameElt_comm (v w : FrameVec) : frameElt v * frameElt w = frameElt w * frameElt v := by
  rw [← frameElt_add, ← frameElt_add, add_comm]

theorem frameElt_inv (v : FrameVec) : (frameElt v)⁻¹ = frameElt v :=
  inv_eq_of_mul_eq_one_right (frameElt_mul_self v)

theorem frameElt_mem_wE8 (v : FrameVec) : frameElt v ∈ wE8 := by
  have h := coord_facts.frame.sift _ (frameEncode_lt v) rfl
  rw [frameArrs_encode] at h
  exact mem_wE8_of_siftW (rep_frameArr v) h

theorem neg_one_pow_mod_two' (n : ℕ) : ((-1 : ℤˣ) ^ n) = (-1) ^ (n % 2) := by
  rw [← Nat.mod_add_div n 2, pow_add, pow_mul]
  simp

theorem sign_frameElt (v : FrameVec) :
    Equiv.Perm.sign (frameElt v) = (-1) ^ (frameWt v % 2) := by
  have hi := coord_facts.frame.inv _ (frameEncode_lt v) rfl
  have hs := coord_facts.frame.sgn _ (frameEncode_lt v) rfl
  rw [frameArrs_encode] at hi hs
  rw [frameElt, sign_of_isInvA hi, frameWt_eq, ← hs]
  exact neg_one_pow_mod_two' _

theorem frameElt_mem_wPlus_iff (v : FrameVec) : frameElt v ∈ wPlus ↔ v ∈ evenSub := by
  rw [mem_wPlus_iff, sign_frameElt, mem_evenSub_iff_frameWt]
  constructor
  · rintro ⟨-, h⟩
    rcases Nat.mod_two_eq_zero_or_one (frameWt v) with h' | h'
    · exact h'
    · rw [h', pow_one] at h
      exact absurd h (by decide)
  · intro h
    exact ⟨frameElt_mem_wE8 v, by rw [h, pow_zero]⟩

theorem framePop_even {v : FrameVec} (hv : v ∈ evenSub) :
    (framePop (frameEncode v) % 2 == 0) = true := by
  rw [beq_iff_eq, ← frameWt_eq]
  exact (mem_evenSub_iff_frameWt v).1 hv

theorem signArrs_encode (v : FrameVec) : signArrs[frameEncode v]! = signArr v := by
  rw [signArrs_get (frameEncode_lt v), frameDecode_frameEncode]

theorem rep_signArr {v : FrameVec} (hv : v ∈ evenSub) : Rep 240 (signArr v) (signPerm v) := by
  have h := coord_facts.sign.inv _ (frameEncode_lt v) (framePop_even hv)
  rw [signArrs_encode] at h
  exact (isInvA_spec' h).1

theorem signPerm_mul_self {v : FrameVec} (hv : v ∈ evenSub) : signPerm v * signPerm v = 1 := by
  have h := coord_facts.sign.inv _ (frameEncode_lt v) (framePop_even hv)
  rw [signArrs_encode] at h
  exact (isInvA_spec' h).2

theorem signPerm_add {v w : FrameVec} (hv : v ∈ evenSub) (hw : w ∈ evenSub) :
    signPerm (v + w) = signPerm v * signPerm w := by
  have h := coord_facts.sign.mul _ (frameEncode_lt v) (framePop_even hv) _ (frameEncode_lt w)
    (framePop_even hw)
  rw [signArrs_encode, signArrs_encode, ← frameEncode_add, signArrs_encode] at h
  exact (eq_of_eqA (rep_compA (rep_signArr hv) (rep_signArr hw))
    (rep_signArr (evenSub.add_mem hv hw)) h).symm

theorem signPerm_inj {v w : FrameVec} (hv : v ∈ evenSub) (hw : w ∈ evenSub)
    (h : signPerm v = signPerm w) : v = w := by
  have he : eqA 240 signArrs[frameEncode v]! signArrs[frameEncode w]! = true := by
    rw [signArrs_encode, signArrs_encode]
    exact (eqA_iff (rep_signArr hv) (rep_signArr hw)).2 h
  exact frameEncode_injective (coord_facts.sign.inj _ (frameEncode_lt v) (framePop_even hv) _
    (frameEncode_lt w) (framePop_even hw) he)

theorem signPerm_mem_wPlus {v : FrameVec} (hv : v ∈ evenSub) : signPerm v ∈ wPlus := by
  have hi := coord_facts.sign.inv _ (frameEncode_lt v) (framePop_even hv)
  have hs := coord_facts.sign.sgn _ (frameEncode_lt v) (framePop_even hv)
  have hw := coord_facts.sign.sift _ (frameEncode_lt v) (framePop_even hv)
  rw [signArrs_encode] at hi hs hw
  refine mem_wPlus_iff.2 ⟨mem_wE8_of_siftW (rep_signArr hv) hw, ?_⟩
  rw [signPerm, sign_of_isInvA hi, neg_one_pow_mod_two', hs, pow_zero]

theorem signPerm_zero : signPerm 0 = 1 := by
  have h := signPerm_add evenSub.zero_mem evenSub.zero_mem
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem frameZ_mem_evenSub : frameZ ∈ evenSub := evenZ.2

theorem signPerm_frameZ : signPerm frameZ = zPerm := by
  have h := coord_facts.sz
  rw [show (255 : ℕ) = frameEncode frameZ from frameEncode_frameZ.symm, signArrs_encode] at h
  exact eq_of_eqA (rep_signArr frameZ_mem_evenSub) rep_negArr h

theorem frameElt_frameZ : frameElt frameZ = zPerm := by
  have h := coord_facts.fz
  rw [show (255 : ℕ) = frameEncode frameZ from frameEncode_frameZ.symm, frameArrs_encode] at h
  exact eq_of_eqA (rep_frameArr frameZ) rep_negArr h

theorem mem_eSub {g : Equiv.Perm (Fin 240)} : g ∈ eSub ↔ ∃ v ∈ evenSub, signPerm v = g := by
  constructor
  · intro hg
    refine closure_induction (p := fun g _ => ∃ v ∈ evenSub, signPerm v = g) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · exact ⟨0, evenSub.zero_mem, signPerm_zero⟩
    · rintro _ _ _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
      exact ⟨v + w, evenSub.add_mem hv hw, signPerm_add hv hw⟩
    · rintro _ _ ⟨v, hv, rfl⟩
      exact ⟨v, hv, (inv_eq_of_mul_eq_one_right (signPerm_mul_self hv)).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact subset_closure ⟨v, hv, rfl⟩

theorem eSub_le_wPlus : eSub ≤ wPlus := by
  intro g hg
  obtain ⟨v, hv, rfl⟩ := mem_eSub.1 hg
  exact signPerm_mem_wPlus hv

theorem mem_e1Sub {g : Equiv.Perm (Fin 240)} : g ∈ e1Sub ↔ ∃ v, frameElt v = g := by
  constructor
  · intro hg
    refine closure_induction (p := fun g _ => ∃ v, frameElt v = g) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨v, rfl⟩
      exact ⟨v, rfl⟩
    · exact ⟨0, frameElt_zero⟩
    · rintro _ _ _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
      exact ⟨v + w, frameElt_add v w⟩
    · rintro _ _ ⟨v, rfl⟩
      exact ⟨v, (frameElt_inv v).symm⟩
  · rintro ⟨v, rfl⟩
    exact subset_closure ⟨v, rfl⟩

theorem mem_e1PlusSub {g : Equiv.Perm (Fin 240)} :
    g ∈ e1PlusSub ↔ ∃ v ∈ evenSub, frameElt v = g := by
  constructor
  · intro hg
    refine closure_induction (p := fun g _ => ∃ v ∈ evenSub, frameElt v = g) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · exact ⟨0, evenSub.zero_mem, frameElt_zero⟩
    · rintro _ _ _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
      exact ⟨v + w, evenSub.add_mem hv hw, frameElt_add v w⟩
    · rintro _ _ ⟨v, hv, rfl⟩
      exact ⟨v, hv, (frameElt_inv v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact subset_closure ⟨v, hv, rfl⟩

theorem e1PlusSub_eq : e1PlusSub = e1Sub ⊓ wPlus := by
  ext g
  rw [mem_inf, mem_e1PlusSub, mem_e1Sub]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, (frameElt_mem_wPlus_iff v).2 hv⟩
  · rintro ⟨⟨v, rfl⟩, h⟩
    exact ⟨v, (frameElt_mem_wPlus_iff v).1 h, rfl⟩

theorem e1Sub_le_wE8 : e1Sub ≤ wE8 := by
  intro g hg
  obtain ⟨v, rfl⟩ := mem_e1Sub.1 hg
  exact frameElt_mem_wE8 v

theorem keyPts_getD (i : Fin 8) : keyPts.getD i 0 = frameRoot i := by
  revert i
  decide

theorem frameRoot_lt (i : Fin 8) : frameRoot i < 240 := by
  rw [← keyPts_getD]
  revert i
  decide

theorem frameElt_frameE (i : Fin 8) : frameElt (frameE i) = refl (frameRoot i) := by
  have h := coord_facts.refl i i.2
  have he : frameEncode (frameE i) = 2 ^ (i : ℕ) := by
    rw [frameE_eq_frameDecode, frameEncode_frameDecode _ (by
      have := i.2
      interval_cases (i : ℕ) <;> norm_num)]
  rw [← he, frameArrs_encode, keyPts_getD] at h
  exact eq_of_eqA (rep_frameArr _) (rep_refl (frameRoot_lt i)) h

theorem sZero_eq_frameElt : sZero = frameElt (frameE 0) := (frameElt_frameE 0).symm

theorem sZero_eq_permMat : sZero = permMat (Equiv.swap 0 1) := by
  have hrep : Rep 240 (permArr (Equiv.swap 0 1)) (refl 1) :=
    rep_of_eqA (rep_refl (by norm_num)) (eqA_symm coord_facts.s0)
  rw [sZero_eq_refl, permMat, permOfArr_eq_of_rep hrep]

theorem vec2_mem_evenSub (i j : Fin 8) (h : i ≠ j) : vec2 i j ∈ evenSub := by
  rw [mem_evenSub_iff_frameWt]
  revert i j
  decide

theorem frameEncode_vec2_pair : ∀ i : Fin 8, (i : ℕ) % 2 = 0 →
    frameEncode (vec2 i (i + 1)) = 2 ^ (i : ℕ) + 2 ^ ((i : ℕ) + 1) ∧ (i : ℕ) ∈ [0, 2, 4, 6] := by
  decide

theorem ne_add_one_of_even : ∀ i : Fin 8, (i : ℕ) % 2 = 0 → i ≠ i + 1 := by decide

theorem signPerm_pair (i : Fin 8) (hi : (i : ℕ) % 2 = 0) :
    signPerm (vec2 i (i + 1)) = frameElt (vec2 i (i + 1)) := by
  have hne := ne_add_one_of_even i hi
  obtain ⟨he, hmem⟩ := frameEncode_vec2_pair i hi
  have h := coord_facts.pair _ hmem
  rw [← he, signArrs_encode, frameArrs_encode] at h
  exact eq_of_eqA (rep_signArr (vec2_mem_evenSub i (i + 1) hne)) (rep_frameArr _) h

theorem weylCoords : WeylCoords where
  signPerm_add _ hv _ hw := signPerm_add hv hw
  signPerm_inj _ hv _ hw h := signPerm_inj hv hw h
  mem_eSub _ := mem_eSub
  signPerm_frameZ := signPerm_frameZ
  frameElt_add := frameElt_add
  frameElt_injective := frameElt_injective
  mem_e1Sub _ := mem_e1Sub
  mem_e1PlusSub _ := mem_e1PlusSub
  e1PlusSub_eq := e1PlusSub_eq
  frameElt_frameZ := frameElt_frameZ
  frameElt_frameE := frameElt_frameE
  sZero_eq := ⟨sZero_eq_frameElt, sZero_eq_permMat⟩
  signPerm_pair := signPerm_pair
  eSub_le := eSub_le_wPlus
  e1Sub_le := e1Sub_le_wE8
