module

public import Certificates.Data.Kernel.Co2J
public import CFSG.Certificates.Kernel.Co2Syl.Sound

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2J

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.TabMatGrp CFSG.KLie.CT CFSG.KC.M1F2
  CFSG.KC.Co2Syl

theorem allK_spec {n : Nat} {f : Nat → Bool} (h : allK n f = true) : ∀ k < n, f k = true :=
  recAll n h

theorem rangeK_spec {lo n : Nat} {f : Nat → Bool} (h : rangeK lo n f = true) :
    ∀ k < n, f (lo + k) = true :=
  allK_spec h

theorem iffK_eq (a b : Bool) : iffK a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

theorem mulT_eq (A B : Nat) : mulT A B = mulF 10 A B := by
  unfold mulT
  exact mulW_eq 10 A B

theorem MatP_mulT (A B : Nat) : MatP 10 (mulT A B) = MatP 10 A * MatP 10 B := by
  rw [mulT_eq, MatP_mul]

theorem mulT_lt (A B : Nat) : mulT A B < 2 ^ 100 := by
  rw [mulT_eq]
  exact mulF_lt 10 A B

theorem IDT_eq : IDT = idF 10 := by decide +kernel

theorem MatP_IDT : MatP 10 IDT = 1 := by
  rw [IDT_eq, MatP_id]

theorem IDT_lt : IDT < 2 ^ 100 := by decide +kernel

theorem beqT {A B : Nat} (hA : A < 2 ^ 100) (hB : B < 2 ^ 100) :
    Nat.beq A B = true ↔ MatP 10 A = MatP 10 B :=
  ⟨fun h => by rw [Nat.eq_of_beq_eq_true h], fun h => by rw [MatP_inj h hA hB, Nat.beq_refl]⟩

theorem involT_iff {X : Nat} (hX : X < 2 ^ 100) :
    involT X = true ↔ MatP 10 X * MatP 10 X = 1 ∧ MatP 10 X ≠ 1 := by
  have e1 := beqT (mulT_lt X X) IDT_lt
  have e2 := beqT hX IDT_lt
  rw [MatP_mulT, MatP_IDT] at e1
  rw [MatP_IDT] at e2
  unfold involT
  rw [andK_eq, notK_eq, Bool.and_eq_true, ne_eq, ← e1, ← e2]
  cases Nat.beq X IDT <;> simp

theorem rowT_lt (M i : Nat) : rowT M i < 1024 :=
  Nat.and_lt_two_pow _ (by decide : 1023 < 2 ^ 10)

theorem jGen_sound {GJ : Nat → Nat} (h : jGenK GJ = true) :
    (∀ i < 10, MatP 22 (GJ i) * MatP 22 (GJ i) = 1) ∧
      ∀ i < 10, ∀ k < 10, MatP 22 (GJ i) * MatP 22 (GJ k) = MatP 22 (GJ k) * MatP 22 (GJ i) := by
  unfold jGenK at h
  rw [andK_eq, Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, fun i hi k hk => ?_⟩
  · rw [← MatP_mulV, Nat.eq_of_beq_eq_true (allK_spec h.1 i hi), MatP_IDP]
  · rw [← MatP_mulV, ← MatP_mulV, Nat.eq_of_beq_eq_true (allK_spec (allK_spec h.2 i hi) k hk)]

@[expose] def bitProd {M : Type*} [Monoid M] (g : Nat → M) : Nat → Nat → M
  | 0, _ => 1
  | n + 1, v => bitProd g n v * (if v.testBit n then g n else 1)

section BitProd

variable {M : Type*} [Monoid M] (g : Nat → M)

theorem bitProd_congr {v w : Nat} : ∀ n, (∀ k < n, v.testBit k = w.testBit k) →
    bitProd g n v = bitProd g n w
  | 0, _ => rfl
  | n + 1, h => by
    simp only [bitProd]
    rw [bitProd_congr n fun k hk => h k (by omega), h n (by omega)]

theorem bitProd_high {v m : Nat} (hv : v < 2 ^ m) : ∀ n, m ≤ n → bitProd g n v = bitProd g m v
  | 0, h => by rw [Nat.le_zero.1 h]
  | n + 1, h => by
    rcases Nat.lt_or_ge n m with hn | hn
    · rw [show m = n + 1 by omega]
    · simp only [bitProd]
      have hb : v.testBit n = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hn))
      rw [hb, if_neg Bool.false_ne_true, mul_one, bitProd_high hv n hn]

theorem bitProd_zero : ∀ n, bitProd g n 0 = 1
  | 0 => rfl
  | n + 1 => by
    simp only [bitProd, Nat.zero_testBit, Bool.false_eq_true, if_false, mul_one]
    exact bitProd_zero n

theorem bitProd_gray {i u : Nat} (hi : i < 10) (hu : u < 2 ^ i) :
    bitProd g 10 (2 ^ i + u) = bitProd g 10 u * g i := by
  have h1 : 2 ^ i + u < 2 ^ (i + 1) := by rw [pow_succ]; omega
  rw [bitProd_high g h1 10 (by omega), bitProd_high g hu 10 (by omega)]
  simp only [bitProd]
  rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hu, Bool.not_false, if_pos rfl,
    bitProd_congr g i fun k hk => Nat.testBit_two_pow_add_gt hk u]

end BitProd

section Gray

variable {GJ JE JS : Nat → Nat}

theorem jEnum_sound (h : jEnumK GJ JE JS = true) :
    (∀ v < 1024, JE v < 2 ^ 484 ∧ MatP 22 (JE v) = bitProd (fun i => MatP 22 (GJ i)) 10 v) ∧
      ∀ a < 1024, ∀ b < 1024, MatP 22 (JE a) = MatP 22 (JE b) → a = b := by
  unfold jEnumK at h
  simp only [andK_eq, Bool.and_eq_true] at h
  obtain ⟨h0, hg, hs⟩ := h
  have he : ∀ v < 1024, JE v < 2 ^ 484 ∧
      MatP 22 (JE v) = bitProd (fun i => MatP 22 (GJ i)) 10 v := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
    intro hv
    rcases Nat.eq_zero_or_pos v with rfl | hv0
    · rw [Nat.eq_of_beq_eq_true h0, MatP_IDP, bitProd_zero]
      exact ⟨IDP_lt, rfl⟩
    have hl1 : 2 ^ v.log2 ≤ v := Nat.log2_self_le (by omega)
    have hl2 : v < 2 ^ (v.log2 + 1) := Nat.lt_log2_self
    have hi : v.log2 < 10 := by
      by_contra hc
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.not_lt.1 hc)
      omega
    have hu : v - 2 ^ v.log2 < 2 ^ v.log2 := by rw [pow_succ] at hl2; omega
    have hrow := allK_spec (allK_spec hg _ hi) (v - 2 ^ v.log2)
      (by
        change v - 2 ^ v.log2 < 1 <<< v.log2
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact hu)
    have e : Nat.add (Nat.shiftLeft 1 v.log2) (v - 2 ^ v.log2) = v := by
      change 1 <<< v.log2 + (v - 2 ^ v.log2) = v
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      omega
    rw [e] at hrow
    have hv' := Nat.eq_of_beq_eq_true hrow
    obtain ⟨-, ihe⟩ := ih (v - 2 ^ v.log2) (by omega) (by omega)
    refine ⟨by rw [hv']; exact mulV_lt _ _, ?_⟩
    have e2 : v = 2 ^ v.log2 + (v - 2 ^ v.log2) := by omega
    rw [hv', MatP_mulV, ihe]
    conv_rhs => rw [e2]
    rw [bitProd_gray _ hi hu]
  refine ⟨he, fun a ha b hb e => ?_⟩
  have hsort : ∀ v < 1024, jSortK JE JS v = true := allK_spec hs
  have hσ : ∀ i < 1024, JS i < 1024 := fun i hi => by
    have := hsort i hi
    unfold jSortK at this
    rw [andK_eq, Bool.and_eq_true] at this
    exact blt_iff.1 this.1
  have hlt : ∀ i, i + 1 < 1024 → JE (JS i) < JE (JS (i + 1)) := fun i hi => by
    have := hsort i (by omega)
    unfold jSortK at this
    rw [andK_eq, Bool.and_eq_true, implK_eq, blt_iff.2 hi, if_pos rfl] at this
    exact blt_iff.1 this.2
  exact sorted_inj (σ := JS) (f := JE) hσ hlt a ha b hb
    (MatP_inj' (he a ha).1 (he b hb).1 e)

end Gray

theorem wProd_mem {G : Nat → Nat} : ∀ n w acc, wLets n w = true → MatP 22 acc ∈ genMon G →
    MatP 22 (wProd G n w acc) ∈ genMon G
  | 0, _, _, _, h => h
  | n + 1, w, acc, hl, h => by
    have hl' : andK (Nat.blt (Nat.land w 7) 5) (wLets n (Nat.shiftRight w 3)) = true := hl
    rw [andK_eq, Bool.and_eq_true] at hl'
    change MatP 22 (strictN (mulV acc (G (Nat.land w 7))) fun a =>
      wProd G n (Nat.shiftRight w 3) a) ∈ genMon G
    rw [strictN_eq']
    refine wProd_mem n _ _ hl'.2 ?_
    rw [MatP_mulV]
    exact (genMon G).mul_mem h (gen_mem G (blt_iff.1 hl'.1))

theorem word_sound {G : Nat → Nat} {w n X : Nat} (h : wordK G w n X = true) :
    MatP 22 X ∈ genMon G := by
  unfold wordK at h
  rw [andK_eq, Bool.and_eq_true] at h
  rw [← Nat.eq_of_beq_eq_true h.2]
  refine wProd_mem n w IDP h.1 ?_
  rw [MatP_IDP]
  exact (genMon G).one_mem

theorem jInT_sound {G GJ JW JL : Nat → Nat} (h : jInTK G GJ JW JL = true) :
    ∀ i < 10, MatP 22 (GJ i) ∈ genMon G := fun i hi =>
  word_sound (allK_spec h i hi)

theorem coord_sound {G GJ JE MK : Nat → Nat} (h : coordAllK G GJ JE MK = true) :
    ∀ k < 5, ∀ i < 10, MatP 22 (G k) * MatP 22 (GJ i) =
      MatP 22 (JE (rowT (MK k) i)) * MatP 22 (G k) := by
  intro k hk i hi
  have := Nat.eq_of_beq_eq_true (allK_spec (allK_spec h k hk) i hi)
  rw [← MatP_mulV, ← MatP_mulV, this]

@[expose] noncomputable def genT (MK : Nat → Nat) : Submonoid (Matrix (Fin 10) (Fin 10) (ZMod 2)) :=
  Submonoid.closure (Set.range fun j : Fin 5 => MatP 10 (MK j))

theorem genT_mem (MK : Nat → Nat) {j : Nat} (hj : j < 5) : MatP 10 (MK j) ∈ genT MK :=
  Submonoid.subset_closure ⟨⟨j, hj⟩, rfl⟩

section Tree

variable {PE PM PS : Nat → Nat} {PT : Nat → Nat → Nat} {MK : Nat → Nat}

theorem edgeI_spec {m X g t : Nat} (h : edgeI PE m X g t = true) (hm : m ≤ t) :
    t < 256 ∧ PE t = mulT X g := by
  unfold edgeI at h
  rw [implK_eq, notK_eq, blt_false (Nat.not_lt.2 hm), Bool.not_false, if_pos rfl, andK_eq,
    Bool.and_eq_true] at h
  exact ⟨blt_iff.1 h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem recI_spec {s : Nat} (h : recI PE PM PS PT MK s = true) :
    (∀ j < 5, PM s ≤ PT s j → PT s j < 256 ∧ PE (PT s j) = mulT (PE s) (MK j)) ∧
    s < PM s ∧ PM s < 257 ∧
    rowK (PM s) (PT s 0) (PT s 1) (PT s 2) (PT s 3) (PT s 4) = nextI PM s ∧
    sortI PE PS s = true := by
  unfold recI at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨e0, e1, e2, e3, e4, hm, hm', hr, hs⟩ := h
  refine ⟨fun j hj hle => ?_, blt_iff.1 hm, blt_iff.1 hm', Nat.eq_of_beq_eq_true hr, hs⟩
  interval_cases j
  · exact edgeI_spec e0 hle
  · exact edgeI_spec e1 hle
  · exact edgeI_spec e2 hle
  · exact edgeI_spec e3 hle
  · exact edgeI_spec e4 hle

structure TreeI (PE PM PS : Nat → Nat) (PT : Nat → Nat → Nat) (MK : Nat → Nat) : Prop where
  ok : ∀ s < 256, recI PE PM PS PT MK s = true
  zero : PE 0 = IDT
  one : PM 0 = 1

theorem treeIK_spec (h : treeIK PE PM PS PT MK = true) : TreeI PE PM PS PT MK := by
  unfold treeIK at h
  simp only [andK_eq, Bool.and_eq_true] at h
  exact ⟨allK_spec h.2.2, Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1⟩

@[expose] noncomputable def MfI (PM : Nat → Nat) (k : Nat) : Nat := if k < 256 then PM k else 256

theorem MfI_succ (k : Nat) : MfI PM (k + 1) = nextI PM k := by
  unfold MfI nextI
  rw [selN_eq]
  by_cases h : k + 1 < 256
  · rw [iteT h, blt_iff.2 h, iteT rfl]
  · rw [iteF h, blt_false h, iteF Bool.false_ne_true]

theorem MfI_lt (hR : TreeI PE PM PS PT MK) (k : Nat) : MfI PM k < BAD := by
  have hB : (257 : Nat) ≤ BAD := by decide
  unfold MfI
  split
  · exact lt_of_lt_of_le (recI_spec (hR.ok k ‹_›)).2.2.1 hB
  · omega

theorem treeI_mem (hR : TreeI PE PM PS PT MK) :
    ∀ t < 256, PE t < 2 ^ 100 ∧ MatP 10 (PE t) ∈ genT MK := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    rw [hR.zero, MatP_IDT]
    exact ⟨IDT_lt, (genT MK).one_mem⟩
  have hP0 : MfI PM 0 ≤ t := by
    unfold MfI
    rw [iteT (by omega : 0 < 256), hR.one]
    omega
  have hkP : MfI PM (Nat.findGreatest (fun k => MfI PM k ≤ t) 256) ≤ t :=
    Nat.findGreatest_spec (P := fun k => MfI PM k ≤ t) (Nat.zero_le 256) hP0
  have hkN := Nat.findGreatest_le (P := fun k => MfI PM k ≤ t) 256
  generalize hk : Nat.findGreatest (fun k => MfI PM k ≤ t) 256 = k at hkP hkN
  have hkN' : k < 256 := by
    rcases Nat.lt_or_ge k 256 with h | h
    · exact h
    · have e : k = 256 := le_antisymm hkN h
      rw [e] at hkP
      unfold MfI at hkP
      rw [iteF (Nat.lt_irrefl 256)] at hkP
      omega
  have hk1 : t < MfI PM (k + 1) := by
    have := Nat.findGreatest_is_greatest (P := fun k => MfI PM k ≤ t) (k := k + 1)
      (by rw [hk]; exact Nat.lt_succ_self k) (Nat.succ_le_of_lt hkN')
    exact Nat.lt_of_not_le this
  obtain ⟨hedge, hkm, -, hrow, -⟩ := recI_spec (hR.ok k hkN')
  have e1 : MfI PM k = PM k := iteT hkN'
  rw [← MfI_succ] at hrow
  have hb : rowK (PM k) (PT k 0) (PT k 1) (PT k 2) (PT k 3) (PT k 4) < BAD := by
    rw [hrow]
    exact MfI_lt hR (k + 1)
  obtain ⟨-, hcov⟩ := rowK_cover hb
  rw [hrow] at hcov
  have hmt : PM k ≤ t := by
    rw [← e1]
    exact hkP
  obtain ⟨j, hj, hjt⟩ : ∃ j < 5, PT k j = t := by
    rcases hcov t hmt hk1 with e | e | e | e | e
    · exact ⟨0, by omega, e.symm⟩
    · exact ⟨1, by omega, e.symm⟩
    · exact ⟨2, by omega, e.symm⟩
    · exact ⟨3, by omega, e.symm⟩
    · exact ⟨4, by omega, e.symm⟩
  obtain ⟨-, he⟩ := hedge j hj (by rw [hjt]; exact hmt)
  rw [hjt] at he
  rw [he, MatP_mulT]
  exact ⟨mulT_lt _ _, (genT MK).mul_mem (ih k (by omega) hkN').2 (genT_mem MK hj)⟩

theorem treeI_inj (hR : TreeI PE PM PS PT MK) :
    ∀ a < 256, ∀ b < 256, MatP 10 (PE a) = MatP 10 (PE b) → a = b := by
  have hs : ∀ i < 256, PS i < 256 := by
    intro i hi
    have h := (recI_spec (hR.ok i hi)).2.2.2.2
    unfold sortI at h
    rw [andK_eq, Bool.and_eq_true] at h
    exact blt_iff.1 h.1
  have hlt : ∀ i, i + 1 < 256 → PE (PS i) < PE (PS (i + 1)) := by
    intro i hi
    have h := (recI_spec (hR.ok i (by omega))).2.2.2.2
    unfold sortI at h
    rw [andK_eq, Bool.and_eq_true, implK_eq, blt_iff.2 hi, iteT rfl] at h
    exact blt_iff.1 h.2
  intro a ha b hb e
  exact sorted_inj (σ := PS) (f := PE) hs hlt a ha b hb
    (MatP_inj e (treeI_mem hR a ha).1 (treeI_mem hR b hb).1)

noncomputable def entI (hR : TreeI PE PM PS PT MK) (k : Fin 256) : genT MK :=
  ⟨MatP 10 (PE k), (treeI_mem hR k k.2).2⟩

theorem entI_inj (hR : TreeI PE PM PS PT MK) : Function.Injective (entI hR) :=
  fun a b e => Fin.ext (treeI_inj hR a a.2 b b.2 (congrArg Subtype.val e))

theorem treeI_card (hR : TreeI PE PM PS PT MK) : 256 ≤ Nat.card (genT MK) := by
  simpa using Nat.card_le_card_of_injective _ (entI_inj hR)

theorem treeI_surj (hR : TreeI PE PM PS PT MK) (hc : Nat.card (genT MK) ≤ 256) :
    ∀ x ∈ genT MK, ∃ s < 256, MatP 10 (PE s) = x := by
  intro x hx
  obtain ⟨k, hk⟩ := ((entI_inj hR).bijective_of_nat_card_le (by simpa using hc)).2 ⟨x, hx⟩
  exact ⟨k, k.2, congrArg Subtype.val hk⟩

end Tree

section Table

variable {PE PM PS : Nat → Nat} {PT : Nat → Nat → Nat} {MK INV CM : Nat → Nat}
  {MR : Nat → Nat → Nat} {NI : Nat}

theorem invHit_spec {INV : Nat → Nat} {t : Nat} : ∀ {NI : Nat}, invHit INV NI t = true →
    ∃ q < NI, INV q = t
  | 0, h => absurd h Bool.false_ne_true
  | NI + 1, h => by
    have h' : bIf(Nat.beq (INV NI) t, true, invHit INV NI t) = true := h
    rw [bIf_eq'] at h'
    by_cases e : Nat.beq (INV NI) t = true
    · exact ⟨NI, by omega, Nat.eq_of_beq_eq_true e⟩
    · rw [if_neg e] at h'
      obtain ⟨q, hq, e'⟩ := invHit_spec h'
      exact ⟨q, by omega, e'⟩

theorem invAll_sound (hR : TreeI PE PM PS PT MK) (h : invAllK PE INV NI = true) :
    (∀ q < NI, INV q < 256 ∧ MatP 10 (PE (INV q)) * MatP 10 (PE (INV q)) = 1 ∧
      MatP 10 (PE (INV q)) ≠ 1) ∧
    ∀ t < 256, MatP 10 (PE t) * MatP 10 (PE t) = 1 → MatP 10 (PE t) ≠ 1 → ∃ q < NI, INV q = t := by
  unfold invAllK at h
  rw [andK_eq, Bool.and_eq_true] at h
  refine ⟨fun q hq => ?_, fun t ht h1 h2 => ?_⟩
  · have := allK_spec h.1 q hq
    unfold invOK at this
    rw [andK_eq, Bool.and_eq_true] at this
    have hl := blt_iff.1 this.1
    exact ⟨hl, (involT_iff (treeI_mem hR _ hl).1).1 this.2⟩
  · have := allK_spec h.2 t ht
    rw [implK_eq, if_pos ((involT_iff (treeI_mem hR t ht).1).2 ⟨h1, h2⟩)] at this
    exact invHit_spec this

theorem tab_sound (hR : TreeI PE PM PS PT MK) {q : Nat} (hq : INV q < 256)
    (h : tabRowK PE INV MR CM q = true) : ∀ t < 256, MR q t < 256 ∧
      MatP 10 (PE (MR q t)) = MatP 10 (PE (INV q)) * MatP 10 (PE t) ∧
      ((CM q).testBit t = true ↔
        MatP 10 (PE (INV q)) * MatP 10 (PE t) = MatP 10 (PE t) * MatP 10 (PE (INV q))) := by
  intro t ht
  have h' := allK_spec h t ht
  unfold tabK at h'
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  rw [iffK_eq, bit_eq, beqT (mulT_lt _ _) (mulT_lt _ _), MatP_mulT, MatP_mulT] at h3
  refine ⟨blt_iff.1 h1, ?_, h3⟩
  rw [Nat.eq_of_beq_eq_true h2, MatP_mulT]

end Table

section EA

variable {PE PM PS : Nat → Nat} {PT : Nat → Nat → Nat} {MK SM EL INV CM RC : Nat → Nat}
  {EX MR : Nat → Nat → Nat} {NS NI : Nat}

@[expose] noncomputable def fixSet (PE : Nat → Nat) (p : Nat → Prop) : Finset Nat :=
  @Finset.filter _ (fun v => ∀ s < 256, p s → vmF 10 (PE s) v = v)
    (fun _ => Classical.propDecidable _) (Finset.range 1024)

theorem mem_fixSet {PE : Nat → Nat} {p : Nat → Prop} {v : Nat} :
    v ∈ fixSet PE p ↔ v < 1024 ∧ ∀ s < 256, p s → vmF 10 (PE s) v = v := by
  unfold fixSet
  exact (@Finset.mem_filter _ (fun v => ∀ s < 256, p s → vmF 10 (PE s) v = v)
    (fun _ => Classical.propDecidable _) (Finset.range 1024) v).trans
    (and_congr Finset.mem_range Iff.rfl)

theorem fixSet_congr {PE : Nat → Nat} {p p' : Nat → Prop} (h : ∀ s < 256, (p s ↔ p' s)) :
    fixSet PE p = fixSet PE p' := by
  ext v
  rw [mem_fixSet, mem_fixSet]
  exact and_congr Iff.rfl (forall₂_congr fun s hs => imp_congr (h s hs) Iff.rfl)

theorem elAt_lt (EL : Nat → Nat) (i c : Nat) : elAt EL i c < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem testBit_elMask (EL : Nat → Nat) (i s : Nat) : ∀ n,
    (elMask EL i n).testBit s = true ↔ ∃ c < n, elAt EL i c = s
  | 0 => by
    change (0 : Nat).testBit s = true ↔ _
    simp
  | n + 1 => by
    change (elMask EL i n ||| 1 <<< elAt EL i n).testBit s = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_elMask EL i s n, decide_eq_true_iff]
    constructor
    · rintro (⟨c, hc, e⟩ | e)
      · exact ⟨c, by omega, e⟩
      · exact ⟨n, by omega, e⟩
    · rintro ⟨c, hc, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc' | hc'
      · exact Or.inl ⟨c, hc', e⟩
      · subst hc'
        exact Or.inr e

theorem testBit_imgMask (MR : Nat → Nat → Nat) (EL : Nat → Nat) (q i s : Nat) : ∀ n,
    (imgMask MR EL q i n).testBit s = true ↔ ∃ c < n, MR q (elAt EL i c) = s
  | 0 => by
    change (0 : Nat).testBit s = true ↔ _
    simp
  | n + 1 => by
    change (imgMask MR EL q i n ||| 1 <<< MR q (elAt EL i n)).testBit s = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_imgMask MR EL q i s n, decide_eq_true_iff]
    constructor
    · rintro (⟨c, hc, e⟩ | e)
      · exact ⟨c, by omega, e⟩
      · exact ⟨n, by omega, e⟩
    · rintro ⟨c, hc, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc' | hc'
      · exact Or.inl ⟨c, hc', e⟩
      · subst hc'
        exact Or.inr e

theorem ea_exists (hR : TreeI PE PM PS PT MK) (hI : invAllK PE INV NI = true)
    (hT : ∀ q < NI, tabRowK PE INV MR CM q = true) (h0 : SM 0 = 1) (hNS : 0 < NS)
    (hS : ∀ i < NS, setK PE SM EL INV CM RC EX MR NS NI i = true)
    (X : Set (Matrix (Fin 10) (Fin 10) (ZMod 2))) (hX : ∀ x ∈ X, ∃ s < 256, MatP 10 (PE s) = x)
    (h1 : 1 ∈ X) (hmul : ∀ x ∈ X, ∀ y ∈ X, x * y ∈ X) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hsq : ∀ x ∈ X, x * x = 1) :
    ∃ i < NS, ∀ s < 256, ((SM i).testBit s = true ↔ MatP 10 (PE s) ∈ X) := by
  classical
  have hinv := invAll_sound hR hI
  have hPE0 : MatP 10 (PE 0) = 1 := by rw [hR.zero, MatP_IDT]
  have key : ∀ ls : List Nat, (∀ s ∈ ls, s < 256 ∧ MatP 10 (PE s) ∈ X) →
      ∃ i < NS, (∀ s < 256, (SM i).testBit s = true → MatP 10 (PE s) ∈ X) ∧
        (SM i).testBit 0 = true ∧ ∀ s ∈ ls, (SM i).testBit s = true := by
    intro ls
    induction ls with
    | nil =>
      intro _
      refine ⟨0, hNS, fun s _ hb => ?_, by rw [h0]; decide, fun s hs => absurd hs List.not_mem_nil⟩
      rw [h0, ← pow_zero (2 : Nat), Nat.testBit_two_pow, decide_eq_true_eq] at hb
      subst hb
      rw [hPE0]
      exact h1
    | cons m ls ih =>
      intro hls
      obtain ⟨i, hi, hiX, hi0, hils⟩ := ih fun s hs => hls s (List.mem_cons_of_mem m hs)
      obtain ⟨hm, hmX⟩ := hls m List.mem_cons_self
      by_cases hbm : (SM i).testBit m = true
      · refine ⟨i, hi, hiX, hi0, fun s hs => ?_⟩
        rcases List.mem_cons.1 hs with rfl | hs
        · exact hbm
        · exact hils s hs
      have hbm' : (SM i).testBit m = false := by simpa using hbm
      have hm0 : MatP 10 (PE m) ≠ 1 := by
        intro e
        have e0 : m = 0 := treeI_inj hR m hm 0 (by norm_num) (by rw [e, hPE0])
        subst e0
        exact hbm hi0
      obtain ⟨q, hq, hqm⟩ := hinv.2 m hm (hsq _ hmX) hm0
      have hset := hS i hi
      unfold setK at hset
      simp only [letB_eq, andK_eq, Bool.and_eq_true] at hset
      obtain ⟨-, hmask, -, hext, -⟩ := hset
      have hmask' := Nat.eq_of_beq_eq_true hmask
      have hel : ∀ t, (SM i).testBit t = true ↔ ∃ c < elN EL i, elAt EL i c = t := fun t => by
        rw [← hmask', testBit_elMask]
      have hiq := (hinv.1 q hq).1
      have htab := tab_sound hR hiq (hT q hq)
      have hland : Nat.land (SM i) (CM q) = SM i := by
        apply Nat.eq_of_testBit_eq
        intro t
        change (SM i &&& CM q).testBit t = _
        rw [Nat.testBit_and]
        by_cases ht : t < 256
        · cases hbt : (SM i).testBit t
          · rfl
          · rw [(htab t ht).2.2.2 (by rw [hqm]; exact hcomm _ hmX _ (hiX t ht hbt))]
            rfl
        · cases hbt : (SM i).testBit t
          · rfl
          · obtain ⟨c, -, hc⟩ := (hel t).1 hbt
            exact absurd (hc ▸ elAt_lt EL i c) ht
      have he := allK_spec hext q hq
      unfold extK at he
      simp only [letB_eq, andK_eq, implK_eq, notK_eq, bit_eq, hqm, hland, Nat.beq_refl, hbm',
        Bool.not_false, Bool.true_and, if_true, Bool.and_eq_true] at he
      have he' : andK (Nat.blt (EX i q) NS)
          (Nat.beq (SM (EX i q)) (Nat.lor (SM i) (imgMask MR EL q i (elN EL i)))) = true := he
      rw [andK_eq, Bool.and_eq_true] at he'
      obtain ⟨hj, hSM⟩ := he'
      have hSj := Nat.eq_of_beq_eq_true hSM
      have hbits : ∀ s, (SM (EX i q)).testBit s =
          ((SM i).testBit s || (imgMask MR EL q i (elN EL i)).testBit s) := fun s => by
        rw [hSj]
        exact Nat.testBit_or _ _ _
      refine ⟨EX i q, blt_iff.1 hj, fun s hs hb => ?_, by rw [hbits, hi0, Bool.true_or], ?_⟩
      · rw [hbits, Bool.or_eq_true] at hb
        rcases hb with hb | hb
        · exact hiX s hs hb
        · obtain ⟨c, hc, rfl⟩ := (testBit_imgMask MR EL q i _ _).1 hb
          have ht := elAt_lt EL i c
          rw [(htab _ ht).2.1, hqm]
          exact hmul _ hmX _ (hiX _ ht ((hel _).2 ⟨c, hc, rfl⟩))
      · intro s hs
        rw [hbits, Bool.or_eq_true]
        rcases List.mem_cons.1 hs with rfl | hs
        · right
          obtain ⟨c, hc, hc0⟩ := (hel 0).1 hi0
          refine (testBit_imgMask MR EL q i _ _).2 ⟨c, hc, ?_⟩
          rw [hc0]
          exact treeI_inj hR _ (htab 0 (by norm_num)).1 _ hm
            (by rw [(htab 0 (by norm_num)).2.1, hqm, hPE0, mul_one])
        · exact Or.inl (hils s hs)
  obtain ⟨i, hi, hiX, -, hils⟩ :=
    key ((List.range 256).filter fun s => decide (MatP 10 (PE s) ∈ X)) fun s hs => by
      simpa [List.mem_filter, List.mem_range] using hs
  exact ⟨i, hi, fun s hs => ⟨hiX s hs, fun hx => hils s (by simp [hs, hx])⟩⟩

theorem el_count {i : Nat} (h : setK PE SM EL INV CM RC EX MR NS NI i = true) :
    ((Finset.range 256).filter fun s => (SM i).testBit s = true).card = elN EL i ∧
      ∀ s, 256 ≤ s → (SM i).testBit s = false := by
  unfold setK at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨hlt, hmask, hinc, -⟩ := h
  have e256 : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  have h256 : SM i < 2 ^ 256 := by
    rw [e256]
    exact blt_iff.1 hlt
  have hm := Nat.eq_of_beq_eq_true hmask
  have hstep : ∀ c, Nat.succ c < elN EL i → elAt EL i c < elAt EL i (Nat.succ c) := by
    intro c hc
    have := allK_spec hinc c (by omega)
    rw [implK_eq, blt_iff.2 hc, if_pos rfl] at this
    exact blt_iff.1 this
  have hmono : ∀ b, b < elN EL i → ∀ a < b, elAt EL i a < elAt EL i b := by
    intro b
    induction b with
    | zero => exact fun _ a ha => absurd ha (Nat.not_lt_zero a)
    | succ b ih =>
      intro hb a ha
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha' | ha'
      · exact (ih (by omega) a ha').trans (hstep b hb)
      · rw [ha']
        exact hstep b hb
  have hset : ((Finset.range 256).filter fun s => (SM i).testBit s = true) =
      (Finset.range (elN EL i)).image (elAt EL i) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    rw [← hm, testBit_elMask]
    constructor
    · rintro ⟨-, c, hc, e⟩
      exact ⟨c, hc, e⟩
    · rintro ⟨c, hc, e⟩
      refine ⟨?_, c, hc, e⟩
      rw [← e]
      exact elAt_lt EL i c
  refine ⟨?_, fun s hs => Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le h256 (Nat.pow_le_pow_right (by norm_num) hs))⟩
  rw [hset, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  rw [Finset.coe_range, Set.mem_Iio] at ha hb
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd hab (hmono b hb a h').ne
  · exact h'
  · exact absurd hab (hmono a ha b h').ne'

theorem ite_xor_xorJ (R A B : Nat) (x y : Bool) :
    (if (x ^^ y) = true then R ^^^ (A ^^^ B) else A ^^^ B) =
      (if x = true then R ^^^ A else A) ^^^ (if y = true then R ^^^ B else B) := by
  apply Nat.eq_of_testBit_eq
  intro j
  cases x <;> cases y <;> simp [Nat.testBit_xor] <;> cases R.testBit j <;> cases A.testBit j <;>
    cases B.testBit j <;> decide

theorem condRec_xorJ (g : Nat → Nat) (a b : Nat → Bool) : ∀ m,
    (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => if (a k ^^ b k) = true then g k ^^^ acc
      else acc) m : Nat) =
      (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => if a k = true then g k ^^^ acc else acc) m :
        Nat) ^^^ Nat.rec (motive := fun _ => Nat) 0
          (fun k acc => if b k = true then g k ^^^ acc else acc) m
  | 0 => (Nat.zero_xor 0).symm
  | m + 1 => by
    simp only [Nat.rec_add_one]
    rw [condRec_xorJ g a b m]
    exact ite_xor_xorJ _ _ _ _ _

theorem vmF_xorJ (d M a b : Nat) : vmF d M (a ^^^ b) = vmF d M a ^^^ vmF d M b := by
  simp only [vmF_rec, Nat.testBit_xor]
  exact condRec_xorJ (rowF d M) (fun k => a.testBit k) (fun k => b.testBit k) d

theorem testBit_fieldsJ (g : Nat → Nat) (hg : ∀ l, g l < 2 ^ 10) (p : Nat) : ∀ m,
    (Nat.rec (motive := fun _ => Nat) 0
      (fun l acc => Nat.lor acc (Nat.shiftLeft (g l) (Nat.mul 10 l))) m : Nat).testBit p =
      (decide (p < 10 * m) && (g (p / 10)).testBit (p % 10))
  | 0 => by
    change (0 : Nat).testBit p = _
    simp
  | m + 1 => by
    change ((Nat.rec (motive := fun _ => Nat) 0
      (fun l acc => Nat.lor acc (Nat.shiftLeft (g l) (Nat.mul 10 l))) m : Nat) |||
        (g m <<< (10 * m))).testBit p = _
    rw [Nat.testBit_or, testBit_fieldsJ g hg p m, Nat.testBit_shiftLeft]
    by_cases h1 : p < 10 * m
    · have h2 : p < 10 * (m + 1) := by omega
      have h3 : ¬ 10 * m ≤ p := by omega
      simp [h1, h2, h3]
    · by_cases h2 : p < 10 * (m + 1)
      · have e1 : p / 10 = m := by omega
        have e2 : p % 10 = p - 10 * m := by omega
        have h3 : 10 * m ≤ p := by omega
        simp [h1, h2, h3, e1, e2]
      · have h3 : (g m).testBit (p - 10 * m) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (hg m)
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, h3]

theorem rcLab_lt (RC : Nat → Nat) (i l : Nat) : rcLab RC i l < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem rcVec_lt (RC : Nat → Nat) (i k : Nat) : rcVec RC i k < 2 ^ 10 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem testBit_fixImg {i x : Nat} (hx : x < 2 ^ 10) (p : Nat) :
    (fixImg PE RC i x).testBit p =
      (decide (p < 10 * 5) && (vmF 10 (PE (rcLab RC i (p / 10))) x ^^^ x).testBit (p % 10)) :=
  testBit_fieldsJ (fun l => Nat.xor (vmF 10 (PE (rcLab RC i l)) x) x)
    (fun _ => Nat.xor_lt_two_pow (vmF_lt 10 _ x) hx) p 5

theorem fixImg_xor {i a b : Nat} (ha : a < 2 ^ 10) (hb : b < 2 ^ 10) (p : Nat) :
    (fixImg PE RC i (a ^^^ b)).testBit p =
      ((fixImg PE RC i a).testBit p ^^ (fixImg PE RC i b).testBit p) := by
  rw [testBit_fixImg (Nat.xor_lt_two_pow ha hb), testBit_fixImg ha, testBit_fixImg hb, vmF_xorJ]
  simp only [Nat.testBit_xor]
  cases decide (p < 10 * 5) <;> cases (vmF 10 (PE (rcLab RC i (p / 10))) a).testBit (p % 10) <;>
    cases (vmF 10 (PE (rcLab RC i (p / 10))) b).testBit (p % 10) <;> cases a.testBit (p % 10) <;>
    cases b.testBit (p % 10) <;> rfl

noncomputable def rcSum (RC : Nat → Nat) (i c m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => if c.testBit k then rcVec RC i k ^^^ acc else acc)
    m

theorem rcSum_lt (RC : Nat → Nat) (i c m : Nat) : rcSum RC i c m < 2 ^ 10 :=
  condRec_lt (rcVec RC i) (fun k => c.testBit k) (rcVec_lt RC i) m

theorem rcSum_xor (RC : Nat → Nat) (i a b m : Nat) :
    rcSum RC i (a ^^^ b) m = rcSum RC i a m ^^^ rcSum RC i b m := by
  unfold rcSum
  simp only [Nat.testBit_xor]
  exact condRec_xorJ (rcVec RC i) (fun k => a.testBit k) (fun k => b.testBit k) m

theorem phi_condRec (φ : Nat → Bool)
    (hφ : ∀ a b, a < 2 ^ 10 → b < 2 ^ 10 → φ (a ^^^ b) = (φ a ^^ φ b)) (g : Nat → Nat)
    (hg : ∀ k, g k < 2 ^ 10) (c : Nat → Bool) : ∀ m,
    φ (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => if c k = true then g k ^^^ acc else acc) m) =
      Nat.rec (motive := fun _ => Bool) false (fun k b => (c k && φ (g k)) ^^ b) m
  | 0 => by
    have h := hφ 0 0 (Nat.two_pow_pos 10) (Nat.two_pow_pos 10)
    rw [Nat.xor_self, Bool.xor_self] at h
    exact h
  | m + 1 => by
    simp only [Nat.rec_add_one]
    rw [← phi_condRec φ hφ g hg c m]
    have hl := condRec_lt g c hg m
    cases c m
    · simp
    · simp [hφ _ _ (hg m) hl]

theorem rec_lowestJ (t : Nat → Bool) (k : Nat) (h0 : ∀ k' < k, t k' = false) (h1 : t k = true)
    (r : Nat) (h2 : ∀ k', k < k' → k' < r → t k' = false) : ∀ m ≤ r,
    (Nat.rec (motive := fun _ => Bool) false (fun k' b => t k' ^^ b) m : Bool) = decide (k < m)
  | 0, _ => by simp
  | m + 1, hm => by
    simp only [Nat.rec_add_one]
    rw [rec_lowestJ t k h0 h1 r h2 m (by omega)]
    rcases lt_trichotomy m k with hlt | heq | hgt
    · have a1 : ¬ k < m := by omega
      have a2 : ¬ k < m + 1 := by omega
      simp [h0 m hlt, a1, a2]
    · subst heq
      simp [h1]
    · have a2 : k < m + 1 := by omega
      simp [h2 m hgt (by omega), hgt, a2]

theorem rank_sound {i : Nat} (h : setK PE SM EL INV CM RC EX MR NS NI i = true) (hne : SM i ≠ 1) :
    elN EL i * (fixSet PE fun s => (SM i).testBit s = true).card ≤ 512 := by
  classical
  unfold setK at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, hrk⟩ := h
  have hb : Nat.beq (SM i) 1 = false := by
    cases e : Nat.beq (SM i) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hne
  rw [implK_eq, notK_eq, hb, Bool.not_false, if_pos rfl] at hrk
  unfold rankK at hrk
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at hrk
  obtain ⟨hlab, -, hn, hpiv⟩ := hrk
  have hn' : 2 * elN EL i ≤ 2 ^ rcR RC i := by
    have := Nat.le_of_ble_eq_true hn
    rw [← Nat.one_shiftLeft]
    exact this
  have hP : ∀ k < rcR RC i, (fixImg PE RC i (rcVec RC i k)).testBit (rcPiv RC i k) = true ∧
      ∀ k' < rcR RC i, k < k' →
        (fixImg PE RC i (rcVec RC i k')).testBit (rcPiv RC i k) = false := by
    intro k hk
    have h' := allK_spec hpiv k hk
    simp only [letB_eq, andK_eq, Bool.and_eq_true, bit_eq] at h'
    refine ⟨h'.1, fun k' hk' hkk' => ?_⟩
    have h'' := allK_spec h'.2 k' hk'
    simpa [implK_eq, notK_eq, bit_eq, blt_iff.2 hkk'] using h''
  have hlab' : ∀ l < 5, (SM i).testBit (rcLab RC i l) = true := fun l hl => by
    have := allK_spec hlab l hl
    rwa [bit_eq] at this
  set F := fixSet PE (fun s => (SM i).testBit s = true) with hF
  have hF10 : ∀ z ∈ F, z < 2 ^ 10 := fun z hz =>
    lt_of_lt_of_eq (mem_fixSet.1 hz).1 (by norm_num)
  have hvan : ∀ z ∈ F, ∀ p, (fixImg PE RC i z).testBit p = false := by
    intro z hz p
    obtain ⟨-, hz2⟩ := mem_fixSet.1 hz
    rw [testBit_fixImg (hF10 z hz)]
    by_cases hp : p < 10 * 5
    · rw [hz2 _ (rcLab_lt RC i _) (hlab' _ (by omega)), Nat.xor_self, Nat.zero_testBit,
        Bool.and_false]
    · simp [hp]
  have hsum : ∀ p c, (fixImg PE RC i (rcSum RC i c (rcR RC i))).testBit p =
      Nat.rec (motive := fun _ => Bool) false
        (fun k b => (c.testBit k && (fixImg PE RC i (rcVec RC i k)).testBit p) ^^ b) (rcR RC i) :=
    fun p c => phi_condRec (fun v => (fixImg PE RC i v).testBit p)
      (fun a b ha hb => fixImg_xor ha hb p) (rcVec RC i) (rcVec_lt RC i) (fun k => c.testBit k)
      (rcR RC i)
  have hkey : ∀ c, c < 2 ^ rcR RC i → c ≠ 0 →
      ∃ p, (fixImg PE RC i (rcSum RC i c (rcR RC i))).testBit p = true := by
    intro c hc hc0
    have hex : ∃ k, c.testBit k = true := by
      by_contra hno
      simp only [not_exists] at hno
      refine hc0 (Nat.eq_of_testBit_eq fun j => ?_)
      rw [Nat.zero_testBit]
      simpa using hno j
    have hk1 : c.testBit (Nat.find hex) = true := Nat.find_spec hex
    have hk0 : ∀ k' < Nat.find hex, c.testBit k' = false := fun k' hk' => by
      simpa using Nat.find_min hex hk'
    have hkr : Nat.find hex < rcR RC i := by
      by_contra hge
      replace hge := Nat.le_of_not_lt hge
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hge))]
        at hk1
      exact Bool.false_ne_true hk1
    refine ⟨rcPiv RC i (Nat.find hex), ?_⟩
    rw [hsum]
    have := rec_lowestJ
      (fun k' => c.testBit k' && (fixImg PE RC i (rcVec RC i k')).testBit (rcPiv RC i (Nat.find hex)))
      (Nat.find hex) (fun k' hk' => by simp [hk0 k' hk']) (by simp [hk1, (hP _ hkr).1]) (rcR RC i)
      (fun k' h1 h2 => by simp [(hP _ hkr).2 k' h2 h1]) (rcR RC i) le_rfl
    exact this.trans (decide_eq_true hkr)
  have hcard : F.card * 2 ^ rcR RC i ≤ 1024 := by
    have := Finset.card_le_card_of_injOn (s := F ×ˢ Finset.range (2 ^ rcR RC i))
      (t := Finset.range 1024) (fun q => q.1 ^^^ rcSum RC i q.2 (rcR RC i)) ?_ ?_
    · rwa [Finset.card_product, Finset.card_range, Finset.card_range] at this
    · intro q hq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product,
        Finset.mem_range] at hq ⊢
      exact lt_of_lt_of_eq (Nat.xor_lt_two_pow (hF10 _ hq.1) (rcSum_lt RC i _ _)) (by norm_num)
    · intro q hq q' hq' he
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product,
        Finset.mem_range] at hq hq'
      have he' : q.1 ^^^ rcSum RC i q.2 (rcR RC i) = q'.1 ^^^ rcSum RC i q'.2 (rcR RC i) := he
      have e1 : q.1 ^^^ q'.1 = rcSum RC i (q.2 ^^^ q'.2) (rcR RC i) := by
        rw [rcSum_xor]
        apply Nat.eq_of_testBit_eq
        intro j
        have h' := congrArg (fun w => Nat.testBit w j) he'
        simp only [Nat.testBit_xor] at h' ⊢
        revert h'
        cases q.1.testBit j <;> cases q'.1.testBit j <;>
          cases (rcSum RC i q.2 (rcR RC i)).testBit j <;>
          cases (rcSum RC i q'.2 (rcR RC i)).testBit j <;> decide
      have hc0 : q.2 ^^^ q'.2 = 0 := by
        by_contra hne0
        obtain ⟨p, hp⟩ := hkey _ (Nat.xor_lt_two_pow hq.2 hq'.2) hne0
        rw [← e1, fixImg_xor (hF10 _ hq.1) (hF10 _ hq'.1), hvan _ hq.1 p, hvan _ hq'.1 p] at hp
        exact absurd hp (by decide)
      have e2 : q.2 = q'.2 := by
        apply Nat.eq_of_testBit_eq
        intro j
        have h' := congrArg (fun w => Nat.testBit w j) hc0
        simp only [Nat.testBit_xor, Nat.zero_testBit] at h'
        revert h'
        cases q.2.testBit j <;> cases q'.2.testBit j <;> decide
      rw [e2] at he'
      have e3 : q.1 = q'.1 := by
        apply Nat.eq_of_testBit_eq
        intro j
        have h' := congrArg (fun w => Nat.testBit w j) he'
        simp only [Nat.testBit_xor] at h'
        revert h'
        cases q.1.testBit j <;> cases q'.1.testBit j <;>
          cases (rcSum RC i q'.2 (rcR RC i)).testBit j <;> decide
      exact Prod.ext e3 e2
  have h1 : 2 * elN EL i * F.card ≤ 2 ^ rcR RC i * F.card := Nat.mul_le_mul_right _ hn'
  have h2 : 2 * elN EL i * F.card ≤ 1024 := by
    rw [Nat.mul_comm (2 ^ rcR RC i)] at h1
    exact h1.trans hcard
  rw [Nat.mul_assoc] at h2
  omega

theorem ea_bound (hR : TreeI PE PM PS PT MK) (hI : invAllK PE INV NI = true)
    (hT : ∀ q < NI, tabRowK PE INV MR CM q = true) (h0 : SM 0 = 1) (hNS : 0 < NS)
    (hS : ∀ i < NS, setK PE SM EL INV CM RC EX MR NS NI i = true)
    (X : Set (Matrix (Fin 10) (Fin 10) (ZMod 2))) (hX : ∀ x ∈ X, ∃ s < 256, MatP 10 (PE s) = x)
    (h1 : 1 ∈ X) (hmul : ∀ x ∈ X, ∀ y ∈ X, x * y ∈ X) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hsq : ∀ x ∈ X, x * x = 1) (hne : X ≠ {1}) :
    Nat.card X * (fixSet PE fun s => MatP 10 (PE s) ∈ X).card ≤ 512 := by
  classical
  obtain ⟨i, hi, hiff⟩ := ea_exists hR hI hT h0 hNS hS X hX h1 hmul hcomm hsq
  have hSi : SM i ≠ 1 := by
    intro e
    refine hne (Set.eq_singleton_iff_unique_mem.2 ⟨h1, fun x hx => ?_⟩)
    obtain ⟨s, hs, rfl⟩ := hX x hx
    have hb := (hiff s hs).2 hx
    rw [e, testBit_one_eq] at hb
    have hs0 : s = 0 := by simpa using hb
    rw [hs0, hR.zero, MatP_IDT]
  have hcard : Nat.card X = ((Finset.range 256).filter fun s => (SM i).testBit s = true).card := by
    have hXe : X = ↑(((Finset.range 256).filter fun s => (SM i).testBit s = true).image
        fun s => MatP 10 (PE s)) := by
      ext x
      simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_range, Set.mem_image,
        Set.mem_setOf_eq]
      constructor
      · intro hx
        obtain ⟨s, hs, rfl⟩ := hX x hx
        exact ⟨s, ⟨hs, (hiff s hs).2 hx⟩, rfl⟩
      · rintro ⟨s, ⟨hs, hb⟩, rfl⟩
        exact (hiff s hs).1 hb
    rw [hXe, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn]
    intro a ha b hb e
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
    exact treeI_inj hR a ha.1 b hb.1 e
  rw [hcard, fixSet_congr fun s hs => (hiff s hs).symm, (el_count (hS i hi)).1]
  exact rank_sound (hS i hi) hSi

end EA

end CFSG.KC.Co2J

end
