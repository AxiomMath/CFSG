module

public import CFSG.LocalAnalysis.RankThreeUC.GL33.Group
public import Certificates.Data.Kernel.GL33K

public section

namespace CFSG.KC.GL33K

open CFSG.GL33 CFSG.GL33.Native

theorem mulK_eq_mulC (a b : ℕ) : mulK a b = mulC a b := rfl

theorem oneK_eq : oneK = oneC := rfl

theorem good_mulK {a b : ℕ} (ha : Good a) (hb : Good b) : Good (mulK a b) := by
  rw [mulK_eq_mulC, ← mulF_eq_mulC]
  exact good_mulF ha hb

theorem ofCode_mulK {a b : ℕ} (ha : Good a) (hb : Good b) :
    ofCode (mulK a b) = ofCode a * ofCode b := by
  rw [mulK_eq_mulC, ← mulF_eq_mulC, ofCode_mulF ha hb]

theorem mulK_lt (a b : ℕ) : mulK a b < 3 ^ 9 := by
  rw [mulK_eq_mulC]
  exact mulC_lt a b

theorem good_oneK : Good oneK := good_oneC

theorem ofCode_oneK : ofCode oneK = 1 := ofCode_oneC

theorem ofCode_inv_of_mulK {a b : ℕ} (ha : Good a) (hb : Good b) (h : mulK a b = oneK) :
    ofCode b = (ofCode a)⁻¹ := by
  have : ofCode a * ofCode b = 1 := by rw [← ofCode_mulK ha hb, h, ofCode_oneK]
  exact eq_inv_of_mul_eq_one_right this

theorem good_conjK {n n' y : ℕ} (hn : Good n) (hn' : Good n') (hy : Good y) :
    Good (conjK n n' y) :=
  good_mulK (good_mulK hn hy) hn'

theorem ofCode_conjK {n n' y : ℕ} (hn : Good n) (hn' : Good n') (hy : Good y)
    (h : mulK n n' = oneK) : ofCode (conjK n n' y) = ofCode n * ofCode y * (ofCode n)⁻¹ := by
  unfold conjK
  rw [ofCode_mulK (good_mulK hn hy) hn', ofCode_mulK hn hy, ofCode_inv_of_mulK hn hn' h]

theorem good_powK {a : ℕ} (ha : Good a) (e : ℕ) : Good (powK a e) := by
  induction e with
  | zero => exact good_oneK
  | succ e ih => exact good_mulK ih ha

theorem ofCode_powK {a : ℕ} (ha : Good a) (e : ℕ) : ofCode (powK a e) = ofCode a ^ e := by
  induction e with
  | zero => exact ofCode_oneK
  | succ e ih =>
    change ofCode (mulK (powK a e) a) = _
    rw [ofCode_mulK (good_powK ha e) ha, ih, pow_succ]

theorem allK_iff {α : Type} (p : α → Bool) (L : List α) : allK p L = true ↔ ∀ x ∈ L, p x = true := by
  induction L with
  | nil => simp [allK]
  | cons c L ih =>
    change (p c && allK p L) = true ↔ _
    rw [Bool.and_eq_true, ih]
    simp

theorem elemK_iff (c : ℕ) (L : List ℕ) : elemK c L = true ↔ c ∈ L := by
  induction L with
  | nil => simp [elemK]
  | cons d L ih =>
    change (c == d || elemK c L) = true ↔ _
    rw [Bool.or_eq_true, ih, beq_iff_eq]
    simp

theorem bitK_two_pow_or (S a c : ℕ) : bitK (S ||| 2 ^ a) c = true ↔ bitK S c = true ∨ c = a := by
  unfold bitK
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_iff]
  exact or_congr_right eq_comm

theorem bitK_maskK (L : List ℕ) (c : ℕ) : bitK (maskK L) c = true ↔ c ∈ L := by
  induction L with
  | nil => simp [maskK, bitK]
  | cons d L ih =>
    change bitK (maskK L ||| 2 ^ d) c = true ↔ _
    rw [bitK_two_pow_or, ih]
    simp [or_comm]

theorem bitK_two_pow (a c : ℕ) : bitK (2 ^ a) c = true ↔ c = a := by
  unfold bitK
  rw [Nat.testBit_two_pow, decide_eq_true_iff]
  exact eq_comm

theorem setK_sound {M : ℕ} {L : List ℕ} (h : setK M L 0 = true) (c : ℕ) :
    bitK M c = true ↔ c ∈ L := by
  suffices ∀ S, setK M L S = true → ∀ c, bitK M c = true ↔ bitK S c = true ∨ c ∈ L by
    rw [this 0 h c]
    simp [bitK]
  clear h c
  induction L with
  | nil =>
    intro S hS c
    have : S = M := by simpa [setK] using hS
    simp [this]
  | cons d L ih =>
    intro S hS c
    change (!bitK S d && setK M L (S ||| 2 ^ d)) = true at hS
    rw [Bool.and_eq_true] at hS
    rw [ih _ hS.2 c, bitK_two_pow_or, List.mem_cons]
    tauto

theorem evalK_mem {a b x : ℕ} {K : Subgroup G} (ha : Good a) (hb : Good b) (hx : Good x)
    (haK : ofCode a ∈ K) (hbK : ofCode b ∈ K) (hxK : ofCode x ∈ K) (w : List (ℕ × ℕ)) :
    Good (evalK a b x w) ∧ ofCode (evalK a b x w) ∈ K := by
  suffices ∀ acc, Good acc → ofCode acc ∈ K →
      Good (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => ih (mulK acc (powK (if l.1 == 0 then a else if l.1 == 1 then b else x)
          l.2))) w acc) ∧
      ofCode (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => ih (mulK acc (powK (if l.1 == 0 then a else if l.1 == 1 then b else x)
          l.2))) w acc) ∈ K from this oneK good_oneK (by rw [ofCode_oneK]; exact K.one_mem)
  induction w with
  | nil => exact fun acc h1 h2 => ⟨h1, h2⟩
  | cons l w ih =>
    intro acc h1 h2
    have hg : Good (if l.1 == 0 then a else if l.1 == 1 then b else x) ∧
        ofCode (if l.1 == 0 then a else if l.1 == 1 then b else x) ∈ K := by
      split_ifs
      · exact ⟨ha, haK⟩
      · exact ⟨hb, hbK⟩
      · exact ⟨hx, hxK⟩
    refine ih _ (good_mulK h1 (good_powK hg.1 _)) ?_
    rw [ofCode_mulK h1 (good_powK hg.1 _), ofCode_powK hg.1]
    exact K.mul_mem h2 (K.pow_mem hg.2 _)

theorem treeK_bits {g₁ g₂ M : ℕ} {R : List (ℕ × ℕ × ℕ)} :
    ∀ {S : ℕ}, treeK g₁ g₂ M R S = true →
      ∀ c, bitK M c = true ↔ bitK S c = true ∨ c ∈ R.map (·.1) := by
  induction R with
  | nil =>
    intro S hS c
    have : S = M := by simpa [treeK] using hS
    simp [this]
  | cons r R ih =>
    intro S hS c
    change (bitK S r.2.1 && !bitK S r.1 && r.1 == mulK r.2.1 (genK g₁ g₂ r.2.2) &&
      treeK g₁ g₂ M R (S ||| 2 ^ r.1)) = true at hS
    rw [Bool.and_eq_true] at hS
    rw [ih hS.2 c, bitK_two_pow_or, List.map_cons, List.mem_cons]
    tauto

theorem genK_mem {a b : ℕ} (ha : Good a) (hb : Good b) (l : ℕ) :
    Good (genK a b l) ∧ ofCode (genK a b l) ∈ sub2 a b := by
  unfold genK
  split_ifs
  · exact ⟨ha, Subgroup.subset_closure (by simp)⟩
  · exact ⟨hb, Subgroup.subset_closure (by simp)⟩

theorem treeK_inv {a b M : ℕ} (ha : Good a) (hb : Good b) {R : List (ℕ × ℕ × ℕ)} :
    ∀ {S : ℕ}, treeK a b M R S = true →
      (∀ c, bitK S c = true → c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ sub2 a b) →
      (∀ c ∈ R.map (·.1), c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ sub2 a b ∧ bitK S c = false) ∧
        (R.map (·.1)).Nodup := by
  induction R with
  | nil => intro S _ _; simp
  | cons r R ih =>
    intro S hS hP
    change (bitK S r.2.1 && !bitK S r.1 && r.1 == mulK r.2.1 (genK a b r.2.2) &&
      treeK a b M R (S ||| 2 ^ r.1)) = true at hS
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hS
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hS
    obtain ⟨p1, p2, p3⟩ := hP _ h1
    have hg := genK_mem ha hb r.2.2
    have hc : r.1 < 3 ^ 9 ∧ Good r.1 ∧ ofCode r.1 ∈ sub2 a b := by
      rw [h3]
      exact ⟨mulK_lt _ _, good_mulK p2 hg.1, by
        rw [ofCode_mulK p2 hg.1]
        exact (sub2 a b).mul_mem p3 hg.2⟩
    have hP' : ∀ c, bitK (S ||| 2 ^ r.1) c = true → c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ sub2 a b := by
      intro c hc'
      rcases (bitK_two_pow_or S r.1 c).1 hc' with h | rfl
      · exact hP c h
      · exact hc
    obtain ⟨i1, i2⟩ := ih h4 hP'
    have hnot : ∀ c ∈ R.map (·.1), bitK S c = false ∧ c ≠ r.1 := by
      intro c hc'
      have hf := (i1 c hc').2.2.2
      have hS' : ¬ (bitK S c = true ∨ c = r.1) := fun h => by
        rw [(bitK_two_pow_or S r.1 c).2 h] at hf
        exact absurd hf (by decide)
      refine ⟨?_, fun e => hS' (Or.inr e)⟩
      cases h : bitK S c
      · rfl
      · exact absurd (Or.inl h) hS'
    refine ⟨fun c hc' => ?_, ?_⟩
    · rw [List.map_cons, List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · exact ⟨hc.1, hc.2.1, hc.2.2, h2⟩
      · exact ⟨(i1 c hc').1, (i1 c hc').2.1, (i1 c hc').2.2.1, (hnot c hc').1⟩
    · rw [List.map_cons]
      exact List.nodup_cons.2 ⟨fun hm => (hnot _ hm).2 rfl, i2⟩

theorem inv_mem_of_mul_mem' (S : Set G) (x : G) (hx : ∀ y ∈ S, y * x ∈ S) :
    ∀ y ∈ S, y * x⁻¹ ∈ S := by
  have hp : ∀ k : ℕ, ∀ y ∈ S, y * x ^ k ∈ S := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, ← mul_assoc]
      exact hx _ (ih y hy)
  have h1 : x ^ (Nat.card G - 1) * x = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one']
  intro y hy
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact hp _ y hy

theorem memK_bits {a b n M : ℕ} {R : List (ℕ × ℕ × ℕ)} (h : memK a b n M R = true) (c : ℕ)
    (hc : bitK M c = true) : c = oneK ∨ c ∈ R.map (·.1) := by
  change ((R.length + 1 == n && treeK a b M R (2 ^ oneK)) && closK a b M R) = true at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  rw [treeK_bits h.1.2 c, bitK_two_pow] at hc
  exact hc

theorem memK_sound {a b n M : ℕ} {R : List (ℕ × ℕ × ℕ)} (h : memK a b n M R = true)
    (ha : Good a) (hb : Good b) :
    (∀ c, bitK M c = true → c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ sub2 a b) ∧
      (∀ x ∈ sub2 a b, bitK M (encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) = true) ∧
      Nat.card (sub2 a b) = n := by
  classical
  have hm := h
  change ((R.length + 1 == n && treeK a b M R (2 ^ oneK)) && closK a b M R) = true at hm
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨hn, ht⟩, hcl⟩ := hm
  have hone : oneK < 3 ^ 9 ∧ Good oneK ∧ ofCode oneK ∈ sub2 a b :=
    ⟨by decide, good_oneK, by rw [ofCode_oneK]; exact (sub2 a b).one_mem⟩
  obtain ⟨i1, i2⟩ := treeK_inv ha hb ht (fun c hc => by
    rw [(bitK_two_pow oneK c).1 hc]
    exact hone)
  have hA : ∀ c, bitK M c = true → c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ sub2 a b := by
    intro c hc
    rcases memK_bits h c hc with rfl | hc'
    · exact hone
    · exact ⟨(i1 c hc').1, (i1 c hc').2.1, (i1 c hc').2.2.1⟩
  have hL : ∀ c, bitK M c = true ↔ c ∈ oneK :: R.map (·.1) := by
    intro c
    refine ⟨fun hc => List.mem_cons.2 (memK_bits h c hc), fun hc => ?_⟩
    rw [treeK_bits ht c, bitK_two_pow]
    exact List.mem_cons.1 hc
  have hcl' : bitK M (mulK oneK a) = true ∧ bitK M (mulK oneK b) = true ∧
      ∀ r ∈ R, bitK M (mulK r.1 a) = true ∧ bitK M (mulK r.1 b) = true := by
    change (bitK M (mulK oneK a) && bitK M (mulK oneK b) &&
      allK (fun r => bitK M (mulK r.1 a) && bitK M (mulK r.1 b)) R) = true at hcl
    rw [Bool.and_eq_true, Bool.and_eq_true, allK_iff] at hcl
    refine ⟨hcl.1.1, hcl.1.2, fun r hr => ?_⟩
    have := hcl.2 r hr
    rwa [Bool.and_eq_true] at this
  have hclos : ∀ c, bitK M c = true → bitK M (mulK c a) = true ∧ bitK M (mulK c b) = true := by
    intro c hc
    rcases memK_bits h c hc with rfl | hc'
    · exact ⟨hcl'.1, hcl'.2.1⟩
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc'
      exact hcl'.2.2 r hr
  set T : Set G := {x | ∃ c, bitK M c = true ∧ ofCode c = x} with hTdef
  have hTmul : ∀ g ∈ ({ofCode a, ofCode b} : Set G), ∀ y ∈ T, y * g ∈ T := by
    rintro g hg _ ⟨c, hc, rfl⟩
    have hgc := (hA c hc).2.1
    rcases hg with rfl | hg
    · exact ⟨mulK c a, (hclos c hc).1, ofCode_mulK hgc ha⟩
    · rw [Set.mem_singleton_iff.1 hg]
      exact ⟨mulK c b, (hclos c hc).2, ofCode_mulK hgc hb⟩
  have key : ∀ x ∈ sub2 a b, ∀ y ∈ T, y * x ∈ T := by
    intro x hx
    have hx' : x ∈ Subgroup.closure {ofCode a, ofCode b} := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem x hx => exact hTmul x hx
    | one => intro y hy; simpa using hy
    | mul x y _ _ hx hy => intro z hz; rw [← mul_assoc]; exact hy _ (hx z hz)
    | inv x _ hx => exact inv_mem_of_mul_mem' T x hx
  have hT1 : (1 : G) ∈ T := ⟨oneK, by rw [treeK_bits ht, bitK_two_pow]; exact Or.inl rfl,
    ofCode_oneK⟩
  have hB : ∀ x ∈ sub2 a b, ∃ c, bitK M c = true ∧ ofCode c = x := by
    intro x hx
    have := key x hx 1 hT1
    rwa [one_mul] at this
  have hmem : ∀ c, bitK M c = true → c ∈ glCodes () := fun c hc =>
    (mem_glCodes_iff c).2 ⟨(hA c hc).1, (hA c hc).2.1⟩
  refine ⟨hA, fun x hx => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := hB x hx
    rw [ofCode_injOn (encode_mem_glCodes _) (hmem c hc) (ofCode_encode _)]
    exact hc
  · have hnd : (oneK :: R.map (·.1)).Nodup := by
      refine List.nodup_cons.2 ⟨fun hm => ?_, i2⟩
      have := (i1 _ hm).2.2.2
      rw [(bitK_two_pow oneK oneK).2 rfl] at this
      exact absurd this (by decide)
    have hnd' : ((oneK :: R.map (·.1)).map ofCode).Nodup :=
      List.Nodup.map_on (fun c hc d hd e => ofCode_injOn (hmem c ((hL c).2 hc))
        (hmem d ((hL d).2 hd)) e) hnd
    have hiff : ∀ x, x ∈ sub2 a b ↔ x ∈ ((oneK :: R.map (·.1)).map ofCode).toFinset := by
      intro x
      rw [List.mem_toFinset, List.mem_map]
      constructor
      · intro hx
        obtain ⟨c, hc, rfl⟩ := hB x hx
        exact ⟨c, (hL c).1 hc, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact (hA c ((hL c).2 hc)).2.2
    rw [← hn]
    calc Nat.card (sub2 a b)
        = Nat.card {x // x ∈ ((oneK :: R.map (·.1)).map ofCode).toFinset} :=
          Nat.card_congr (Equiv.subtypeEquivRight hiff)
      _ = ((oneK :: R.map (·.1)).map ofCode).toFinset.card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ = R.length + 1 := by
          rw [List.toFinset_card_of_nodup hnd', List.length_map, List.length_cons,
            List.length_map]

theorem orbK_sound {n₁ n₁' n₂ n₂' H : ℕ} {X T : List ℕ} {R : List (ℕ × ℕ × ℕ)}
    (h : orbK n₁ n₁' n₂ n₂' H X T R 0 = true) (h1 : Good n₁) (h1' : Good n₁') (h2 : Good n₂)
    (h2' : Good n₂') (hi1 : mulK n₁ n₁' = oneK) (hi2 : mulK n₂ n₂' = oneK)
    (hX : ∀ x ∈ X, Good x) {t : ℕ} (ht : t ∈ T) :
    bitK H t = true ∨ ∃ x ∈ X, ∃ n ∈ sub2 n₁ n₂, ofCode t = n * ofCode x * n⁻¹ := by
  suffices ∀ (R : List (ℕ × ℕ × ℕ)) (A : ℕ), orbK n₁ n₁' n₂ n₂' H X T R A = true →
      (∀ c, bitK A c = true → Good c ∧ ∃ x ∈ X, ∃ n ∈ sub2 n₁ n₂,
        ofCode c = n * ofCode x * n⁻¹) →
      bitK H t = true ∨ ∃ x ∈ X, ∃ n ∈ sub2 n₁ n₂, ofCode t = n * ofCode x * n⁻¹ from
    this R 0 h fun c hc => absurd hc (by simp [bitK])
  intro R
  induction R with
  | nil =>
    intro A hA hQ
    change allK (fun t => bitK H t || bitK A t) T = true at hA
    have := (allK_iff _ T).1 hA t ht
    rw [Bool.or_eq_true] at this
    rcases this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (hQ t h1).2
  | cons r R ih =>
    intro A hA hQ
    change ((r.2.2 == 2 && elemK r.1 X || bitK A r.2.1 && r.1 == cnjK n₁ n₁' n₂ n₂' r.2.2 r.2.1) &&
      orbK n₁ n₁' n₂ n₂' H X T R (A ||| 2 ^ r.1)) = true at hA
    rw [Bool.and_eq_true] at hA
    obtain ⟨hA1, hA2⟩ := hA
    have hr : Good r.1 ∧ ∃ x ∈ X, ∃ n ∈ sub2 n₁ n₂, ofCode r.1 = n * ofCode x * n⁻¹ := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, elemK_iff] at hA1
      rcases hA1 with ⟨-, hx⟩ | ⟨hp, he⟩
      · exact ⟨hX _ hx, r.1, hx, 1, (sub2 n₁ n₂).one_mem, by simp⟩
      · obtain ⟨hg, x, hx, m, hm, e⟩ := hQ _ hp
        have hn1 : ofCode n₁ ∈ sub2 n₁ n₂ := Subgroup.subset_closure (by simp)
        have hn2 : ofCode n₂ ∈ sub2 n₁ n₂ := Subgroup.subset_closure (by simp)
        rw [he]
        unfold cnjK
        split_ifs
        · refine ⟨good_conjK h1 h1' hg, x, hx, ofCode n₁ * m, (sub2 n₁ n₂).mul_mem hn1 hm, ?_⟩
          rw [ofCode_conjK h1 h1' hg hi1, e]
          group
        · refine ⟨good_conjK h2 h2' hg, x, hx, ofCode n₂ * m, (sub2 n₁ n₂).mul_mem hn2 hm, ?_⟩
          rw [ofCode_conjK h2 h2' hg hi2, e]
          group
    refine ih _ hA2 fun c hc => ?_
    rcases (bitK_two_pow_or A r.1 c).1 hc with hc | rfl
    · exact hQ c hc
    · exact hr

theorem keysK_sound {v₁ v₂ v₃ k : ℕ} {R : List (ℕ × ℕ)} (h : keysK v₁ v₂ v₃ R k = true) :
    (∀ r ∈ R, mulK r.1 r.2 = oneK) ∧
      R.Pairwise (fun r s => keyK v₁ v₂ v₃ r.1 r.2 ≠ keyK v₁ v₂ v₃ s.1 s.2) := by
  suffices ∀ k, keysK v₁ v₂ v₃ R k = true → (∀ r ∈ R, mulK r.1 r.2 = oneK) ∧
      (∀ r ∈ R, k < keyK v₁ v₂ v₃ r.1 r.2) ∧
      R.Pairwise (fun r s => keyK v₁ v₂ v₃ r.1 r.2 ≠ keyK v₁ v₂ v₃ s.1 s.2) from
    ⟨(this k h).1, (this k h).2.2⟩
  clear h k
  induction R with
  | nil => simp
  | cons r R ih =>
    intro k hk
    change (mulK r.1 r.2 == oneK && decide (k < keyK v₁ v₂ v₃ r.1 r.2) &&
      keysK v₁ v₂ v₃ R (keyK v₁ v₂ v₃ r.1 r.2)) = true at hk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    obtain ⟨i1, i2, i3⟩ := ih _ h3
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact h1
      · exact i1 s hs
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact h2
      · exact h2.trans (i2 s hs)
    · exact List.Pairwise.cons (fun s hs => (i2 s hs).ne) i3

end CFSG.KC.GL33K

end
