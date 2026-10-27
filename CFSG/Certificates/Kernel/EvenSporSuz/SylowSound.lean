module

public import Certificates.Data.Kernel.EvenSporSuz.Sylow
public import CFSG.Certificates.Kernel.Misc.Spec.F3Lanes

public section

namespace CFSG.KC.EvenSporSuz.Syl

open CFSG.KC.ONanSmall CFSG.KC.M24G CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec

theorem findK_mem {k v : Nat} : ∀ {t : KTree (Nat × Nat)}, findK k t = some v → (k, v) ∈ t.toList
  | .leaf, h => by simp [findK] at h
  | .node l x r, h => by
    unfold findK at h
    simp only [KTree.toList, List.mem_append, List.mem_cons]
    split at h
    · cases h
      rename_i hk
      exact Or.inr (Or.inl (by rw [hk]))
    · split at h
      · exact Or.inl (findK_mem h)
      · exact Or.inr (Or.inr (findK_mem h))

theorem bal_toList {α : Type} : ∀ (d n : Nat) (L : List α),
    (bal d n L).1.toList ++ (bal d n L).2 = L
  | 0, _, L => by simp [bal, KTree.toList]
  | _ + 1, 0, L => by simp [bal, KTree.toList]
  | d + 1, n + 1, L => by
    have h1 := bal_toList d (n / 2) L
    rcases hb : bal d (n / 2) L with ⟨l, _ | ⟨x, L'⟩⟩
    · rw [hb] at h1
      simp only [bal, hb]
      simpa using h1
    · rw [hb] at h1
      have h2 := bal_toList d (n - n / 2) L'
      rcases hb2 : bal d (n - n / 2) L' with ⟨r, R⟩
      rw [hb2] at h2
      simp only [bal, hb, hb2, KTree.toList, List.append_assoc, List.cons_append]
      simp only at h1 h2
      rw [h2]
      exact h1

theorem mem_of_treeOf {L : List (Nat × Nat)} {p : Nat × Nat} (h : p ∈ (treeOf L).toList) :
    p ∈ L := by
  have := bal_toList 20 L.length L
  rw [← this]
  exact List.mem_append_left _ h

theorem findK_treeOf {L : List (Nat × Nat)} {k v : Nat} (h : findK k (treeOf L) = some v) :
    (k, v) ∈ L :=
  mem_of_treeOf (findK_mem h)

theorem isSome_findK_treeOf {L : List (Nat × Nat)} {k : Nat} (h : (findK k (treeOf L)).isSome) :
    ∃ v, (k, v) ∈ L := by
  rcases hf : findK k (treeOf L) with _ | v
  · rw [hf] at h
    cases h
  · exact ⟨v, findK_treeOf hf⟩

theorem canon3_of_canonK {X : Nat} (h : canonK X = true) : Canon3 X := by
  simp only [canonK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hl : ∀ t < 144, (fun _ => 1 * 252) t < 256 := fun _ _ => by norm_num
  have hl1 : ∀ t < 144, (fun _ => 1) t < 256 := fun _ _ => by norm_num
  have hb2 : ∀ t < 144, ∀ b, 2 ≤ b → b < 8 → X.testBit (8 * t + b) = false := by
    intro t ht b hb1 hb2
    have h := congrArg (fun y => Nat.testBit y (8 * t + b)) h2
    simp only [Nat.zero_testBit] at h
    change (X &&& laneOnes * 252).testBit (8 * t + b) = false at h
    rw [Nat.testBit_and, laneOnes_eq, lanes_mul, testBit_lanes hl t b hb2] at h
    have h252 : (1 * 252 : Nat).testBit b = true := by interval_cases b <;> decide
    simpa [ht, h252] using h
  have hb01 : ∀ t < 144, X.testBit (8 * t) = true → X.testBit (8 * t + 1) = true → False := by
    intro t ht ha hb
    have h := congrArg (fun y => Nat.testBit y (8 * t + 0)) h3
    simp only [Nat.zero_testBit] at h
    change ((X &&& X >>> 1) &&& laneOnes).testBit (8 * t + 0) = false at h
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, laneOnes_eq,
      testBit_lanes hl1 t 0 (by norm_num)] at h
    rw [show 1 + (8 * t + 0) = 8 * t + 1 by omega, Nat.add_zero] at h
    simp [ht, ha, hb] at h
  refine ⟨?_, fun t ht => ?_⟩
  · change X >>> 1152 = 0 at h1
    rw [Nat.shiftRight_eq_div_pow] at h1
    by_contra hc
    have := Nat.div_pos (Nat.le_of_not_lt hc) (by positivity)
    omega
  · have hv : ∀ i, (lane8 X t).testBit i = (decide (i < 8) && X.testBit (8 * t + i)) := by
      intro i
      unfold lane8
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i]
    have h4 : lane8 X t < 2 ^ 2 := Nat.lt_pow_two_of_testBit _ fun i hi => by
      rw [hv]
      by_cases h8 : i < 8
      · simp [h8, hb2 t ht i hi h8]
      · simp [h8]
    by_contra hge
    have h3' : lane8 X t = 3 := by omega
    have e0 := hv 0
    have e1 := hv 1
    rw [h3'] at e0 e1
    have t0 : (3 : Nat).testBit 0 = true := by decide
    have t1 : (3 : Nat).testBit 1 = true := by decide
    rw [t0, Nat.add_zero] at e0
    rw [t1] at e1
    exact hb01 t ht (by simpa using e0.symm) (by simpa using e1.symm)

theorem pairwise_of_incK : ∀ {L : List (Nat × Nat)}, incK L = true →
    (L.map Prod.fst).Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | a :: b :: L, h => by
    simp only [incK, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := pairwise_of_incK h.2
    have ih' : ∀ y ∈ L.map Prod.fst, b.1 < y := by
      simp only [List.map_cons, List.pairwise_cons] at ih
      exact ih.1
    rw [List.map_cons]
    refine List.Pairwise.cons ?_ ih
    intro y hy
    rw [List.map_cons, List.mem_cons] at hy
    rcases hy with hy | hy
    · omega
    · have := ih' y hy
      omega

theorem nodup_of_incK {L : List (Nat × Nat)} (h : incK L = true) : (L.map Prod.fst).Nodup :=
  (pairwise_of_incK h).imp (fun h => Nat.ne_of_lt h)

theorem letQ_eq (y : Nat) (k : Nat → Bool) : letQ y k = k y := by cases y <;> rfl

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem ind_eq (a b : Nat) : ind a b = if a = b then 1 else 0 := by
  unfold ind
  by_cases h : a = b
  · subst h
    simp [Nat.beq_refl]
  · simp [h, beq_false h]

noncomputable abbrev sqN (L : List (Nat × Nat)) (x : Nat) : Nat := L.countP fun p => decide (mulF3 p.1 p.1 = x)

theorem cnt_step {P : Prop} [Decidable P] {a n : Nat} (ha : (if P then 1 else 0) ≤ a)
    (hn : n = a - (if P then 1 else 0)) : n + (if decide P = true then 1 else 0) = a := by
  by_cases hP : P
  · simp only [hP, ↓reduceIte, decide_true] at ha hn ⊢
    omega
  · simp only [hP, ↓reduceIte, decide_false, Bool.false_eq_true] at ha hn ⊢
    omega

theorem chunkGo_sound {T OT : KTree (Nat × Nat)} {G GI : List Nat} {z x1 x2 : Nat} :
    ∀ {L : List (Nat × Nat)} {a b c : Nat}, chunkGo T OT G GI z x1 x2 L a b c = true →
      (∀ p ∈ L, elemK T OT G GI z p.1 p.2 (mulF3 p.1 p.1) = true) ∧ sqN L z = a ∧
        sqN L x1 = b ∧ sqN L x2 = c
  | [], a, b, c, h => by
    simp only [chunkGo, Bool.and_eq_true, Nat.beq_eq] at h
    simp [h.1.1, h.1.2, h.2]
  | p :: L, a, b, c, h => by
    simp only [chunkGo, letQ_eq, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨he, hL⟩, ha⟩, hb⟩, hc⟩ := h
    obtain ⟨h1, h2, h3, h4⟩ := chunkGo_sound hL
    rw [ind_eq] at ha hb hc h2 h3 h4
    refine ⟨fun q hq => ?_, ?_, ?_, ?_⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact he
      · exact h1 q hq
    · simp only [sqN] at h2 ⊢
      rw [List.countP_cons]
      exact cnt_step ha h2
    · simp only [sqN] at h3 ⊢
      rw [List.countP_cons]
      exact cnt_step hb h3
    · simp only [sqN] at h4 ⊢
      rw [List.countP_cons]
      exact cnt_step hc h4

theorem slice_zero {α : Type} (L : List α) : slice L 0 = L.take 1024 := by simp [slice]

theorem slice_succ {α : Type} (L : List α) (c : Nat) :
    slice L (c + 1) = slice (L.drop 1024) c := by
  simp only [slice]
  rw [List.drop_drop]
  congr 2
  omega

theorem countP_slices {α : Type} (P : α → Bool) : ∀ (n : Nat) (L : List α), L.length ≤ 1024 * n →
    L.countP P = ∑ c ∈ Finset.range n, (slice L c).countP P
  | 0, L, h => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [this]
  | n + 1, L, h => by
    rw [Finset.sum_range_succ']
    simp only [slice_succ, slice_zero]
    rw [← countP_slices P n (L.drop 1024) (by simp only [List.length_drop]; omega)]
    conv_lhs => rw [← List.take_append_drop 1024 L]
    rw [List.countP_append, add_comm]

theorem mem_slices {α : Type} {p : α} : ∀ (n : Nat) (L : List α), L.length ≤ 1024 * n → p ∈ L →
    ∃ c < n, p ∈ slice L c
  | 0, L, h, hp => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [this] at hp
  | n + 1, L, h, hp => by
    rw [← List.take_append_drop 1024 L, List.mem_append] at hp
    rcases hp with hp | hp
    · exact ⟨0, by omega, by rwa [slice_zero]⟩
    · obtain ⟨c, hc, h'⟩ := mem_slices n (L.drop 1024) (by simp only [List.length_drop]; omega) hp
      exact ⟨c + 1, by omega, by rwa [slice_succ]⟩

theorem sum_getD (l : List Nat) : ∑ c ∈ Finset.range l.length, l.getD c 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ← ih]
    simp [add_comm]

abbrev monG (G : List Nat) : Submonoid (Matrix (Fin 12) (Fin 12) (ZMod 3)) :=
  Submonoid.closure (Set.range fun k : Fin 4 => pkMat3 (G.getD k 0))

theorem gen_mem {G : List Nat} {k : Nat} (hk : k < 4) : pkMat3 (G.getD k 0) ∈ monG G :=
  Submonoid.subset_closure ⟨⟨k, hk⟩, rfl⟩

def GensOK (G GI : List Nat) : Prop :=
  ∀ k < 4, Canon3 (G.getD k 0) ∧ Canon3 (GI.getD k 0) ∧
    pkMat3 (G.getD k 0) * pkMat3 (GI.getD k 0) = 1

theorem mem_monG {T : KTree (Nat × Nat)} {OT : KTree (Nat × Nat)} {G GI : List Nat} {z : Nat}
    {ED : List (Nat × Nat)} (hT : T = treeOf ED) (hG : GensOK G GI)
    (hall : ∀ p ∈ ED, elemK T OT G GI z p.1 p.2 (mulF3 p.1 p.1) = true) :
    ∀ d, ∀ p ∈ ED, p.2 / 4 = d → Canon3 p.1 ∧ pkMat3 p.1 ∈ monG G := by
  intro d
  induction d with
  | zero =>
    intro p hp hd
    have h := hall p hp
    simp only [elemK, Bool.and_eq_true, hd, Nat.beq_refl, cond_true, Nat.beq_eq] at h
    refine ⟨canon3_of_canonK h.1.1.1, ?_⟩
    rw [h.1.2, canon3_one3.2]
    exact one_mem _
  | succ d ih =>
    intro p hp hd
    have h := hall p hp
    have hb : Nat.beq (p.2 / 4) 0 = false := by rw [hd]; rfl
    simp only [elemK, Bool.and_eq_true, hb, cond_false] at h
    obtain ⟨⟨⟨hc, -⟩, hpar⟩, -⟩ := h
    have hce := canon3_of_canonK hc
    have hk : p.2 % 4 < 4 := Nat.mod_lt _ (by omega)
    obtain ⟨hg, hgi, hm⟩ := hG _ hk
    split at hpar
    · rename_i c hf
      rw [hT] at hf
      have hmem := findK_treeOf hf
      simp only [Nat.beq_eq] at hpar
      obtain ⟨-, hq⟩ := ih _ hmem (by simp only; omega)
      refine ⟨hce, ?_⟩
      have hmul := (canon3_mulF3 hce hgi).2
      have hm' : pkMat3 (GI.getD (p.2 % 4) 0) * pkMat3 (G.getD (p.2 % 4) 0) = 1 :=
        mul_eq_one_comm.1 hm
      have : pkMat3 p.1 = pkMat3 (mulF3 p.1 (GI.getD (p.2 % 4) 0)) * pkMat3 (G.getD (p.2 % 4) 0) := by
        rw [hmul, Matrix.mul_assoc, hm', Matrix.mul_one]
      rw [this]
      exact mul_mem hq (gen_mem hk)
    · cases hpar

theorem conj_monG {OT : KTree (Nat × Nat)} {G GI R : List Nat} {OD : List (Nat × Nat)}
    (hT : OT = treeOf OD) (hG : GensOK G GI)
    (hall : ∀ p ∈ OD, orbK OT G GI R p.1 p.2 = true) :
    ∀ d, ∀ p ∈ OD, p.2 / 4 % 64 = d → Canon3 p.1 ∧ p.2 / 256 < 14 ∧
      ∃ h ∈ monG G, pkMat3 p.1 * h = h * pkMat3 (R.getD (p.2 / 256) 0) := by
  intro d
  induction d with
  | zero =>
    intro p hp hd
    have h := hall p hp
    simp only [orbK, Bool.and_eq_true, hd, Nat.beq_refl, cond_true, Nat.beq_eq, Nat.blt_eq] at h
    refine ⟨canon3_of_canonK h.1.1, h.1.2, 1, one_mem _, ?_⟩
    rw [h.2, Matrix.mul_one, Matrix.one_mul]
  | succ d ih =>
    intro p hp hd
    have h := hall p hp
    have hb : Nat.beq (p.2 / 4 % 64) 0 = false := by rw [hd]; rfl
    simp only [orbK, Bool.and_eq_true, hb, cond_false, Nat.blt_eq] at h
    obtain ⟨⟨hc, hlt⟩, hpar⟩ := h
    have hcv := canon3_of_canonK hc
    have hk : p.2 % 4 < 4 := Nat.mod_lt _ (by omega)
    obtain ⟨hg, hgi, hm⟩ := hG _ hk
    split at hpar
    · rename_i c hf
      rw [hT] at hf
      have hmem := findK_treeOf hf
      simp only [Nat.beq_eq] at hpar
      obtain ⟨-, -, h', hh', he⟩ := ih _ hmem (by simp only; omega)
      have hkk : c / 256 = p.2 / 256 := by omega
      simp only at he
      rw [hkk] at he
      refine ⟨hcv, hlt, pkMat3 (G.getD (p.2 % 4) 0) * h', mul_mem (gen_mem hk) hh', ?_⟩
      have h1 := canon3_mulF3 hgi hcv
      rw [(canon3_mulF3 h1.1 hg).2, h1.2] at he
      have hm' : pkMat3 (GI.getD (p.2 % 4) 0) * pkMat3 (G.getD (p.2 % 4) 0) = 1 :=
        mul_eq_one_comm.1 hm
      calc pkMat3 p.1 * (pkMat3 (G.getD (p.2 % 4) 0) * h')
          = pkMat3 (G.getD (p.2 % 4) 0) * (pkMat3 (GI.getD (p.2 % 4) 0) * pkMat3 p.1 *
              pkMat3 (G.getD (p.2 % 4) 0) * h') := by
            simp only [← Matrix.mul_assoc, hm, Matrix.one_mul]
        _ = pkMat3 (G.getD (p.2 % 4) 0) * h' * pkMat3 (R.getD (p.2 / 256) 0) := by
            rw [he, Matrix.mul_assoc]
    · cases hpar

structure SylFacts (G GI : List Nat) (z x1 x2 : Nat) (R C TG : List Nat)
    (ED OD : List (Nat × Nat)) : Prop where
  gens : GensOK G GI
  len : ED.length = 16384
  nodup : (ED.map Prod.fst).Nodup
  one : ∃ p ∈ ED, p.1 = one3
  mem : ∀ p ∈ ED, Canon3 p.1 ∧ pkMat3 p.1 ∈ monG G
  closed : ∀ p ∈ ED, ∀ k < 4, ∃ v, (mulF3 p.1 (G.getD k 0), v) ∈ ED
  cz : sqN ED z = 1056
  c1 : sqN ED x1 = 384
  c2 : sqN ED x2 = 352
  cover : ∀ p ∈ ED, mulF3 p.1 p.1 = one3 → p.1 ≠ one3 → p.1 ≠ z →
    ∃ k < 14, ∃ h ∈ monG G, pkMat3 p.1 * h = h * pkMat3 (R.getD k 0)
  canon : Canon3 z ∧ Canon3 x1 ∧ Canon3 x2
  central : ∀ k < 4, mulF3 (G.getD k 0) x1 = mulF3 x1 (G.getD k 0) ∧
    mulF3 (G.getD k 0) x2 = mulF3 x2 (G.getD k 0) ∧ mulF3 (G.getD k 0) z = mulF3 z (G.getD k 0)
  zneg : z = 2 * one3
  x2eq : x2 = mulF3 z x1
  reps : ∀ k < 14, Canon3 (R.getD k 0) ∧ Canon3 (C.getD k 0) ∧
    (TG.getD k 0 = 1 ∨ TG.getD k 0 = 2) ∧
    mulF3 (R.getD k 0) (C.getD k 0) = mulF3 (C.getD k 0) (tgtL x1 x2 (TG.getD k 0))

theorem getD_mem_of_lt {l : List Nat} {k : Nat} (hk : k < l.length) : l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem syl_sound {G GI : List Nat} {z x1 x2 : Nat} {R C TG : List Nat}
    {ED OD : List (Nat × Nat)} {sz s1 s2 : List Nat}
    (hg : globK G GI z x1 x2 R C TG ED sz s1 s2 = true)
    (hc : ∀ c < 16, chunkK (treeOf ED) (treeOf OD) G GI z x1 x2 ED sz s1 s2 c = true)
    (ho : OD.all (fun p => orbK (treeOf OD) G GI R p.1 p.2) = true) :
    SylFacts G GI z x1 x2 R C TG ED OD := by
  simp only [globK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range,
    List.any_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hG4, hGI4⟩, hgens⟩, hz⟩, h1⟩, h2⟩, hcen⟩, hzn⟩, hx2⟩, hR⟩, hC⟩,
    hTG⟩, hreps⟩, hlen⟩, hinc⟩, hone⟩, hsz⟩, hs1⟩, hs2⟩, hsum⟩, hsum1⟩, hsum2⟩ := hg
  have hG : GensOK G GI := fun k hk => by
    obtain ⟨⟨a, b⟩, c⟩ := hgens k hk
    refine ⟨canon3_of_canonK a, canon3_of_canonK b, ?_⟩
    rw [← (canon3_mulF3 (canon3_of_canonK a) (canon3_of_canonK b)).2, c, canon3_one3.2]
  have hlen' : ED.length ≤ 1024 * 16 := by omega
  have hch := fun c (hc' : c < 16) => chunkGo_sound (hc c hc')
  have hall : ∀ p ∈ ED, elemK (treeOf ED) (treeOf OD) G GI z p.1 p.2 (mulF3 p.1 p.1) = true := by
    intro p hp
    obtain ⟨c, hc', hpc⟩ := mem_slices 16 ED hlen' hp
    exact (hch c hc').1 p hpc
  have hcnt : ∀ (x : Nat) (s : List Nat), s.length = 16 →
      (∀ c < 16, sqN (slice ED c) x = s.getD c 0) → sqN ED x = s.sum := by
    intro x s hs h
    rw [sqN, countP_slices _ 16 ED hlen', ← sum_getD, hs]
    exact Finset.sum_congr rfl fun c hc' => h c (Finset.mem_range.1 hc')
  have horb : ∀ p ∈ OD, orbK (treeOf OD) G GI R p.1 p.2 = true := by
    simpa only [List.all_eq_true] using ho
  have hO := conj_monG rfl hG horb
  refine ⟨hG, hlen, nodup_of_incK hinc, ?_, fun p hp => mem_monG rfl hG hall _ p hp rfl,
    ?_, ?_, ?_, ?_, ?_, ⟨canon3_of_canonK hz, canon3_of_canonK h1, canon3_of_canonK h2⟩, ?_, hzn,
    hx2, ?_⟩
  · obtain ⟨p, hp, he⟩ := hone
    exact ⟨p, hp, he⟩
  · intro p hp k hk
    have h := hall p hp
    simp only [elemK, Bool.and_eq_true, List.all_eq_true] at h
    exact isSome_findK_treeOf (h.1.1.2 _ (getD_mem_of_lt (by omega)))
  · rw [hcnt z sz hsz fun c hc' => (hch c hc').2.1, hsum]
  · rw [hcnt x1 s1 hs1 fun c hc' => (hch c hc').2.2.1, hsum1]
  · rw [hcnt x2 s2 hs2 fun c hc' => (hch c hc').2.2.2, hsum2]
  · intro p hp hsq hne1 hnez
    have h := hall p hp
    simp only [elemK, Bool.and_eq_true] at h
    have hcov := h.2
    simp only [hsq, Nat.beq_refl, beq_false hne1, beq_false hnez,
      Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or] at hcov
    obtain ⟨v, hv⟩ := isSome_findK_treeOf hcov
    obtain ⟨-, hk, h', hh', he⟩ := hO _ _ hv rfl
    exact ⟨_, hk, h', hh', he⟩
  · intro k hk
    have h := hcen _ (getD_mem_of_lt (by omega : k < G.length))
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro k hk
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hreps k hk
    refine ⟨canon3_of_canonK a, canon3_of_canonK b, ?_, d⟩
    simpa only [Bool.or_eq_true, Nat.beq_eq] using c

end CFSG.KC.EvenSporSuz.Syl
