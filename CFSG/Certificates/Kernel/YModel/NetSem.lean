module

public import CFSG.Certificates.Kernel.BenesSound
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.KDense.SortSound

public section

namespace CFSG.KC.YModel.Sem

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem shl1 (k : Nat) : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k

theorem wid_eq (k : Nat) : wid k = 2 ^ k := shl1 k

theorem andB_eq {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem testBit_planes {S : Nat} (P : Nat → Nat) : ∀ n, (∀ b < n, P b < 2 ^ S) →
    (∀ u < n, ∀ r < S, (Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Nat.lor acc (Nat.shiftLeft (P b) (Nat.mul b S))) n).testBit (S * u + r) =
        (P u).testBit r) ∧
    Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Nat.lor acc (Nat.shiftLeft (P b) (Nat.mul b S))) n < 2 ^ (S * n)
  | 0, _ => ⟨fun u hu => absurd hu (Nat.not_lt_zero u), by simp⟩
  | n + 1, hP => by
    obtain ⟨ih1, ih2⟩ := testBit_planes P n fun b hb => hP b (by omega)
    have hPn := hP n (by omega)
    change (∀ u < n + 1, ∀ r < S, (Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Nat.lor acc (Nat.shiftLeft (P b) (Nat.mul b S))) n ||| (P n <<< (n * S))).testBit
        (S * u + r) = (P u).testBit r) ∧ (Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Nat.lor acc (Nat.shiftLeft (P b) (Nat.mul b S))) n ||| (P n <<< (n * S))) <
        2 ^ (S * (n + 1))
    generalize Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Nat.lor acc (Nat.shiftLeft (P b) (Nat.mul b S))) n = A at ih1 ih2
    refine ⟨fun u hu r hr => ?_, ?_⟩
    · rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · have : ¬ S * u + r ≥ n * S := by
          have : S * u + S ≤ S * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hu
          rw [Nat.mul_comm n S]
          omega
        rw [ih1 u hu r hr, decide_eq_false this, Bool.false_and, Bool.or_false]
      · rw [Nat.testBit_lt_two_pow (lt_two_pow_mono ih2 (by omega)), Bool.false_or,
          decide_eq_true (by rw [Nat.mul_comm u S]; omega)]
        rw [show S * u + r - u * S = r by rw [Nat.mul_comm u S]; omega, Bool.true_and]
    · apply Nat.or_lt_two_pow (lt_two_pow_mono ih2 (by rw [Nat.mul_succ]; omega))
      rw [Nat.shiftLeft_eq, Nat.mul_succ, Nat.pow_add, Nat.mul_comm n S, Nat.mul_comm (P n)]
      exact Nat.mul_lt_mul_of_pos_left hPn (Nat.two_pow_pos _)

theorem idPlane_lt {k b : Nat} (hb : b < k) : idPlane (2 ^ k) b < 2 ^ 2 ^ k :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [idPlane_testBit hb, decide_eq_false (by omega), Bool.false_and]

theorem idP_eq (k : Nat) : idP k = Nat.rec (motive := fun _ => Nat) 0
    (fun b acc => Nat.lor acc (Nat.shiftLeft (idPlane (2 ^ k) b) (Nat.mul b (2 ^ k)))) k := by
  unfold idP
  rw [shl1]

theorem testBit_idP {k u r : Nat} (hu : u < k) (hr : r < 2 ^ k) :
    (idP k).testBit (2 ^ k * u + r) = r.testBit u := by
  rw [idP_eq, (testBit_planes (S := 2 ^ k) (fun b => idPlane (2 ^ k) b) k
    (fun b hb => idPlane_lt hb)).1 u hu r hr, idPlane_testBit hu, decide_eq_true hr, Bool.true_and]

theorem eq_of_bits {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (h : ∀ u < k, a.testBit u = b.testBit u) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro u
  by_cases hu : u < k
  · exact h u hu
  · rw [Nat.testBit_lt_two_pow (lt_two_pow_mono ha (by omega)),
      Nat.testBit_lt_two_pow (lt_two_pow_mono hb (by omega))]

@[expose] def Acts (k P : Nat) (f : Nat → Nat) (F : Nat → Nat) : Prop :=
  (∀ r < 2 ^ k, f r < 2 ^ k) ∧
    ∀ X, ∀ u < P, ∀ r < 2 ^ k, (F X).testBit (2 ^ k * u + r) = X.testBit (2 ^ k * u + f r)

theorem acts_id (k P : Nat) : Acts k P (fun r => r) (fun X => X) :=
  ⟨fun _ h => h, fun _ _ _ _ _ => rfl⟩

theorem Acts.comp {k P : Nat} {f g F G : Nat → Nat} (hF : Acts k P f F) (hG : Acts k P g G) :
    Acts k P (fun r => f (g r)) (fun X => G (F X)) :=
  ⟨fun r hr => hF.1 _ (hG.1 r hr), fun X u hu r hr => by
    rw [hG.2 (F X) u hu r hr, hF.2 X u hu _ (hG.1 r hr)]⟩

theorem Acts.congr {k P : Nat} {f g F : Nat → Nat} (hF : Acts k P f F)
    (h : ∀ r < 2 ^ k, f r = g r) : Acts k P g F :=
  ⟨fun r hr => h r hr ▸ hF.1 r hr, fun X u hu r hr => by rw [hF.2 X u hu r hr, h r hr]⟩

theorem acts_netApply {k P N : Nat} (h : StagesValid k N) :
    Acts k P (benesPerm k N) (netApply k (2 ^ k) (repU (2 ^ k) P) N) :=
  ⟨fun _ hr => benesPerm_lt h hr, fun X => (testBit_netApply rfl h X).1⟩

@[expose] noncomputable def compN (k : Nat) : List Nat → Nat → Nat
  | [] => fun r => r
  | N :: Ns => fun r => benesPerm k N (compN k Ns r)

theorem netsApply_cons (k W U N : Nat) (Ns : List Nat) (X : Nat) :
    netsApply k W U (N :: Ns) X = netsApply k W U Ns (netApply k W U N X) :=
  Benes.strictN_eq _ _

theorem acts_netsApply {k P : Nat} : ∀ Ns : List Nat, (∀ N ∈ Ns, StagesValid k N) →
    Acts k P (compN k Ns) (netsApply k (2 ^ k) (repU (2 ^ k) P) Ns)
  | [], _ => acts_id k P
  | N :: Ns, h => by
    have h1 := acts_netApply (P := P) (h N List.mem_cons_self)
    have h2 := acts_netsApply (P := P) Ns fun N' hN' => h N' (List.mem_cons_of_mem _ hN')
    have := h1.comp h2
    refine ⟨this.1, fun X u hu r hr => ?_⟩
    rw [netsApply_cons]
    exact this.2 X u hu r hr

@[expose] noncomputable def wF (k m : Nat) (Nf : Nat → Nat) : List Nat → Nat → Nat
  | [] => fun r => r
  | c :: w => fun r => if c < m then benesPerm k (Nf c) (wF k m Nf w r) else wF k m Nf w r

theorem wordAp_cons (k m : Nat) (Nf : Nat → Nat) (c : Nat) (w : List Nat) (X : Nat) :
    wordAp k m Nf (c :: w) X = wordAp k m Nf w (if c < m then apK k (Nf c) X else X) := by
  change strictN (Bool.rec (motive := fun _ => Nat) X (apK k (Nf c) X) (Nat.blt c m))
    (wordAp k m Nf w) = _
  rw [Benes.strictN_eq]
  cases hb : Nat.blt c m
  · have : ¬ c < m := fun h => by rw [← Nat.blt_eq] at h; rw [h] at hb; exact absurd hb (by decide)
    rw [if_neg this]
  · rw [if_pos (Nat.blt_eq.mp hb)]

theorem acts_wordAp {k m : Nat} {Nf : Nat → Nat} (hv : ∀ c < m, StagesValid k (Nf c)) :
    ∀ w : List Nat, Acts k k (wF k m Nf w) (wordAp k m Nf w)
  | [] => acts_id k k
  | c :: w => by
    have ih := acts_wordAp hv w
    by_cases hc : c < m
    · have h1 : Acts k k (benesPerm k (Nf c)) (apK k (Nf c)) := by
        have := acts_netApply (P := k) (hv c hc)
        unfold apK
        rw [wid_eq]
        exact this
      have := h1.comp ih
      refine ⟨fun r hr => ?_, fun X u hu r hr => ?_⟩
      · change (if c < m then _ else _) < _
        rw [if_pos hc]
        exact this.1 r hr
      · rw [wordAp_cons, if_pos hc]
        change _ = X.testBit (2 ^ k * u + if c < m then _ else _)
        rw [if_pos hc]
        exact this.2 X u hu r hr
    · refine ⟨fun r hr => ?_, fun X u hu r hr => ?_⟩
      · change (if c < m then _ else _) < _
        rw [if_neg hc]
        exact ih.1 r hr
      · rw [wordAp_cons, if_neg hc]
        change _ = X.testBit (2 ^ k * u + if c < m then _ else _)
        rw [if_neg hc]
        exact ih.2 X u hu r hr

theorem wF_zero {k : Nat} {Nf : Nat → Nat} : ∀ (w : List Nat) (i : Nat), wF k 0 Nf w i = i
  | [], _ => rfl
  | c :: w, i => by
    change (if c < 0 then _ else wF k 0 Nf w i) = i
    rw [if_neg (Nat.not_lt_zero c), wF_zero w i]

theorem eq_of_idP {k : Nat} {f g F G : Nat → Nat} (hF : Acts k k f F) (hG : Acts k k g G)
    (h : F (idP k) = G (idP k)) : ∀ r < 2 ^ k, f r = g r := by
  intro r hr
  apply eq_of_bits (hF.1 r hr) (hG.1 r hr)
  intro u hu
  rw [← testBit_idP hu (hF.1 r hr), ← testBit_idP hu (hG.1 r hr), ← hF.2 _ u hu r hr,
    ← hG.2 _ u hu r hr, h]

theorem eq_of_point {k b x : Nat} {f F : Nat → Nat} (hF : Acts k 1 f F) (hb : b < 2 ^ k)
    (h : F (Nat.shiftLeft 1 x) = Nat.shiftLeft 1 b) : f b = x := by
  have e := hF.2 (Nat.shiftLeft 1 x) 0 (by decide) b hb
  rw [h, Nat.mul_zero, Nat.zero_add, Nat.zero_add, shl1, shl1, Nat.testBit_two_pow,
    Nat.testBit_two_pow] at e
  exact (by simpa using e : x = f b).symm

theorem repU_one' (k : Nat) : (1 : Nat) = repU (2 ^ k) 1 := (repU_one (Nat.two_pow_pos k)).symm

theorem fieldAt_eq' (w X i : Nat) : fieldAt w X i = (X >>> (w * i)) % 2 ^ w := by
  change (X >>> (w * i)) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

theorem testBit_fieldAt {w X i j : Nat} :
    (fieldAt w X i).testBit j = (decide (j < w) && X.testBit (w * i + j)) := by
  rw [fieldAt_eq', Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem testBit_hiMask {k j : Nat} (hk : k ≤ 32) (h1 : k ≤ j) (h2 : j < 32) :
    (2 ^ 32 - 1 - (2 ^ k - 1)).testBit j = true := by
  have e : 2 ^ 32 - 1 - (2 ^ k - 1) = 2 ^ k * (2 ^ (32 - k) - 1) := by
    have h3 : 2 ^ k * 2 ^ (32 - k) = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
    have h4 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h5 : 2 ^ k ≤ 2 ^ k * 2 ^ (32 - k) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    rw [Nat.mul_sub_one]
    omega
  rw [e, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  omega

theorem rawPlane_n {RAW rec n h b : Nat} (hrec : 0 < rec) (hR : RAW < 2 ^ (rec * n))
    (hn : n ≤ 2 ^ h) : rawPlane RAW rec n h 0 b = rawPlane RAW rec (2 ^ h) h 0 b := by
  rw [KDense.SortAux.rawPlane_eq, KDense.SortAux.rawPlane_eq]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro q
  have hd : ∀ N, (Nat.div (ones (Nat.mul rec N)) (ones rec)).testBit q =
      (decide (q < rec * N) && (1 : Nat).testBit (q % rec)) := by
    intro N
    rw [ndiv, ones_eq, ones_eq, nmul, ← Nat.one_mul ((2 ^ (rec * N) - 1) / (2 ^ rec - 1))]
    exact testBit_mul_div hrec rfl (Nat.one_lt_two_pow (by omega)) q
  simp only [nland, Nat.testBit_and, hd]
  by_cases h1 : q < rec * n
  · rw [decide_eq_true h1, decide_eq_true
      (Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ hn))]
  · rw [decide_eq_false h1, Bool.false_and, Bool.and_false]
    rw [nshr, Nat.testBit_shiftRight, Nat.testBit_lt_two_pow (lt_two_pow_mono hR (by simp; omega)),
      Bool.false_and]

theorem rawPlane_lt' {RAW n k b : Nat} (hR : RAW < 2 ^ (32 * n)) (hn : n ≤ 2 ^ k) :
    rawPlane RAW 32 n k 0 b < 2 ^ 2 ^ k := by
  rw [rawPlane_n (by decide) hR hn]
  exact KDense.SortAux.rawPlane_lt (by decide) rfl

theorem testBit_rawPlane' {RAW n k b q : Nat} (hR : RAW < 2 ^ (32 * n)) (hn : n ≤ 2 ^ k) :
    (rawPlane RAW 32 n k 0 b).testBit q = (decide (q < 2 ^ k) && RAW.testBit (32 * q + b)) := by
  rw [rawPlane_n (by decide) hR hn]
  exact KDense.SortAux.testBit_rawPlane (by decide) rfl q

theorem letOK_spec {k n F N : Nat} (hk : k ≤ 32) (h : letOK k n F N = true) :
    n ≤ 2 ^ k ∧ StagesValid k N ∧ (∀ i < n, fieldAt 32 F i = benesPerm k N i) ∧
      ∀ i, n ≤ i → i < 2 ^ k → benesPerm k N i = i := by
  obtain ⟨h1, h2⟩ := andB_eq h
  obtain ⟨h2, h3⟩ := andB_eq h2
  obtain ⟨h3, h4⟩ := andB_eq h3
  have hn : n ≤ 2 ^ k := by rw [← wid_eq]; exact Nat.le_of_ble_eq_true h1
  have hv := stagesValid_of_ymodel h2
  obtain ⟨-, h3⟩ := andB_eq h3
  obtain ⟨h5, h6⟩ := andB_eq h3
  have hR : F < 2 ^ (32 * n) := by
    have := Nat.le_of_ble_eq_true h5
    rw [nmul, shl1] at this
    exact this
  have hhi : ∀ p < n, ∀ j, k ≤ j → j < 32 → F.testBit (32 * p + j) = false := by
    intro p hp j hj1 hj2
    have e := congrArg (fun x => x.testBit (32 * p + j)) (Nat.eq_of_beq_eq_true h6)
    have hM : (Nat.mul (Nat.div (ones (Nat.mul 32 n)) (ones 32)) (Nat.sub (ones 32) (ones k))).testBit
        (32 * p + j) = true := by
      rw [nmul, ndiv, nsub, nmul, ones_eq, ones_eq, ones_eq, Nat.mul_comm,
        testBit_mul_div (by decide) rfl (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
          (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)),
        decide_eq_true (by omega), Bool.true_and,
        show (32 * p + j) % 32 = j by omega, testBit_hiMask hk hj1 hj2]
    simp only [Nat.zero_testBit] at e
    rw [nland, Nat.testBit_and, hM, Bool.and_true] at e
    exact e
  have hcol := Nat.eq_of_beq_eq_true h4
  rw [shl1] at hcol
  have hP : ∀ b < k, Nat.lor (rawPlane F 32 n k 0 b) (Nat.land (idPlane (2 ^ k) b)
      (Nat.xor (ones (2 ^ k)) (ones n))) < 2 ^ 2 ^ k := fun b hb =>
    Nat.or_lt_two_pow (rawPlane_lt' hR hn) (Nat.lt_of_le_of_lt Nat.and_le_left (idPlane_lt hb))
  have key : ∀ u < k, ∀ r < 2 ^ k, (benesPerm k N r).testBit u =
      ((decide (r < n) && F.testBit (32 * r + u)) || (decide (n ≤ r) && r.testBit u)) := by
    intro u hu r hr
    have e := congrArg (fun x => x.testBit (2 ^ k * u + r)) hcol
    simp only at e
    rw [(testBit_netApply rfl hv (idP k)).1 u hu r hr, testBit_idP hu (benesPerm_lt hv hr)] at e
    rw [e]
    unfold colPlanes
    rw [shl1, (testBit_planes (S := 2 ^ k) _ k hP).1 u hu r hr, nlor, Nat.testBit_or,
      testBit_rawPlane' hR hn, nland, Nat.testBit_and, idPlane_testBit hu, nxor, Nat.testBit_xor,
      KDense.SortAux.testBit_ones, KDense.SortAux.testBit_ones, decide_eq_true hr]
    by_cases hrn : r < n
    · simp [hrn, show ¬ n ≤ r by omega]
    · rw [Nat.testBit_lt_two_pow (lt_two_pow_mono hR (by omega))]
      simp [hrn, show n ≤ r by omega]
  have hfix : ∀ i, n ≤ i → i < 2 ^ k → benesPerm k N i = i := by
    intro i h1 h2
    apply eq_of_bits (benesPerm_lt hv h2) h2
    intro u hu
    rw [key u hu i h2]
    simp [show ¬ i < n by omega, h1]
  refine ⟨hn, hv, fun i hi => ?_, hfix⟩
  have hi' : i < 2 ^ k := by omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_fieldAt]
  by_cases hj : j < k
  · rw [key j hj i hi']
    simp [hi, show j < 32 by omega]
  · rw [Nat.testBit_lt_two_pow (lt_two_pow_mono (benesPerm_lt hv hi') (by omega))]
    by_cases hj2 : j < 32
    · rw [decide_eq_true hj2, Bool.true_and, hhi i hi j (by omega) hj2]
    · rw [decide_eq_false hj2, Bool.false_and]

theorem perm_lt {k n N : Nat} (hn : n ≤ 2 ^ k) (hv : StagesValid k N)
    (hfix : ∀ i, n ≤ i → i < 2 ^ k → benesPerm k N i = i) {i : Nat} (hi : i < n) :
    benesPerm k N i < n := by
  by_contra hc
  have hlt := benesPerm_lt hv (show i < 2 ^ k by omega)
  have e := hfix _ (by omega) hlt
  have := congrArg (benesInv k N) e
  rw [benesInv_benesPerm hv, benesInv_benesPerm hv] at this
  omega

theorem invCand_eq_foldl (n : Nat) (t : Array Nat) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand {n : Nat} {t : Array Nat} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem isInvA_invCand {n : Nat} {t : Array Nat} (hlt : ∀ i < n, t[i]! < n)
    (hinj : ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j) : isInvA n t (invCand n t) = true := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j := ⟨hlt, hinj⟩
  have ht : Rep n t (permOfArr n t) := fun x => by
    rw [permOfArr, dite_eq_left hc]
    rfl
  have hr := rep_invCand ht
  rw [isInvA, allLt_iff]
  intro i hi
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨hlt i hi, ?_⟩
  rw [ht.apply hi, hr.apply (permOfArr n t ⟨i, hi⟩).2]
  simp

end CFSG.KC.YModel.Sem

end
