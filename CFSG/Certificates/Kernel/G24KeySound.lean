module

public import Certificates.Data.Kernel.G24Key
public import Certificates.Data.Kernel.DigitScan
public import Certificates.Data.Kernel.Co1BPair
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Sporadic.Co1Block.TwoBD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSylow
public import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.G24Key

open CFSG.KC.Enum CFSG.KC.Pack CFSG.KC.DigitScan

abbrev Pm := Equiv.Perm (Fin 1365)

@[expose] def PtRep (P : Nat) (g : Pm) : Prop := ∀ x : Fin 1365, ap P x = (g x : Nat)

@[expose] noncomputable def treeE (γ : ℕ → Pm) (PAR PG : ℕ → ℕ) : ℕ → ℕ → Pm
  | 0, _ => 1
  | _ + 1, 0 => 1
  | f + 1, m + 1 => γ (t12 PG m) * treeE γ PAR PG f (t12 PAR m)

theorem treeE_zero (γ : ℕ → Pm) (PAR PG : ℕ → ℕ) (f : ℕ) : treeE γ PAR PG f 0 = 1 := by
  cases f <;> rfl

theorem treeE_mem {G : Type*} [SetLike G Pm] [SubgroupClass G Pm] {H : G} {γ : ℕ → Pm}
    (hγ : ∀ l, γ l ∈ H) (PAR PG : ℕ → ℕ) : ∀ f node, treeE γ PAR PG f node ∈ H
  | 0, _ => one_mem H
  | _ + 1, 0 => one_mem H
  | f + 1, m + 1 => mul_mem (hγ _) (treeE_mem hγ PAR PG f _)

theorem downK_succ (S PAR PG : Nat → Nat) (f m p : Nat) :
    downK S PAR PG (f + 1) (m + 1) p = ap (S (t12 PG m)) (downK S PAR PG f (t12 PAR m) p) := by
  change strictN (Nat.sub (m + 1) 1) (fun k => strictN (t12 PAR k)
    (fun r => ap (S (t12 PG k)) (downK S PAR PG f r p))) = _
  rw [strictN_eq, strictN_eq]
  rfl

theorem upK_succ (SI PAR PG : Nat → Nat) (f m p : Nat) :
    upK SI PAR PG (f + 1) (m + 1) p = upK SI PAR PG f (t12 PAR m) (ap (SI (t12 PG m)) p) := by
  change strictN (Nat.sub (m + 1) 1) (fun k => strictN (ap (SI (t12 PG k)) p)
    (fun q => strictN (t12 PAR k) (fun r => upK SI PAR PG f r q))) = _
  rw [strictN_eq, strictN_eq, strictN_eq]
  rfl

variable {S SI : ℕ → ℕ} {γ : ℕ → Pm}

theorem downK_eq (hS : ∀ l, PtRep (S l) (γ l)) (PAR PG : ℕ → ℕ) :
    ∀ f node (x : Fin 1365), downK S PAR PG f node x = (treeE γ PAR PG f node x : ℕ)
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | f + 1, m + 1, x => by
    rw [downK_succ, downK_eq hS PAR PG f _ x, hS]
    rfl

theorem upK_eq (hSI : ∀ l, PtRep (SI l) (γ l)⁻¹) (PAR PG : ℕ → ℕ) :
    ∀ f node (x : Fin 1365), upK SI PAR PG f node x = ((treeE γ PAR PG f node)⁻¹ x : ℕ)
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | f + 1, m + 1, x => by
    rw [upK_succ, hSI, upK_eq hSI PAR PG f _ _]
    simp only [treeE, mul_inv_rev, Equiv.Perm.mul_apply]

theorem eK_eq (hS : ∀ l, PtRep (S l) (γ l)) (hSI : ∀ l, PtRep (SI l) (γ l)⁻¹) {E : ℕ} {e : Pm}
    (hE : PtRep E e) (PAR PG : ℕ → ℕ) (f node : ℕ) (x : Fin 1365) :
    eK S SI PAR PG f E node x =
      ((treeE γ PAR PG f node * e * (treeE γ PAR PG f node)⁻¹) x : ℕ) := by
  unfold eK
  rw [strictN_eq, upK_eq hSI, hE, downK_eq hS]
  rfl

@[expose] noncomputable def wordE (a b : Pm) (W : ℕ) : ℕ → Pm
  | 0 => 1
  | i + 1 => (if Nat.land (Nat.shiftRight W i) 1 = 0 then a else b) * wordE a b W i

theorem wpt_eq {A B : ℕ} {a b : Pm} (hA : PtRep A a) (hB : PtRep B b) (W : ℕ) :
    ∀ L (x : Fin 1365), wpt A B W L x = (wordE a b W L x : ℕ)
  | 0, _ => rfl
  | L + 1, x => by
    change ap (nIf(Nat.beq fld(W, L, nat_lit 1) (nat_lit 0), A, B)) (wpt A B W L x) = _
    rw [wpt_eq hA hB W L x]
    simp only [wordE, Equiv.Perm.mul_apply]
    by_cases h : Nat.land (Nat.shiftRight W L) 1 = 0
    · rw [if_pos h, nif_true (Nat.beq_eq_true_eq _ _ ▸ h), hA]
    · rw [if_neg h, nif_false (Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)), hB]

@[expose] def keyE (g : Pm) : ℕ := ((g 0 : ℕ) * 2048 + g 1) * 2048 + g 2

theorem keyOf_eq (f : ℕ → ℕ) : keyOf f = (f 0 * 2048 + f 1) * 2048 + f 2 := by
  unfold keyOf
  rw [strictN_eq, strictN_eq, strictN_eq]
  rfl

theorem keyOf_pt {f : ℕ → ℕ} {g : Pm} (h : ∀ x : Fin 1365, f x = g x) : keyOf f = keyE g := by
  rw [keyOf_eq]
  have h0 : f 0 = g 0 := h 0
  have h1 : f 1 = g 1 := h 1
  have h2 : f 2 = g 2 := h 2
  rw [h0, h1, h2]
  rfl

theorem keyE_inj {g h : Pm} (e : keyE g = keyE h) : g 0 = h 0 ∧ g 1 = h 1 ∧ g 2 = h 2 := by
  unfold keyE at e
  have a0 := (g 0).2
  have a1 := (g 1).2
  have a2 := (g 2).2
  have b0 := (h 0).2
  have b1 := (h 1).2
  have b2 := (h 2).2
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> omega

theorem kpt_keyE (g : Pm) {t : ℕ} (ht : t < 3) : kpt (keyE g) t = (g ⟨t, by omega⟩ : ℕ) := by
  unfold kpt
  change Nat.land (Nat.shiftRight (keyE g) (11 * (2 - t))) (2 ^ 11 - 1) = _
  rw [fld_eq]
  unfold keyE
  have a0 := (g 0).2
  have a1 := (g 1).2
  have a2 := (g 2).2
  interval_cases t
  · norm_num
    have : (g 0 : ℕ) = (g ⟨0, by omega⟩ : ℕ) := rfl
    omega
  · norm_num
    have : (g 1 : ℕ) = (g ⟨1, by omega⟩ : ℕ) := rfl
    omega
  · norm_num
    have : (g 2 : ℕ) = (g ⟨2, by omega⟩ : ℕ) := rfl
    omega

theorem kmap_keyE {G : ℕ} {g : Pm} (hG : PtRep G g) (e : Pm) : kmap G (keyE e) = keyE (g * e) := by
  unfold kmap
  rw [keyOf_eq, kpt_keyE e (by norm_num), kpt_keyE e (by norm_num), kpt_keyE e (by norm_num),
    hG, hG, hG]
  rfl

theorem keyK_eq (hS : ∀ l, PtRep (S l) (γ l)) (hSI : ∀ l, PtRep (SI l) (γ l)⁻¹) {E : ℕ} {e : Pm}
    (hE : PtRep E e) (PAR PG : ℕ → ℕ) (f node : ℕ) :
    keyK S SI PAR PG f E node =
      keyE (treeE γ PAR PG f node * e * (treeE γ PAR PG f node)⁻¹) :=
  keyOf_pt (eK_eq hS hSI hE PAR PG f node)

theorem treeK_spec (hS : ∀ l, PtRep (S l) (γ l)) {TP TG : ℕ → ℕ} {f : ℕ} {K : ℕ → ℕ} {n : ℕ}
    (h : treeK S TP TG f K n = true) : ∀ k < n, K k = keyE (treeE γ TP TG f k) := by
  intro k hk
  rw [Nat.eq_of_beq_eq_true (allN_spec h k hk)]
  exact keyOf_pt (downK_eq hS TP TG f k)

theorem closK_spec {G : ℕ → ℕ} {J : ℕ} {K CL : ℕ → ℕ} {n : ℕ} (h : closK G J K CL n = true) :
    ∀ i < n, ∀ j < J, t12 CL (J * i + j) < n ∧ K (t12 CL (J * i + j)) = kmap (G j) (K i) := by
  intro i hi j hj
  have h1 := allN_spec h i hi
  rw [strictB_eq] at h1
  have h2 := allN_spec h1 j hj
  rw [strictB_eq, band_iff] at h2
  exact ⟨Nat.le_of_ble_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem recK_spec {S TP TG : ℕ → ℕ} {f : ℕ} {K : ℕ → ℕ} {A B R0 R1 k r : ℕ}
    (h : recK S TP TG f K A B R0 R1 k r = true) :
    (Nat.land r 1 = 0 ∧ Nat.shiftRight r 1 < 3 ∧
        (k = 0 ∨ downK S TP TG f k (kpt (K k) (Nat.shiftRight r 1)) ≠ Nat.shiftRight r 1)) ∨
      (Nat.land r 1 ≠ 0 ∧ k ≠ 0 ∧ ∀ b < 3, downK S TP TG f k (kpt (K k) b) = b ∧
        wpt A B (Nat.shiftRight r 10) (Nat.land (Nat.shiftRight r 2) 255) (kpt (K k) b) =
          ap (if Nat.land (Nat.shiftRight r 1) 1 = 0 then R0 else R1)
            (wpt A B (Nat.shiftRight r 10) (Nat.land (Nat.shiftRight r 2) 255) b)) := by
  have bIf_eq : ∀ c t e : Bool, Bool.rec (motive := fun _ => Bool) e t c =
      (if c = true then t else e) := by
    intro c t e
    cases c <;> rfl
  have nIf_eq : ∀ (c : Bool) (t e : Nat), Bool.rec (motive := fun _ => Nat) e t c =
      (if c = true then t else e) := by
    intro c t e
    cases c <;> rfl
  unfold recK at h
  simp only [strictB_eq, bIf_eq, nIf_eq, Nat.beq_eq, Nat.blt_eq] at h
  by_cases hr : Nat.land r 1 = 0
  · rw [if_pos hr] at h
    by_cases h3 : Nat.shiftRight r 1 < 3
    · rw [if_pos h3] at h
      refine Or.inl ⟨hr, h3, ?_⟩
      by_cases hk : k = 0
      · exact Or.inl hk
      · rw [if_neg hk] at h
        refine Or.inr fun e => ?_
        rw [if_pos e] at h
        exact Bool.false_ne_true h
    · rw [if_neg h3] at h
      exact absurd h Bool.false_ne_true
  · rw [if_neg hr] at h
    by_cases hk : k = 0
    · simp [hk] at h
    · refine Or.inr ⟨hr, hk, fun b hb => ?_⟩
      simp only [hk, ↓reduceIte] at h
      have h2 := allN_spec h b hb
      by_cases hd : downK S TP TG f k (kpt (K k) b) = b
      · rw [if_pos hd] at h2
        exact ⟨hd, Nat.eq_of_beq_eq_true h2⟩
      · rw [if_neg hd] at h2
        exact absurd h2 Bool.false_ne_true

theorem sortedK_fold {K o : ℕ → ℕ} {n : ℕ} {f : ℕ → ℕ → ℕ} :
    ∀ (l : List ℕ) (s : ℕ), l.foldr f s ≠ 0 →
      (∀ x s, f x s ≠ 0 → s ≠ 0 ∧ o x < n ∧ K (o x) + 1 < s ∧ f x s = K (o x) + 1) →
      (∀ a ∈ l, o a < n ∧ l.foldr f s ≤ K (o a) + 1) ∧ l.Pairwise (fun a b => K (o a) < K (o b))
  | [], _, _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | x :: l, s, h, hf => by
    rw [List.foldr_cons] at h ⊢
    obtain ⟨h0, hx, hlt, he⟩ := hf x _ h
    obtain ⟨ih1, ih2⟩ := sortedK_fold l s h0 hf
    refine ⟨fun a ha => ?_, List.Pairwise.cons (fun b hb => ?_) ih2⟩
    · rw [he]
      rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨hx, le_rfl⟩
      · have := ih1 a ha
        exact ⟨this.1, by omega⟩
    · have := ih1 b hb
      omega

theorem sortedK_injOn {K ORD : ℕ → ℕ} {n : ℕ} (h : sortedK K ORD n = true) :
    ∀ i < n, ∀ j < n, K i = K j → i = j := by
  unfold sortedK at h
  rw [foldN_eq, Nat.blt_eq] at h
  have key := sortedK_fold (K := K) (o := t12 ORD) (n := n) (List.range n) _
    (Nat.pos_iff_ne_zero.1 h) ?hf
  case hf =>
    have nrec : ∀ (c : Bool) (t e : ℕ), Bool.rec (motive := fun _ => ℕ) e t c =
        if c = true then t else e := fun c t e => by cases c <;> rfl
    intro x s hne
    simp only [nrec, strictN_eq, Nat.beq_eq, Nat.blt_eq] at hne ⊢
    split_ifs at hne ⊢ <;> omega
  obtain ⟨h1, h2⟩ := key
  have hlt : ∀ a < n, t12 ORD a < n := fun a ha => (h1 a (List.mem_range.2 ha)).1
  have hmono : ∀ a < n, ∀ b < n, a < b → K (t12 ORD a) < K (t12 ORD b) := by
    intro a ha b hb hab
    have := List.pairwise_iff_getElem.1 h2 a b (by simpa using ha) (by simpa using hb) hab
    simpa using this
  have hinj : ∀ a < n, ∀ b < n, K (t12 ORD a) = K (t12 ORD b) → a = b := by
    intro a ha b hb e
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · exact absurd e (Nat.ne_of_lt (hmono a ha b hb hab))
    · exact hab
    · exact absurd e.symm (Nat.ne_of_lt (hmono b hb a ha hab))
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
    (fun a _ => t12 ORD a) (fun a ha => Finset.mem_range.2 (hlt a (Finset.mem_range.1 ha)))
    (fun a b ha hb e => hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb)
      (congrArg K e)) le_rfl
  intro i hi j hj e
  obtain ⟨a, ha, rfl⟩ := hsurj i (Finset.mem_range.2 hi)
  obtain ⟨b, hb, rfl⟩ := hsurj j (Finset.mem_range.2 hj)
  rw [hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e]

theorem scanK_brec_true (t e : Bool) : Bool.rec (motive := fun _ => Bool) e t true = t := rfl

theorem scanK_brec_false (t e : Bool) : Bool.rec (motive := fun _ => Bool) e t false = e := rfl

theorem scanK_lrec {l : List Char} (h : List.rec (motive := fun _ => Bool) true
    (fun _ _ _ => false) l = true) : l = [] := by
  cases l
  · rfl
  · exact absurd h Bool.false_ne_true

theorem scanK_nil (F : ℕ → ℕ → Bool) (N i v : ℕ) (op : Bool) :
    scanRun F N [] i v op = bAnd(op, bAnd(F i v, Nat.beq (Nat.succ i) N)) := rfl

theorem scanK_cons (F : ℕ → ℕ → Bool) (N : ℕ) (ch : Char) (rest : List Char) (i v : ℕ)
    (op : Bool) : scanRun F N (ch :: rest) i v op = strictB (Char.toNat ch) (fun c =>
      bIf(Nat.beq c (nat_lit 32),
        bAnd(op, bAnd(F i v, strictB (Nat.succ i) (fun j => scanRun F N rest j (nat_lit 0) false))),
      bIf(Nat.beq c (nat_lit 10),
        bAnd(op, bAnd(F i v, bAnd(Nat.beq (Nat.succ i) N,
          List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rest))),
      bAnd(Nat.ble (nat_lit 48) c, bAnd(Nat.ble c (nat_lit 57),
        strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48)))
          (fun u => scanRun F N rest i u true)))))) := rfl

theorem scanK_ne_space {c : Char} (h : c.isDigit = true) : c ≠ ' ' := by
  rintro rfl
  exact absurd h (by decide)

theorem scanK_of_toNat {c : Char} {k : ℕ} (h : c.toNat = k) : c = Char.ofNat k := by
  rw [← h, Char.ofNat_toNat]

theorem scanK_isDigit {c : Char} (h1 : 48 ≤ c.toNat) (h2 : c.toNat ≤ 57) : c.isDigit = true := by
  have e : c.toNat = c.val.toNat := rfl
  simp only [Char.isDigit, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq,
    UInt32.le_iff_toNat_le]
  constructor <;> simp <;> omega

theorem scanK_split_single {d : List Char} (h : ∀ c ∈ d, c ≠ ' ') : d.splitOn ' ' = [d] :=
  List.splitOn_eq_singleton fun hm => h ' ' hm rfl

theorem scanK_split_space {d : List Char} (h : ∀ c ∈ d, c ≠ ' ') (r : List Char) :
    (d ++ ' ' :: r).splitOn ' ' = d :: r.splitOn ' ' :=
  List.splitOn_append_cons_self_of_not_mem (fun hm => h ' ' hm rfl) r

theorem scanRun_sound {F : ℕ → ℕ → Bool} {N : ℕ} : ∀ (cs d : List Char) (i v : ℕ) (op : Bool),
    (∀ c ∈ d, c.isDigit = true) → (op = true ↔ d ≠ []) → v = CFSG.KC.Str.decVal d →
    scanRun F N cs i v op = true →
    ((d ++ cs).splitOn ' ').all CFSG.KC.Co1BPair.goodP = true ∧
      ((d ++ cs).splitOn ' ').length + i = N ∧
      ∀ t < ((d ++ cs).splitOn ' ').length,
        F (i + t) (CFSG.KC.Str.decVal ((((d ++ cs).splitOn ' ').getD t []).filter Char.isDigit))
          = true
  | [], d, i, v, op, hd, hop, hv, h => by
    rw [scanK_nil, band_iff, band_iff, Nat.beq_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hne := hop.1 h1
    have hf : d.filter Char.isDigit = d := List.filter_eq_self.2 hd
    rw [List.append_nil, scanK_split_single fun c hc => scanK_ne_space (hd c hc)]
    refine ⟨?_, by simp; omega, fun t ht => ?_⟩
    · simp only [List.all_cons, List.all_nil, Bool.and_true, CFSG.KC.Co1BPair.goodP]
      have : d.isEmpty = false := by simpa using hne
      simp [this, List.all_eq_true.2 hd]
    · have ht0 : t = 0 := by simpa using ht
      subst ht0
      simpa [hf, ← hv] using h2
  | ch :: rest, d, i, v, op, hd, hop, hv, h => by
    simp only [scanK_cons, strictB_eq] at h
    cases h32 : Nat.beq (Char.toNat ch) (nat_lit 32)
    · simp only [h32, scanK_brec_false] at h
      cases h10 : Nat.beq (Char.toNat ch) (nat_lit 10)
      · simp only [h10, scanK_brec_false, band_iff, Nat.ble_eq] at h
        obtain ⟨hlo, hhi, h⟩ := h
        have hdig := scanK_isDigit hlo hhi
        have e : d ++ ch :: rest = (d ++ [ch]) ++ rest := by simp
        rw [e]
        refine scanRun_sound rest (d ++ [ch]) i _ true (fun c hc => ?_) (by simp) ?_ h
        · rcases List.mem_append.1 hc with hc | hc
          · exact hd c hc
          · rw [List.mem_singleton.1 hc]
            exact hdig
        · rw [hv, CFSG.KC.Str.decVal, CFSG.KC.Str.decVal, List.foldl_append]
          rfl
      · simp only [h10, scanK_brec_true, band_iff, Nat.beq_eq] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        have hne := hop.1 h1
        have hr := scanK_lrec h4
        subst hr
        have hch : ch = '\n' := scanK_of_toNat (Nat.eq_of_beq_eq_true h10)
        subst hch
        have hsp : ∀ c ∈ d ++ ['\n'], c ≠ ' ' := by
          intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact scanK_ne_space (hd c hc)
          · rw [List.mem_singleton.1 hc]
            decide
        have hf : (d ++ ['\n']).filter Char.isDigit = d := by
          rw [List.filter_append, List.filter_eq_self.2 hd]
          simp
        rw [scanK_split_single hsp]
        refine ⟨?_, by simp; omega, fun t ht => ?_⟩
        · simp only [List.all_cons, List.all_nil, Bool.and_true, CFSG.KC.Co1BPair.goodP]
          have : d.isEmpty = false := by simpa using hne
          simp [this, List.all_eq_true.2 hd, List.dropLast_concat]
        · have ht0 : t = 0 := by simpa using ht
          subst ht0
          simpa [hf, ← hv] using h2
    · simp only [h32, scanK_brec_true, band_iff] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hch : ch = ' ' := scanK_of_toNat (Nat.eq_of_beq_eq_true h32)
      subst hch
      obtain ⟨ih1, ih2, ih3⟩ := scanRun_sound rest [] (i + 1) 0 false
        (fun c hc => absurd hc List.not_mem_nil) (by simp) rfl h3
      rw [List.nil_append] at ih1 ih2 ih3
      have hne := hop.1 h1
      have hf : d.filter Char.isDigit = d := List.filter_eq_self.2 hd
      rw [scanK_split_space (fun c hc => scanK_ne_space (hd c hc)) rest]
      refine ⟨?_, by simp; omega, fun t ht => ?_⟩
      · rw [List.all_cons, ih1, Bool.and_true, CFSG.KC.Co1BPair.goodP]
        have : d.isEmpty = false := by simpa using hne
        simp [this, List.all_eq_true.2 hd]
      · rcases t with _ | t
        · simpa [hf, ← hv] using h2
        · have := ih3 t (by simpa using ht)
          rw [show i + (t + 1) = i + 1 + t by omega]
          simpa using this

theorem scanK_sound {F : ℕ → ℕ → Bool} {N : ℕ} {cs : List Char} (h : scanK F N cs = true) :
    (cs.splitOn ' ').all CFSG.KC.Co1BPair.goodP = true ∧
      (CFSG.KC.Co1BPair.numsOf cs).length = N ∧
      ∀ i < N, F i ((CFSG.KC.Co1BPair.numsOf cs).getD i 0) = true := by
  obtain ⟨h1, h2, h3⟩ := scanRun_sound cs [] 0 0 false (fun c hc => absurd hc List.not_mem_nil)
    (by simp) rfl h
  rw [List.nil_append] at h1 h2 h3
  refine ⟨h1, by simpa [CFSG.KC.Co1BPair.numsOf] using h2, fun i hi => ?_⟩
  have := h3 i (by omega)
  rw [Nat.zero_add] at this
  have e : (CFSG.KC.Co1BPair.numsOf cs).getD i 0 =
      CFSG.KC.Str.decVal (((cs.splitOn ' ').getD i []).filter Char.isDigit) := by
    rw [CFSG.KC.Co1BPair.numsOf, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getD_eq_getElem?_getD]
    cases (cs.splitOn ' ')[i]? <;> rfl
  rw [e]
  exact this

section Sep

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Schreier.Tits CFSG.Certificates


theorem twoBD_eq_one {g : Pm} (hg : g ∈ twoBD) (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) :
    g = 1 := by
  have hQ := (valid_ofArrays (n := 1365) (hn := by norm_num) (k := 2) (hk := twoBStrong_two_le)
    (b := twoBChainBase) (hb := twoB_nodup) twoB_allPerms (by norm_num : 0 < 4) twoB_chainOK).1
  rw [← twoBQ_original] at hg
  refine RawSchreierDatum.eq_one_of_fixes_base _ hQ hg fun i => ?_
  have hm : twoBQ.base.get i ∈ twoBQ.base.toList := by simp [Vector.get, Vector.toList]
  rw [RawSchreierDatum.ofArrays_base_toList] at hm
  have hl : finList 1365 twoBChainBase = [0, 1, 2] := by decide
  rw [hl] at hm
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e <;> rw [e]
  · exact h0
  · exact h1
  · exact h2

theorem twoBD_eq_of_keyE {g h : Pm} (hg : g ∈ twoBD) (hh : h ∈ twoBD) (e : keyE g = keyE h) :
    g = h := by
  obtain ⟨e0, e1, e2⟩ := keyE_inj e
  have hm : h⁻¹ * g ∈ twoBD := mul_mem (inv_mem hh) hg
  have := twoBD_eq_one hm (by rw [Equiv.Perm.mul_apply, e0]; simp)
    (by rw [Equiv.Perm.mul_apply, e1]; simp) (by rw [Equiv.Perm.mul_apply, e2]; simp)
  rw [inv_mul_eq_one] at this
  exact this.symm

end Sep

section Count

open CFSG.EvenSporadicStandard.Induction.AutBound

variable {G : Type*} [Group G]

theorem ncard_conj_mul_le (H : Subgroup G) [Finite H] {t : G} (ht : t ∈ H) {K : Subgroup G}
    (hKH : K ≤ H) (hK : ∀ k ∈ K, k * t = t * k) :
    {z : G | ∃ d ∈ H, z = d * t * d⁻¹}.ncard * Nat.card K ≤ Nat.card H := by
  classical
  let C := {z : G | ∃ d ∈ H, z = d * t * d⁻¹}
  have hd : ∀ z : C, ∃ d ∈ H, (z : G) = d * t * d⁻¹ := fun z => z.2
  let dz : C → G := fun z => (hd z).choose
  have hdz : ∀ z : C, dz z ∈ H ∧ (z : G) = dz z * t * (dz z)⁻¹ := fun z => (hd z).choose_spec
  let Ψ : C × K → H := fun p => ⟨dz p.1 * p.2, mul_mem (hdz p.1).1 (hKH p.2.2)⟩
  have hinj : Function.Injective Ψ := by
    rintro ⟨z, k⟩ ⟨z', k'⟩ e
    have e' : dz z * k = dz z' * k' := congrArg Subtype.val e
    have hc : ∀ (w : C) (c : K), dz w * c * t * (dz w * c)⁻¹ = w := fun w c => by
      rw [(hdz w).2]
      calc dz w * c * t * (dz w * c)⁻¹ = dz w * ((c : G) * t) * (c : G)⁻¹ * (dz w)⁻¹ := by group
        _ = dz w * t * (dz w)⁻¹ := by rw [hK c c.2]; group
    have hzz : z = z' := Subtype.ext (by rw [← hc z k, ← hc z' k', e'])
    subst hzz
    have : (k : G) = k' := mul_left_cancel e'
    rw [Subtype.ext this]
  have := Nat.card_le_card_of_injective Ψ hinj
  rwa [Nat.card_prod, Nat.card_coe_set_eq] at this

theorem eq_image_of_ncard_le {S : Set G} (hS : S.Finite) {m : ℕ} (hle : S.ncard ≤ m)
    {f : ℕ → G} (hf : ∀ i < m, f i ∈ S) (hinj : ∀ i < m, ∀ j < m, f i = f j → i = j) :
    ∀ z ∈ S, ∃ i < m, f i = z := by
  have hsub : f '' Set.Iio m ⊆ S := by
    rintro _ ⟨i, hi, rfl⟩
    exact hf i hi
  have hc : (f '' Set.Iio m).ncard = m := by
    rw [Set.InjOn.ncard_image (s := Set.Iio m) (f := f) fun i hi j hj e => hinj i hi j hj e,
      Set.ncard_Iio_nat]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hc]; exact hle) hS
  intro z hz
  rw [← heq] at hz
  obtain ⟨i, hi, rfl⟩ := hz
  exact ⟨i, hi, rfl⟩

theorem closure_subset_of_closed {E : Set G} (hE : E.Finite) (h1 : (1 : G) ∈ E) {s : Set G}
    (hcl : ∀ x ∈ s, ∀ y ∈ E, x * y ∈ E) : (Subgroup.closure s : Set G) ⊆ E := by
  have hinv : ∀ x ∈ s, ∀ y ∈ E, x⁻¹ * y ∈ E := by
    intro x hx y hy
    have hmaps : Set.MapsTo (fun z => x * z) E E := fun z hz => hcl x hx z hz
    have hinj : Set.InjOn (fun z => x * z) E := fun a _ b _ e => mul_left_cancel e
    have hsurj := (Set.Finite.injOn_iff_bijOn_of_mapsTo hE hmaps).1 hinj
    obtain ⟨z, hz, e⟩ := hsurj.surjOn hy
    have : x⁻¹ * y = z := by
      change x * z = y at e
      rw [← e, inv_mul_cancel_left]
    rw [this]
    exact hz
  intro g hg
  have := Subgroup.closure_induction_left (p := fun g _ => g ∈ E) h1
    (fun x hx y _ hy => hcl x hx y hy) (fun x hx y _ hy => hinv x hx y hy) hg
  exact this

theorem closure_eq_of_tree {γ : ℕ → G} {J n : ℕ} {e : ℕ → G}
    (he : ∀ k < n, e k ∈ Subgroup.closure (γ '' Set.Iio J)) (hn : 0 < n) (h0 : e 0 = 1)
    (hcl : ∀ i < n, ∀ j < J, ∃ c < n, e c = γ j * e i)
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) :
    (Subgroup.closure (γ '' Set.Iio J) : Set G) = e '' Set.Iio n ∧
      Nat.card (Subgroup.closure (γ '' Set.Iio J)) = n := by
  have hE : (e '' Set.Iio n).Finite := (Set.finite_Iio n).image e
  have hsub : (Subgroup.closure (γ '' Set.Iio J) : Set G) ⊆ e '' Set.Iio n := by
    refine closure_subset_of_closed hE ⟨0, hn, h0⟩ ?_
    rintro _ ⟨j, hj, rfl⟩ _ ⟨i, hi, rfl⟩
    obtain ⟨c, hc, e'⟩ := hcl i hi j hj
    exact ⟨c, hc, e'⟩
  have heq : (Subgroup.closure (γ '' Set.Iio J) : Set G) = e '' Set.Iio n := by
    refine Set.Subset.antisymm hsub ?_
    rintro _ ⟨k, hk, rfl⟩
    exact he k hk
  refine ⟨heq, ?_⟩
  have hc : Nat.card (Subgroup.closure (γ '' Set.Iio J)) =
      ((Subgroup.closure (γ '' Set.Iio J) : Set G)).ncard := Nat.card_coe_set_eq _
  rw [hc, heq, Set.InjOn.ncard_image (s := Set.Iio n) (f := e) fun i hi j hj e' => hinj i hi j hj e',
    Set.ncard_Iio_nat]

theorem le_ncard_of_inj {S : Set G} (hS : S.Finite) {n : ℕ} {f : ℕ → G} (hf : ∀ i < n, f i ∈ S)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ S.ncard := by
  have hsub : f '' Set.Iio n ⊆ S := by
    rintro _ ⟨i, hi, rfl⟩
    exact hf i hi
  have := Set.ncard_le_ncard hsub hS
  rwa [Set.InjOn.ncard_image (s := Set.Iio n) (f := f) fun i hi j hj e => hinj i hi j hj e,
    Set.ncard_Iio_nat] at this

theorem fusion_of_sylow {H T : Subgroup G} [Finite H] (hTH : T ≤ H)
    (hcard : Nat.card T = 2 ^ (Nat.card H).factorization 2) {a b : G}
    (hT : ∀ z ∈ T, z * z = 1 → z ≠ 1 →
      (∃ d ∈ H, d * z * d⁻¹ = a) ∨ ∃ d ∈ H, d * z * d⁻¹ = b) :
    ∀ z ∈ H, z * z = 1 → z ≠ 1 → (∃ d ∈ H, d * z * d⁻¹ = a) ∨ ∃ d ∈ H, d * z * d⁻¹ = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Subgroup ↥H := T.subgroupOf H
  have hT'card : Nat.card T' = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  let S : Sylow 2 ↥H := Sylow.ofCard T' (by rw [hT'card, hcard])
  let Q : Set ↥H := {w | (∃ d ∈ H, d * (w : G) * d⁻¹ = a) ∨ ∃ d ∈ H, d * (w : G) * d⁻¹ = b}
  have hconj : ∀ n z, z ∈ Q → n * z * n⁻¹ ∈ Q := by
    rintro n z (⟨d, hd, e⟩ | ⟨d, hd, e⟩)
    · refine Or.inl ⟨d * (n : G)⁻¹, mul_mem hd (inv_mem n.2), ?_⟩
      rw [← e]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · refine Or.inr ⟨d * (n : G)⁻¹, mul_mem hd (inv_mem n.2), ?_⟩
      rw [← e]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have hQ : ∀ z ∈ (S : Subgroup ↥H), orderOf z = 2 → z ∈ Q := by
    intro z hzS hz2
    have hzT : (z : G) ∈ T := hzS
    have hzsq : (z : G) * z = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz2, pow_two] at this
      exact congrArg Subtype.val this
    have hz1 : (z : G) ≠ 1 := fun h => by
      have : z = 1 := Subtype.ext h
      rw [this, orderOf_one] at hz2
      omega
    exact hT _ hzT hzsq hz1
  have hcov := cover_of_sylow S Q hconj hQ
  intro z hz hzsq hz1
  have hz2 : orderOf (⟨z, hz⟩ : ↥H) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using hzsq)
    · exact fun h => hz1 (congrArg Subtype.val h)
  exact hcov _ hz2

end Count

open CFSG.KS.Raw

theorem ap_eq_unpack (P : ℕ) {p : ℕ} (hp : p < 1365) : ap P p = (unpack 1365 11 P)[p]! := by
  rw [CFSG.KC.BfsPin.unpack_get' hp, mask_eq]
  rfl

theorem ptRep_of_rep {P : ℕ} {g : Pm}
    (h : CFSG.Monster.B.Co2.Rep 1365 (unpack 1365 11 P) g) : PtRep P g := fun x => by
  rw [ap_eq_unpack P x.2]
  exact h x

end CFSG.KC.G24Key

end
