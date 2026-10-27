module

public import Certificates.Data.Kernel.Misc.RuBigZR
public import CFSG.Certificates.Kernel.Misc.RuScanSound
public import CFSG.Quasithin.Vol2.KGFactC31OrbSound

public section

namespace CFSG.KC.Misc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Quasithin.KGC31

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem shl1 (r : Nat) : Nat.shiftLeft 1 r = 2 ^ r := Nat.one_shiftLeft r

theorem anyK_iff {n : Nat} {f : Nat → Bool} : anyK n f = true ↔ ∃ i < n, f i = true := by
  unfold anyK
  rw [RuBase.bIf_eq]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have ha : allN n (fun i => bIf(f i, false, true)) = true := RuBase.allN_iff.2 fun i hi => by
      rw [RuBase.bIf_eq, if_neg (hne i hi)]
    rw [if_pos ha] at h
    exact Bool.false_ne_true h
  · rintro ⟨i, hi, hf⟩
    have ha : allN n (fun i => bIf(f i, false, true)) = false := by
      rw [Bool.eq_false_iff]
      intro h
      have h1 := RuBase.allN_iff.1 h i hi
      rw [RuBase.bIf_eq, if_pos hf] at h1
      exact Bool.false_ne_true h1
    rw [ha]
    rfl

@[expose] def PtR (f : Nat → Nat) (g : Equiv.Perm (Fin 4060)) : Prop :=
  ∀ x : Fin 4060, f x = (g x : Nat)

theorem ptR_apP {p : Nat} {g : Equiv.Perm (Fin 4060)} (hp : PRep 4060 12 p g) : PtR (apP p) g :=
  fun x => apP_eq hp x

theorem ptR_comp {f f' : Nat → Nat} {g g' : Equiv.Perm (Fin 4060)} (hf : PtR f g)
    (hf' : PtR f' g') : PtR (fun x => f (f' x)) (g * g') := fun x => by
  change f (f' x) = _
  rw [hf' x, hf (g' x), Equiv.Perm.mul_apply]

theorem ptR_lt {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hf : PtR f g) {x : Nat}
    (hx : x < 4060) : f x < 4060 := by
  have h := hf ⟨x, hx⟩
  simp only at h
  rw [h]
  exact (g ⟨x, hx⟩).2

theorem ptR_lAp {A AI : Nat → Nat → Nat} {gens : List (Equiv.Perm (Fin 4060))} {m : Nat}
    (hA : ∀ k < m, PtR (A k) (gens.getD k 1)) (hAI : ∀ k < m, PtR (AI k) (gens.getD k 1)⁻¹)
    {l : Int} (hl0 : l ≠ 0) (hlm : l.natAbs ≤ m) :
    PtR (lAp A AI l)
        (if 0 < l then gens.getD (l.natAbs - 1) 1 else (gens.getD (l.natAbs - 1) 1)⁻¹) ∧
      PtR (lAp AI A l)
        (if 0 < l then gens.getD (l.natAbs - 1) 1 else (gens.getD (l.natAbs - 1) 1)⁻¹)⁻¹ := by
  cases l with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast] at hl0 hlm ⊢
    have hk : 0 < k := by omega
    have hpos : (0 : Int) < (k : Int) := by omega
    rw [if_pos hpos, Int.natAbs_natCast]
    rw [Int.natAbs_natCast] at hlm
    exact ⟨fun x => hA (k - 1) (by omega) x, fun x => hAI (k - 1) (by omega) x⟩
  | negSucc k =>
    have hneg : ¬ (0 : Int) < Int.negSucc k := fun h => absurd h (by
      have := Int.negSucc_lt_zero k
      omega)
    rw [if_neg hneg, Int.natAbs_negSucc, Nat.succ_sub_one, inv_inv]
    rw [Int.natAbs_negSucc] at hlm
    exact ⟨fun x => hAI k (by omega) x, fun x => hA k (by omega) x⟩

theorem ptR_wAp {A AI : Nat → Nat → Nat} {gens : List (Equiv.Perm (Fin 4060))} {m : Nat}
    (hA : ∀ k < m, PtR (A k) (gens.getD k 1)) (hAI : ∀ k < m, PtR (AI k) (gens.getD k 1)⁻¹) :
    ∀ (w : List Int), (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) →
      PtR (wAp A AI w) (evalSigned gens w) ∧ PtR (wApI A AI w) (evalSigned gens w)⁻¹
  | [], _ => ⟨fun x => by rw [evalSigned_nil]; rfl, fun x => by rw [evalSigned_nil, inv_one]; rfl⟩
  | l :: w, hw => by
    obtain ⟨ih1, ih2⟩ := ptR_wAp hA hAI w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    obtain ⟨hl0, hlm⟩ := hw l List.mem_cons_self
    obtain ⟨h1, h2⟩ := ptR_lAp hA hAI hl0 hlm
    rw [evalSigned_cons, mul_inv_rev]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · change strictN (wAp A AI w x) (fun v => lAp A AI l v) = _
      rw [sN, ih1 x, h1 _, Equiv.Perm.mul_apply]
    · change strictN (lAp AI A l x) (fun y => wApI A AI w y) = _
      rw [sN, h2 x, ih2 _, Equiv.Perm.mul_apply]

theorem ptR_itF {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hf : PtR f g) :
    ∀ k, PtR (itF f k) (g ^ k)
  | 0 => fun x => by rw [pow_zero]; rfl
  | k + 1 => fun x => by
    change strictN (itF f k x) f = _
    rw [sN, ptR_itF hf k x, hf _, pow_succ', Equiv.Perm.mul_apply]

theorem testBit_img4 {f : Nat → Nat} (hf : ∀ b < 4, f b < 4096) {b i : Nat} (hb : b < 4)
    (hi : i < 12) : (img4 f).testBit (12 * b + i) = (f b).testBit i := by
  have hz : ∀ k < 4, ∀ j, 12 ≤ j → (f k).testBit j = false := fun k hk j hj =>
    P.testBit_lt_4096 (hf k hk) hj
  have e : img4 f = f 0 <<< 0 ||| f 1 <<< 12 ||| f 2 <<< 24 ||| f 3 <<< 36 := by
    rw [img4, Raw.Orb.foldN_eq]
    simp [List.range_succ, Nat.or_assoc, Nat.or_comm, Nat.or_left_comm]
  rw [e]
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  interval_cases b
  · have h1 : ¬ 12 ≤ i := by omega
    have h2 : ¬ 24 ≤ i := by omega
    have h3 : ¬ 36 ≤ i := by omega
    simp [h1, h2, h3]
  · have h2 : ¬ 24 ≤ 12 + i := by omega
    have h3 : ¬ 36 ≤ 12 + i := by omega
    simp [h2, h3, hz 0 (by norm_num) (12 + i) (by omega)]
  · have h3 : ¬ 36 ≤ 24 + i := by omega
    have e1 : 24 + i - 12 = 12 + i := by omega
    simp [h3, e1, hz 0 (by norm_num) (24 + i) (by omega), hz 1 (by norm_num) (12 + i) (by omega)]
  · have e1 : 36 + i - 12 = 24 + i := by omega
    have e2 : 36 + i - 24 = 12 + i := by omega
    simp [e1, e2, hz 0 (by norm_num) (36 + i) (by omega), hz 1 (by norm_num) (24 + i) (by omega),
      hz 2 (by norm_num) (12 + i) (by omega)]

theorem eq_of_img4_pt {f f' : Nat → Nat} (hf : ∀ b < 4, f b < 4096) (hf' : ∀ b < 4, f' b < 4096)
    (h : img4 f = img4 f') {b : Nat} (hb : b < 4) : f b = f' b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · rw [← testBit_img4 hf hb hi, ← testBit_img4 hf' hb hi, h]
  · rw [P.testBit_lt_4096 (hf b hb) (by omega), P.testBit_lt_4096 (hf' b hb) (by omega)]

theorem eq_of_pts {H : Subgroup (Equiv.Perm (Fin 4060))} {bs : List Nat}
    (hH : BaseFaithful H bs) (hbs : ∀ x ∈ bs, x < 4) {g g' : Equiv.Perm (Fin 4060)} (hg : g ∈ H)
    (hg' : g' ∈ H) {f f' : Nat → Nat} (hf : PtR f g) (hf' : PtR f' g')
    (h : ∀ b < 4, f b = f' b) : g = g' := by
  have h1 := hH (g'⁻¹ * g) (H.mul_mem (H.inv_mem hg') hg) fun x hx => by
    have e : g x = g' x := by
      apply Fin.ext
      rw [← hf x, ← hf' x]
      exact h x (hbs x hx)
    rw [Equiv.Perm.mul_apply, e]
    simp
  calc g = g' * (g'⁻¹ * g) := by group
    _ = g' := by rw [h1, mul_one]

theorem ptR_lt4096 {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hf : PtR f g) :
    ∀ b < 4, f b < 4096 :=
  fun _ hb => lt_trans (ptR_lt hf (by omega)) (by norm_num)

theorem eq_of_img4 {H : Subgroup (Equiv.Perm (Fin 4060))} {bs : List Nat}
    (hH : BaseFaithful H bs) (hbs : ∀ x ∈ bs, x < 4) {g g' : Equiv.Perm (Fin 4060)} (hg : g ∈ H)
    (hg' : g' ∈ H) {f f' : Nat → Nat} (hf : PtR f g) (hf' : PtR f' g') (h : img4 f = img4 f') :
    g = g' :=
  eq_of_pts hH hbs hg hg' hf hf' fun _ hb => eq_of_img4_pt (ptR_lt4096 hf) (ptR_lt4096 hf') h hb

theorem img4_eq_of_eq {f f' : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hf : PtR f g)
    (hf' : PtR f' g) : img4 f = img4 f' := by
  have h : ∀ b < 4, f b = f' b := fun b hb => by
    rw [hf ⟨b, by omega⟩, hf' ⟨b, by omega⟩]
  rw [img4, img4, Raw.Orb.foldN_eq, Raw.Orb.foldN_eq]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.foldr_cons, List.foldr_nil]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

@[expose] noncomputable def mProd (v : Nat → Equiv.Perm (Fin 4060)) : Nat → Nat →
    Equiv.Perm (Fin 4060)
  | 0, _ => 1
  | i + 1, m => (if m.testBit i then v i else 1) * mProd v i m

theorem fld_one_beq (m i : Nat) : Nat.beq (fld(m, i, 1)) 1 = m.testBit i := by
  change Nat.beq ((m >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem ptR_mAp {P : Nat → Nat} {o : Nat} {v : Nat → Equiv.Perm (Fin 4060)} (m : Nat) :
    ∀ {r : Nat}, (∀ i < r, PtR (apP (P (o + i))) (v i)) → PtR (mAp P o r m) (mProd v r m)
  | 0, _ => fun x => rfl
  | r + 1, hP => fun x => by
    have ih := ptR_mAp m (r := r) fun i hi => hP i (by omega)
    change strictN (mAp P o r m x) (fun y =>
      nIf(Nat.beq (fld(m, r, nat_lit 1)) (nat_lit 1), apP (P (Nat.add o r)) y, y)) = _
    rw [sN, fld_one_beq, mProd, Equiv.Perm.mul_apply, ih x]
    cases hb : m.testBit r
    · simp
    · simpa using hP r (by omega) (mProd v r m x)

theorem val_maskVec (r m : Nat) (i : Fin r) : (maskVec r m i).val = m / 2 ^ i.val % 2 :=
  ZMod.val_cast_of_lt (Nat.mod_lt _ (by norm_num))

theorem mProd_eq_eElt {v : Nat → Equiv.Perm (Fin 4060)} (m : Nat) :
    ∀ {r : Nat}, (∀ i < r, ∀ j < r, Commute (v i) (v j)) →
      mProd v r m = eElt (fun i : Fin r => v i) (maskVec r m)
  | 0, _ => by simp [mProd, eElt]
  | r + 1, hc => by
    have ih := mProd_eq_eElt m (r := r) fun i hi j hj => hc i (by omega) j (by omega)
    rw [mProd, ih]
    simp only [eElt]
    rw [List.ofFn_succ', List.prod_concat]
    have e : (List.ofFn fun i : Fin r => v ((Fin.castSucc i : Fin (r + 1)) : Nat) ^
        (maskVec (r + 1) m i.castSucc).val) = List.ofFn fun i : Fin r => v i ^ (maskVec r m i).val := by
      congr 1
    rw [e, val_maskVec]
    have hx : (if m.testBit r then v r else 1) = v r ^ (m / 2 ^ r % 2) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ r) with h | h <;> simp [h]
    simp only [Fin.val_last]
    rw [hx]
    exact ((commute_eElt (v := fun i : Fin r => v i)
      (fun i => (hc r (by omega) i (by omega)).pow_left _) (maskVec r m))).eq

theorem foldr_count (p : Nat → Bool) :
    ∀ l : List Nat, l.foldr (fun x c => nIf(p x, Nat.succ c, c)) 0 = (l.filter p).length
  | [] => rfl
  | a :: l => by
    rw [List.foldr_cons, foldr_count p l, List.filter_cons]
    cases hpa : p a <;> simp

theorem fixC_eq (f : Nat → Nat) :
    fixC f = ((List.range 4060).filter fun x => Nat.beq (f x) x).length := by
  rw [fixC, Raw.Orb.foldN_eq]
  exact foldr_count _ _

theorem pointList_fix (f : Nat → Nat) :
    CFSG.Certificates.PointList 4060 ((List.range 4060).filter fun x => Nat.beq (f x) x) :=
  ⟨fun q hq => List.mem_range.1 (List.mem_filter.1 hq).1, List.pairwise_lt_range.filter _⟩

theorem finSet_fix {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hf : PtR f g) :
    CFSG.Certificates.finSet 4060 ((List.range 4060).filter fun x => Nat.beq (f x) x) =
      {p | g p = p} := by
  ext p
  simp only [CFSG.Certificates.finSet, Set.mem_setOf_eq, List.mem_filter, List.mem_range,
    Nat.beq_eq]
  rw [hf p]
  exact ⟨fun h => Fin.ext h.2, fun h => ⟨p.2, by rw [h]⟩⟩

theorem inSp_iff {P : Nat → Nat} {o r u : Nat} :
    inSp P o r u = true ↔ ∃ m < 2 ^ r, mImg P o r m = u := by
  rw [inSp, anyK_iff, shl1]
  simp only [Nat.beq_eq]

section Base

variable {H : Subgroup (Equiv.Perm (Fin 4060))} {bs : List Nat} (hH : BaseFaithful H bs)
  (hbs : ∀ x ∈ bs, x < 4)

include hH hbs

theorem eq_one_of_base {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hg : g ∈ H) (hf : PtR f g)
    (h : ∀ b < 4, f b = b) : g = 1 :=
  hH g hg fun x hx => Fin.ext (by rw [← hf x]; exact h x (hbs x hx))

theorem mProd_mem {v : Nat → Equiv.Perm (Fin 4060)} (hv : ∀ i, v i ∈ H) (m : Nat) :
    ∀ r, mProd v r m ∈ H
  | 0 => H.one_mem
  | r + 1 => H.mul_mem (by split_ifs <;> first | exact hv r | exact H.one_mem) (mProd_mem hv m r)

theorem ebB_sound {P : Nat → Nat} {o r : Nat} {v : Nat → Equiv.Perm (Fin 4060)}
    (hP : ∀ i < r, PtR (apP (P (o + i))) (v i)) (hv : ∀ i, v i ∈ H) (h : ebB P o r = true) :
    EBasis (fun i : Fin r => v i) := by
  unfold ebB at h
  rw [RuBase.bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hsq : ∀ i < r, v i * v i = 1 ∧ ∀ j < r, Commute (v i) (v j) := by
    intro i hi
    have hi' := RuBase.allN_iff.1 h1 i hi
    rw [sB, RuBase.bAnd_eq', Bool.and_eq_true] at hi'
    refine ⟨eq_one_of_base hH hbs (H.mul_mem (hv i) (hv i)) (ptR_comp (hP i hi) (hP i hi))
      fun b hb => Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 hi'.1 b hb), fun j hj => ?_⟩
    have hj' := RuBase.allN_iff.1 hi'.2 j hj
    rw [sB] at hj'
    exact eq_of_pts hH hbs (H.mul_mem (hv i) (hv j)) (H.mul_mem (hv j) (hv i))
      (ptR_comp (hP i hi) (hP j hj)) (ptR_comp (hP j hj) (hP i hi))
      fun b hb => Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 hj' b hb)
  have hc : ∀ i < r, ∀ j < r, Commute (v i) (v j) := fun i hi j hj => (hsq i hi).2 j hj
  refine ⟨fun i => (hsq i i.2).1, fun i j => hc i i.2 j j.2, fun c hc1 => ?_⟩
  obtain ⟨m, hm, rfl⟩ := exists_maskVec c
  rw [← mProd_eq_eElt m hc] at hc1
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · funext i
    simp [maskVec]
  exfalso
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h3 := RuBase.allN_iff.1 h2 m' (by rw [shl1]; exact (by omega : m' < 2 ^ r - 1))
  rw [RuBase.bIf_eq] at h3
  have h4 : allN 4 (fun b => Nat.beq (mAp P o r (Nat.succ m') b) b) = true :=
    RuBase.allN_iff.2 fun b hb => by
      rw [Nat.beq_eq, ptR_mAp (m' + 1) hP ⟨b, by omega⟩, hc1]
      rfl
  rw [if_pos h4] at h3
  exact Bool.false_ne_true h3

theorem inSp_sound {P : Nat → Nat} {o r : Nat} {v : Nat → Equiv.Perm (Fin 4060)}
    (hP : ∀ i < r, PtR (apP (P (o + i))) (v i)) (hv : ∀ i, v i ∈ H)
    (hc : ∀ i < r, ∀ j < r, Commute (v i) (v j)) {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)}
    (hg : g ∈ H) (hf : PtR f g) (h : inSp P o r (img4 f) = true) :
    ∃ m < 2 ^ r, g = eElt (fun i : Fin r => v i) (maskVec r m) := by
  obtain ⟨m, hm, e⟩ := inSp_iff.1 h
  refine ⟨m, hm, ?_⟩
  rw [← mProd_eq_eElt m hc]
  exact (eq_of_img4 hH hbs (mProd_mem hH hbs hv m r) hg (ptR_mAp m hP) hf e).symm

theorem ordB_sound {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hg : g ∈ H) (hf : PtR f g)
    {p : Nat} (h : ordB f p = true) : g ^ p = 1 ∧ g ≠ 1 := by
  unfold ordB at h
  rw [RuBase.bAnd_eq', Bool.and_eq_true, RuBase.bIf_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨eq_one_of_base hH hbs (H.pow_mem hg p) (ptR_itF hf p)
    fun b hb => Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 h1 b hb), fun e => ?_⟩
  have h3 : allN 4 (fun b => Nat.beq (f b) b) = true := RuBase.allN_iff.2 fun b hb => by
    rw [Nat.beq_eq, hf ⟨b, hb.trans (by norm_num)⟩, e]
    rfl
  rw [if_pos h3] at h2
  exact Bool.false_ne_true h2

theorem normB_sound {P : Nat → Nat} {o r : Nat} {v : Nat → Equiv.Perm (Fin 4060)}
    (hP : ∀ i < r, PtR (apP (P (o + i))) (v i)) (hv : ∀ i, v i ∈ H)
    (hc : ∀ i < r, ∀ j < r, Commute (v i) (v j)) {A AI : Nat → Nat} {a : Equiv.Perm (Fin 4060)}
    (ha : a ∈ H) (hA : PtR A a) (hAI : PtR AI a⁻¹) (h : normB P o r A AI = true) :
    ∀ i < r, ∃ m < 2 ^ r, a * v i * a⁻¹ = eElt (fun i : Fin r => v i) (maskVec r m) := by
  intro i hi
  have h1 := RuBase.allN_iff.1 h i hi
  rw [sB] at h1
  exact inSp_sound hH hbs hP hv hc (H.mul_mem (H.mul_mem ha (hv i)) (H.inv_mem ha))
    (ptR_comp (ptR_comp hA (hP i hi)) hAI) h1

end Base

end CFSG.KC.Misc.RuBigZ

end
