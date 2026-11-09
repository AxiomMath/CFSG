module

public import CFSG.Certificates.Kernel.O8N3Sound

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.N3Split

theorem o8_pairwise_of_zip_lt : ∀ (l : List ℕ),
    (l.zip l.tail).all (fun p => decide (p.1 < p.2)) = true → l.Pairwise (· < ·)
  | [] => fun _ => List.Pairwise.nil
  | [_] => fun _ => List.pairwise_singleton _ _
  | a :: b :: t => by
    intro h
    simp only [List.tail_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
      decide_eq_true_eq] at h
    have ih := o8_pairwise_of_zip_lt (b :: t) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hx)

theorem o8_cent_eq_of_orb {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true) {s : ℕ}
    (ts : List (ℕ × ℕ)) (ks : List ℕ)
    (hts : ts.all (fun p => decide (p.1 < E.keys.size) && decide (p.2 < E.keys.size) &&
      mulK (E.keys.getD p.1 0) s == mulK (E.keys.getD p.2 0) (E.keys.getD p.1 0)) = true)
    (hys : ((ts.map Prod.snd).zip (ts.map Prod.snd).tail).all (fun p => decide (p.1 < p.2)) = true)
    (hks : ks.all (fun i => decide (i < E.keys.size) &&
      (mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0))) = true)
    (hkz : (ks.zip ks.tail).all (fun p => decide (p.1 < p.2)) = true)
    (hcard : E.keys.size ≤ ts.length * ks.length) :
    ((Finset.range E.keys.size).filter fun i =>
      mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0)) = ks.toFinset := by
  classical
  have hkd : ks.Nodup := (o8_pairwise_of_zip_lt ks hkz).imp (fun h => h.ne)
  have hyd : (ts.map Prod.snd).Nodup :=
    (o8_pairwise_of_zip_lt _ hys).imp (fun h => h.ne)
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hts hks
  set S : Mat12 := toMatK s with hSdef
  set Cf := (Finset.range E.keys.size).filter fun i =>
    mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0) with hCf
  have hPQ : ∀ k x, Rep k x → k < 2 ^ 144 →
      ((x : Mat12) * S = S * x ↔ mulK k s = mulK s k) := by
    intro k x hx hk
    rw [← hx, hSdef, ← toMatK_mulK, ← toMatK_mulK]
    exact ⟨fun e => eq_of_toMatK_eq (mulK_lt _ _) (mulK_lt _ _) e, fun e => by rw [e]⟩
  have hcC := card_filter_eq hE (fun k => mulK k s = mulK s k)
    (fun x : GL12 => (x : Mat12) * S = S * x) hPQ
  have hTs : ∀ j : Fin ts.length, ts[j].1 < E.keys.size := fun j => (hts _ (List.getElem_mem _)).1.1
  choose T hT using fun j : Fin ts.length => Enum.exists_mem hE _ (hTs j)
  have hconj : ∀ j : Fin ts.length,
      (T j : Mat12) * S = toMatK (E.keys.getD ts[j].2 0) * T j := by
    intro j
    have e := (hts _ (List.getElem_mem j.2)).2
    rw [← (hT j).2, hSdef, ← toMatK_mulK, ← toMatK_mulK]
    exact congrArg toMatK e
  have hinj : Function.Injective fun p : Fin ts.length ×
      {x : GL12 // x ∈ grpOf gs ∧ (x : Mat12) * S = S * x} =>
        (⟨T p.1 * p.2.1, mul_mem (hT p.1).1 p.2.2.1⟩ : grpOf gs) := by
    rintro ⟨j, c⟩ ⟨k, c'⟩ e
    have e1 : T j * c.1 = T k * c'.1 := congrArg Subtype.val e
    have hu : ((c'.1 * c.1⁻¹ : GL12) : Mat12) * S = S * (c'.1 * c.1⁻¹ : GL12) := by
      have h1 : Commute (c.1 : Mat12) S := c.2.2
      have h2 : Commute (c'.1 : Mat12) S := c'.2.2
      rw [Units.val_mul]
      exact (h2.mul_left h1.units_inv_left).eq
    have e2 : T j = T k * (c'.1 * c.1⁻¹) := by rw [← mul_assoc, ← e1, mul_inv_cancel_right]
    have hY : toMatK (E.keys.getD ts[j].2 0) = toMatK (E.keys.getD ts[k].2 0) := by
      have a1 := hconj j
      have a2 := hconj k
      rw [e2, Units.val_mul, mul_assoc, hu, ← mul_assoc, a2, ← mul_assoc] at a1
      have a3 := (Units.mul_left_inj (c'.1 * c.1⁻¹)).1 a1
      exact ((Units.mul_left_inj (T k)).1 a3).symm
    have hjk : j = k := by
      have hb1 := (hts _ (List.getElem_mem j.2)).1.2
      have hb2 := (hts _ (List.getElem_mem k.2)).1.2
      have hi := Enum.index_unique hE hb1 hb2
        (eq_of_toMatK_eq (Enum.key_lt hE hb1) (Enum.key_lt hE hb2) hY)
      have hm : (ts.map Prod.snd)[j.1]'(by simp) = (ts.map Prod.snd)[k.1]'(by simp) := by
        simpa using hi
      exact Fin.ext ((hyd.getElem_inj_iff).1 hm)
    subst hjk
    have e3 : c.1 = c'.1 := mul_left_cancel e1
    exact Prod.ext rfl (Subtype.ext e3)
  have hle : ts.length * Cf.card ≤ E.keys.size := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, hcC, ← hCf,
      Enum.card_eq hE] at this
  have hsub : ks.toFinset ⊆ Cf := by
    intro i hi
    have h := hks i (List.mem_toFinset.1 hi)
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 h.1, h.2⟩
  have hck : Cf.card ≤ ks.toFinset.card := by
    rw [List.toFinset_card_of_nodup hkd]
    have hpos : 0 < ts.length := by
      rcases Nat.eq_zero_or_pos ts.length with h0 | h0
      · have hid := (Enum.of_enumOK hE).2.2.1
        obtain ⟨i, hi, -⟩ := exists_of_memK hid
        rw [h0, Nat.zero_mul] at hcard
        omega
      · exact h0
    exact Nat.le_of_mul_le_mul_left (hle.trans hcard) hpos
  exact (Finset.eq_of_subset_of_card_le hsub hck).symm

theorem commCount_of_orb {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true) {s : ℕ}
    (ts : List (ℕ × ℕ)) (ks : List ℕ)
    (hts : ts.all (fun p => decide (p.1 < E.keys.size) && decide (p.2 < E.keys.size) &&
      mulK (E.keys.getD p.1 0) s == mulK (E.keys.getD p.2 0) (E.keys.getD p.1 0)) = true)
    (hys : ((ts.map Prod.snd).zip (ts.map Prod.snd).tail).all (fun p => decide (p.1 < p.2)) = true)
    (hks : ks.all (fun i => decide (i < E.keys.size) &&
      (mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0))) = true)
    (hkz : (ks.zip ks.tail).all (fun p => decide (p.1 < p.2)) = true)
    (hcard : E.keys.size ≤ ts.length * ks.length) : commCount E s = ks.length := by
  classical
  rw [commCount, o8_cent_eq_of_orb hE ts ks hts hys hks hkz hcard,
    List.toFinset_card_of_nodup ((o8_pairwise_of_zip_lt ks hkz).imp (fun h => h.ne))]

theorem kerOn_of_orb {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true) {s : ℕ}
    (vs : List ℕ) (ts : List (ℕ × ℕ)) (ks : List ℕ)
    (hts : ts.all (fun p => decide (p.1 < E.keys.size) && decide (p.2 < E.keys.size) &&
      mulK (E.keys.getD p.1 0) s == mulK (E.keys.getD p.2 0) (E.keys.getD p.1 0)) = true)
    (hys : ((ts.map Prod.snd).zip (ts.map Prod.snd).tail).all (fun p => decide (p.1 < p.2)) = true)
    (hks : ks.all (fun i => decide (i < E.keys.size) &&
      (mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0))) = true)
    (hkz : (ks.zip ks.tail).all (fun p => decide (p.1 < p.2)) = true)
    (hcard : E.keys.size ≤ ts.length * ks.length) :
    kerOn E s vs = (ks.filter fun i => fixesOn vs (E.keys.getD i 0)).length := by
  classical
  have hkd : ks.Nodup := (o8_pairwise_of_zip_lt ks hkz).imp (fun h => h.ne)
  have heq := o8_cent_eq_of_orb hE ts ks hts hys hks hkz hcard
  have e1 : ((Finset.range E.keys.size).filter fun i =>
      mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0) ∧ fixesOn vs (E.keys.getD i 0) = true) =
      (ks.filter fun i => fixesOn vs (E.keys.getD i 0)).toFinset := by
    rw [← Finset.filter_filter, heq, List.toFinset_filter]
  rw [kerOn, e1, List.toFinset_card_of_nodup (hkd.filter _)]

theorem candB_false_of_cent {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true) {s : ℕ}
    {vs : List ℕ} (hlen : 3 ≤ vs.length) (hnd : vs.Nodup)
    (hfix : vs.all (fun v => decide (v < 4096) && mulVecK s v == v) = true)
    (ts : List (ℕ × ℕ)) (ks : List ℕ)
    (hts : ts.all (fun p => decide (p.1 < E.keys.size) && decide (p.2 < E.keys.size) &&
      mulK (E.keys.getD p.1 0) s == mulK (E.keys.getD p.2 0) (E.keys.getD p.1 0)) = true)
    (hys : ((ts.map Prod.snd).zip (ts.map Prod.snd).tail).all (fun p => decide (p.1 < p.2)) = true)
    (hks : ks.all (fun i => decide (i < E.keys.size) &&
      (mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0)) &&
        vs.all fun v => mulVecK (E.keys.getD i 0) v == v) = true)
    (hkz : (ks.zip ks.tail).all (fun p => decide (p.1 < p.2)) = true)
    (hcard : E.keys.size ≤ ts.length * ks.length) : candB E s = false := by
  classical
  have hks' : ks.all (fun i => decide (i < E.keys.size) &&
      (mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0))) = true := by
    simp only [List.all_eq_true, Bool.and_eq_true] at hks ⊢
    exact fun i hi => (hks i hi).1
  have heq := o8_cent_eq_of_orb hE ts ks hts hys hks' hkz hcard
  simp only [List.all_eq_true, Bool.and_eq_true] at hks
  apply candB_false_of_zfix hlen hnd hfix
  rw [List.all_eq_true]
  intro i hi
  by_cases hc : mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0)
  · have hm : i ∈ (Finset.range E.keys.size).filter fun i =>
        mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (List.mem_range.1 hi), hc⟩
    rw [heq] at hm
    rw [List.all_eq_true.2 (hks i (List.mem_toFinset.1 hm)).2, Bool.or_true]
  · have hf : (mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0)) = false := by
      simpa using hc
    rw [hf, Bool.not_false, Bool.true_or]

end CFSG.KC.O8

end
