module

public import CFSG.Certificates.Kernel.RouteP.MonoSet
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound
public import Certificates.Data.Kernel.RouteP.Ronan
import CFSG.Certificates.Kernel.RouteP.GeomSound

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.RouteP CFSG.KC.Fi24NetPt CFSG.KS.Fi24NetPt
  CFSG.KS.Fi24Net

private theorem ksRN_memS_land (a b N : Nat) :
    memS (Nat.land a b) N = (memS a N && memS b N) := by
  unfold memS
  rw [show Nat.land a b = a &&& b from rfl, Nat.testBit_and]

theorem land_shr_one (a p : Nat) :
    Nat.land (Nat.shiftRight a p) 1 = if a.testBit p then 1 else 0 := by
  have h1 : Nat.land (Nat.shiftRight a p) 1 = (a >>> p) % 2 := Nat.and_one_is_mod _
  have h2 : a.testBit p = decide ((a >>> p) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [h1, h2]
  by_cases h : (a >>> p) % 2 = 1
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    omega

theorem kvN_eq (a b p : Nat) : kvN a b p = kv a b p := by
  unfold kvN kv
  rw [land_shr_one, land_shr_one]
  by_cases ha : a.testBit p = true <;> by_cases hb : b.testBit p = true <;> simp [ha, hb]

theorem eLN_eq (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (N : Nat) :
    eLN NW KA KB z N = eL NW KA KB z N := by
  unfold eLN eL
  by_cases hN : N < 920808
  · rw [if_pos hN]
    have hb : Nat.blt N (nat_lit 920808) = true := Nat.blt_eq.mpr hN
    rw [hb]
    cases z with
    | ofNat m =>
      cases m with
      | zero =>
        have e1 : fibF NW (Int.ofNat 0) (N / 3) = N / 3 := by simp [fibF]
        have e2 : lK NW KA KB (Int.ofNat 0) (N / 3) = 0 := by simp [lK]
        rw [e1, e2]
        change N = _
        omega
      | succ k =>
        have e1 : fibF NW (Int.ofNat (k + 1)) = pF (NW k) := by simp [fibF]
        have e2 : ∀ p, lK NW KA KB (Int.ofNat (k + 1)) p = kv (KA k) (KB k) p := by
          intro p
          simp [lK]
        rw [e1, e2]
        change 3 * ptF (NW k) (N / 3) + (N % 3 + kvN (KA k) (KB k) (N / 3)) % 3 = _
        rw [ptF_eq, kvN_eq]
    | negSucc n =>
      have e1 : fibF NW (Int.negSucc n) = pR (NW n) := rfl
      have e2 : ∀ p, lK NW KA KB (Int.negSucc n) p = (2 * kv (KA n) (KB n) (pR (NW n) p)) % 3 :=
        fun p => rfl
      rw [e1, e2]
      change 3 * ptR (NW n) (N / 3) + (N % 3 + 2 * kvN (KA n) (KB n) (ptR (NW n) (N / 3))) % 3 = _
      rw [ptR_eq, kvN_eq]
      omega
  · rw [if_neg hN]
    have hb : Nat.blt N (nat_lit 920808) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hN (Nat.blt_eq.mp h)
    rw [hb]

theorem ptW_eq (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) :
    ∀ (w : List Int) (N : Nat), ptW NW KA KB w N = eW NW KA KB w N
  | [], _ => rfl
  | z :: w, N => by
    change strictN (ptW NW KA KB w N) (eLN NW KA KB z) = eL NW KA KB z (eW NW KA KB w N)
    rw [strictN_eq', eLN_eq, ptW_eq NW KA KB w N]

theorem twd_letters : ∀ (n c : Nat), ∀ z ∈ twd n c, z = -1 ∨ z = -2
  | 0, _, z, h => by
    change z ∈ ([] : List Int) at h
    simp at h
  | n + 1, c, z, h => by
    change z ∈ Int.negSucc (Nat.land c 1) :: twd n (Nat.shiftRight c 1) at h
    rcases List.mem_cons.mp h with rfl | h
    · have h2 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
      rcases Nat.mod_two_eq_zero_or_one c with h0 | h0
      · rw [h2, h0]
        exact Or.inl rfl
      · rw [h2, h0]
        exact Or.inr rfl
    · exact twd_letters n _ z h

theorem baseOK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {zg : List Int} {R : Nat → Nat}
    {i : Nat} (h : baseOK NW KA KB zg R i = true) :
    (i < 3 → pl R i = zS NW KA KB zg ([1, 3, 4].getD i 0)) ∧
      (3 ≤ i → pl R i = imgW NW KA KB (gMW (i - 1)) (pl R 0)) := by
  unfold baseOK at h
  cases hb : Nat.blt i 3 with
  | true =>
    rw [hb] at h
    have hi : i < 3 := Nat.blt_eq.mp hb
    exact ⟨fun _ => Nat.eq_of_beq_eq_true h, fun h3 => absurd hi (by omega)⟩
  | false =>
    rw [hb] at h
    have hi : ¬ i < 3 := fun hlt => by
      rw [Nat.blt_eq.mpr hlt] at hb
      exact absurd hb (by decide)
    exact ⟨fun h3 => absurd h3 hi, fun _ => Nat.eq_of_beq_eq_true h⟩

theorem entOK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {R E : Nat → Nat} {e : Nat}
    (h : entOK NW KA KB R E e = true) :
    ptW NW KA KB (twd (eLen (E e)) (eCode (E e))) 0 = eU (E e) ∧
      pl R (e + 6) = Nat.land (imgW NW KA KB (twd (eLen (E e)) (eCode (E e))) (pl R 0))
        (tgt R (eGrp (E e))) := by
  unfold entOK at h
  simp only [letB_eq'] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Benes.andB_true h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

private theorem ksRN_list_all (l : List Int) (f : Int → Bool) :
    List.rec (motive := fun _ => Bool) true (fun z _ ih => andB (f z) ih) l = true →
      ∀ z ∈ l, f z = true := by
  induction l with
  | nil => intro _ z hz; simp at hz
  | cons z l ih =>
    intro h z' hz'
    change andB (f z) (List.rec (motive := fun _ => Bool) true
      (fun z _ ih => andB (f z) ih) l) = true at h
    obtain ⟨h1, h2⟩ := CFSG.KC.Benes.andB_true h
    rcases List.mem_cons.mp hz' with rfl | hz'
    · exact h1
    · exact ih h2 z' hz'

private theorem ksRN_memS_unionE (R E : Nat → Nat) (pt : Bool) (lo N : Nat) :
    ∀ n, memS (unionE R E pt lo n) N = true →
      ∃ i < n, memS (pl R (lo + i + 6)) N = true ∨
        (pt = true ∧ memS (single (eU (E (lo + i)))) N = true) := by
  intro n
  induction n with
  | zero =>
    intro h
    change memS 0 N = true at h
    rw [memS, Nat.zero_testBit] at h
    exact False.elim (Bool.false_ne_true h)
  | succ n ih =>
    intro h
    change memS (Nat.lor (Nat.lor (pl R (lo + n + 6))
      (Bool.rec (motive := fun _ => Nat) 0 (single (eU (E (lo + n)))) pt))
        (unionE R E pt lo n)) N = true at h
    rw [memS_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [memS_lor, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨n, by omega, Or.inl h⟩
      · cases pt with
        | false => exact absurd h (by simp [memS])
        | true => exact ⟨n, by omega, Or.inr ⟨rfl, h⟩⟩
    · obtain ⟨i, hi, h⟩ := ih h
      exact ⟨i, by omega, h⟩

private theorem ksRN_grpOK_entries {R E : Nat → Nat} {g lo hi : Nat}
    (h : grpOK R E g lo hi = true) :
    ∀ e, lo ≤ e → e < hi → eGrp (E e) = g ∧
      (g % 2 = 1 → memS (src R g) (eU (E e)) = true) ∧
      (g % 2 = 0 → (ePar (E e) = e ∧ memS (tgt R g) (eU (E e)) = true) ∨
        (lo ≤ ePar (E e) ∧ ePar (E e) < e ∧
          memS (pl R (ePar (E e) + 6)) (eU (E e)) = true)) := by
  unfold grpOK at h
  simp only [letB_eq'] at h
  obtain ⟨h1, _⟩ := CFSG.KC.Benes.andB_true h
  intro e hle hlt
  have hi' : e - lo < hi - lo := by omega
  have hf := allI_spec h1 (e - lo) hi'
  obtain ⟨hge, hfr⟩ := CFSG.KC.Benes.andB_true hf
  have he : lo.add (e - lo) = e := Nat.add_sub_cancel' hle
  rw [he] at hge hfr
  refine ⟨Nat.eq_of_beq_eq_true hge, ?_, ?_⟩
  · intro hg
    have hb : Nat.beq (Nat.land g 1) 1 = true := by
      rw [show Nat.land g 1 = 1 from (Nat.and_one_is_mod g).trans hg]
      rfl
    rw [hb] at hfr
    simpa only [memP_eq] using hfr
  · intro hg
    have hb : Nat.beq (Nat.land g 1) 1 = false := by
      rw [show Nat.land g 1 = 0 from (Nat.and_one_is_mod g).trans hg]
      rfl
    have hs : spanPt R E g lo e = true := by simpa only [hb] using hfr
    unfold spanPt at hs
    simp only [letB_eq'] at hs
    rcases orB_true hs with hs | hs
    · obtain ⟨hp, ht⟩ := CFSG.KC.Benes.andB_true hs
      exact Or.inl ⟨Nat.eq_of_beq_eq_true hp, by simpa only [memP_eq] using ht⟩
    · obtain ⟨hle', hs⟩ := CFSG.KC.Benes.andB_true hs
      obtain ⟨hlt', ht⟩ := CFSG.KC.Benes.andB_true hs
      exact Or.inr ⟨Nat.le_of_ble_eq_true hle', Nat.blt_eq.mp hlt',
        by simpa only [memP_eq] using ht⟩

private theorem ksRN_grpOK_cover {R E : Nat → Nat} {g lo hi : Nat}
    (h : grpOK R E g lo hi = true) :
    ∀ N, memS (tgt R g) N = true → ∃ e, lo ≤ e ∧ e < hi ∧
      (memS (pl R (e + 6)) N = true ∨ (g % 2 = 0 ∧ memS (single (eU (E e))) N = true)) := by
  unfold grpOK at h
  simp only [letB_eq'] at h
  obtain ⟨_, h2⟩ := CFSG.KC.Benes.andB_true h
  intro N hN
  have hV : Nat.land (tgt R g)
      (unionE R E (Nat.beq (Nat.land g 1) 0) lo (hi - lo)) = tgt R g :=
    Nat.eq_of_beq_eq_true h2
  have hU : memS (unionE R E (Nat.beq (Nat.land g 1) 0) lo (hi - lo)) N = true := by
    have e : memS (Nat.land (tgt R g)
        (unionE R E (Nat.beq (Nat.land g 1) 0) lo (hi - lo))) N = memS (tgt R g) N := by
      rw [hV]
    rw [ksRN_memS_land, hN, Bool.true_and] at e
    exact e
  obtain ⟨i, hi, hmem⟩ :=
    ksRN_memS_unionE R E (Nat.beq (Nat.land g 1) 0) lo N (hi - lo) hU
  refine ⟨lo + i, by omega, by omega, ?_⟩
  rcases hmem with h | ⟨hpt, hsingle⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_, hsingle⟩
    have h0 : Nat.land g 1 = 0 := Nat.eq_of_beq_eq_true hpt
    exact (Nat.and_one_is_mod g).symm.trans h0

theorem grpOK_spec {R E : Nat → Nat} {g lo hi : Nat} (h : grpOK R E g lo hi = true) :
    (∀ e, lo ≤ e → e < hi → eGrp (E e) = g ∧
      (g % 2 = 1 → memS (src R g) (eU (E e)) = true) ∧
      (g % 2 = 0 → (ePar (E e) = e ∧ memS (tgt R g) (eU (E e)) = true) ∨
        (lo ≤ ePar (E e) ∧ ePar (E e) < e ∧ memS (pl R (ePar (E e) + 6)) (eU (E e)) = true))) ∧
    ∀ N, memS (tgt R g) N = true → ∃ e, lo ≤ e ∧ e < hi ∧
      (memS (pl R (e + 6)) N = true ∨ (g % 2 = 0 ∧ memS (single (eU (E e))) N = true)) :=
  ⟨ksRN_grpOK_entries h, ksRN_grpOK_cover h⟩

theorem n4OK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {R : Nat → Nat} {w : List Int}
    (h : n4OK NW KA KB R w = true) :
    ∀ N, memS (imgW NW KA KB w (pl R 0)) N = true → memS (l3S R) N = true := by
  unfold n4OK at h
  simp only [letB_eq'] at h
  have hH : Nat.land (imgW NW KA KB w (pl R 0)) (l3S R) = imgW NW KA KB w (pl R 0) :=
    Nat.eq_of_beq_eq_true h
  intro N hN
  have e : memS (Nat.land (imgW NW KA KB w (pl R 0)) (l3S R)) N =
      memS (imgW NW KA KB w (pl R 0)) N := by rw [hH]
  rw [ksRN_memS_land, hN, Bool.true_and] at e
  exact e

theorem h4OK_spec {NWP : Nat → Nat → Nat} {KAP KBP : Nat → Nat} {NWO : Nat → Nat → Nat}
    {KAO KBO : Nat → Nat} {NWC : Nat → Nat → Nat} {KAC KBC : Nat → Nat} {R : Nat → Nat}
    (h : h4OK NWP KAP KBP NWO KAO KBO NWC KAC KBC R = true) :
    (∀ z ∈ ([-7, -8, -9] : List Int), eLN NWO KAO KBO z 0 = 0 ∧ (eLN NWO KAO KBO z 1479 = 1479 ∨
      memS (pl R 0) (eLN NWO KAO KBO z 1479) = true ∧
      memS (imgW NWP KAP KBP (gMW 1) (pl R 0)) (eLN NWO KAO KBO z 1479) = true)) ∧
    (∀ z ∈ h4P, eLN NWP KAP KBP z 0 = 0 ∧ (eLN NWP KAP KBP z 1479 = 1479 ∨
      memS (pl R 0) (eLN NWP KAP KBP z 1479) = true ∧
      memS (imgW NWP KAP KBP (gMW 1) (pl R 0)) (eLN NWP KAP KBP z 1479) = true)) ∧
    closeS NWC KAC KBC h4L 7 (single 1479) = pl R 0 := by
  unfold h4OK at h
  simp only [letB_eq'] at h
  obtain ⟨hAB, hC⟩ := CFSG.KC.Benes.andB_true h
  obtain ⟨hA, hB⟩ := CFSG.KC.Benes.andB_true hAB
  have hobj : ∀ z ∈ ([-7, -8, -9] : List Int),
      h4Pt NWO KAO KBO (pl R 0) (imgW NWP KAP KBP (gMW 1) (pl R 0)) z = true :=
    ksRN_list_all ([-7, -8, -9] : List Int)
      (fun z => h4Pt NWO KAO KBO (pl R 0) (imgW NWP KAP KBP (gMW 1) (pl R 0)) z) hA
  have hpres : ∀ z ∈ h4P,
      h4Pt NWP KAP KBP (pl R 0) (imgW NWP KAP KBP (gMW 1) (pl R 0)) z = true :=
    ksRN_list_all h4P
      (fun z => h4Pt NWP KAP KBP (pl R 0) (imgW NWP KAP KBP (gMW 1) (pl R 0)) z) hB
  refine ⟨?_, ?_, Nat.eq_of_beq_eq_true hC⟩
  · intro z hz
    have hp := hobj z hz
    unfold h4Pt at hp
    simp only [letB_eq'] at hp
    obtain ⟨h0, hrest⟩ := CFSG.KC.Benes.andB_true hp
    refine ⟨Nat.eq_of_beq_eq_true h0, ?_⟩
    rcases orB_true hrest with h | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    · obtain ⟨hG, hX⟩ := CFSG.KC.Benes.andB_true h
      exact Or.inr ⟨by simpa only [memP_eq] using hG, by simpa only [memP_eq] using hX⟩
  · intro z hz
    have hp := hpres z hz
    unfold h4Pt at hp
    simp only [letB_eq'] at hp
    obtain ⟨h0, hrest⟩ := CFSG.KC.Benes.andB_true hp
    refine ⟨Nat.eq_of_beq_eq_true h0, ?_⟩
    rcases orB_true hrest with h | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    · obtain ⟨hG, hX⟩ := CFSG.KC.Benes.andB_true h
      exact Or.inr ⟨by simpa only [memP_eq] using hG, by simpa only [memP_eq] using hX⟩

end CFSG.KS.RouteP

end
