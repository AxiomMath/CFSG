module

public import CFSG.Certificates.Kernel.RouteP.MonoSet
public import CFSG.Certificates.Kernel.RouteP.TreeBFS
public import Certificates.Data.Kernel.RouteP.Geom

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.RouteP CFSG.KC.Benes CFSG.KS.Fi24Net

theorem allI_spec {n : Nat} {f : Nat → Bool} (h : allI n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have e : allI (n + 1) f = andB (f n) (allI n f) := rfl
    obtain ⟨h1, h2⟩ := andB_true (e ▸ h)
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

theorem orB_true {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem memP_eq (s N : Nat) : memP s N = memS s N := rfl

structure GeomCoreFacts (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (NWO : Nat → Nat → Nat)
    (KAO KBO : Nat → Nat) (zg ag : List Int) (S : Nat → Nat) (A : Nat) : Prop where
  closed : ∀ i < 7, closedS NW KA KB zg (S i) = true
  count : ∀ i < 7, pcount (Nat.land (S i) ptsS) = gSize i
  disj : ∀ i < 7, ∀ j < 7, i ≠ j → Nat.land (S i) (S j) = 0
  cover : Nat.land (lorI S 7) ptsS = ptsS
  root : ∀ i < 7, ptOK NW KA KB (gMW i) 0 (gRoot i) = true
  up : ∀ i < 7, ∀ j < 7, gLev i + 1 < gLev j → Nat.land (imgW NW KA KB (gMW i) (S 1)) (S j) = 0
  down : ∀ i < 7, gLev i = 0 ∨ (memS (imgW NW KA KB (gMW i) (S 1)) (gWit i) = true ∧
    memS (S (gWl i)) (gWit i) = true ∧ gLev (gWl i) + 1 = gLev i)
  a_closed : closedS NWO KAO KBO ag A = true
  a_count : pcount (Nat.land A ptsS) = 3510
  fix0 : ∀ t < 3, ptOK NWO KAO KBO [((t + 7 : Nat) : Int)] 0 0 = true
  fix1 : ∀ t < 3, ptOK NWO KAO KBO [((t + 7 : Nat) : Int)] 1479 1479 = true
  tau : Nat.land (Nat.land (imgS NWO KAO KBO (-10) (S 1)) (S 1)) A =
    Nat.land (imgS NWO KAO KBO (-10) (S 1)) (S 1)

theorem geomCore_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {NWO : Nat → Nat → Nat}
    {KAO KBO : Nat → Nat} {zg ag : List Int} {S : Nat → Nat} {A : Nat}
    (h : geomCore NW KA KB NWO KAO KBO zg ag S A = true) :
    GeomCoreFacts NW KA KB NWO KAO KBO zg ag S A := by
  unfold geomCore at h
  obtain ⟨ho, h⟩ := andB_true h
  obtain ⟨hd, hs⟩ := andB_true h
  unfold orbSetsOK at ho
  obtain ⟨ho1, ho⟩ := andB_true ho
  obtain ⟨ho2, ho3⟩ := andB_true ho
  unfold s1SetOK at hs
  obtain ⟨ha, hs⟩ := andB_true hs
  obtain ⟨ha1, ha2⟩ := andB_true ha
  obtain ⟨hf, ht⟩ := andB_true hs
  rw [letB_eq'] at ht
  have hdi : ∀ i < 7, distSetOK NW KA KB S i = true := allI_spec hd
  have hdi' : ∀ i < 7, ptOK NW KA KB (gMW i) 0 (gRoot i) = true ∧
      andB (allI 7 fun j => orB (Nat.ble (gLev j) (gLev i + 1))
          (Nat.beq (Nat.land (imgW NW KA KB (gMW i) (S 1)) (S j)) 0))
        (orB (Nat.beq (gLev i) 0) (andB (memP (imgW NW KA KB (gMW i) (S 1)) (gWit i))
          (andB (memP (S (gWl i)) (gWit i)) (Nat.beq (gLev (gWl i) + 1) (gLev i))))) = true :=
    fun i hi => by
      have := hdi i hi
      unfold distSetOK at this
      rw [letB_eq'] at this
      exact andB_true this
  refine ⟨fun i hi => (andB_true (allI_spec ho1 i hi)).1,
    fun i hi => Nat.eq_of_beq_eq_true (andB_true (allI_spec ho1 i hi)).2,
    fun i hi j hj hij => ?_, Nat.eq_of_beq_eq_true ho3, fun i hi => (hdi' i hi).1,
    fun i hi j hj hlt => ?_, fun i hi => ?_, ha1, Nat.eq_of_beq_eq_true ha2,
    fun t ht' => (andB_true (allI_spec hf t ht')).1, fun t ht' => (andB_true (allI_spec hf t ht')).2,
    Nat.eq_of_beq_eq_true ht⟩
  · rcases orB_true (allI_spec (allI_spec ho2 i hi) j hj) with e | e
    · exact absurd (Nat.eq_of_beq_eq_true e) hij
    · exact Nat.eq_of_beq_eq_true e
  · rcases orB_true (allI_spec (andB_true (hdi' i hi).2).1 j hj) with e | e
    · have := Nat.le_of_ble_eq_true e
      omega
    · exact Nat.eq_of_beq_eq_true e
  · rcases orB_true (andB_true (hdi' i hi).2).2 with e | e
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
    · obtain ⟨e1, e⟩ := andB_true e
      obtain ⟨e2, e3⟩ := andB_true e
      exact Or.inr ⟨e1, e2, Nat.eq_of_beq_eq_true e3⟩

theorem sel7_eq (a : Nat → Nat) {i : Nat} (hi : i < 7) :
    sel7 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) i = a i := by
  interval_cases i <;> rfl

theorem geomSetOK_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {NWO : Nat → Nat → Nat}
    {KAO KBO : Nat → Nat} {zg ag : List Int} (h : geomSetOK NW KA KB NWO KAO KBO zg ag = true) :
    GeomCoreFacts NW KA KB NWO KAO KBO zg ag
      (sel7 (zS NW KA KB zg 0) (zS NW KA KB zg 1) (zS NW KA KB zg 2) (zS NW KA KB zg 3)
        (zS NW KA KB zg 4) (zS NW KA KB zg 5) (zS NW KA KB zg 6))
      (closeS NWO KAO KBO ag 10 (single 99705)) := by
  unfold geomSetOK at h
  simp only [letB_eq'] at h
  exact geomCore_spec h

theorem testBit_lorI (S : Nat → Nat) (q : Nat) :
    ∀ n, (lorI S n).testBit q = true → ∃ i < n, (S i).testBit q = true
  | 0, h => by simp [lorI] at h
  | n + 1, h => by
    have e : lorI S (n + 1) = (S n ||| lorI S n) := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨n, by omega, h⟩
    · obtain ⟨i, hi, h⟩ := testBit_lorI S q n h
      exact ⟨i, by omega, h⟩

theorem cover_memS {S : Nat → Nat} {n : Nat} (h : Nat.land (lorI S n) ptsS = ptsS) {N : Nat}
    (hN : N < 920808) : ∃ i < n, memS (S i) N = true := by
  have hq : ptsS.testBit (N % 3 * 524288 + N / 3) = true := by
    rw [testBit_ptsS]
    have hm : (N % 3 * 524288 + N / 3) % 524288 = N / 3 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq, hm]
    omega
  rw [← h] at hq
  change (lorI S n &&& ptsS).testBit _ = true at hq
  rw [Nat.testBit_and, Bool.and_eq_true] at hq
  exact testBit_lorI S _ n hq.1

theorem disj_memS {a b : Nat} (h : Nat.land a b = 0) (N : Nat) :
    ¬ (memS a N = true ∧ memS b N = true) := by
  rintro ⟨ha, hb⟩
  have e : (Nat.land a b).testBit (N % 3 * 524288 + N / 3) = true := by
    change (a &&& b).testBit _ = true
    rw [Nat.testBit_and, Bool.and_eq_true]
    exact ⟨ha, hb⟩
  rw [h, Nat.zero_testBit] at e
  exact Bool.false_ne_true e

open CFSG.Sporadic.Th.Native CFSG.Perm.Native in
theorem tree_of_orbOK {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {letters : Array Table}
    {lv : Array Nat} {c : Nat → Int} {gens : List Int} {r k m : Nat} (hr : r < 920808)
    (hgens : gens = lv.toList.map c) (hg : ∀ z ∈ gens, LOK NW KA KB z)
    (hap : ∀ l ∈ lv, ∀ x < 920808, ap letters[l]! x = eL NW KA KB (c l) x)
    (hlv : ∀ l ∈ lv, l < 2 ^ 32) (h : orbOK NW KA KB gens r k m = true) :
    (treeBFS 920808 r letters lv).pts.size = m ∧
      treeOK 920808 r (treeBFS 920808 r letters lv) letters lv = true ∧
      ∀ x < 920808, (∃ j < (treeBFS 920808 r letters lv).pts.size,
        ap (treeBFS 920808 r letters lv).pts j = x) ↔ memS (closeS NW KA KB gens k (single r)) x = true := by
  obtain ⟨hroot, hcl, hmin, hcnt⟩ := orb_spec hr hg h
  set S := closeS NW KA KB gens k (single r)
  have hn : (920808 : Nat) < 2 ^ 32 := by decide
  have hF : ∀ l ∈ lv, ∀ x < 920808, ap letters[l]! x < 920808 := by
    intro l hl x hx
    rw [hap l hl x hx]
    exact eL_lt (hg _ (by rw [hgens]; exact List.mem_map.2 ⟨l, by simpa using hl, rfl⟩)) hx
  have hO1 : (fun x => decide (x < 920808) && memS S x) r = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hr, hroot⟩
  have hO2 : ∀ x, (fun x => decide (x < 920808) && memS S x) x = true → x < 920808 := fun x hx => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    exact hx.1
  have hO3 : ∀ x, (fun x => decide (x < 920808) && memS S x) x = true → ∀ l ∈ lv,
      (fun x => decide (x < 920808) && memS S x) (ap letters[l]! x) = true := by
    intro x hx l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    have hz : c l ∈ gens := by rw [hgens]; exact List.mem_map.2 ⟨l, by simpa using hl, rfl⟩
    rw [hap l hl x hx.1]
    exact ⟨eL_lt (hg _ hz) hx.1, hcl x hx.1 hx.2 _ hz⟩
  have hO4 : ∀ P : Nat → Prop, P r → (∀ x, P x → ∀ l ∈ lv, P (ap letters[l]! x)) →
      ∀ x, (fun x => decide (x < 920808) && memS S x) x = true → P x := by
    intro P hP0 hP x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    refine hmin P hP0 (fun N hN z hz => ?_) x hx.1 hx.2
    rw [hgens] at hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    have hl' : l ∈ lv := by simpa using hl
    by_cases hN' : N < 920808
    · rw [← hap l hl' N hN']
      exact hP N hN l hl'
    · unfold eL
      rw [if_neg hN']
      exact hN
  refine ⟨treeBFS_size hn hr hF hO1 hO2 hO3 hO4 ?_, treeOK_treeBFS hn hr hF hlv, fun x hx => ?_⟩
  · rw [← hcnt]
    exact congrArg List.length (List.filter_congr fun x hx => by
      have hx' : x < 920808 := List.mem_range.1 hx
      simp [hx'])
  · rw [exists_treeBFS_pts_iff hn hr hF hO1 hO2 hO3 hO4 x]
    simp [hx]

end CFSG.KS.RouteP

end
