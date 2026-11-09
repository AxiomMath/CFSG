module

public import Certificates.Data.Kernel.Spor.Fi24SevB
public import CFSG.Certificates.Kernel.Spor.Fi24SevSound

public section

namespace CFSG.KS.Fi24SevB

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt
  CFSG.KS.Fi24ThreeO CFSG.KS.Fi24Sev Finset

variable {NW : Nat → Nat → Nat} {NT : Nat → Nat}

theorem agB_spec {u v : List Nat} (h : agB NW NT u v = true) :
    ∀ b ∈ cb, cP NW NT u b = cP NW NT v b := by
  intro b hb
  have e := Nat.eq_of_beq_eq_true (allL_spec h b hb)
  rw [ptC_eq, ptC_eq] at e
  exact e

theorem allL_of {α : Type} {f : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, f a = true) → allL f l = true
  | [], _ => rfl
  | a :: l, h => by
    change andB (f a) (allL f l) = true
    rw [h a List.mem_cons_self, allL_of (fun b hb => h b (List.mem_cons_of_mem a hb))]
    rfl

theorem agB_of {u v : List Nat} (h : ∀ b ∈ cb, cP NW NT u b = cP NW NT v b) :
    agB NW NT u v = true := by
  unfold agB
  refine allL_of fun b hb => ?_
  rw [ptC_eq, ptC_eq, h b hb]
  exact Nat.beq_refl _

theorem eqOK_spec {ps : List (List Nat × List Nat)} (h : eqOK NW NT ps = true) :
    ∀ p ∈ ps, ∀ b ∈ cb, cP NW NT p.1 b = cP NW NT p.2 b :=
  fun p hp => agB_spec (allL_spec h p hp)

theorem neOK_spec {ps : List (List Nat × List Nat)} (h : neOK NW NT ps = true) :
    ∀ p ∈ ps, ∃ b ∈ cb, cP NW NT p.1 b ≠ cP NW NT p.2 b := by
  intro p hp
  have h1 := allL_spec h p hp
  by_contra hc
  push_neg at hc
  rw [agB_of hc] at h1
  exact absurd h1 (by decide)

theorem slIn_spec {sl part : List (Nat × List Nat × List Nat)} (h : slIn NW NT sl part = true) :
    ∀ e ∈ part, (∀ z ∈ e.2.1, 2 ≤ z ∧ (z ≤ 5 ∨ (z / 2 - 3 < e.1 ∧ ∃ e' ∈ sl, e'.1 = z / 2 - 3))) ∧
      ∀ b ∈ cb, cP NW NT (expU sl e.2.1) b = cP NW NT e.2.2 b := by
  intro e he
  obtain ⟨h1, h2⟩ := andB_true' (allL_spec h e he)
  refine ⟨fun z hz => ?_, agB_spec h2⟩
  obtain ⟨hz2, hz⟩ := andB_true' (allL_spec h1 z hz)
  refine ⟨ble_true hz2, ?_⟩
  rcases orB_true' hz with hz | hz
  · exact Or.inl (ble_true hz)
  · obtain ⟨hlt, hu⟩ := andB_true' hz
    refine Or.inr ⟨by simpa [Nat.shiftRight_eq_div_pow] using blt_true hlt, ?_⟩
    have key : ∀ (l : List (Nat × List Nat × List Nat)) (k : Nat), hasU l k = true →
        ∃ e' ∈ l, e'.1 = k := by
      intro l k
      induction l with
      | nil => intro h0; exact absurd h0 (by simp [hasU])
      | cons a l ih =>
        intro h0
        rcases orB_true' h0 with h0 | h0
        · exact ⟨a, List.mem_cons_self, Nat.eq_of_beq_eq_true h0⟩
        · obtain ⟨e', he', h'⟩ := ih h0
          exact ⟨e', List.mem_cons_of_mem a he', h'⟩
    simpa [Nat.shiftRight_eq_div_pow] using key sl _ hu

theorem hasU_spec {sl : List (Nat × List Nat × List Nat)} {k : Nat} (h : hasU sl k = true) :
    ∃ e ∈ sl, e.1 = k := by
  induction sl with
  | nil => exact absurd h (by simp [hasU])
  | cons a l ih =>
    rcases orB_true' h with h0 | h0
    · exact ⟨a, List.mem_cons_self, Nat.eq_of_beq_eq_true h0⟩
    · obtain ⟨e', he', h'⟩ := ih h0
      exact ⟨e', List.mem_cons_of_mem a he', h'⟩

theorem cjOK_spec {sl : List (Nat × List Nat × List Nat)} {c : Nat × Nat × List Nat × List Nat}
    (h : cjOK NW NT sl c = true) :
    (∀ l ∈ c.2.2.1, ∃ e ∈ sl, e.1 = l / 2) ∧
      (∀ b ∈ cb, cP NW NT (mW sl c.2.2.1) b = cP NW NT c.2.2.2 b) ∧
      ∀ b ∈ cb, cP NW NT (c.2.2.2 ++ cubeW sl c.1) b =
        cP NW NT (lIf (Nat.beq c.2.1 0) (findU sl 66) (findU sl 67) ++ c.2.2.2) b := by
  obtain ⟨h1, h2⟩ := andB_true' h
  obtain ⟨h3, h4⟩ := andB_true' h2
  refine ⟨fun l hl => ?_, agB_spec h3, agB_spec h4⟩
  have := hasU_spec (allL_spec h1 l hl)
  simpa [Nat.shiftRight_eq_div_pow] using this

theorem fixK_spec (hV : VN NW NT) {w : List Nat} {n : Nat} (h : fixK NW NT w n = true) :
    #((range 306936).filter (fun x => cP NW NT w x = x)) = n := by
  have e := Nat.eq_of_beq_eq_true h
  rw [CFSG.KS.Fi24FixP.popcount_19, CFSG.KS.Fi24FixP.sum_bits] at e
  rw [← e]
  have hsub : (range 306936).filter (fun x => cP NW NT w x = x) =
      (range 524288).filter (fun x => (fixC NW NT w).testBit x = true) := by
    ext x
    simp only [mem_filter, mem_range, testBit_fixC hV]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h1, h2⟩
    · rintro ⟨-, h1, h2⟩
      exact ⟨h1, h2⟩
  rw [hsub]

theorem testBit_zero_mod (x y : Nat) (h : x.testBit 0 = y.testBit 0) : x % 2 = y % 2 := by
  rw [Nat.testBit_zero, Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp_all

set_option exponentiation.threshold 4096 in
theorem bitK_eq (m q : Nat) : bitK m q = Nat.land (Nat.shiftRight m q) 1 := by
  unfold bitK
  rw [strictN_eq]
  have h12 : mk12 = 2 ^ 4096 - 1 := by
    unfold mk12
    change 1 <<< 4096 - 1 = _
    rw [Nat.one_shiftLeft]
  rw [h12]
  change ((m >>> ((q >>> 12) <<< 12)) &&& (2 ^ 4096 - 1)) >>> (q &&& 4095) &&& 1 = (m >>> q) &&& 1
  rw [Nat.and_one_is_mod, Nat.and_one_is_mod]
  apply testBit_zero_mod
  have hA : (q >>> 12) <<< 12 = q / 4096 * 4096 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hr : q &&& 4095 = q % 4096 := by
    rw [show (4095 : Nat) = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [hA, hr]
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.add_zero]
  have e1 : q % 4096 < 4096 := Nat.mod_lt _ (by omega)
  have e2 : q / 4096 * 4096 + q % 4096 = q := by omega
  simp only [e1, e2, decide_true, Bool.true_and, Bool.and_true]

theorem swpB_eq : swpB = swpK := by
  funext d m q
  unfold swpB swpK
  rw [bitK_eq, bitK_eq]

theorem ptFB_eq : ptFB = ptF := by
  funext M q
  unfold ptFB ptF
  rw [swpB_eq]

theorem ptRB_eq : ptRB = ptR := by
  funext M q
  unfold ptRB ptR
  rw [swpB_eq]

theorem letNB_eq : letNB = letN := by
  funext NW l x
  unfold letNB letN
  rw [ptFB_eq, ptRB_eq]

theorem apCB_eq : apCB = apC := by
  funext NW NT c x
  unfold apCB apC
  rw [ptFB_eq, letNB_eq]

theorem ptCB_eq : ptCB = ptC := by
  funext NW NT cs x
  unfold ptCB ptC
  rw [apCB_eq]

theorem agBB_eq : agBB = agB := by
  funext NW NT u v
  unfold agBB agB
  rw [ptCB_eq]

theorem slInB_eq : slInB = slIn := by
  funext NW NT sl part
  unfold slInB slIn
  rw [agBB_eq]

theorem brec_same (a b : Bool) : Bool.rec (motive := fun _ => Bool) a a b = a := by
  cases b <;> rfl

end CFSG.KS.Fi24SevB

end
