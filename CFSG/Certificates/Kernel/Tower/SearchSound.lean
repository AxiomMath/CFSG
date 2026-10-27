module

public import CFSG.Certificates.Kernel.Tower.Search14Sound
public import CFSG.Certificates.Kernel.Tower.L3QSound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower Subgroup

variable {X : Type*} [Group X] {n : Nat} {mul : Nat → Nat → Nat} {dec : Nat → X}

theorem allFrom_get {a k : Nat} {p : Nat → Bool} (h : allFrom a k p = true) {i : Nat} (hi : i < k) :
    p (a + i) = true :=
  allB_eq_true.1 h i hi

theorem allFrom_two {a k₁ k₂ : Nat} {p : Nat → Bool} (h₁ : allFrom a k₁ p = true)
    (h₂ : allFrom (a + k₁) k₂ p = true) : allFrom a (k₁ + k₂) p = true := by
  refine allB_eq_true.2 fun i hi => ?_
  by_cases h : i < k₁
  · exact allB_eq_true.1 h₁ i h
  · have := allB_eq_true.1 h₂ (i - k₁) (by omega)
    change p (a + k₁ + (i - k₁)) = true at this
    change p (a + i) = true
    rwa [Nat.add_assoc, Nat.add_sub_cancel' (by omega)] at this

variable {GS PT GI LB RP nl OT CZ : Nat}

theorem s13_labParts (h : labOK n mul GS GI LB RP nl = true) :
    (∀ i < 4, l16 GI i < n ∧ mul (l16 GS i) (l16 GI i) = 0) ∧
    (∀ l < nl, rpL RP l < n ∧ lbL LB (rpL RP l) = l) ∧
    ∀ c < n, lbL LB c < nl ∧ lbW LB c < n ∧
      mul (lbW LB c) (rpL RP (lbL LB c)) = mul c (lbW LB c) ∧
      ∀ i < 4, lbL LB (mul (mul (l16 GS i) c) (l16 GI i)) = lbL LB c := by
  simp only [labOK, labC, Bool.and_eq_true, allB_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun i hi => ⟨Nat.le_of_ble_eq_true (h1 i hi).1, Nat.eq_of_beq_eq_true (h1 i hi).2⟩,
    fun l hl => ⟨Nat.le_of_ble_eq_true (h2 l hl).1, Nat.eq_of_beq_eq_true (h2 l hl).2⟩,
    fun c hc => ⟨Nat.le_of_ble_eq_true (h3 c hc).1.1.1, Nat.le_of_ble_eq_true (h3 c hc).1.1.2,
      Nat.eq_of_beq_eq_true (h3 c hc).1.2, fun i hi => Nat.eq_of_beq_eq_true ((h3 c hc).2 i hi)⟩⟩

theorem s13_lab_conj (M : IsModel (⊤ : Subgroup X) n mul dec) (hT : treeB n 4 mul GS PT = true)
    (hlab : labOK n mul GS GI LB RP nl = true) (g : X) :
    ∀ c < n, lbL LB (M.code (g * dec c * g⁻¹)) = lbL LB c := by
  obtain ⟨hGI, -, hC⟩ := s13_labParts hlab
  suffices H : ∀ d, ∀ e < n, ptDep PT e = d → ∀ c < n,
      lbL LB (M.code (dec e * dec c * (dec e)⁻¹)) = lbL LB c by
    have h := H _ _ (M.code_lt (mem_top g)) rfl
    rwa [M.dec_code (mem_top g)] at h
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro e he hd c hc
    by_cases h0 : e = 0
    · subst h0
      rw [M.dec_zero, one_mul, inv_one, mul_one, M.code_dec hc]
    · obtain ⟨hgi, hpar, hdep, hmul⟩ := treeB_get hT he h0
      have hg := treeB_gen hT hgi
      have hz := M.code_lt (mem_top (dec (ptPar PT e) * dec c * (dec (ptPar PT e))⁻¹))
      have e1 : dec e = dec (l16 GS (ptGi PT e)) * dec (ptPar PT e) := by
        rw [← M.dec_mul _ hg _ hpar, hmul]
      have e2 : dec e * dec c * (dec e)⁻¹ = dec (mul (mul (l16 GS (ptGi PT e))
          (M.code (dec (ptPar PT e) * dec c * (dec (ptPar PT e))⁻¹))) (l16 GI (ptGi PT e))) := by
        rw [M.dec_conj hg hz (hGI _ hgi).1 (hGI _ hgi).2, M.dec_code (mem_top _), e1]
        group
      rw [e2, M.code_dec (M.conj_lt hg hz (hGI _ hgi).1), (hC _ hz).2.2.2 _ hgi]
      exact ih _ (hd ▸ hdep) _ hpar rfl c hc

theorem s13_rep (M : IsModel (⊤ : Subgroup X) n mul dec)
    (hlab : labOK n mul GS GI LB RP nl = true) {c : Nat} (hc : c < n) :
    rpL RP (lbL LB c) < n ∧
      dec c = dec (lbW LB c) * dec (rpL RP (lbL LB c)) * (dec (lbW LB c))⁻¹ := by
  obtain ⟨-, hR, hC⟩ := s13_labParts hlab
  obtain ⟨hl, hw, hm, -⟩ := hC c hc
  have hr := (hR _ hl).1
  have h1 := M.dec_mul _ hw _ hr
  rw [hm, M.dec_mul _ hc _ hw] at h1
  exact ⟨hr, eq_mul_inv_of_mul_eq h1⟩

theorem s13_conj_iff (M : IsModel (⊤ : Subgroup X) n mul dec)
    (hT : treeB n 4 mul GS PT = true) (hlab : labOK n mul GS GI LB RP nl = true) {a b : Nat}
    (ha : a < n) (hb : b < n) : Conj (dec a) (dec b) ↔ lbL LB a = lbL LB b := by
  constructor
  · rintro ⟨k, hk⟩
    have h := s13_lab_conj M hT hlab k b hb
    rw [← hk, M.code_dec ha] at h
    exact h
  · intro h
    refine ⟨dec (lbW LB a) * (dec (lbW LB b))⁻¹, ?_⟩
    rw [(s13_rep M hlab ha).2, (s13_rep M hlab hb).2, h]
    group

theorem s13_card (M : IsModel (⊤ : Subgroup X) n mul dec) (hT : treeB n 4 mul GS PT = true)
    (hlab : labOK n mul GS GI LB RP nl = true) {c : Nat} (hc : c < n) :
    Nat.card (MulAction.orbit (ConjAct X) (dec c)) =
      cntB n (fun d => Nat.beq (lbL LB d) (lbL LB c)) := by
  classical
  rw [cntB_eq_card]
  set F := (Finset.range n).filter fun d => Nat.beq (lbL LB d) (lbL LB c) = true
  have hO : MulAction.orbit (ConjAct X) (dec c) = ↑(F.image dec) := by
    ext y
    rw [Finset.coe_image, Set.mem_image]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨M.code (g • dec c), ?_, M.dec_code (mem_top _)⟩
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨M.code_lt (mem_top _), ?_⟩
      rw [ConjAct.smul_def, s13_lab_conj M hT hlab _ c hc]
      exact Nat.beq_refl _
    · rintro ⟨d, hd, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨k, hk⟩ := (s13_conj_iff M hT hlab hd.1 hc).2 (Nat.eq_of_beq_eq_true hd.2)
      refine ⟨ConjAct.toConjAct k, ?_⟩
      change ConjAct.toConjAct k • dec c = dec d
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hk]
  have hinj : Set.InjOn dec ↑F := by
    intro a ha b hb h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    exact M.inj a ha.1 b hb.1 h
  rw [hO, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]

theorem s13_czOf (hlab : labOK n mul GS GI LB RP nl = true) (hcz : czOK n LB CZ 0 nl = true)
    {c : Nat} (hc : c < n) : czOf LB CZ c = cntB n (fun d => Nat.beq (lbL LB d) (lbL LB c)) := by
  have hl := ((s13_labParts hlab).2.2 c hc).1
  have h := allFrom_get hcz hl
  rw [Nat.zero_add] at h
  exact Nat.eq_of_beq_eq_true h

theorem s13_czOf_aut (M : IsModel (⊤ : Subgroup X) n mul dec) (hT : treeB n 4 mul GS PT = true)
    (hlab : labOK n mul GS GI LB RP nl = true) (hcz : czOK n LB CZ 0 nl = true) (γ : MulAut X)
    {a b : Nat} (ha : a < n) (hb : b < n) (h : dec b = γ (dec a)) :
    czOf LB CZ b = czOf LB CZ a := by
  rw [s13_czOf hlab hcz hb, s13_czOf hlab hcz ha, ← s13_card M hT hlab hb, ← s13_card M hT hlab ha,
    h, s14_card_orbit]

theorem s13_hParts {t HL : Nat} (h : hOK n mul t HL = true) :
    (∀ j < 128, hL HL j < n ∧ mul (hL HL j) t = mul t (hL HL j)) ∧
      ∀ j < 127, hL HL j < hL HL (j + 1) := by
  simp only [hOK, Bool.and_eq_true, allB_eq_true] at h
  exact ⟨fun j hj => ⟨Nat.le_of_ble_eq_true (h.1.1 j hj).1, Nat.eq_of_beq_eq_true (h.1.1 j hj).2⟩,
    fun j hj => Nat.le_of_ble_eq_true (h.1.2 j hj)⟩

theorem s13_cntH (M : IsModel (⊤ : Subgroup X) n mul dec) {t HL u : Nat} (ht : t < n)
    (hH : hOK n mul t HL = true) (hu : u < n) :
    cntH mul HL u = Nat.card {x : X // x * dec t = dec t * x ∧ x * dec u = dec u * x} := by
  obtain ⟨hHL, hinc⟩ := s13_hParts hH
  have hst : ∀ i j, i < j → j < 128 → hL HL i < hL HL j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact lt_trans (ih h (by omega)) (hinc j (by omega))
      · exact hinc i (by omega)
  rw [cntH, cntB_eq, length_filter_range]
  refine Nat.card_eq_of_bijective (fun j => ⟨dec (hL HL j.1),
    (M.comm_iff (hHL _ j.2.1).1 ht).1 (hHL _ j.2.1).2,
    (M.comm_iff (hHL _ j.2.1).1 hu).1 (Nat.eq_of_beq_eq_true j.2.2)⟩) ⟨?_, ?_⟩
  · intro ⟨a, ha, _⟩ ⟨b, hb, _⟩ hab
    have e := M.inj _ (hHL a ha).1 _ (hHL b hb).1 (congrArg Subtype.val hab)
    apply Subtype.ext
    change a = b
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd e (Nat.ne_of_lt (hst a b h hb))
    · exact h
    · exact absurd e (Nat.ne_of_gt (hst b a h ha))
  · rintro ⟨x, hxt, hxu⟩
    obtain ⟨j, hj, e⟩ := hOK_mem M ht hH x hxt
    have hc : mul (hL HL j) u = mul u (hL HL j) := by
      rw [M.comm_iff (hHL j hj).1 hu, e]
      exact hxu
    refine ⟨⟨j, hj, ?_⟩, Subtype.ext e⟩
    change Nat.beq (mul (hL HL j) u) (mul u (hL HL j)) = true
    rw [hc, Nat.beq_refl]

theorem s13_cntH_aut (M : IsModel (⊤ : Subgroup X) n mul dec) {t HL : Nat} (ht : t < n)
    (hH : hOK n mul t HL = true) (γ : MulAut X) (hγt : γ (dec t) = dec t) {u u' : Nat}
    (hu : u < n) (hu' : u' < n) (h : dec u' = γ (dec u)) : cntH mul HL u' = cntH mul HL u := by
  rw [s13_cntH M ht hH hu', s13_cntH M ht hH hu, h]
  have hiff : ∀ a : X, (a * dec t = dec t * a ∧ a * dec u = dec u * a) ↔
      (γ.toEquiv a * dec t = dec t * γ.toEquiv a ∧
        γ.toEquiv a * γ (dec u) = γ (dec u) * γ.toEquiv a) := by
    intro a
    have e1 : γ a * dec t = dec t * γ a ↔ a * dec t = dec t * a := by
      conv_lhs => rw [← hγt]
      rw [← map_mul, ← map_mul, γ.injective.eq_iff]
    have e2 : γ a * γ (dec u) = γ (dec u) * γ a ↔ a * dec u = dec u * a := by
      rw [← map_mul, ← map_mul, γ.injective.eq_iff]
    change _ ↔ (γ a * dec t = dec t * γ a ∧ γ a * γ (dec u) = γ (dec u) * γ a)
    rw [e1, e2]
  exact Nat.card_congr (Equiv.subtypeEquiv γ.toEquiv hiff).symm

theorem s13_cand (M : IsModel (⊤ : Subgroup X) n mul dec) (hord : ordOK n mul OT = true)
    (hT : treeB n 4 mul GS PT = true) (hlab : labOK n mul GS GI LB RP nl = true)
    (hcz : czOK n LB CZ 0 nl = true) {t HL w cw CL RK c : Nat} (hH : hOK n mul t HL = true)
    (ht : t < n) (hcm : cmOK n mul t OT LB CZ HL w cw CL RK c = true) (hw : w < n)
    (γ : MulAut X) (hγt : γ (dec t) = dec t) {u : Nat} (hu : u < n) (h : dec u = γ (dec w)) :
    rkL RK u < c ∧ clL CL (rkL RK u) = u := by
  simp only [cmOK, Bool.and_eq_true] at hcm
  have hcw := Nat.eq_of_beq_eq_true hcm.1
  have hx : (!candB mul t OT LB CZ HL w cw u ||
      (Nat.blt (rkL RK u) c && Nat.beq (clL CL (rkL RK u)) u)) = true := allB_eq_true.1 hcm.2 u hu
  have hcand : candB mul t OT LB CZ HL w cw u = true := by
    obtain ⟨m, m', e⟩ := s14_mul_aut M γ hw ht hu ht h hγt.symm
    simp only [candB, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [s14_oe_aut M hord γ hw hu h, Nat.beq_refl]
    · rw [s14_oe_aut M hord γ m m' e, Nat.beq_refl]
    · rw [s13_czOf_aut M hT hlab hcz γ hw hu h, Nat.beq_refl]
    · rw [s13_cntH_aut M ht hH γ hγt hw hu h, hcw, Nat.beq_refl]
  rw [hcand, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hx
  exact ⟨Nat.le_of_ble_eq_true hx.1, Nat.eq_of_beq_eq_true hx.2⟩

theorem s13_pv_lane {A B C D : Nat} (hA : A ≤ 3) (hB : B ≤ 3) (hC : C ≤ 3) (hD : D ≤ 3) :
    lane (Nat.add A (Nat.add (Nat.mul 4 B) (Nat.add (Nat.mul 16 C) (Nat.mul 64 D)))) 2 3 0 = A ∧
      lane (Nat.add A (Nat.add (Nat.mul 4 B) (Nat.add (Nat.mul 16 C) (Nat.mul 64 D)))) 2 3 1 = B ∧
      lane (Nat.add A (Nat.add (Nat.mul 4 B) (Nat.add (Nat.mul 16 C) (Nat.mul 64 D)))) 2 3 2 = C ∧
      lane (Nat.add A (Nat.add (Nat.mul 4 B) (Nat.add (Nat.mul 16 C) (Nat.mul 64 D)))) 2 3 3 =
        D := by
  have e : Nat.add A (Nat.add (Nat.mul 4 B) (Nat.add (Nat.mul 16 C) (Nat.mul 64 D))) =
      A + (4 * B + (16 * C + 64 * D)) := rfl
  have l : ∀ T i, lane T 2 3 i = T / 2 ^ (2 * i) % 4 := fun T i => lane_eq T 2 i
  simp only [e, l]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem s13_pvParts {t PV : Nat} (h : pvOK mul t OT GS PV = true) :
    lane PV 8 255 0 = pvOf mul t OT (l16 GS 1) (l16 GS 2) ∧
      lane PV 8 255 1 = pvOf mul t OT (l16 GS 1) (l16 GS 3) ∧
      lane PV 8 255 2 = pvOf mul t OT (l16 GS 2) (l16 GS 3) := by
  simp only [pvOK, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem s13_ipE (M : IsModel (⊤ : Subgroup X) n mul dec) (hord : ordOK n mul OT = true)
    (γ : MulAut X) {t : Nat} (hγt : γ (dec t) = dec t) {x y x' y' P : Nat} (hx : x < n)
    (hy : y < n) (hx' : x' < n) (hy' : y' < n) (ht : t < n) (hX : dec x' = γ (dec x))
    (hY : dec y' = γ (dec y)) (hP : P = pvOf mul t OT x y) : ipE mul t OT P x' y' = true := by
  obtain ⟨m1, m1', e1⟩ := s14_mul_aut M γ hx hy hx' hy' hX hY
  obtain ⟨a1, a1', f1⟩ := s14_mul_aut M γ hx ht hx' ht hX hγt.symm
  obtain ⟨b1, b1', f2⟩ := s14_mul_aut M γ hy ht hy' ht hY hγt.symm
  obtain ⟨m2, m2', e2⟩ := s14_mul_aut M γ a1 b1 a1' b1' f1 f2
  obtain ⟨c1, c1', f3⟩ := s14_mul_aut M γ hx hx hx' hx' hX hX
  obtain ⟨m3, m3', e3⟩ := s14_mul_aut M γ c1 hy c1' hy' f3 hY
  obtain ⟨m4, m4', e4⟩ := s14_mul_aut M γ m1 hy m1' hy' e1 hY
  have l : ∀ c, oe OT c ≤ 3 := fun c => lane_le _ _ _ _
  obtain ⟨q0, q1, q2, q3⟩ := s13_pv_lane (l (mul x y)) (l (mul (mul x t) (mul y t)))
    (l (mul (mul x x) y)) (l (mul (mul x y) y))
  rw [hP]
  unfold pvOf ipE
  rw [q0, q1, q2, q3, s14_oe_aut M hord γ m1 m1' e1, s14_oe_aut M hord γ m2 m2' e2,
    s14_oe_aut M hord γ m3 m3' e3, s14_oe_aut M hord γ m4 m4' e4]
  simp only [Nat.beq_refl, Bool.and_self]

theorem s13_w1 {HL R1 n1 u v : Nat} (h : w1C mul HL R1 n1 u v = true) :
    Nat.land v 511 < n1 ∧ Nat.shiftRight v 9 < 128 ∧
      mul (hL HL (Nat.shiftRight v 9)) u =
        mul (lane R1 13 8191 (Nat.land v 511)) (hL HL (Nat.shiftRight v 9)) := by
  simp only [w1C, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1, Nat.le_of_ble_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem s13_w2 {HL R1 R2 n2 r1 u v : Nat} (h : w2C mul HL R1 R2 n2 r1 u v = true) :
    Nat.land v 4095 < n2 ∧ Nat.shiftRight v 12 < 128 ∧
      Nat.land (lane R2 24 16777215 (Nat.land v 4095)) 1023 = r1 ∧
      mul (hL HL (Nat.shiftRight v 12)) (lane R1 13 8191 r1) =
        mul (lane R1 13 8191 r1) (hL HL (Nat.shiftRight v 12)) ∧
      mul (hL HL (Nat.shiftRight v 12)) u =
        mul (r2u2 R2 (Nat.land v 4095)) (hL HL (Nat.shiftRight v 12)) := by
  simp only [w2C, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1.1.1, Nat.le_of_ble_eq_true h.1.1.1.2,
    Nat.eq_of_beq_eq_true h.1.1.2, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem s13_w3 {HL R1 R2 R3 n3 r2 u v : Nat} (h : w3C mul HL R1 R2 R3 n3 r2 u v = true) :
    Nat.land v 131071 < n3 ∧ Nat.shiftRight v 17 < 128 ∧
      Nat.land (r3L R3 (Nat.land v 131071)) 4095 = r2 ∧
      mul (hL HL (Nat.shiftRight v 17)) (r2u1 R1 R2 r2) =
        mul (r2u1 R1 R2 r2) (hL HL (Nat.shiftRight v 17)) ∧
      mul (hL HL (Nat.shiftRight v 17)) (r2u2 R2 r2) =
        mul (r2u2 R2 r2) (hL HL (Nat.shiftRight v 17)) ∧
      mul (hL HL (Nat.shiftRight v 17)) u =
        mul (Nat.land (Nat.shiftRight (r3L R3 (Nat.land v 131071)) 12) 8191)
          (hL HL (Nat.shiftRight v 17)) := by
  simp only [w3C, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1.1.1.1, Nat.le_of_ble_eq_true h.1.1.1.1.2,
    Nat.eq_of_beq_eq_true h.1.1.1.2, Nat.eq_of_beq_eq_true h.1.1.2, Nat.eq_of_beq_eq_true h.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

theorem s13_edge (M : IsModel (⊤ : Subgroup X) n mul dec) (hT : treeB n 4 mul GS PT = true)
    {IM f x s : Nat} (γ : MulAut X)
    (hIM : ∀ i < 4, l16 IM i < n ∧ dec (l16 IM i) = γ (dec (l16 GS i))) (hx : x < n)
    (hs : s < 4) (h1 : ptDep PT x < f) (h2 : ptDep PT (mul (l16 GS s) x) < f) :
    fpK mul PT IM f (mul (l16 GS s) x) = mul (l16 IM s) (fpK mul PT IM f x) := by
  have hg := treeB_gen hT hs
  obtain ⟨a1, a2⟩ := s14_fpK M hT γ hIM f x hx h1
  obtain ⟨b1, b2⟩ := s14_fpK M hT γ hIM f _ (M.mul_lt _ hg _ hx) h2
  obtain ⟨i1, i2⟩ := hIM s hs
  apply M.inj _ b1 _ (M.mul_lt _ i1 _ a1)
  rw [b2, M.dec_mul _ hg _ hx, map_mul, M.dec_mul _ i1 _ a1, i2, a2]

theorem s13_l16_land (T : Nat) {i : Nat} (hi : i < 4) :
    l16 (Nat.land T 18446744073709551615) i = l16 T i := by
  have e : Nat.land T 18446744073709551615 = T % 2 ^ 64 := Nat.and_two_pow_sub_one_eq_mod T 64
  rw [e, s14_l16, s14_l16]
  interval_cases i <;> simp only [Nat.reduceMul, Nat.reducePow] <;> omega

theorem search_complete (M : IsModel (⊤ : Subgroup X) 8192 mul dec) {GS PT t : Nat}
    (hT : treeB 8192 4 mul GS PT = true) (ht : l16 GS 0 = t)
    {OT LB RP CZ HL CW GI PV CL1 CL2 CL3 RK1 RK2 RK3 R1 W1 R2 R3 AI : Nat} {W2 W3 : Nat → Nat}
    {nl c1 c2 c3 n1 n2 n3 na : Nat}
    (hord : ordOK 8192 mul OT = true) (hlab : labOK 8192 mul GS GI LB RP nl = true)
    (hcz : czOK 8192 LB CZ 0 nl = true)
    (hH : hOK 8192 mul t HL = true)
    (hc1 : cmOK 8192 mul t OT LB CZ HL (l16 GS 1) (lane CW 8 255 0) CL1 RK1 c1 = true)
    (hc2 : cmOK 8192 mul t OT LB CZ HL (l16 GS 2) (lane CW 8 255 1) CL2 RK2 c2 = true)
    (hc3 : cmOK 8192 mul t OT LB CZ HL (l16 GS 3) (lane CW 8 255 2) CL3 RK3 c3 = true)
    (hpv : pvOK mul t OT GS PV = true) (h1 : lvl1B mul HL CL1 c1 R1 W1 n1 = true)
    (h2 : allB n1 (fun r1 => lvl2At mul t OT HL CL2 c2 R1 R2 PV n2 (W2 r1) r1) = true)
    (h3 : allFrom 0 n2 (fun r2 => lvl3At mul t OT HL CL3 c3 R1 R2 R3 PV n3 (W3 r2) r2) = true)
    (hr3 : allFrom 0 n3 (fun r3 => Nat.blt (Nat.land (r3L R3 r3) 4095) n2 &&
      outC 8192 mul GS PT AI na (r3IM t R1 R2 R3 r3) (Nat.shiftRight (r3L R3 r3) 25)) = true)
    (hu2 : allB n2 (fun r2 => Nat.blt (r2u2 R2 r2) 8192) = true)
    (α : MulAut X) (hα : α (dec t) = dec t) :
    ∃ h : X, h * dec t = dec t * h ∧ ∃ a < na, ∀ i < 4,
      h * α (dec (l16 GS i)) * h⁻¹ = dec (l16 (Nat.shiftRight AI (Nat.mul 64 a)) i) := by
  have hg : ∀ i < 4, l16 GS i < 8192 := fun i hi => treeB_gen hT hi
  have ht8 : t < 8192 := by
    rw [← ht]
    exact hg 0 (by norm_num)
  obtain ⟨hHL, -⟩ := s13_hParts hH
  obtain ⟨pv0, pv1, pv2⟩ := s13_pvParts hpv
  have hR : ∀ T i, lane T 13 8191 i < 8192 := fun T i => by
    have := lane_le T 13 8191 i
    omega
  obtain ⟨u, hu, hdu⟩ : ∃ u < 8192, dec u = α (dec (l16 GS 1)) :=
    ⟨_, M.code_lt (mem_top _), M.dec_code (mem_top _)⟩
  obtain ⟨hk1, hcl1⟩ := s13_cand M hord hT hlab hcz hH ht8 hc1 (hg 1 (by norm_num)) α hα hu hdu
  have hw1 : w1C mul HL R1 n1 (clL CL1 (rkL RK1 u)) (lane W1 16 65535 (rkL RK1 u)) = true :=
    allB_eq_true.1 h1 _ hk1
  rw [hcl1] at hw1
  obtain ⟨hr1, hj1, hm1⟩ := s13_w1 hw1
  generalize Nat.land (lane W1 16 65535 (rkL RK1 u)) 511 = r1 at hr1 hm1
  generalize Nat.shiftRight (lane W1 16 65535 (rkL RK1 u)) 9 = j1 at hj1 hm1
  obtain ⟨hH1, hH1t⟩ := hHL j1 hj1
  have c1 := s14_conj_eq M hH1 hu (hR R1 r1) hm1
  have ct1 := s14_conj_eq M hH1 ht8 ht8 hH1t
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ : MulAut X, ∀ x, γ x = dec (hL HL j1) * α x * (dec (hL HL j1))⁻¹ :=
    ⟨MulAut.conj _ * α, fun x => by rw [MulAut.mul_apply, MulAut.conj_apply]⟩
  have g10 : γ₁ (dec t) = dec t := by rw [hγ₁, hα, ct1]
  have g11 : γ₁ (dec (l16 GS 1)) = dec (lane R1 13 8191 r1) := by rw [hγ₁, ← hdu, c1]
  obtain ⟨u', hu', hdu'⟩ : ∃ u < 8192, dec u = γ₁ (dec (l16 GS 2)) :=
    ⟨_, M.code_lt (mem_top _), M.dec_code (mem_top _)⟩
  obtain ⟨hk2, hcl2⟩ := s13_cand M hord hT hlab hcz hH ht8 hc2 (hg 2 (by norm_num)) γ₁ g10 hu' hdu'
  have hip2 : ipE mul t OT (lane PV 8 255 0) (lane R1 13 8191 r1) u' = true :=
    s13_ipE M hord γ₁ g10 (hg 1 (by norm_num)) (hg 2 (by norm_num)) (hR R1 r1) hu' ht8 g11.symm
      hdu' pv0
  have hl2 : lvl2At mul t OT HL CL2 c2 R1 R2 PV n2 (W2 r1) r1 = true := allB_eq_true.1 h2 r1 hr1
  have hw2 : (!ipE mul t OT (lane PV 8 255 0) (lane R1 13 8191 r1) (clL CL2 (rkL RK2 u')) ||
      w2C mul HL R1 R2 n2 r1 (clL CL2 (rkL RK2 u')) (lane (W2 r1) 20 1048575 (rkL RK2 u'))) =
      true := allB_eq_true.1 hl2 _ hk2
  rw [hcl2, hip2, Bool.not_true, Bool.false_or] at hw2
  obtain ⟨hr2, hj2, hp1, hm2a, hm2b⟩ := s13_w2 hw2
  generalize Nat.land (lane (W2 r1) 20 1048575 (rkL RK2 u')) 4095 = r2 at hr2 hp1 hm2b
  generalize Nat.shiftRight (lane (W2 r1) 20 1048575 (rkL RK2 u')) 12 = j2 at hj2 hm2a hm2b
  have hU2 : r2u2 R2 r2 < 8192 := Nat.le_of_ble_eq_true (allB_eq_true.1 hu2 r2 hr2)
  have hr2u1 : r2u1 R1 R2 r2 = lane R1 13 8191 r1 := by
    unfold r2u1
    rw [hp1]
  have hU1 : r2u1 R1 R2 r2 < 8192 := by
    rw [hr2u1]
    exact hR R1 r1
  obtain ⟨hH2, hH2t⟩ := hHL j2 hj2
  have c2 := s14_conj_eq M hH2 hu' hU2 hm2b
  have ct2 := s14_conj_eq M hH2 ht8 ht8 hH2t
  have cr2 := s14_conj_eq M hH2 (hR R1 r1) (hR R1 r1) hm2a
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ : MulAut X, ∀ x, γ x = dec (hL HL j2) * γ₁ x * (dec (hL HL j2))⁻¹ :=
    ⟨MulAut.conj _ * γ₁, fun x => by rw [MulAut.mul_apply, MulAut.conj_apply]⟩
  have g20 : γ₂ (dec t) = dec t := by rw [hγ₂, g10, ct2]
  have g21 : γ₂ (dec (l16 GS 1)) = dec (r2u1 R1 R2 r2) := by rw [hγ₂, g11, cr2, hr2u1]
  have g22 : γ₂ (dec (l16 GS 2)) = dec (r2u2 R2 r2) := by rw [hγ₂, ← hdu', c2]
  obtain ⟨v, hv, hdv⟩ : ∃ u < 8192, dec u = γ₂ (dec (l16 GS 3)) :=
    ⟨_, M.code_lt (mem_top _), M.dec_code (mem_top _)⟩
  obtain ⟨hk3, hcl3⟩ := s13_cand M hord hT hlab hcz hH ht8 hc3 (hg 3 (by norm_num)) γ₂ g20 hv hdv
  have hip13 : ipE mul t OT (lane PV 8 255 1) (r2u1 R1 R2 r2) v = true :=
    s13_ipE M hord γ₂ g20 (hg 1 (by norm_num)) (hg 3 (by norm_num)) hU1 hv ht8 g21.symm hdv pv1
  have hip23 : ipE mul t OT (lane PV 8 255 2) (r2u2 R2 r2) v = true :=
    s13_ipE M hord γ₂ g20 (hg 2 (by norm_num)) (hg 3 (by norm_num)) hU2 hv ht8 g22.symm hdv pv2
  have hl3 : lvl3At mul t OT HL CL3 c3 R1 R2 R3 PV n3 (W3 r2) r2 = true := by
    have := allFrom_get h3 hr2
    rwa [Nat.zero_add] at this
  have hw3 : (!ipE mul t OT (lane PV 8 255 1) (r2u1 R1 R2 r2) (clL CL3 (rkL RK3 v)) ||
      !ipE mul t OT (lane PV 8 255 2) (r2u2 R2 r2) (clL CL3 (rkL RK3 v)) ||
      w3C mul HL R1 R2 R3 n3 r2 (clL CL3 (rkL RK3 v)) (lane (W3 r2) 24 16777215 (rkL RK3 v))) =
      true := allB_eq_true.1 hl3 _ hk3
  rw [hcl3, hip13, hip23, Bool.not_true, Bool.false_or, Bool.false_or] at hw3
  obtain ⟨hq3, hj3, hp3, hm3a, hm3b, hm3c⟩ := s13_w3 hw3
  generalize Nat.land (lane (W3 r2) 24 16777215 (rkL RK3 v)) 131071 = r3 at hq3 hp3 hm3c
  generalize Nat.shiftRight (lane (W3 r2) 24 16777215 (rkL RK3 v)) 17 = j3 at hj3 hm3a hm3b hm3c
  have hV : Nat.land (Nat.shiftRight (r3L R3 r3) 12) 8191 < 8192 :=
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  obtain ⟨hH3, hH3t⟩ := hHL j3 hj3
  have c3 := s14_conj_eq M hH3 hv hV hm3c
  have ct3 := s14_conj_eq M hH3 ht8 ht8 hH3t
  have cu1 := s14_conj_eq M hH3 hU1 hU1 hm3a
  have cu2 := s14_conj_eq M hH3 hU2 hU2 hm3b
  obtain ⟨γ₃, hγ₃⟩ : ∃ γ : MulAut X, ∀ x, γ x = dec (hL HL j3) * γ₂ x * (dec (hL HL j3))⁻¹ :=
    ⟨MulAut.conj _ * γ₂, fun x => by rw [MulAut.mul_apply, MulAut.conj_apply]⟩
  have g30 : γ₃ (dec t) = dec t := by rw [hγ₃, g20, ct3]
  have g31 : γ₃ (dec (l16 GS 1)) = dec (r2u1 R1 R2 r2) := by rw [hγ₃, g21, cu1]
  have g32 : γ₃ (dec (l16 GS 2)) = dec (r2u2 R2 r2) := by rw [hγ₃, g22, cu2]
  have g33 : γ₃ (dec (l16 GS 3)) = dec (Nat.land (Nat.shiftRight (r3L R3 r3) 12) 8191) := by
    rw [hγ₃, ← hdv, c3]
  have hγ : ∀ x, dec (hL HL j3) * dec (hL HL j2) * dec (hL HL j1) * α x *
      (dec (hL HL j3) * dec (hL HL j2) * dec (hL HL j1))⁻¹ = γ₃ x := by
    intro x
    rw [hγ₃, hγ₂, hγ₁]
    group
  have ho := allFrom_get hr3 hq3
  rw [Nat.zero_add, Bool.and_eq_true] at ho
  have hIMe : r3IM t R1 R2 R3 r3 = e14Im t (r2u1 R1 R2 r2) (r2u2 R2 r2)
      (Nat.land (Nat.shiftRight (r3L R3 r3) 12) 8191) := by
    unfold r3IM
    rw [hp3]
    rfl
  have ho2 := ho.2
  rw [hIMe] at ho2
  have hIM := s14_im M (by norm_num) ht8 hU1 hU2 hV γ₃ (by rw [ht, g30]) g31 g32 g33
  generalize Nat.shiftRight (r3L R3 r3) 25 = o at ho2
  unfold outC at ho2
  cases hb : Nat.beq (Nat.land o 1) 0
  · rw [hb, cond_false] at ho2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ho2
    obtain ⟨⟨⟨⟨hx, hs⟩, hd1⟩, hd2⟩, hne⟩ := ho2
    exact absurd (s13_edge M hT γ₃ hIM (Nat.le_of_ble_eq_true hx) (Nat.le_of_ble_eq_true hs)
      (Nat.le_of_ble_eq_true hd1) (Nat.le_of_ble_eq_true hd2)) (Nat.ne_of_beq_eq_false hne)
  · rw [hb, cond_true, Bool.and_eq_true] at ho2
    obtain ⟨ha, hAI⟩ := ho2
    refine ⟨dec (hL HL j3) * dec (hL HL j2) * dec (hL HL j1), ?_, Nat.shiftRight o 1,
      Nat.le_of_ble_eq_true ha, fun i hi => ?_⟩
    · rw [← mul_inv_eq_iff_eq_mul]
      have e := hγ (dec t)
      rw [hα] at e
      rw [e, g30]
    · rw [hγ, ← (hIM i hi).2, ← Nat.eq_of_beq_eq_true hAI, s13_l16_land _ hi]

end Certificates.KernelTower
