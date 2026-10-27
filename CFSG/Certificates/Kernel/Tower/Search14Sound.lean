module

public import CFSG.Certificates.Kernel.Tower.Cls14Sound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower Subgroup

variable {X : Type*} [Group X] {n : Nat} {mul : Nat → Nat → Nat} {dec : Nat → X}

theorem s14_sqK (M : IsModel (⊤ : Subgroup X) n mul dec) {c : Nat} (hc : c < n) :
    ∀ k, sqK mul c k < n ∧ dec (sqK mul c k) = dec c ^ (2 ^ k) := by
  intro k
  induction k with
  | zero =>
    refine ⟨hc, ?_⟩
    rw [pow_zero, pow_one]
    rfl
  | succ k ih =>
    rw [cls16_sqK_succ]
    refine ⟨M.mul_lt _ ih.1 _ ih.1, ?_⟩
    rw [M.dec_mul _ ih.1 _ ih.1, ih.2, ← pow_add]
    congr 1
    rw [pow_succ]
    omega

theorem s14_sqK_zero (M : IsModel (⊤ : Subgroup X) n mul dec) {c : Nat} (hc : c < n) (k : Nat) :
    sqK mul c k = 0 ↔ dec c ^ (2 ^ k) = 1 := by
  rw [← (s14_sqK M hc k).2, M.dec_eq_one_iff (s14_sqK M hc k).1]

theorem s14_oe_le (M : IsModel (⊤ : Subgroup X) n mul dec) {a b e e' : Nat} (ha : a < n)
    (hb : b < n) (hab : ∀ k, dec a ^ (2 ^ k) = 1 ↔ dec b ^ (2 ^ k) = 1)
    (he : ordC mul a e = true) (he' : ordC mul b e' = true) : e ≤ e' := by
  obtain ⟨-, h2⟩ := cls16_ordC_parts he
  obtain ⟨h1', -⟩ := cls16_ordC_parts he'
  rw [s14_sqK_zero M hb] at h1'
  by_contra hlt
  rcases h2 with h2 | ⟨h2, h3⟩
  · omega
  · apply h3
    rw [s14_sqK_zero M ha, hab]
    have e1 : 2 ^ (e - 1) = 2 ^ e' * 2 ^ (e - 1 - e') := by
      rw [← pow_add]
      congr 1
      omega
    rw [e1, pow_mul, h1', one_pow]

theorem s14_oe_aut (M : IsModel (⊤ : Subgroup X) n mul dec) {OT : Nat}
    (hord : ordOK n mul OT = true) (γ : MulAut X) {a b : Nat} (ha : a < n) (hb : b < n)
    (h : dec b = γ (dec a)) : oe OT b = oe OT a := by
  have hab : ∀ k, dec b ^ (2 ^ k) = 1 ↔ dec a ^ (2 ^ k) = 1 := fun k => by
    rw [h, ← map_pow, map_eq_one_iff _ γ.injective]
  exact le_antisymm (s14_oe_le M hb ha hab (allB_eq_true.1 hord b hb) (allB_eq_true.1 hord a ha))
    (s14_oe_le M ha hb (fun k => (hab k).symm) (allB_eq_true.1 hord a ha)
      (allB_eq_true.1 hord b hb))

theorem s14_card_orbit (γ : MulAut X) (x : X) :
    Nat.card (MulAction.orbit (ConjAct X) (γ x)) = Nat.card (MulAction.orbit (ConjAct X) x) := by
  have e : MulAction.orbit (ConjAct X) (γ x) = γ '' MulAction.orbit (ConjAct X) x := by
    ext y
    simp only [MulAction.mem_orbit_iff, Set.mem_image, ConjAct.smul_def]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨γ.symm (ConjAct.ofConjAct g) * x * (γ.symm (ConjAct.ofConjAct g))⁻¹,
        ⟨ConjAct.toConjAct (γ.symm (ConjAct.ofConjAct g)), by rw [ConjAct.ofConjAct_toConjAct]⟩, ?_⟩
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · rintro ⟨z, ⟨g, rfl⟩, rfl⟩
      refine ⟨ConjAct.toConjAct (γ (ConjAct.ofConjAct g)), ?_⟩
      rw [ConjAct.ofConjAct_toConjAct, map_mul, map_mul, map_inv]
  rw [e, Nat.card_image_of_injective γ.injective]

theorem s14_mul_aut (M : IsModel (⊤ : Subgroup X) n mul dec) (γ : MulAut X) {a b a' b' : Nat}
    (ha : a < n) (hb : b < n) (ha' : a' < n) (hb' : b' < n) (h1 : dec a' = γ (dec a))
    (h2 : dec b' = γ (dec b)) :
    mul a b < n ∧ mul a' b' < n ∧ dec (mul a' b') = γ (dec (mul a b)) :=
  ⟨M.mul_lt _ ha _ hb, M.mul_lt _ ha' _ hb', by
    rw [M.dec_mul _ ha' _ hb', M.dec_mul _ ha _ hb, map_mul, h1, h2]⟩

variable {GS PT GI LB RP nl OT CZ : Nat}

theorem s14_ocOf_aut (M : IsModel (⊤ : Subgroup X) n mul dec) (hn : n < 32768)
    (hT : treeB n 4 mul GS PT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true)
    (hord : ordOK n mul OT = true) (hcz : czOK16 n LB CZ = true) (γ : MulAut X) {a b : Nat}
    (ha : a < n) (hb : b < n) (h : dec b = γ (dec a)) : ocOf OT LB CZ b = ocOf OT LB CZ a := by
  unfold ocOf cz15
  rw [s14_oe_aut M hord γ ha hb h, ← cls16_card M hn hT hlab hcz hb,
    ← cls16_card M hn hT hlab hcz ha, h, s14_card_orbit]

theorem s14_ivOf_aut (M : IsModel (⊤ : Subgroup X) n mul dec) (hn : n < 32768)
    (hT : treeB n 4 mul GS PT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true)
    (hord : ordOK n mul OT = true) (hcz : czOK16 n LB CZ = true) (γ : MulAut X)
    {s u s' u' : Nat} (hs : s < n) (hu : u < n) (hs' : s' < n) (hu' : u' < n)
    (hS : dec s' = γ (dec s)) (hU : dec u' = γ (dec u)) :
    ivOf mul OT LB CZ s' u' = ivOf mul OT LB CZ s u := by
  obtain ⟨m1, m1', e1⟩ := s14_mul_aut M γ hu hs hu' hs' hU hS
  unfold ivOf
  rw [s14_ocOf_aut M hn hT hlab hord hcz γ hu hu' hU, s14_ocOf_aut M hn hT hlab hord hcz γ m1 m1' e1]

theorem s14_pvOf_aut (M : IsModel (⊤ : Subgroup X) n mul dec) (hn : n < 32768)
    (hT : treeB n 4 mul GS PT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true)
    (hord : ordOK n mul OT = true) (hcz : czOK16 n LB CZ = true) (γ : MulAut X)
    {s x y s' x' y' : Nat} (hs : s < n) (hx : x < n) (hy : y < n) (hs' : s' < n) (hx' : x' < n)
    (hy' : y' < n) (hS : dec s' = γ (dec s)) (hX : dec x' = γ (dec x))
    (hY : dec y' = γ (dec y)) :
    pvOf16 mul OT LB CZ s' x' y' = pvOf16 mul OT LB CZ s x y := by
  obtain ⟨m1, m1', e1⟩ := s14_mul_aut M γ hx hy hx' hy' hX hY
  obtain ⟨m2, m2', e2⟩ := s14_mul_aut M γ hx hs hx' hs' hX hS
  obtain ⟨m3, m3', e3⟩ := s14_mul_aut M γ m2 hy m2' hy' e2 hY
  obtain ⟨m4, m4', e4⟩ := s14_mul_aut M γ hx hx hx' hx' hX hX
  obtain ⟨m5, m5', e5⟩ := s14_mul_aut M γ m4 hy m4' hy' e4 hY
  obtain ⟨m6, m6', e6⟩ := s14_mul_aut M γ m1 hy m1' hy' e1 hY
  unfold pvOf16
  rw [s14_ocOf_aut M hn hT hlab hord hcz γ m1 m1' e1, s14_ocOf_aut M hn hT hlab hord hcz γ m3 m3' e3,
    s14_ocOf_aut M hn hT hlab hord hcz γ m5 m5' e5, s14_ocOf_aut M hn hT hlab hord hcz γ m6 m6' e6]

theorem s14_hParts {t HL : Nat} (h : hOK16 n mul t HL = true) :
    t < n ∧ ∀ j < 256, l16 HL j < n ∧ mul (l16 HL j) t = mul t (l16 HL j) := by
  simp only [hOK16, Bool.and_eq_true, allB_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1.1, fun j hj =>
    ⟨Nat.le_of_ble_eq_true (h.1.1.2 j hj).1, Nat.eq_of_beq_eq_true (h.1.1.2 j hj).2⟩⟩

theorem s14_kyParts {KY PV : Nat} (h : kyOK mul OT LB CZ GS KY PV = true) :
    kyL KY 0 = ivOf mul OT LB CZ (l16 GS 0) (l16 GS 1) ∧
      kyL KY 1 = ivOf mul OT LB CZ (l16 GS 0) (l16 GS 2) ∧
      kyL KY 2 = ivOf mul OT LB CZ (l16 GS 0) (l16 GS 3) ∧
      pvL PV 0 = pvOf16 mul OT LB CZ (l16 GS 0) (l16 GS 1) (l16 GS 2) ∧
      pvL PV 1 = pvOf16 mul OT LB CZ (l16 GS 0) (l16 GS 1) (l16 GS 3) ∧
      pvL PV 2 = pvOf16 mul OT LB CZ (l16 GS 0) (l16 GS 2) (l16 GS 3) := by
  simp only [kyOK, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1.1.1.1, Nat.eq_of_beq_eq_true h.1.1.1.1.2,
    Nat.eq_of_beq_eq_true h.1.1.1.2, Nat.eq_of_beq_eq_true h.1.1.2, Nat.eq_of_beq_eq_true h.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

theorem s14_cand {t K CL RK c u : Nat} (hc : cmOK16 n mul t OT LB CZ K CL RK c = true)
    (hu : u < n) (hK : ivOf mul OT LB CZ t u = K) : rkL RK u < c ∧ l16 CL (rkL RK u) = u := by
  have h : (!Nat.beq (ivOf mul OT LB CZ t u) K ||
      (Nat.blt (rkL RK u) c && Nat.beq (l16 CL (rkL RK u)) u)) = true := allB_eq_true.1 hc u hu
  rw [hK, Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem s14_w1 {HL R1 n1 u v : Nat} (h : e14W1 n mul HL R1 n1 u v = true) :
    Nat.land v 511 < n1 ∧ Nat.shiftRight v 9 < 256 ∧ l16 R1 (Nat.land v 511) < n ∧
      mul (l16 HL (Nat.shiftRight v 9)) u =
        mul (l16 R1 (Nat.land v 511)) (l16 HL (Nat.shiftRight v 9)) := by
  simp only [e14W1, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1.1, Nat.le_of_ble_eq_true h.1.1.2,
    Nat.le_of_ble_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem s14_w2 {HL R1 R2 n2 r1 u v : Nat} (h : e14W2 n mul HL R1 R2 n2 r1 u v = true) :
    Nat.land v 4095 < n2 ∧ Nat.shiftRight v 12 < 256 ∧ e14P1 R2 (Nat.land v 4095) = r1 ∧
      e14P2 R2 (Nat.land v 4095) < n ∧
      mul (l16 HL (Nat.shiftRight v 12)) (l16 R1 r1) =
        mul (l16 R1 r1) (l16 HL (Nat.shiftRight v 12)) ∧
      mul (l16 HL (Nat.shiftRight v 12)) u =
        mul (e14P2 R2 (Nat.land v 4095)) (l16 HL (Nat.shiftRight v 12)) := by
  simp only [e14W2, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1.1.1.1, Nat.le_of_ble_eq_true h.1.1.1.1.2,
    Nat.eq_of_beq_eq_true h.1.1.1.2, Nat.le_of_ble_eq_true h.1.1.2, Nat.eq_of_beq_eq_true h.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

theorem s14_conj_eq (M : IsModel (⊤ : Subgroup X) n mul dec) {a u r : Nat} (ha : a < n)
    (hu : u < n) (hr : r < n) (h : mul a u = mul r a) : dec a * dec u * (dec a)⁻¹ = dec r := by
  have h1 := congrArg dec h
  rw [M.dec_mul _ ha _ hu, M.dec_mul _ hr _ ha] at h1
  rw [h1, mul_inv_cancel_right]

theorem s14_conj_mul (a b y : X) : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group

theorem s14_l16 (T i : Nat) : l16 T i = T / 2 ^ (16 * i) % 65536 := lane_eq T 16 i

theorem s14_e14Im {t u1 u2 v : Nat} (ht : t < 65536) (h1 : u1 < 65536) (h2 : u2 < 65536)
    (hv : v < 65536) :
    l16 (e14Im t u1 u2 v) 0 = t ∧ l16 (e14Im t u1 u2 v) 1 = u1 ∧ l16 (e14Im t u1 u2 v) 2 = u2 ∧
      l16 (e14Im t u1 u2 v) 3 = v := by
  have e : e14Im t u1 u2 v = t + (u1 * 2 ^ 16 + (u2 * 2 ^ 32 + v * 2 ^ 48)) := by
    change t + (u1 <<< 16 + (u2 <<< 32 + v <<< 48)) = _
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  simp only [s14_l16, e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem s14_fpK (M : IsModel (⊤ : Subgroup X) n mul dec) (hT : treeB n 4 mul GS PT = true)
    {IM : Nat} (γ : MulAut X) (hIM : ∀ i < 4, l16 IM i < n ∧ dec (l16 IM i) = γ (dec (l16 GS i))) :
    ∀ f, ∀ c < n, ptDep PT c < f → fpK mul PT IM f c < n ∧ dec (fpK mul PT IM f c) = γ (dec c) := by
  intro f
  induction f with
  | zero => intro c _ h; omega
  | succ f ih =>
    intro c hc hd
    by_cases h0 : c = 0
    · subst h0
      have e0 : fpK mul PT IM (f + 1) 0 = 0 := rfl
      rw [e0, M.dec_zero, map_one]
      exact ⟨M.zero_lt, rfl⟩
    · obtain ⟨hgi, hpar, hdep, hmul⟩ := treeB_get hT hc h0
      obtain ⟨ih1, ih2⟩ := ih _ hpar (by omega)
      have hb : Nat.beq c 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      have e0 : fpK mul PT IM (f + 1) c =
          mul (l16 IM (ptGi PT c)) (fpK mul PT IM f (ptPar PT c)) := by
        change cond (Nat.beq c 0) 0 (mul (l16 IM (ptGi PT c)) (fpK mul PT IM f (ptPar PT c))) = _
        rw [hb]
        rfl
      obtain ⟨hi1, hi2⟩ := hIM _ hgi
      rw [e0]
      refine ⟨M.mul_lt _ hi1 _ ih1, ?_⟩
      rw [M.dec_mul _ hi1 _ ih1, hi2, ih2, ← map_mul, ← M.dec_mul _ (treeB_gen hT hgi) _ hpar, hmul]

theorem s14_sp_false (M : IsModel (⊤ : Subgroup X) n mul dec) (hT : treeB n 4 mul GS PT = true)
    {IM f o : Nat} (γ : MulAut X)
    (hIM : ∀ i < 4, l16 IM i < n ∧ dec (l16 IM i) = γ (dec (l16 GS i)))
    (hx : Nat.land o 16383 < n) (hs : Nat.shiftRight o 14 < 4) :
    e14Sp mul GS PT IM f o = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [e14Sp, Bool.and_eq_true, Bool.not_eq_true'] at h
  generalize Nat.shiftRight o 14 = s at hs h
  generalize Nat.land o 16383 = x at hx h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hg := treeB_gen hT hs
  have hgx := M.mul_lt _ hg _ hx
  obtain ⟨a1, a2⟩ := s14_fpK M hT γ hIM f x hx (Nat.le_of_ble_eq_true h1)
  obtain ⟨b1, b2⟩ := s14_fpK M hT γ hIM f _ hgx (Nat.le_of_ble_eq_true h2)
  obtain ⟨i1, i2⟩ := hIM s hs
  apply Nat.ne_of_beq_eq_false h3
  apply M.inj _ b1 _ (M.mul_lt _ i1 _ a1)
  rw [b2, M.dec_mul _ hg _ hx, map_mul, M.dec_mul _ i1 _ a1, i2, a2]

theorem s14_lvl12 (M : IsModel (⊤ : Subgroup X) n mul dec) (hn : n < 32768) {t HL KY PV CL1 CL2 RK1 RK2 R1 W1 R2 : Nat}
    {W2 : Nat → Nat} {c1 c2 n1 n2 : Nat} (hT : treeB n 4 mul GS PT = true)
    (hord : ordOK n mul OT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true)
    (hcz : czOK16 n LB CZ = true) (hH : hOK16 n mul t HL = true)
    (hky : kyOK mul OT LB CZ GS KY PV = true)
    (hc1 : cmOK16 n mul t OT LB CZ (kyL KY 0) CL1 RK1 c1 = true)
    (hc2 : cmOK16 n mul t OT LB CZ (kyL KY 1) CL2 RK2 c2 = true)
    (h1 : e14Lvl1 n mul HL CL1 c1 R1 W1 n1 = true)
    (h2 : allB n1 (fun r1 => e14Lvl2 n mul OT LB CZ t HL CL2 c2 R1 R2 (pvL PV 0) n2 (W2 r1) r1) = true)
    (β : MulAut X) (hβ : β (dec (l16 GS 0)) = dec t) :
    ∃ h : X, h * dec t = dec t * h ∧ ∃ r2 < n2, l16 R1 (e14P1 R2 r2) < n ∧ e14P2 R2 r2 < n ∧
      h * β (dec (l16 GS 1)) * h⁻¹ = dec (l16 R1 (e14P1 R2 r2)) ∧
      h * β (dec (l16 GS 2)) * h⁻¹ = dec (e14P2 R2 r2) := by
  obtain ⟨ht, hHL⟩ := s14_hParts hH
  obtain ⟨k0, k1, -, p0, -, -⟩ := s14_kyParts hky
  have hg : ∀ i < 4, l16 GS i < n := fun i hi => treeB_gen hT hi
  have hg0 := hg 0 (by norm_num)
  obtain ⟨u, hu, hdu⟩ : ∃ u < n, dec u = β (dec (l16 GS 1)) :=
    ⟨_, M.code_lt (mem_top _), M.dec_code (mem_top _)⟩
  have hK1 : ivOf mul OT LB CZ t u = kyL KY 0 := by
    rw [k0]
    exact s14_ivOf_aut M hn hT hlab hord hcz β hg0 (hg 1 (by norm_num)) ht hu hβ.symm hdu
  obtain ⟨hk1, hcl1⟩ := s14_cand hc1 hu hK1
  have hw1 : e14W1 n mul HL R1 n1 (l16 CL1 (rkL RK1 u)) (lane W1 32 4294967295 (rkL RK1 u)) =
      true := allB_eq_true.1 h1 _ hk1
  rw [hcl1] at hw1
  obtain ⟨hr1, hj1, hR1, hm1⟩ := s14_w1 hw1
  generalize Nat.land (lane W1 32 4294967295 (rkL RK1 u)) 511 = r1 at hr1 hR1 hm1
  generalize Nat.shiftRight (lane W1 32 4294967295 (rkL RK1 u)) 9 = j1 at hj1 hm1
  obtain ⟨hH1, hH1t⟩ := hHL j1 hj1
  have c1 := s14_conj_eq M hH1 hu hR1 hm1
  have ct1 := s14_conj_eq M hH1 ht ht hH1t
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ : MulAut X, ∀ x, γ x = dec (l16 HL j1) * β x * (dec (l16 HL j1))⁻¹ :=
    ⟨MulAut.conj _ * β, fun x => by rw [MulAut.mul_apply, MulAut.conj_apply]⟩
  have g10 : γ₁ (dec (l16 GS 0)) = dec t := by rw [hγ₁, hβ, ct1]
  have g11 : γ₁ (dec (l16 GS 1)) = dec (l16 R1 r1) := by rw [hγ₁, ← hdu, c1]
  obtain ⟨u', hu', hdu'⟩ : ∃ u < n, dec u = γ₁ (dec (l16 GS 2)) :=
    ⟨_, M.code_lt (mem_top _), M.dec_code (mem_top _)⟩
  have hK2 : ivOf mul OT LB CZ t u' = kyL KY 1 := by
    rw [k1]
    exact s14_ivOf_aut M hn hT hlab hord hcz γ₁ hg0 (hg 2 (by norm_num)) ht hu' g10.symm hdu'
  have hP : pvOf16 mul OT LB CZ t (l16 R1 r1) u' = pvL PV 0 := by
    rw [p0]
    exact s14_pvOf_aut M hn hT hlab hord hcz γ₁ hg0 (hg 1 (by norm_num)) (hg 2 (by norm_num)) ht
      hR1 hu' g10.symm g11.symm hdu'
  obtain ⟨hk2, hcl2⟩ := s14_cand hc2 hu' hK2
  have hl2 : e14Lvl2 n mul OT LB CZ t HL CL2 c2 R1 R2 (pvL PV 0) n2 (W2 r1) r1 = true :=
    allB_eq_true.1 h2 r1 hr1
  have hw2 : (!Nat.beq (pvOf16 mul OT LB CZ t (l16 R1 r1) (l16 CL2 (rkL RK2 u'))) (pvL PV 0) ||
      e14W2 n mul HL R1 R2 n2 r1 (l16 CL2 (rkL RK2 u'))
        (lane (W2 r1) 32 4294967295 (rkL RK2 u'))) = true := allB_eq_true.1 hl2 _ hk2
  rw [hcl2, hP, Nat.beq_refl, Bool.not_true, Bool.false_or] at hw2
  obtain ⟨hr2, hj2, hp1, hp2, hm2a, hm2b⟩ := s14_w2 hw2
  generalize Nat.land (lane (W2 r1) 32 4294967295 (rkL RK2 u')) 4095 = r2 at hr2 hp1 hp2 hm2b
  generalize Nat.shiftRight (lane (W2 r1) 32 4294967295 (rkL RK2 u')) 12 = j2 at hj2 hm2a hm2b
  obtain ⟨hH2, hH2t⟩ := hHL j2 hj2
  have c2 := s14_conj_eq M hH2 hu' hp2 hm2b
  have ct2 := s14_conj_eq M hH2 ht ht hH2t
  have cr2 := s14_conj_eq M hH2 hR1 hR1 hm2a
  refine ⟨dec (l16 HL j2) * dec (l16 HL j1), ?_, r2, hr2, by rw [hp1]; exact hR1, hp2, ?_, ?_⟩
  · rw [← mul_inv_eq_iff_eq_mul, s14_conj_mul, ct1, ct2]
  · rw [hp1, s14_conj_mul, ← hγ₁, g11, cr2]
  · rw [s14_conj_mul, ← hγ₁, ← hdu', c2]

theorem s14_im (M : IsModel (⊤ : Subgroup X) n mul dec) (hn : n ≤ 65536) {t u1 u2 v : Nat}
    (ht : t < n) (h1 : u1 < n) (h2 : u2 < n) (hv : v < n) (γ : MulAut X)
    (g0 : γ (dec (l16 GS 0)) = dec t) (g1 : γ (dec (l16 GS 1)) = dec u1)
    (g2 : γ (dec (l16 GS 2)) = dec u2) (g3 : γ (dec (l16 GS 3)) = dec v) :
    ∀ i < 4, l16 (e14Im t u1 u2 v) i < n ∧ dec (l16 (e14Im t u1 u2 v) i) = γ (dec (l16 GS i)) := by
  obtain ⟨a0, a1, a2, a3⟩ := s14_e14Im (t := t) (u1 := u1) (u2 := u2) (v := v) (by omega)
    (by omega) (by omega) (by omega)
  intro i hi
  interval_cases i
  · rw [a0, g0]
    exact ⟨ht, rfl⟩
  · rw [a1, g1]
    exact ⟨h1, rfl⟩
  · rw [a2, g2]
    exact ⟨h2, rfl⟩
  · rw [a3, g3]
    exact ⟨hv, rfl⟩

theorem e14_empty {n : Nat} (hn : n = 16384) (M : IsModel (⊤ : Subgroup X) n mul dec)
    {GS PT t : Nat} (hT : treeB n 4 mul GS PT = true)
    {OT LB RP CZ HL GI KY PV CL1 CL2 RK1 RK2 R1 W1 R2 : Nat} {W2 SP : Nat → Nat}
    {nl c1 c2 n1 n2 f : Nat}
    (hord : ordOK n mul OT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true)
    (hcz : czOK16 n LB CZ = true) (hH : hOK16 n mul t HL = true)
    (hky : kyOK mul OT LB CZ GS KY PV = true)
    (hc1 : cmOK16 n mul t OT LB CZ (kyL KY 0) CL1 RK1 c1 = true)
    (hc2 : cmOK16 n mul t OT LB CZ (kyL KY 1) CL2 RK2 c2 = true)
    (h1 : e14Lvl1 n mul HL CL1 c1 R1 W1 n1 = true)
    (h2 : allB n1 (fun r1 => e14Lvl2 n mul OT LB CZ t HL CL2 c2 R1 R2 (pvL PV 0) n2 (W2 r1) r1) = true)
    (h3 : allB n2 (fun r2 => e14Lvl3 n mul OT LB CZ t GS PT f R1 R2 (kyL KY 2) (pvL PV 1)
      (pvL PV 2) (SP r2) r2) = true)
    (β : MulAut X) : β (dec (l16 GS 0)) ≠ dec t := by
  intro hβ
  have hn' : n < 32768 := by omega
  obtain ⟨ht, -⟩ := s14_hParts hH
  obtain ⟨-, -, k2, -, p1, p2⟩ := s14_kyParts hky
  have hg : ∀ i < 4, l16 GS i < n := fun i hi => treeB_gen hT hi
  obtain ⟨h, hht, r2, hr2, hu1, hu2, e1, e2⟩ :=
    s14_lvl12 M hn' hT hord hlab hcz hH hky hc1 hc2 h1 h2 β hβ
  obtain ⟨γ, hγ⟩ : ∃ γ : MulAut X, ∀ x, γ x = h * β x * h⁻¹ :=
    ⟨MulAut.conj h * β, fun x => by rw [MulAut.mul_apply, MulAut.conj_apply]⟩
  have g0 : γ (dec (l16 GS 0)) = dec t := by rw [hγ, hβ, hht, mul_inv_cancel_right]
  have g1 : γ (dec (l16 GS 1)) = dec (l16 R1 (e14P1 R2 r2)) := by rw [hγ, e1]
  have g2 : γ (dec (l16 GS 2)) = dec (e14P2 R2 r2) := by rw [hγ, e2]
  obtain ⟨v, hv, hdv⟩ : ∃ v < n, dec v = γ (dec (l16 GS 3)) :=
    ⟨_, M.code_lt (mem_top _), M.dec_code (mem_top _)⟩
  have hK : ivOf mul OT LB CZ t v = kyL KY 2 := by
    rw [k2]
    exact s14_ivOf_aut M hn' hT hlab hord hcz γ (hg 0 (by norm_num)) (hg 3 (by norm_num)) ht hv
      g0.symm hdv
  have hP13 : pvOf16 mul OT LB CZ t (l16 R1 (e14P1 R2 r2)) v = pvL PV 1 := by
    rw [p1]
    exact s14_pvOf_aut M hn' hT hlab hord hcz γ (hg 0 (by norm_num)) (hg 1 (by norm_num))
      (hg 3 (by norm_num)) ht hu1 hv g0.symm g1.symm hdv
  have hP23 : pvOf16 mul OT LB CZ t (e14P2 R2 r2) v = pvL PV 2 := by
    rw [p2]
    exact s14_pvOf_aut M hn' hT hlab hord hcz γ (hg 0 (by norm_num)) (hg 2 (by norm_num))
      (hg 3 (by norm_num)) ht hu2 hv g0.symm g2.symm hdv
  have hl3 : e14Lvl3 n mul OT LB CZ t GS PT f R1 R2 (kyL KY 2) (pvL PV 1) (pvL PV 2) (SP r2) r2 =
      true := allB_eq_true.1 h3 r2 hr2
  have hv3 : (!Nat.beq (ivOf mul OT LB CZ t v) (kyL KY 2) ||
      !Nat.beq (pvOf16 mul OT LB CZ t (l16 R1 (e14P1 R2 r2)) v) (pvL PV 1) ||
      !Nat.beq (pvOf16 mul OT LB CZ t (e14P2 R2 r2) v) (pvL PV 2) ||
      e14Sp mul GS PT (e14Im t (l16 R1 (e14P1 R2 r2)) (e14P2 R2 r2) v) f (l16 (SP r2) v)) = true :=
    allB_eq_true.1 hl3 v hv
  rw [hK, hP13, hP23] at hv3
  simp only [Nat.beq_refl, Bool.not_true, Bool.false_or] at hv3
  have hIM := s14_im M (by omega) ht hu1 hu2 hv γ g0 g1 g2 hdv.symm
  have ho : l16 (SP r2) v ≤ 65535 := lane_le _ _ _ _
  have hs : Nat.shiftRight (l16 (SP r2) v) 14 < 4 := by
    have e : Nat.shiftRight (l16 (SP r2) v) 14 = l16 (SP r2) v / 2 ^ 14 :=
      Nat.shiftRight_eq_div_pow _ 14
    rw [e]
    omega
  have hx : Nat.land (l16 (SP r2) v) 16383 < n := lt_of_le_of_lt Nat.and_le_right (by omega)
  rw [s14_sp_false M hT γ hIM hx hs] at hv3
  exact Bool.false_ne_true hv3

end Certificates.KernelTower
