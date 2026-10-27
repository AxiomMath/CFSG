module

public import Certificates.Data.Kernel.Tower.L1
public import CFSG.Certificates.Kernel.Tower.WSound
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerFacts

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower CFSG.SCATWreath Subgroup

theorem nbeq (a b : Nat) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

theorem cntB_eq (n : Nat) (f : Nat → Bool) : cntB n f = ((List.range n).filter f).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : cntB (n + 1) f = Nat.add (cond (f n) 1 0) (cntB n f) := rfl
    rw [e, ih, List.range_succ, List.filter_append, List.length_append]
    rcases Bool.eq_false_or_eq_true (f n) with h | h <;> simp [h, List.filter_cons] <;> try omega

theorem cntW_eq (SM AC x : Nat) : cntW SM AC x = cntC (wm SM AC) (List.range 8192) x := by
  rw [cntW, cntB_eq, cntC]
  exact congrArg List.length (List.filter_congr fun c _ => nbeq _ _)

theorem ninvW_eq (SM AC x : Nat) :
    ninvW SM AC x = cntC (wm SM AC) (invols 8192 (wm SM AC)) x := by
  rw [ninvW, cntB_eq, cntC, invols, List.filter_filter]
  refine congrArg List.length (List.filter_congr fun c _ => ?_)
  simp only [nbeq, bne]
  cases (c == 0) <;> cases (wm SM AC c c == 0) <;> cases (wm SM AC x c == wm SM AC c x) <;> rfl

theorem bit_le (T i : Nat) : bit T i ≤ 1 := Nat.and_le_right

theorem cast_xor {p q : Nat} (hp : p ≤ 1) (hq : q ≤ 1) :
    ((Nat.xor p q : Nat) : ZMod 2) = (p : ZMod 2) + q := by
  interval_cases p <;> interval_cases q <;> decide

theorem cast_eq_zero {p : Nat} (hp : p ≤ 1) : (p : ZMod 2) = 0 ↔ p = 0 := by
  interval_cases p <;> decide

theorem wm_shr (SM AC a b : Nat) : Nat.shiftRight (wm SM AC a b) 6 =
    lane SM 7 127 (Nat.add (Nat.mul 128 (Nat.shiftRight a 6)) (Nat.shiftRight b 6)) := by
  have h1 : Nat.land a 63 < 2 ^ 6 := Nat.lt_succ_of_le Nat.and_le_right
  have h2 : lane AC 6 63 (Nat.add (Nat.mul 64 (Nat.shiftRight a 6)) (Nat.land b 63)) < 2 ^ 6 :=
    Nat.lt_succ_of_le (lane_le _ _ _ _)
  have hx : Nat.xor (Nat.land a 63) (lane AC 6 63 (Nat.add (Nat.mul 64 (Nat.shiftRight a 6))
      (Nat.land b 63))) < 64 := Nat.xor_lt_two_pow h1 h2
  rw [wm, shr6]
  generalize lane SM 7 127 (Nat.add (Nat.mul 128 (Nat.shiftRight a 6)) (Nat.shiftRight b 6)) = k
  generalize Nat.xor (Nat.land a 63) (lane AC 6 63 (Nat.add (Nat.mul 64 (Nat.shiftRight a 6))
    (Nat.land b 63))) = x at hx ⊢
  change (64 * k + x) / 64 = k
  omega

theorem psi_get {SM PS : Nat} (h : psiOK SM PS = true) {i j : Nat} (hi : i < 128) (hj : j < 128) :
    bit PS (lane SM 7 127 (Nat.add (Nat.mul 128 i) j)) = Nat.xor (bit PS i) (bit PS j) := by
  rw [psiOK, Bool.and_eq_true, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true (allB_eq_true.1 (allB_eq_true.1 h.2 i hi) j hj)

theorem psi_zero {SM PS : Nat} (h : psiOK SM PS = true) : bit PS 0 = 0 := by
  rw [psiOK, Bool.and_eq_true, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1.1

theorem psi_one {SM PS : Nat} (h : psiOK SM PS = true) : bit PS 1 = 1 := by
  rw [psiOK, Bool.and_eq_true, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1.2

variable {X : Type*} [Group X]

@[expose] def centConj (g x : X) : centralizer {x} ≃* centralizer {g * x * g⁻¹} where
  toFun y := ⟨g * y * g⁻¹, by
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 y.2
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group⟩
  invFun y := ⟨g⁻¹ * y * g, by
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 y.2
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group⟩
  left_inv y := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' y z := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem pinv_of_mulEquiv {Y : Type*} [Group Y] {S : Subgroup X} {S' : Subgroup Y} (e : S ≃* S')
    (h : PInv S) : PInv S' := by
  refine ⟨(Nat.card_congr e.toEquiv).symm.trans h.1, Eq.trans ?_ h.2⟩
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ne_eq]
  rw [← map_pow, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]

variable {SM AC PS RW MR : Nat} {dec : Nat → X}

@[expose] noncomputable def psiHom (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec)
    (hP : psiOK SM PS = true) : X →* Multiplicative (ZMod 2) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd ((bit PS (Nat.shiftRight (M.code x) 6) : Nat) :
    ZMod 2)) fun x y => by
    have hx := M.code_lt (mem_top x)
    have hy := M.code_lt (mem_top y)
    have hi : Nat.shiftRight (M.code x) 6 < 128 := by rw [shr6]; omega
    have hj : Nat.shiftRight (M.code y) 6 < 128 := by rw [shr6]; omega
    rw [M.code_mul (mem_top x) (mem_top y), wm_shr, psi_get hP hi hj,
      cast_xor (bit_le _ _) (bit_le _ _), ofAdd_add]

theorem psiHom_apply (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec) (hP : psiOK SM PS = true)
    (x : X) : psiHom M hP x =
      Multiplicative.ofAdd ((bit PS (Nat.shiftRight (M.code x) 6) : Nat) : ZMod 2) := rfl

theorem mem_ker_psiHom (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec) (hP : psiOK SM PS = true)
    (x : X) : x ∈ (psiHom M hP).ker ↔ bit PS (Nat.shiftRight (M.code x) 6) = 0 := by
  rw [MonoidHom.mem_ker, psiHom_apply, ofAdd_eq_one, cast_eq_zero (bit_le _ _)]

theorem card_cent_dec (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec) {r : Nat}
    (hr : r < 8192) : Nat.card (centralizer {dec r}) = cntW SM AC r := by
  have h := M.card_cent_eq hr
  rw [top_inf_eq] at h
  rw [h, cntW_eq]

theorem ninv_cent_dec (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec) {r : Nat}
    (hr : r < 8192) :
    Nat.card {y : centralizer {dec r} // y ^ 2 = 1 ∧ y ≠ 1} = ninvW SM AC r := by
  have h := M.ninv_cent_eq hr
  rw [top_inf_eq] at h
  rw [h, ninvW_eq]

theorem invC_of (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec)
    (hI : invOK SM AC PS RW MR = true) {x : X} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ r < 8192, ∃ w < 8192, x = dec w * dec r * (dec w)⁻¹ ∧
      invC SM AC PS MR (M.code x) r w = true := by
  have hc := M.code_lt (mem_top x)
  have hdc := M.dec_code (mem_top x)
  have hsq := (M.dec_sq_iff hc).1 (by rw [hdc]; exact ⟨hx2, hx1⟩)
  have h := allB_eq_true.1 hI _ hc
  have hc0 : Nat.beq (M.code x) 0 = false := by
    rw [nbeq]
    exact beq_eq_false_iff_ne.2 hsq.1
  have hcc : Nat.beq (wm SM AC (M.code x) (M.code x)) 0 = true := by
    rw [nbeq, beq_iff_eq]
    exact hsq.2
  rw [hc0, hcc] at h
  simp only [Bool.false_or, Bool.not_true] at h
  have he := lane_le RW 26 67108863 (M.code x)
  generalize lane RW 26 67108863 (M.code x) = e at h he
  have hr : Nat.land e 8191 < 8192 := Nat.lt_succ_of_le Nat.and_le_right
  have hw : Nat.shiftRight e 13 < 8192 := by
    change e >>> 13 < 8192
    rw [Nat.shiftRight_eq_div_pow]
    omega
  refine ⟨Nat.land e 8191, hr, Nat.shiftRight e 13, hw, ?_, h⟩
  rw [invC, Bool.and_eq_true] at h
  have hm := Nat.eq_of_beq_eq_true h.1
  have h1 := M.dec_mul _ hc _ hw
  have h2 := M.dec_mul _ hw _ hr
  rw [hm, h2, hdc] at h1
  exact eq_mul_inv_of_mul_eq h1.symm

theorem invC_cond {c r w : Nat} (h : invC SM AC PS MR c r w = true) :
    cond (Nat.beq (bit PS (Nat.shiftRight c 6)) 1) (Nat.beq r 64) (Nat.beq (bit MR r) 1) = true := by
  rw [invC, Bool.and_eq_true] at h
  exact h.2

theorem l1_sound (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec)
    (h1 : l1OK SM AC PS RW MR = true) (h2 : repsOK SM AC MR = true) : L1Facts X (dec 64) := by
  rw [l1OK, Bool.and_eq_true, Bool.and_eq_true] at h1
  obtain ⟨⟨hT, hP⟩, hI⟩ := h1
  have h64 : (64 : Nat) < 8192 := by norm_num
  have hc64 : M.code (dec 64) = 64 := M.code_dec h64
  have hf64 : psiHom M hP (dec 64) = Multiplicative.ofAdd 1 := by
    rw [psiHom_apply, hc64]
    change Multiplicative.ofAdd ((bit PS 1 : Nat) : ZMod 2) = _
    rw [psi_one hP, Nat.cast_one]
  have hsurj : Function.Surjective (psiHom M hP) := by
    intro z
    obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective z
    fin_cases a
    · exact ⟨1, map_one _⟩
    · exact ⟨dec 64, hf64⟩
  refine ⟨?_, (psiHom M hP).ker, ?_, ?_, ?_, ?_⟩
  · rw [card_cent_dec M h64, Nat.eq_of_beq_eq_true hT]
    norm_num
  · rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    rfl
  · rw [MonoidHom.mem_ker, hf64]
    decide
  · intro x hxQ hx2 hx1
    obtain ⟨r, hr, w, hw, rfl, hC⟩ := invC_of M hI hx2 hx1
    have hb := (mem_ker_psiHom M hP _).1 hxQ
    have hc := invC_cond hC
    rw [hb] at hc
    have hmr : bit MR r = 1 := Nat.eq_of_beq_eq_true hc
    have hR := allB_eq_true.1 h2 r hr
    have hmr0 : Nat.beq (bit MR r) 0 = false := by rw [hmr]; rfl
    rw [hmr0, Bool.false_or, repN, Bool.and_eq_true, Bool.or_eq_true] at hR
    have hcard : Nat.card (centralizer {dec w * dec r * (dec w)⁻¹}) = cntW SM AC r := by
      rw [← Nat.card_congr (centConj (dec w) (dec r)).toEquiv, card_cent_dec M hr]
    refine ⟨by rw [hcard]; exact Nat.le_of_ble_eq_true hR.1, fun hp => ?_⟩
    have hp' := pinv_of_mulEquiv (centConj (dec w) (dec r)).symm hp
    have hc256 : cntW SM AC r = 256 := by rw [← card_cent_dec M hr, hp'.1]; norm_num
    rcases hR.2 with h | h
    · rw [hc256] at h
      exact absurd h (by decide)
    · rw [Bool.not_eq_true', ← ninv_cent_dec M hr, hp'.2] at h
      exact absurd h (by decide)
  · intro x hxQ hx2
    have hx1 : x ≠ 1 := fun h => hxQ (h ▸ (psiHom M hP).ker.one_mem)
    obtain ⟨r, hr, w, hw, rfl, hC⟩ := invC_of M hI hx2 hx1
    have hb : bit PS (Nat.shiftRight (M.code (dec w * dec r * (dec w)⁻¹)) 6) = 1 := by
      have := bit_le PS (Nat.shiftRight (M.code (dec w * dec r * (dec w)⁻¹)) 6)
      have h0 := mt (mem_ker_psiHom M hP _).2 hxQ
      omega
    have hc := invC_cond hC
    rw [hb] at hc
    have hr64 : r = 64 := Nat.eq_of_beq_eq_true hc
    subst hr64
    exact ⟨dec w, rfl⟩

end Certificates.KernelTower
