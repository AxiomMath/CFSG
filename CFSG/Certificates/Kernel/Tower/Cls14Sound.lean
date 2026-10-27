module

public import Certificates.Data.Kernel.Tower.Cls14
public import CFSG.Certificates.Kernel.Tower.OutSound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower

variable {X : Type*} [Group X] {n : Nat} {mul : Nat → Nat → Nat} {dec : Nat → X}

section Cls16

open Subgroup

theorem cls16_sqK_succ (mul : Nat → Nat → Nat) (c k : Nat) :
    sqK mul c (k + 1) = mul (sqK mul c k) (sqK mul c k) := rfl

theorem cls16_ordC_parts {c e : Nat} (h : ordC mul c e = true) :
    sqK mul c e = 0 ∧ (e = 0 ∧ c = 0 ∨ 0 < e ∧ sqK mul c (e - 1) ≠ 0) := by
  rw [ordC, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, ?_⟩
  rcases h.2 with h2 | h2
  · exact Or.inl ⟨Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩
  · exact Or.inr ⟨Nat.le_of_ble_eq_true h2.1, Nat.ne_of_beq_eq_false h2.2⟩

theorem cls16_oe_one (M : IsModel (⊤ : Subgroup X) n mul dec) {OT : Nat}
    (hord : ordOK n mul OT = true) {c : Nat} (hc : c < n) :
    oe OT c = 1 ↔ c ≠ 0 ∧ mul c c = 0 := by
  have h00 : mul 0 0 = 0 := by
    rw [← M.dec_eq_one_iff (M.mul_lt _ M.zero_lt _ M.zero_lt), M.dec_mul _ M.zero_lt _ M.zero_lt,
      M.dec_zero, one_mul]
  obtain ⟨h1, h2⟩ := cls16_ordC_parts (allB_eq_true.1 hord c hc)
  constructor
  · intro he
    rw [he] at h1 h2
    rcases h2 with h2 | h2
    · exact absurd h2.1 (by decide)
    · exact ⟨h2.2, h1⟩
  · rintro ⟨hc0, hcc⟩
    have hz : ∀ k, sqK mul c (k + 1) = 0 := by
      intro k
      induction k with
      | zero => exact hcc
      | succ k ih => rw [cls16_sqK_succ, ih, h00]
    rcases h2 with h2 | ⟨h2, h3⟩
    · exact absurd h2.2 hc0
    · rcases Nat.lt_or_ge (oe OT c) 2 with h4 | h4
      · omega
      · have e : oe OT c - 1 = (oe OT c - 2) + 1 := by omega
        rw [e] at h3
        exact absurd (hz _) h3

theorem cls16_labParts {k GS GI LB RP nl : Nat} (h : labOK16 n k mul GS GI LB RP nl = true) :
    (∀ i < k, l16 GI i < n ∧ mul (l16 GS i) (l16 GI i) = 0) ∧
    (∀ l < nl, l16 RP l < n ∧ lbL LB (l16 RP l) = l) ∧
    ∀ c < n, lbL LB c < nl ∧ lbW LB c < n ∧
      mul (lbW LB c) (l16 RP (lbL LB c)) = mul c (lbW LB c) ∧
      ∀ i < k, lbL LB (mul (mul (l16 GS i) c) (l16 GI i)) = lbL LB c := by
  simp only [labOK16, labC16, Bool.and_eq_true, allB_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun i hi => ⟨Nat.le_of_ble_eq_true (h1 i hi).1, Nat.eq_of_beq_eq_true (h1 i hi).2⟩,
    fun l hl => ⟨Nat.le_of_ble_eq_true (h2 l hl).1, Nat.eq_of_beq_eq_true (h2 l hl).2⟩,
    fun c hc => ⟨Nat.le_of_ble_eq_true (h3 c hc).1.1.1, Nat.le_of_ble_eq_true (h3 c hc).1.1.2,
      Nat.eq_of_beq_eq_true (h3 c hc).1.2, fun i hi => Nat.eq_of_beq_eq_true ((h3 c hc).2 i hi)⟩⟩

variable {GS PT GI LB RP nl : Nat}

theorem cls16_lab_conj (M : IsModel (⊤ : Subgroup X) n mul dec) (hT : treeB n 4 mul GS PT = true)
    (hlab : labOK16 n 4 mul GS GI LB RP nl = true) (g : X) :
    ∀ c < n, lbL LB (M.code (g * dec c * g⁻¹)) = lbL LB c := by
  obtain ⟨hGI, -, hC⟩ := cls16_labParts hlab
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

theorem cls16_rep (M : IsModel (⊤ : Subgroup X) n mul dec)
    (hlab : labOK16 n 4 mul GS GI LB RP nl = true) {c : Nat} (hc : c < n) :
    l16 RP (lbL LB c) < n ∧
      dec c = dec (lbW LB c) * dec (l16 RP (lbL LB c)) * (dec (lbW LB c))⁻¹ := by
  obtain ⟨-, hR, hC⟩ := cls16_labParts hlab
  obtain ⟨hl, hw, hm, -⟩ := hC c hc
  have hr := (hR _ hl).1
  have h1 := M.dec_mul _ hw _ hr
  rw [hm, M.dec_mul _ hc _ hw] at h1
  exact ⟨hr, eq_mul_inv_of_mul_eq h1⟩

theorem cls16_conj_iff (M : IsModel (⊤ : Subgroup X) n mul dec)
    (hT : treeB n 4 mul GS PT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true) {a b : Nat}
    (ha : a < n) (hb : b < n) : Conj (dec a) (dec b) ↔ lbL LB a = lbL LB b := by
  constructor
  · rintro ⟨k, hk⟩
    have h := cls16_lab_conj M hT hlab k b hb
    rw [← hk, M.code_dec ha] at h
    exact h
  · intro h
    refine ⟨dec (lbW LB a) * (dec (lbW LB b))⁻¹, ?_⟩
    rw [(cls16_rep M hlab ha).2, (cls16_rep M hlab hb).2, h]
    group

theorem cls16_cntB_le (f : Nat → Bool) : ∀ m, cntB m f ≤ m := by
  intro m
  induction m with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    have e : cntB (m + 1) f = cond (f m) 1 0 + cntB m f := rfl
    rw [e]
    cases f m <;> simp only [cond_true, cond_false] <;> omega

theorem cls16_lane (T i : Nat) : lane T 15 32767 i = T / 2 ^ (15 * i) % 32768 := lane_eq T 15 i

theorem cls16_lane_add (T m l : Nat) (h : T / 2 ^ (15 * m) % 32768 + 1 < 32768) :
    (T + 2 ^ (15 * m)) / 2 ^ (15 * l) % 32768 =
      T / 2 ^ (15 * l) % 32768 + if l = m then 1 else 0 := by
  have h32 : (32768 : Nat) = 2 ^ 15 := by norm_num
  rcases Nat.lt_trichotomy l m with hl | rfl | hl
  · rw [if_neg (by omega)]
    have e : 2 ^ (15 * m) = 2 ^ (15 * l) * (32768 * 2 ^ (15 * (m - l - 1))) := by
      rw [h32, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, Nat.add_zero]
  · rw [if_pos rfl, Nat.add_div_right _ (by positivity)]
    generalize T / 2 ^ (15 * l) = a at h ⊢
    omega
  · rw [if_neg (by omega), Nat.add_zero]
    have e : 2 ^ (15 * l) = 2 ^ (15 * m) * (32768 * 2 ^ (15 * (l - m - 1))) := by
      rw [h32, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.add_div_right _ (by positivity),
      ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    have e2 : (T / 2 ^ (15 * m) + 1) / 32768 = T / 2 ^ (15 * m) / 32768 := by
      generalize T / 2 ^ (15 * m) = a at h ⊢
      omega
    rw [e2]

theorem cls16_hist (LB : Nat) : ∀ m, m < 32768 → ∀ l,
    histB m LB / 2 ^ (15 * l) % 32768 = cntB m (fun c => Nat.beq (lbL LB c) l) := by
  intro m
  induction m with
  | zero => intro _ l; simp [histB, cntB]
  | succ m ih =>
    intro hm l
    have e1 : histB (m + 1) LB = histB m LB + 2 ^ (15 * lbL LB m) := by
      change histB m LB + 1 <<< (15 * lbL LB m) = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    have e2 : cntB (m + 1) (fun c => Nat.beq (lbL LB c) l) =
        cond (Nat.beq (lbL LB m) l) 1 0 + cntB m (fun c => Nat.beq (lbL LB c) l) := rfl
    have hle := cls16_cntB_le (fun c => Nat.beq (lbL LB c) (lbL LB m)) m
    rw [e1, cls16_lane_add _ _ _ (by rw [ih (by omega)]; omega), ih (by omega), e2]
    by_cases h : l = lbL LB m
    · subst h
      rw [if_pos rfl, Nat.beq_refl]
      simp only [cond_true]
      omega
    · have hb : Nat.beq (lbL LB m) l = false :=
        Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h').symm
      rw [if_neg h, hb]
      simp only [cond_false]
      omega

theorem cls16_cz (hn : n < 32768) {CZ : Nat} (hcz : czOK16 n LB CZ = true) (l : Nat) :
    lane CZ 15 32767 l = cntB n (fun c => Nat.beq (lbL LB c) l) := by
  rw [cls16_lane, ← Nat.eq_of_beq_eq_true hcz, cls16_hist LB n hn]

theorem cls16_card (M : IsModel (⊤ : Subgroup X) n mul dec) (hn : n < 32768)
    (hT : treeB n 4 mul GS PT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true) {CZ : Nat}
    (hcz : czOK16 n LB CZ = true) {c : Nat} (hc : c < n) :
    Nat.card (MulAction.orbit (ConjAct X) (dec c)) = lane CZ 15 32767 (lbL LB c) := by
  classical
  rw [cls16_cz hn hcz, cntB_eq_card]
  set F := (Finset.range n).filter fun d => Nat.beq (lbL LB d) (lbL LB c) = true
  have hO : MulAction.orbit (ConjAct X) (dec c) = ↑(F.image dec) := by
    ext y
    rw [Finset.coe_image, Set.mem_image]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨M.code (g • dec c), ?_, M.dec_code (mem_top _)⟩
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨M.code_lt (mem_top _), ?_⟩
      rw [ConjAct.smul_def, cls16_lab_conj M hT hlab _ c hc]
      exact Nat.beq_refl _
    · rintro ⟨d, hd, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨k, hk⟩ := (cls16_conj_iff M hT hlab hd.1 hc).2 (Nat.eq_of_beq_eq_true hd.2)
      refine ⟨ConjAct.toConjAct k, ?_⟩
      change ConjAct.toConjAct k • dec c = dec d
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hk]
  have hinj : Set.InjOn dec ↑F := by
    intro a ha b hb h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    exact M.inj a ha.1 b hb.1 h
  rw [hO, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]

theorem cls16_finite (M : IsModel (⊤ : Subgroup X) n mul dec) : Finite X ∧ Nat.card X = n := by
  have hb : Function.Bijective (fun i : Fin n => dec i) :=
    ⟨fun a b h => Fin.ext (M.inj a a.2 b b.2 h), fun y => by
      obtain ⟨c, hc, e⟩ := M.surj y (mem_top y)
      exact ⟨⟨c, hc⟩, e⟩⟩
  refine ⟨Finite.of_surjective _ hb.2, ?_⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem cls16_ninv (M : IsModel (⊤ : Subgroup X) n mul dec) {OT : Nat}
    (hord : ordOK n mul OT = true) {r : Nat} (hr : r < n) :
    Nat.card {y : centralizer {dec r} // y ^ 2 = 1 ∧ y ≠ 1} = ninvC n mul OT r := by
  have h := M.ninv_cent_eq hr
  rw [top_inf_eq] at h
  rw [h, ninvC, cntB_eq, CFSG.SCATWreath.cntC, CFSG.SCATWreath.invols, List.filter_filter]
  congr 1
  refine List.filter_congr fun c hc => ?_
  rw [List.mem_range] at hc
  rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, beq_iff_eq, Nat.beq_eq, Nat.beq_eq, cls16_oe_one M hord hc]
  exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩

end Cls16

theorem pcB_sound (M : IsModel (⊤ : Subgroup X) n mul dec) (hn : n = 16384) {GS PT : Nat}
    (hT : treeB n 4 mul GS PT = true) {OT LB RP CZ GI nl t x0 : Nat} (ht : t < n) (hx0 : x0 < n)
    (hord : ordOK n mul OT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true)
    (hcz : czOK16 n LB CZ = true) (hpc : pcB n mul OT LB RP CZ nl t x0 = true) :
    ∀ x : X, IsPInv x → Conj x (dec t) ∨ Conj x (dec x0) := by
  intro x hx
  obtain ⟨hx2, hx1, hP⟩ := hx
  obtain ⟨hfin, hX⟩ := cls16_finite M
  have hc := M.code_lt (Subgroup.mem_top x)
  have hxc := M.dec_code (Subgroup.mem_top x)
  obtain ⟨-, -, hC⟩ := cls16_labParts hlab
  have hl := (hC _ hc).1
  obtain ⟨hr, hrep⟩ := cls16_rep M hlab hc
  have hrl : lbL LB (l16 RP (lbL LB (M.code x))) = lbL LB (M.code x) :=
    ((cls16_labParts hlab).2.1 _ hl).2
  generalize hw : dec (lbW LB (M.code x)) = w at hrep
  generalize hR : l16 RP (lbL LB (M.code x)) = r at hr hrep hrl
  have er : w⁻¹ * x * w⁻¹⁻¹ = dec r := by rw [← hxc, hrep]; group
  have hPr := Certificates.KernelTower.pinv_of_mulEquiv (centConj w⁻¹ x) hP
  rw [er] at hPr
  have hr2 : dec r ^ 2 = 1 ∧ dec r ≠ 1 := by
    rw [← er]
    refine ⟨by rw [conj_pow, hx2]; group, fun h => hx1 ?_⟩
    have h' : w * (w⁻¹ * x * w⁻¹⁻¹) * w⁻¹ = w * 1 * w⁻¹ := by rw [h]
    simpa [mul_assoc] using h'
  have hoe := (cls16_oe_one M hord hr).2 ((M.dec_sq_iff hr).1 hr2)
  have hcm := card_cent_mul (dec r)
  rw [hPr.1, hX, cls16_card M (by omega) hT hlab hcz hr, hrl] at hcm
  have h64 : lane CZ 15 32767 (lbL LB (M.code x)) = 64 := by
    have e : (2 : Nat) ^ 8 = 256 := by norm_num
    rw [e] at hcm
    omega
  have h87 : ninvC n mul OT r = 87 := by
    rw [← cls16_ninv M hord hr]
    exact hPr.2
  have hp := allB_eq_true.1 hpc _ hl
  rw [hR, hoe, h64, h87] at hp
  simp only [Nat.beq_refl, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
  rw [← hxc]
  rcases hp with hp | hp
  · exact Or.inl ((cls16_conj_iff M hT hlab hc ht).2 (Nat.eq_of_beq_eq_true hp))
  · exact Or.inr ((cls16_conj_iff M hT hlab hc hx0).2 (Nat.eq_of_beq_eq_true hp))

variable {GS XT t x0 : Nat}

theorem chiB_parts (h : chiB n mul GS XT t x0 = true) :
    bit XT 0 = 0 ∧ bit XT t = 1 ∧ bit XT x0 = 1 := by
  rw [chiB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1.1, Nat.eq_of_beq_eq_true h.1.1.2,
    Nat.eq_of_beq_eq_true h.1.2⟩

theorem chiB_edge (h : chiB n mul GS XT t x0 = true) {c s : Nat} (hc : c < n) (hs : s < 4) :
    bit XT (mul (l16 GS s) c) = bit XT (l16 GS s) ^^^ bit XT c := by
  rw [chiB, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true (allB_eq_true.1 (allB_eq_true.1 h.2 c hc) s hs)

theorem chiB_mul (M : IsModel (⊤ : Subgroup X) n mul dec) {PT : Nat}
    (hT : treeB n 4 mul GS PT = true) (h : chiB n mul GS XT t x0 = true) :
    ∀ c < n, ∀ y : X, bit XT (M.code (dec c * y)) = bit XT c ^^^ bit XT (M.code y) := by
  suffices H : ∀ d, ∀ c < n, ptDep PT c = d → ∀ y : X,
      bit XT (M.code (dec c * y)) = bit XT c ^^^ bit XT (M.code y) from
    fun c hc => H _ c hc rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro c hc hd y
    by_cases h0 : c = 0
    · subst h0
      rw [M.dec_zero, one_mul, (chiB_parts h).1, Nat.zero_xor]
    · obtain ⟨hgi, hpar, hdep, hmul⟩ := treeB_get hT hc h0
      have hg := treeB_gen hT hgi
      have e1 : dec c * y = dec (l16 GS (ptGi PT c)) * (dec (ptPar PT c) * y) := by
        rw [← mul_assoc, ← M.dec_mul _ hg _ hpar, hmul]
      have hz := M.code_lt (Subgroup.mem_top (dec (ptPar PT c) * y))
      have hc' : bit XT c = bit XT (l16 GS (ptGi PT c)) ^^^ bit XT (ptPar PT c) := by
        rw [← chiB_edge h hpar hgi, hmul]
      rw [e1, M.code_mul (Subgroup.mem_top _) (Subgroup.mem_top _), M.code_dec hg,
        chiB_edge h hz hgi, ih _ (hd ▸ hdep) _ hpar rfl y, hc', Nat.xor_assoc]

theorem bit_cases (XT c : Nat) : bit XT c = 0 ∨ bit XT c = 1 := by
  have h : bit XT c = Nat.shiftRight XT c % 2 := Nat.and_one_is_mod _
  omega

@[expose] noncomputable def bitQ (M : IsModel (⊤ : Subgroup X) n mul dec) {PT : Nat}
    (hT : treeB n 4 mul GS PT = true) (h : chiB n mul GS XT t x0 = true) : Subgroup X where
  carrier := {x | bit XT (M.code x) = 0}
  mul_mem' {a b} ha hb := by
    have ha' : bit XT (M.code a) = 0 := ha
    have hb' : bit XT (M.code b) = 0 := hb
    have e : a * b = dec (M.code a) * b := by rw [M.dec_code (Subgroup.mem_top a)]
    change bit XT (M.code (a * b)) = 0
    rw [e, chiB_mul M hT h _ (M.code_lt (Subgroup.mem_top a)), ha', hb', Nat.zero_xor]
  one_mem' := by
    change bit XT (M.code 1) = 0
    rw [M.code_one]
    exact (chiB_parts h).1
  inv_mem' {a} ha := by
    change bit XT (M.code a⁻¹) = 0
    have h1 := chiB_mul M hT h _ (M.code_lt (Subgroup.mem_top a⁻¹)) a
    rw [M.dec_code (Subgroup.mem_top _), inv_mul_cancel, M.code_one, (chiB_parts h).1] at h1
    change bit XT (M.code a) = 0 at ha
    rw [ha, Nat.xor_zero] at h1
    exact h1.symm

theorem mem_bitQ (M : IsModel (⊤ : Subgroup X) n mul dec) {PT : Nat}
    (hT : treeB n 4 mul GS PT = true) (h : chiB n mul GS XT t x0 = true) (x : X) :
    x ∈ bitQ M hT h ↔ bit XT (M.code x) = 0 := Iff.rfl

theorem bitQ_index (M : IsModel (⊤ : Subgroup X) n mul dec) {PT : Nat}
    (hT : treeB n 4 mul GS PT = true) (h : chiB n mul GS XT t x0 = true) (ht : t < n) :
    (bitQ M hT h).index = 2 := by
  refine Subgroup.index_eq_two_iff.mpr ⟨dec t, fun b => ?_⟩
  rw [mem_bitQ, mem_bitQ]
  have e : b * dec t = dec (M.code b) * dec t := by rw [M.dec_code (Subgroup.mem_top b)]
  rw [e, chiB_mul M hT h _ (M.code_lt (Subgroup.mem_top b)), M.code_dec ht, (chiB_parts h).2.1]
  rcases bit_cases XT (M.code b) with hb | hb <;> rw [hb] <;> first | decide | simp [Xor]

theorem bit_mul (M : IsModel (⊤ : Subgroup X) n mul dec) {PT : Nat}
    (hT : treeB n 4 mul GS PT = true) (h : chiB n mul GS XT t x0 = true) (a b : X) :
    bit XT (M.code (a * b)) = bit XT (M.code a) ^^^ bit XT (M.code b) := by
  have e : a * b = dec (M.code a) * b := by rw [M.dec_code (Subgroup.mem_top a)]
  rw [e, chiB_mul M hT h _ (M.code_lt (Subgroup.mem_top a))]

theorem bitQ_normal (M : IsModel (⊤ : Subgroup X) n mul dec) {PT : Nat}
    (hT : treeB n 4 mul GS PT = true) (h : chiB n mul GS XT t x0 = true) :
    (bitQ M hT h).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_bitQ] at hx ⊢
  have hi := bit_mul M hT h g⁻¹ g
  rw [inv_mul_cancel, M.code_one, (chiB_parts h).1] at hi
  rw [bit_mul M hT h, bit_mul M hT h, hx, Nat.xor_zero]
  rcases bit_cases XT (M.code g) with hg | hg <;>
    rcases bit_cases XT (M.code g⁻¹) with hg' | hg' <;> rw [hg, hg'] at hi <;> rw [hg, hg'] <;>
    first | decide | exact absurd hi (by decide)

theorem not_mem_bitQ (M : IsModel (⊤ : Subgroup X) n mul dec) {PT : Nat}
    (hT : treeB n 4 mul GS PT = true) (h : chiB n mul GS XT t x0 = true) (ht : t < n)
    (hx0 : x0 < n) : dec t ∉ bitQ M hT h ∧ dec x0 ∉ bitQ M hT h := by
  rw [mem_bitQ, mem_bitQ, M.code_dec ht, M.code_dec hx0, (chiB_parts h).2.1, (chiB_parts h).2.2]
  decide

end Certificates.KernelTower

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup

theorem l2Facts_of_parts {X : Type*} [Group X] {t x₀ : X} (Q : Subgroup X) (hN : Q.Normal)
    (hQ : Q.index = 2) (htQ : t ∉ Q) (hxQ : x₀ ∉ Q) (hcls : ∀ x, IsPInv x → Conj x t ∨ Conj x x₀)
    (hno : ∀ β : MulAut X, β x₀ ≠ t) : L2Facts X t := by
  refine ⟨Q, hQ, htQ, fun x hx hP => ?_, x₀, hcls, Or.inr fun D hD => absurd hD (hno D.α)⟩
  rcases hcls x hP with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h := hN.conj_mem _ hx k⁻¹
    have e : k⁻¹ * (k * t * k⁻¹) * k⁻¹⁻¹ = t := by group
    rw [e] at h
    exact htQ h
  · have h := hN.conj_mem _ hx k⁻¹
    have e : k⁻¹ * (k * x₀ * k⁻¹) * k⁻¹⁻¹ = x₀ := by group
    rw [e] at h
    exact hxQ h

end CFSG.OddStandard.AltStdSmall4.Tower
