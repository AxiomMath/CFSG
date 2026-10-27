module

public import Certificates.Data.Kernel.TitsOctK
public import CFSG.Certificates.Kernel.TwoF4LieSound
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLayers

public section

namespace CFSG.KC.TitsOctSound

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TwoF4LieSound
open CFSG.Quasithin.H13.F45Ru (Layers)

theorem blt_d (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_eq]

theorem ble_d (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]

theorem beq_d (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem bIf_d (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem nIf_d (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem allN_iff' {n : ℕ} {f : ℕ → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  CFSG.KS.Raw.Orb.allN_iff

@[expose] noncomputable def ev (g : Pm) (n : ℕ) : ℕ := if h : n < 1755 then (g ⟨n, h⟩ : ℕ) else n

theorem ev_lt (g : Pm) {n : ℕ} (h : n < 1755) : ev g n < 1755 := by
  simp only [ev, h, dif_pos]
  exact (g ⟨n, h⟩).2

theorem ev_fin (g : Pm) (p : Fin 1755) : ev g p = g p := by simp [ev, p.2]

theorem ev_mul (g h : Pm) {n : ℕ} (hn : n < 1755) : ev (g * h) n = ev g (ev h n) := by
  have := ev_lt h hn
  simp [ev, hn, this, Equiv.Perm.mul_apply]

theorem ev_one (n : ℕ) : ev 1 n = n := by unfold ev; split <;> simp

theorem ev_inj (g : Pm) {n m : ℕ} (hn : n < 1755) (hm : m < 1755) (h : ev g n = ev g m) : n = m := by
  simp only [ev, hn, hm, dif_pos] at h
  have := g.injective (Fin.ext h)
  exact congrArg Fin.val this

theorem gp_ev {P : ℕ} {g : Pm} (hP : PR P g) {n : ℕ} (hn : n < 1755) : gp P n = ev g n := by
  have := gp_eq hP ⟨n, hn⟩
  simpa [ev, hn] using this

theorem ev_pow_mul (g : Pm) {n : ℕ} (hn : n < 1755) :
    ∀ m, (fun y => ev g y)^[m] n = ev (g ^ m) n
  | 0 => by simp [ev_one]
  | m + 1 => by
    rw [Function.iterate_succ_apply', ev_pow_mul g hn m, pow_succ', ev_mul _ _ hn]

theorem ev_eq_one {g : Pm} (h : ∀ n < 1755, ev g n = n) : g = 1 := by
  ext p
  have := h p p.2
  rw [ev_fin] at this
  simpa using this

variable {lp : ℕ → ℕ} {PL : ℕ}

theorem onLine_iff {p w : ℕ} : onLine lp p w = true ↔ ∃ k < 3, lp (3 * w + k) = p := by
  unfold onLine
  simp only [bIf_d, beq_d, Nat.mul_eq, Nat.add_eq]
  constructor
  · intro h
    by_cases h0 : p = lp (3 * w)
    · exact ⟨0, by norm_num, by simpa using h0.symm⟩
    by_cases h1 : p = lp (3 * w + 1)
    · exact ⟨1, by norm_num, h1.symm⟩
    simp [h0, h1] at h
    exact ⟨2, by norm_num, h.symm⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> simp

theorem adjK_iff {x y : ℕ} : adjK lp x y = true ↔ y < 4680 ∧ x < 4680 ∧
    ((x < 1755 ∧ 1755 ≤ y ∧ onLine lp x (y - 1755) = true) ∨
      (1755 ≤ x ∧ y < 1755 ∧ onLine lp y (x - 1755) = true)) := by
  simp only [adjK, bIf_d, blt_d, ble_d, Nat.sub_eq]
  by_cases hx : x < 1755 <;> by_cases hy : y < 1755 <;> by_cases hy' : y < 4680 <;>
    by_cases hx' : x < 4680 <;> simp [hx, hy, hy', hx'] <;> omega

theorem degK_eq (x : ℕ) : degK x = if x < 1755 then 5 else 3 := by
  simp only [degK, nIf_d, blt_d]
  by_cases hx : x < 1755 <;> simp [hx]

theorem nbK_pt {x k : ℕ} (hx : x < 1755) : nbK lp PL x k = plK PL x k + 1755 := by
  simp [nbK, nIf_d, blt_d, hx]

theorem nbK_ln {x k : ℕ} (hx : 1755 ≤ x) : nbK lp PL x k = lp (3 * (x - 1755) + k) := by
  have : ¬ x < 1755 := by omega
  simp [nbK, nIf_d, blt_d, this]

theorem exists_of_anyN {n : ℕ} {f : ℕ → Bool} (hf : anyN n f = true) : ∃ i < n, f i = true := by
  unfold anyN at hf
  by_contra hne
  push Not at hne
  have hA : allN n (fun i => bIf(f i, false, true)) = true := by
    rw [allN_iff']
    intro i hi
    have hfi : f i = false := by simpa using hne i hi
    simp only [hfi]
  rw [hA] at hf
  exact Bool.false_ne_true hf

theorem incK_sound (h : incK lp PL = true) :
    (∀ x < 1755, ∀ k < 5, plK PL x k < 2925 ∧ onLine lp x (plK PL x k) = true) ∧
    (∀ x < 1755, ∀ k < 5, ∀ j < k, plK PL x k ≠ plK PL x j) ∧
    (∀ v < 2925, ∀ k < 3, ∃ j < 5, plK PL (lp (3 * v + k)) j = v) := by
  unfold incK at h
  simp only [bAnd_eq', Bool.and_eq_true, allN_iff', strictB_eq'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx k hk => ?_, fun x hx k hk j hj e => ?_, fun v hv k hk => ?_⟩
  · obtain ⟨hlt, hon⟩ := (h1 x hx).1 k hk
    exact ⟨by simpa using hlt, hon⟩
  · have := (h1 x hx).2 k hk j hj
    rw [e, Nat.beq_refl] at this
    exact Bool.false_ne_true this
  · obtain ⟨j, hj, e⟩ := exists_of_anyN (h2 v hv k hk)
    exact ⟨j, hj, Nat.eq_of_beq_eq_true e⟩

@[expose] def NbOK (lp : ℕ → ℕ) (PL : ℕ) : Prop :=
  (∀ x < 4680, ∀ y, adjK lp x y = true ↔ ∃ k < degK x, nbK lp PL x k = y) ∧
  (∀ x < 4680, ∀ k < degK x, ∀ j < degK x, nbK lp PL x k = nbK lp PL x j → k = j)

theorem nbOK_of_incK (hlp : ∀ i < 8775, lp i < 1755)
    (hlpd : ∀ v < 2925, ∀ k < 3, ∀ j < 3, lp (3 * v + k) = lp (3 * v + j) → k = j)
    (h : incK lp PL = true) : NbOK lp PL := by
  obtain ⟨h1, h2, h3⟩ := incK_sound h
  refine ⟨fun x hx y => ?_, fun x hx k hk j hj e => ?_⟩
  · rw [adjK_iff, degK_eq]
    by_cases hxp : x < 1755
    · rw [if_pos hxp]
      simp only [nbK_pt hxp]
      constructor
      · rintro ⟨hy, -, ⟨-, hy1, hon⟩ | ⟨h', -⟩⟩
        · obtain ⟨k, hk, e⟩ := onLine_iff.1 hon
          obtain ⟨j, hj, ej⟩ := h3 (y - 1755) (by omega) k hk
          rw [e] at ej
          exact ⟨j, hj, by omega⟩
        · omega
      · rintro ⟨k, hk, rfl⟩
        obtain ⟨hv, hon⟩ := h1 x hxp k hk
        refine ⟨by omega, hx, Or.inl ⟨hxp, by omega, ?_⟩⟩
        simpa using hon
    · rw [if_neg hxp]
      simp only [nbK_ln (show 1755 ≤ x by omega)]
      constructor
      · rintro ⟨-, -, ⟨h', -⟩ | ⟨-, hy, hon⟩⟩
        · omega
        · obtain ⟨k, hk, e⟩ := onLine_iff.1 hon
          exact ⟨k, hk, e⟩
      · rintro ⟨k, hk, rfl⟩
        have hi : 3 * (x - 1755) + k < 8775 := by omega
        refine ⟨by have := hlp _ hi; omega, hx, Or.inr ⟨by omega, hlp _ hi, ?_⟩⟩
        exact onLine_iff.2 ⟨k, hk, rfl⟩
  · rw [degK_eq] at hk hj
    by_cases hxp : x < 1755
    · simp only [hxp, if_true] at hk hj
      rw [nbK_pt hxp, nbK_pt hxp] at e
      have e' : plK PL x k = plK PL x j := by omega
      rcases lt_trichotomy k j with hkj | hkj | hkj
      · exact absurd e'.symm (h2 x hxp j hj k hkj)
      · exact hkj
      · exact absurd e' (h2 x hxp k hk j hkj)
    · simp only [hxp, if_false] at hk hj
      rw [nbK_ln (by omega), nbK_ln (by omega)] at e
      exact hlpd (x - 1755) (by omega) k hk j hj e

theorem layK_sound {b cnt LAY PAR : ℕ} (h : layK lp PL b cnt LAY PAR = true) :
    b < 4680 ∧ layAt LAY b = 0 ∧
    ((Finset.range 4680).filter (fun x => layAt LAY x = 8)).card = cnt ∧
    ∀ x < 4680, layAt LAY x ≤ 8 ∧
      (x ≠ b → adjK lp x (fw 13 PAR x) = true ∧ layAt LAY (fw 13 PAR x) + 1 = layAt LAY x) ∧
      (∀ k < degK x, layAt LAY (nbK lp PL x k) ≤ layAt LAY x + 1) ∧
      (1 ≤ layAt LAY x → layAt LAY x ≤ 7 → ∀ k < degK x,
        layAt LAY (nbK lp PL x k) + 1 = layAt LAY x → nbK lp PL x k = fw 13 PAR x) := by
  have inner : ∀ (F : ℕ → ℕ) k,
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
        ∑ l ∈ Finset.range k, F l := by
    intro F k
    induction k with
    | zero => simp
    | succ k ih =>
      change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
      rw [ih, Finset.sum_range_succ, Nat.add_comm]
  have outer : ∀ (m : ℕ) (f : ℕ → ℕ) hi, CFSG.KC.Loop.sumBelow m hi f =
      ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m) := by
    intro m f hi
    induction hi with
    | zero => simp [CFSG.KC.Loop.sumBelow]
    | succ hi ih =>
      have e : CFSG.KC.Loop.sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0
          (fun l ih2 => Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i)
            (Nat.blt i m)) (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64)
          (CFSG.KC.Loop.sumBelow m hi f) := rfl
      have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
        change hi <<< 6 + l = _
        rw [Nat.shiftLeft_eq, Nat.mul_comm]
      rw [e, inner, ih, Nat.mul_succ, Finset.sum_range_add]
      simp only [e2]
      exact Nat.add_comm _ _
  have spec : ∀ {m hi : ℕ} (f : ℕ → ℕ), m ≤ 64 * hi →
      CFSG.KC.Loop.sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
    intro m hi f hm
    rw [outer]
    obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
    rw [hd, Finset.sum_range_add]
    have h2 : ∑ l ∈ Finset.range d,
        Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      have hb : Nat.blt (m + l) m = false := by
        cases e : Nat.blt (m + l) m
        · rfl
        · rw [Nat.blt_eq] at e
          omega
      rw [hb]
    rw [h2, Nat.add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hb : Nat.blt i m = true := by
      rw [Nat.blt_eq]
      exact Finset.mem_range.1 hi
    rw [hb]
  unfold layK at h
  simp only [bAnd_eq', Bool.and_eq_true, allN_iff', strictB_eq'] at h
  obtain ⟨hb, h0, hc, hx⟩ := h
  refine ⟨by simpa using hb, Nat.eq_of_beq_eq_true h0, ?_, fun x hx' => ?_⟩
  · have e : ∑ i ∈ Finset.range 4680,
        Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (layAt LAY i) 8) = cnt :=
      (spec _ (by decide)).symm.trans (Nat.eq_of_beq_eq_true hc)
    rw [← e, Finset.card_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [beq_d]
    by_cases h8 : layAt LAY x = 8 <;> simp [h8]
  · have hxx := hx x hx'
    simp only [allNb, allN_iff'] at hxx
    obtain ⟨hl8, hpar, hnb, hlast⟩ := hxx
    refine ⟨by simpa using hl8, fun hxb => ?_, fun k hk => ?_, fun h1 h7 k hk e => ?_⟩
    · simp only [bIf_d, beq_d, hxb, decide_false, Bool.false_eq_true, if_false,
        Bool.and_eq_true, decide_eq_true_eq] at hpar
      exact ⟨hpar.1, hpar.2⟩
    · simpa using hnb k hk
    · have c0 : ¬ layAt LAY x = 0 := by omega
      have c7 : ¬ 7 < layAt LAY x := by omega
      simp only [bIf_d, beq_d, blt_d, c0, c7, decide_false, Bool.false_eq_true, if_false,
        allN_iff'] at hlast
      have := hlast k hk
      simpa [e] using this

section Graph

variable {V : Type*} {Γ : SimpleGraph V} {c : V → ℕ} {d : ℕ → V}

theorem layers_of_layK (hc : ∀ x, c x < 4680) (hdc : ∀ x, d (c x) = x)
    (hcd : ∀ n < 4680, c (d n) = n) (hadj : ∀ x y, Γ.Adj x y ↔ adjK lp (c x) (c y) = true)
    (hnb : NbOK lp PL) {b cnt LAY PAR : ℕ} (h : layK lp PL b cnt LAY PAR = true) :
    Layers Γ 8 (d b) (fun x => layAt LAY (c x)) ∧ {y | Γ.dist (d b) y = 8}.ncard = cnt := by
  obtain ⟨hb, h0, hcnt, hx⟩ := layK_sound h
  have hinj : Function.Injective c := fun x y e => by rw [← hdc x, e, hdc y]
  have hadjc : ∀ x y, Γ.Adj x y → ∃ k < degK (c x), nbK lp PL (c x) k = c y := fun x y hxy =>
    (hnb.1 (c x) (hc x) (c y)).1 ((hadj x y).1 hxy)
  have hL : Layers Γ 8 (d b) (fun x => layAt LAY (c x)) := by
    refine ⟨by simp only [hcd b hb, h0], fun x => (hx _ (hc x)).1, ?_, ?_, ?_⟩
    · intro x hxb
      have hne : c x ≠ b := fun e => hxb (by rw [← hdc x, e])
      obtain ⟨hpa, hpl⟩ := (hx _ (hc x)).2.1 hne
      have hp : fw 13 PAR (c x) < 4680 := (adjK_iff.1 hpa).1
      refine ⟨d (fw 13 PAR (c x)), ?_, ?_⟩
      · rw [hadj, hcd _ hp]
        exact hpa
      · simp only [hcd _ hp]
        exact hpl
    · intro x y hxy
      obtain ⟨k, hk, e⟩ := hadjc x y hxy
      have := (hx _ (hc x)).2.2.1 k hk
      rwa [e] at this
    · intro x y z h1 h7 hy hz ey ez
      obtain ⟨k, hk, e⟩ := hadjc x y hy
      obtain ⟨j, hj, e'⟩ := hadjc x z hz
      have u := (hx _ (hc x)).2.2.2 h1 (by omega)
      have uy := u k hk (by rw [e]; exact ey)
      have uz := u j hj (by rw [e']; exact ez)
      exact hinj (by rw [← e, ← e', uy, uz])
  refine ⟨hL, ?_⟩
  have hset : c '' {y | Γ.dist (d b) y = 8} =
      ↑((Finset.range 4680).filter (fun x => layAt LAY x = 8)) := by
    ext n
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hL.dist_eq] at hy
      exact ⟨hc y, hy⟩
    · rintro ⟨hn, h8⟩
      refine ⟨d n, ?_, hcd n hn⟩
      rw [hL.dist_eq, hcd n hn]
      exact h8
  rw [← Set.ncard_image_of_injective _ hinj, hset, Set.ncard_coe_finset, hcnt]

end Graph

theorem cycK_sound {C : List ℕ} (h : cycK lp C = true) :
    C.length = 16 ∧ ∀ i < 16, adjK lp (C.getD i 0) (C.getD ((i + 1) % 16) 0) = true ∧
      C.getD i 0 ≠ C.getD ((i + 2) % 16) 0 := by
  unfold cycK at h
  simp only [bAnd_eq', Bool.and_eq_true, allN_iff'] at h
  obtain ⟨hl, hc⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true hl, fun i hi => ?_⟩
  obtain ⟨ha, hn⟩ := hc i hi
  refine ⟨ha, fun e => ?_⟩
  change bIf(Nat.beq (C.getD i 0) (C.getD ((i + 2) % 16) 0), false, true) = true at hn
  rw [e, Nat.beq_refl] at hn
  exact Bool.false_ne_true hn

theorem bindK_sound {F FI A : ℕ → ℕ} {ws : List (List ℕ)} (h : bindK F FI A ws = true) :
    ∀ j (hj : j < ws.length), ∀ x < 1755, gp (A j) x = wPt F FI ws[j] x := by
  intro j hj x hx
  have := (allL_iff ws 0).1 h j hj
  rw [Nat.zero_add, strictB_eq', allN_iff'] at this
  exact Nat.eq_of_beq_eq_true (this x hx)

theorem lineMap_iff {f : ℕ → ℕ} {v w : ℕ} :
    lineMap lp f v w = true ↔ ∀ k < 3, onLine lp (f (lp (3 * v + k))) w = true := by
  unfold lineMap
  rw [allN_iff']
  rfl

theorem actV_pt {f : ℕ → ℕ} {y x : ℕ} (hy : y < 1755) :
    actV lp f y x = true ↔ x < 1755 ∧ f y = x := by
  simp [actV, bIf_d, blt_d, beq_d, hy]

theorem actV_ln {f : ℕ → ℕ} {y x : ℕ} (hy : 1755 ≤ y) :
    actV lp f y x = true ↔ 1755 ≤ x ∧ x < 4680 ∧
      ∀ k < 3, onLine lp (f (lp (3 * (y - 1755) + k))) (x - 1755) = true := by
  have : ¬ y < 1755 := by omega
  simp only [actV, bIf_d, blt_d, ble_d, this, decide_false, if_false, Nat.sub_eq]
  rw [← lineMap_iff]
  by_cases h1 : 1755 ≤ x <;> by_cases h2 : x < 4680 <;> simp [h1, h2]

theorem fixV_sound {f : ℕ → ℕ} {a : ℕ} (h : fixV lp PL f a = true) :
    actV lp f a a = true ∧ ∀ k < degK a, actV lp f (nbK lp PL a k) (nbK lp PL a k) = true := by
  unfold fixV allNb at h
  rw [bIf_d] at h
  by_cases h1 : actV lp f a a = true
  · rw [if_pos h1, allN_iff'] at h
    exact ⟨h1, h⟩
  · simp [h1] at h

theorem recK_sound {A : ℕ → ℕ} {k root cnt LAY ORD PA LB PS : ℕ}
    (h : recK lp A k root cnt LAY ORD PA LB PS = true) :
    fw 13 ORD 0 = root ∧
    (∀ i < cnt, fw 13 ORD i < 4680 ∧ (i ≠ 0 → fw 11 PA i < i ∧ fw 3 LB i < k ∧
      actV lp (gp (A (fw 3 LB i))) (fw 13 ORD (fw 11 PA i)) (fw 13 ORD i) = true)) ∧
    ∀ x < 4680, layAt LAY x = 8 → fw 13 PS x < cnt ∧ fw 13 ORD (fw 13 PS x) = x := by
  unfold recK at h
  simp only [bAnd_eq', Bool.and_eq_true, allN_iff', strictB_eq'] at h
  obtain ⟨h0, hst, hcov⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h0, fun i hi => ?_, fun x hx hl => ?_⟩
  · have hi' := hst i hi
    by_cases hi0 : i = 0
    · simp only [bIf_d, blt_d, beq_d, hi0, decide_true, if_true, Bool.and_true,
        decide_eq_true_eq] at hi'
      rw [hi0]
      exact ⟨hi'.1, fun h => absurd rfl h⟩
    · simp only [bIf_d, bAnd_eq', blt_d, beq_d, hi0, decide_false, Bool.false_eq_true, if_false,
        Bool.and_eq_true, decide_eq_true_eq] at hi'
      exact ⟨hi'.1, fun _ => hi'.2⟩
  · have hx' := hcov x hx
    simp only [bIf_d, bAnd_eq', blt_d, beq_d, hl, decide_true, if_true, Bool.and_eq_true,
      decide_eq_true_eq] at hx'
    exact hx'

theorem rec_reach {X V : Type*} [Group X] [MulAction X V] {c : ℕ → V} {a : ℕ → X} {S : Set X}
    {A : ℕ → ℕ} {k root cnt LAY ORD PA LB PS : ℕ} (ha : ∀ j < k, a j ∈ S)
    (hact : ∀ j < k, ∀ y x, y < 4680 → x < 4680 → actV lp (gp (A j)) y x = true →
      a j • c y = c x)
    (h : recK lp A k root cnt LAY ORD PA LB PS = true) :
    ∀ x < 4680, layAt LAY x = 8 → ∃ g ∈ Subgroup.closure S, g • c root = c x := by
  obtain ⟨h0, hst, hcov⟩ := recK_sound h
  have key : ∀ i < cnt, ∃ g ∈ Subgroup.closure S, g • c root = c (fw 13 ORD i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        exact ⟨1, Subgroup.one_mem _, by rw [one_smul, h0]⟩
      · obtain ⟨hlt, hpi, hlb, hav⟩ := (hst i hi).1, (hst i hi).2 hi0
        obtain ⟨g, hg, e⟩ := ih _ hpi (by omega)
        refine ⟨a (fw 3 LB i) * g,
          Subgroup.mul_mem _ (Subgroup.subset_closure (ha _ hlb)) hg, ?_⟩
        rw [mul_smul, e]
        exact hact _ hlb _ _ (hst _ (by omega)).1 hlt hav
  intro x hx h8
  obtain ⟨hq, e⟩ := hcov x hx h8
  obtain ⟨g, hg, e'⟩ := key _ hq
  exact ⟨g, hg, by rw [e', e]⟩

theorem locK_sound {F FI : ℕ → ℕ} {a b0 d : ℕ} {ws : List (List ℕ)} {prs : List ℕ}
    (h : locK lp F FI PL a b0 d ws prs = true) :
    ws.length = d * (d - 1) ∧ prs.length = ws.length ∧ (ws.headD [1]).length = 0 ∧
    prs.headD 0 = 1 ∧ (∀ i < prs.length, ∀ j < i, prs.getD i 0 ≠ prs.getD j 0) ∧
    (∀ u < d, ∀ u' < d, u ≠ u' → u * d + u' ∈ prs) ∧
    ∀ i (hi : i < ws.length), prs.getD i 0 / d < d ∧ prs.getD i 0 / d ≠ prs.getD i 0 % d ∧
      actV lp (wPt F FI ws[i]) a a = true ∧ actV lp (wPt F FI ws[i]) b0 b0 = true ∧
      actV lp (wPt F FI ws[i]) (nbK lp PL a 0) (nbK lp PL a (prs.getD i 0 / d)) = true ∧
      actV lp (wPt F FI ws[i]) (nbK lp PL a 1) (nbK lp PL a (prs.getD i 0 % d)) = true := by
  unfold locK distK at h
  simp only [bAnd_eq', Bool.and_eq_true, allN_iff', strictB_eq'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, fun i hi j hj e => ?_, fun u hu u' hu' hne => ?_, fun i hi => ?_⟩
  · have := h5 i hi j hj
    rw [e, Nat.beq_refl] at this
    exact Bool.false_ne_true this
  · have := h6 u hu u' hu'
    simp only [bIf_d, beq_d, hne, decide_false, Bool.false_eq_true, if_false] at this
    exact memK_iff.1 this
  · have hr := (allL_iff ws 0).1 h7 i hi
    rw [Nat.zero_add] at hr
    simp only [strictB_eq', bAnd_eq', Bool.and_eq_true, bIf_d, blt_d, beq_d,
      decide_eq_true_eq] at hr
    obtain ⟨hu, hne, a1, a2, a3, a4⟩ := hr
    refine ⟨hu, fun e => ?_, a1, a2, a3, a4⟩
    have e' : Nat.div (prs.getD i 0) d = Nat.mod (prs.getD i 0) d := e
    exact absurd e' (by simpa using hne)

theorem smallK_sound {A : ℕ → ℕ} {n1 t q0 : ℕ} (h : smallK lp A PL n1 t q0 = true) :
    (∀ x < 1755, gp n1 (gp n1 x) = x) ∧ gp n1 0 = 0 ∧ gp t 0 = 0 ∧ lineMap lp (gp t) 0 0 = true ∧
    lineMap lp (gp q0) 0 0 = true ∧
    (∀ k < 5, plK PL 0 k ≠ 0 → ∃ i < 4, lineMap lp (tn1 t n1 i) 0 (plK PL 0 k) = true) ∧
    (∀ j < 5, gp n1 (gp (A j) (gp n1 0)) = 0 ∧
      lineMap lp (fun x => gp n1 (gp (A j) (gp n1 x))) 0 0 = true) ∧
    ∀ p < 1755, p ≠ 0 → gp t p = p → ∃ j < 5, gp (A j) p ≠ p := by
  unfold smallK at h
  simp only [bAnd_eq', Bool.and_eq_true, allN_iff', strictB_eq'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨fun x hx => Nat.eq_of_beq_eq_true (h1 x hx), Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3, h4, h5, fun k hk hne => ?_, fun j hj => ?_, fun p hp hp0 htp => ?_⟩
  · have hk' := h6 k hk
    simp only [bIf_d, beq_d, hne, decide_false, Bool.false_eq_true, if_false] at hk'
    exact exists_of_anyN hk'
  · obtain ⟨e1, e2⟩ := h7 j hj
    exact ⟨Nat.eq_of_beq_eq_true e1, e2⟩
  · have hp' := h8 p hp
    simp only [bIf_d, beq_d, hp0, htp, decide_false, decide_true, Bool.false_eq_true, if_false,
      if_true] at hp'
    obtain ⟨j, hj, e⟩ := exists_of_anyN hp'
    refine ⟨j, hj, fun e' => ?_⟩
    simp [e'] at e

theorem farK_sound {LAY : ℕ} (h : farK LAY = true) :
    layAt LAY 87 = 8 ∧ ∀ p < 1755, layAt LAY p ≤ 6 ∨ layAt LAY p = 8 := by
  unfold farK at h
  simp only [bAnd_eq', Bool.and_eq_true, allN_iff', strictB_eq'] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun p hp => ?_⟩
  have hp' := h.2 p hp
  simp only [bIf_d, ble_d, beq_d] at hp'
  by_cases h6 : layAt LAY p ≤ 6
  · exact Or.inl h6
  · simp only [h6, decide_false, Bool.false_eq_true, if_false, decide_eq_true_eq] at hp'
    exact Or.inr hp'

theorem cycFrom_iff {g : ℕ → ℕ} {x : ℕ} :
    ∀ n y, cycFrom g x n y = true ↔ (∀ j < n, g^[j] y ≠ x) ∧ g^[n] y = x
  | 0, y => by simp [cycFrom, beq_d]
  | n + 1, y => by
    change Bool.rec (motive := fun _ => Bool) (strictB (g y) (cycFrom g x n)) false
      (Nat.beq y x) = true ↔ _
    rw [strictB_eq', bIf_d, beq_d]
    by_cases hy : y = x
    · simp only [hy, decide_true, if_true, Bool.false_eq_true, false_iff, not_and]
      intro h
      exact absurd rfl (h 0 (by omega))
    · rw [if_neg (by simpa using hy), cycFrom_iff n (g y)]
      simp only [Function.iterate_succ_apply]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun j hj => ?_, h2⟩
        cases j with
        | zero => exact hy
        | succ j => simpa [Function.iterate_succ_apply] using h1 j (by omega)
      · rintro ⟨h1, h2⟩
        exact ⟨fun j hj => by simpa [Function.iterate_succ_apply] using h1 (j + 1) (by omega), h2⟩

theorem witRow_sound {A : ℕ → ℕ} {LAY ORD PA LB PS n1 q0 i : ℕ} {r : List ℕ}
    (h : witRow A LAY ORD PA LB PS n1 q0 i r = true) :
    i = 0 ∨
    (∃ x < 1755, gp n1 (sigK A LAY ORD PA LB PS (fw 13 ORD i)
        (gp n1 (sigK A LAY ORD PA LB PS (fw 13 ORD i) x))) ≠ x) ∨
    (∃ x < 1755, ∃ L, 0 < L ∧ ¬ L ∣ 35942400 ∧
      (∀ m, 0 < m → m < L →
        (fun y => gp n1 (sigK A LAY ORD PA LB PS (fw 13 ORD i) (gp q0 y)))^[m] x ≠ x) ∧
      (fun y => gp n1 (sigK A LAY ORD PA LB PS (fw 13 ORD i) (gp q0 y)))^[L] x = x) := by
  unfold witRow at h
  simp only [strictB_eq'] at h
  by_cases hk0 : r.headD 0 = 0
  · rw [hk0, Nat.beq_refl] at h
    exact Or.inl (Nat.eq_of_beq_eq_true h)
  have hb0 : Nat.beq (r.headD 0) 0 = false := by
    cases e : Nat.beq (r.headD 0) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk0
  rw [hb0] at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨-, hx, hrest⟩ := h
  have hx' : r.getD 1 0 < 1755 := by simpa using hx
  by_cases hk1 : r.headD 0 = 1
  · rw [hk1, Nat.beq_refl] at hrest
    simp only [strictB_eq'] at hrest
    refine Or.inr (Or.inl ⟨r.getD 1 0, hx', fun e => ?_⟩)
    rw [e, Nat.beq_refl] at hrest
    exact Bool.false_ne_true hrest
  have hb1 : Nat.beq (r.headD 0) 1 = false := by
    cases e : Nat.beq (r.headD 0) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk1
  rw [hb1] at hrest
  simp only [bAnd_eq', Bool.and_eq_true, strictB_eq'] at hrest
  obtain ⟨-, hL0, hdiv, hcyc⟩ := hrest
  have hL : 0 < r.getD 2 0 := by simpa using hL0
  refine Or.inr (Or.inr ⟨r.getD 1 0, hx', r.getD 2 0, hL, fun hd => ?_, ?_, ?_⟩)
  · have hm : Nat.mod 35942400 (r.getD 2 0) = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [hm] at hdiv
    exact Bool.false_ne_true hdiv
  · obtain ⟨hne, -⟩ := (cycFrom_iff _ _).1 hcyc
    intro m hm0 hmL
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Function.iterate_succ_apply]
    exact hne j (by simp only [Nat.sub_eq]; omega)
  · obtain ⟨-, he⟩ := (cycFrom_iff _ _).1 hcyc
    obtain ⟨L', hL'⟩ : ∃ L', r.getD 2 0 = L' + 1 := ⟨r.getD 2 0 - 1, by omega⟩
    rw [hL', Function.iterate_succ_apply]
    rw [hL'] at he
    simpa using he

theorem witK_sound {A : ℕ → ℕ} {LAY ORD PA LB PS n1 q0 i₀ : ℕ} {R : List (List ℕ)}
    (h : witK A LAY ORD PA LB PS n1 q0 i₀ R = true) :
    ∀ i (hi : i < R.length), witRow A LAY ORD PA LB PS n1 q0 (i₀ + i) R[i] = true := by
  intro i hi
  have := (allL_iff R 0).1 h i hi
  rwa [Nat.zero_add] at this

section Rigid

variable {A : ℕ → ℕ} {a : ℕ → Pm} {LAY ORD PA LB PS : ℕ}

theorem sigR_succ (k n j : ℕ) : sigR A ORD PA LB k (n + 1) j =
    if j = 0 then k else gp (A (fw 3 LB j)) (sigR A ORD PA LB k n (fw 11 PA j)) := by
  change Bool.rec (motive := fun _ => ℕ) (strictN (sigR A ORD PA LB k n (fw 11 PA j))
    (fun y => gp (A (fw 3 LB j)) y)) k (Nat.beq j 0) = _
  rw [strictN_eq', nIf_d, beq_d]
  by_cases hj : j = 0 <;> simp [hj]

theorem rec_pts (hA : ∀ j < 5, PR (A j) (a j))
    (hrec : recK lp A 5 87 1024 LAY ORD PA LB PS = true) :
    ∀ i < 1024, fw 13 ORD i < 1755 ∧
      (i ≠ 0 → ev (a (fw 3 LB i)) (fw 13 ORD (fw 11 PA i)) = fw 13 ORD i) := by
  obtain ⟨h0, hst, -⟩ := recK_sound hrec
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [h0]
      exact ⟨by norm_num, fun h => absurd rfl h⟩
    · obtain ⟨hpi, hlb, hav⟩ := (hst i hi).2 hi0
      have hp := (ih _ hpi (by omega)).1
      obtain ⟨hlt, e⟩ := (actV_pt hp).1 hav
      refine ⟨hlt, fun _ => ?_⟩
      rw [← gp_ev (hA _ hlb) hp]
      exact e

theorem sig_eq (hA : ∀ j < 5, PR (A j) (a j))
    (hrec : recK lp A 5 87 1024 LAY ORD PA LB PS = true) (hfar : farK LAY = true)
    {σ : Pm} (h6 : ∀ n < 1755, layAt LAY n ≤ 6 → ev σ n = n)
    (hc : ∀ j < 5, σ * a j = a j * σ) :
    ∀ x < 1755, ev σ x = sigK A LAY ORD PA LB PS (ev σ 87) x := by
  obtain ⟨h0, hst, hcov⟩ := recK_sound hrec
  have hpts := rec_pts hA hrec
  have hrecσ : ∀ i < 1024, ∀ n, i < n → ev σ (fw 13 ORD i) = sigR A ORD PA LB (ev σ 87) n i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi n hn
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [sigR_succ]
      by_cases hi0 : i = 0
      · subst hi0
        rw [if_pos rfl, h0]
      · rw [if_neg hi0]
        obtain ⟨hpi, hlb, -⟩ := (hst i hi).2 hi0
        have hp := (hpts (fw 11 PA i) (by omega)).1
        rw [← ih _ hpi (by omega) n (by omega), gp_ev (hA _ hlb) (ev_lt σ hp),
          ← (hpts i hi).2 hi0, ← ev_mul _ _ hp, ← ev_mul _ _ hp, hc _ hlb]
  intro x hx
  obtain ⟨-, hfar'⟩ := farK_sound hfar
  unfold sigK
  rw [nIf_d, ble_d, strictN_eq']
  by_cases hl : layAt LAY x ≤ 6
  · rw [if_pos (by simpa using hl)]
    exact h6 x hx hl
  · rw [if_neg (by simpa using hl)]
    have h8 : layAt LAY x = 8 := (hfar' x hx).resolve_left hl
    obtain ⟨hq, e⟩ := hcov x (by omega) h8
    rw [← hrecσ _ hq (fw 13 PS x + 1) (by omega), e]

theorem rigid (hA : ∀ j < 5, PR (A j) (a j))
    (hrec : recK lp A 5 87 1024 LAY ORD PA LB PS = true) (hfar : farK LAY = true)
    {N1 Q0 : ℕ} {n₁ q₀ : Pm} (hN1 : PR N1 n₁) (hQ0 : PR Q0 q₀)
    (hwit : ∀ i < 1024, ∃ r, witRow A LAY ORD PA LB PS N1 Q0 i r = true)
    {σ : Pm} (h6 : ∀ n < 1755, layAt LAY n ≤ 6 → ev σ n = n)
    (hc : ∀ j < 5, σ * a j = a j * σ) (h2 : (n₁ * σ) ^ 2 = 1)
    (hq : (n₁ * σ * q₀) ^ 35942400 = 1) : σ = 1 := by
  obtain ⟨h0, -, hcov⟩ := recK_sound hrec
  obtain ⟨h87, hfar'⟩ := farK_sound hfar
  have hs := sig_eq hA hrec hfar h6 hc
  have h1 := sig_eq (σ := 1) hA hrec hfar (fun n _ _ => ev_one n) (fun j _ => by simp)
  simp only [ev_one] at h1
  have hσ87 : ev σ 87 < 1755 := ev_lt σ (by norm_num)
  have hl87 : layAt LAY (ev σ 87) = 8 := by
    rcases hfar' _ hσ87 with hl | hl
    · exfalso
      have e := h6 _ hσ87 hl
      have e' := ev_inj σ hσ87 (by norm_num) e
      rw [e', h87] at hl
      omega
    · exact hl
  obtain ⟨hq', e87⟩ := hcov _ (by omega) hl87
  set i := fw 13 PS (ev σ 87) with hi
  obtain ⟨r, hr⟩ := hwit i hq'
  have hsk : ∀ x < 1755, sigK A LAY ORD PA LB PS (fw 13 ORD i) x = ev σ x := by
    intro x hx
    rw [e87, hs x hx]
  have hσ : ev σ 87 = 87 := by
    rcases witRow_sound hr with hi0 | ⟨x, hx, hne⟩ | ⟨x, hx, L, hL0, hLd, hmin, hret⟩
    · rw [← e87, hi0, h0]
    · exfalso
      apply hne
      have hy : ev n₁ (ev σ x) < 1755 := ev_lt n₁ (ev_lt σ hx)
      have key : ev ((n₁ * σ) ^ 2) x = x := by rw [h2, ev_one]
      rw [sq, ev_mul (n₁ * σ) (n₁ * σ) hx, ev_mul n₁ σ hx, ev_mul n₁ σ hy] at key
      rw [hsk x hx, gp_ev hN1 (ev_lt σ hx), hsk _ hy, gp_ev hN1 (ev_lt σ hy)]
      exact key
    · exfalso
      have hG : ∀ y < 1755, gp N1 (sigK A LAY ORD PA LB PS (fw 13 ORD i) (gp Q0 y)) =
          ev (n₁ * σ * q₀) y := by
        intro y hy
        rw [gp_ev hQ0 hy, hsk _ (ev_lt q₀ hy), gp_ev hN1 (ev_lt σ (ev_lt q₀ hy)),
          ev_mul (n₁ * σ) q₀ hy, ev_mul n₁ σ (ev_lt q₀ hy)]
      have hit : ∀ m, (fun y => gp N1 (sigK A LAY ORD PA LB PS (fw 13 ORD i) (gp Q0 y)))^[m] x =
          (fun y => ev (n₁ * σ * q₀) y)^[m] x := by
        intro m
        induction m with
        | zero => rfl
        | succ m ihm =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihm]
          apply hG
          rw [ev_pow_mul _ hx]
          exact ev_lt _ hx
      set g := n₁ * σ * q₀
      have hret' : ev (g ^ L) x = x := by rw [← ev_pow_mul _ hx, ← hit]; exact hret
      have hgN : ev (g ^ 35942400) x = x := by rw [hq, ev_one]
      have hgm : ∀ m, ev (g ^ (L * m)) x = x := by
        intro m
        induction m with
        | zero => simp [ev_one]
        | succ m ihm =>
          rw [Nat.mul_succ, pow_add, ev_mul _ _ hx, hret', ihm]
      have hlt' := Nat.mod_lt 35942400 hL0
      have hmod : ev (g ^ (35942400 % L)) x = x := by
        have e := Nat.mod_add_div 35942400 L
        rw [← e, pow_add, ev_mul _ _ hx, hgm] at hgN
        exact hgN
      have hpos : 0 < 35942400 % L := Nat.pos_of_ne_zero (fun h0' => hLd (Nat.dvd_of_mod_eq_zero h0'))
      apply hmin _ hpos hlt'
      rw [hit, ev_pow_mul _ hx]
      exact hmod
  apply ev_eq_one
  intro n hn
  rw [hs n hn, hσ, ← h1 n hn]

end Rigid

end CFSG.KC.TitsOctSound

end
