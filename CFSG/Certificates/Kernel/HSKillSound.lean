module

public import Certificates.Data.Kernel.HSKill
public import CFSG.Certificates.Kernel.HOrbSound
import CFSG.Certificates.Kernel.Co2KillSound
import CFSG.Certificates.Kernel.LceSP.Main
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Certificates.HSKill

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.HSK CFSG.Certificates.LCE CFSG.Certificates.HO

theorem sliceEnt_eq (e lo cnt : ℕ) :
    HSK.sliceEnt e lo cnt = 4 * cnt + (wWord e / 256 ^ lo % 256 ^ cnt) <<< 12 :=
  Co2Kill.sliceEnt_eq e lo cnt

theorem catEnt_spec {G : Type*} [Group G] (gen : ℕ → G) {e f b n1 n2 : ℕ}
    (he : entOK e b n1 = true) (hf : entOK f b n2 = true) (hn : n1 + n2 < 1024) :
    entOK (HSK.catEnt e f) b (n1 + n2) = true ∧ wLen (HSK.catEnt e f) = wLen e + wLen f ∧
      bval gen (wWord (HSK.catEnt e f)) (wLen (HSK.catEnt e f)) =
        bval gen (wWord e) (wLen e) * bval gen (wWord f) (wLen f) :=
  Co2Kill.catEnt_spec gen he hf hn

theorem letEnt_spec {G : Type*} [Group G] (gen : ℕ → G) {c : ℕ} (hc : c < 254) :
    entOK (HSK.letEnt c) 254 1 = true ∧ wLen (HSK.letEnt c) = 1 ∧
      bval gen (wWord (HSK.letEnt c)) (wLen (HSK.letEnt c)) = letV gen c :=
  Co2Kill.letEnt_spec gen hc

theorem gw_spec {G : Type*} [Group G] (gen : ℕ → G) {GW : ℕ → ℕ} {k : ℕ}
    (hk : conjOK (GW k) = true ∧ entOK (GW k) (nat_lit 4) (nat_lit 63) = true) :
    entOK (HSK.sigma GW k) 254 31 = true ∧ entOK (HSK.sigInv GW k) 254 31 = true ∧
      bval gen (wWord (HSK.sigInv GW k)) (wLen (HSK.sigInv GW k)) =
        (bval gen (wWord (HSK.sigma GW k)) (wLen (HSK.sigma GW k)))⁻¹ ∧
      bval gen (wWord (GW k)) (wLen (GW k)) =
        (bval gen (wWord (HSK.sigma GW k)) (wLen (HSK.sigma GW k)))⁻¹ * gen 0 *
          bval gen (wWord (HSK.sigma GW k)) (wLen (HSK.sigma GW k)) := by
  obtain ⟨hc, hent⟩ := hk
  replace hent : entOK (GW k) 4 63 = true := hent
  unfold conjOK at hc
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at hc
  obtain ⟨hodd, hmid, hsig⟩ := hc
  obtain ⟨hWlt, hn, hl⟩ := (entOK_iff _ _ _).1 hent
  set n := wLen (GW k) with hndef
  set W := wWord (GW k) with hWdef
  have hgh : HSK.gHalf GW k = n / 2 := rfl
  set h := n / 2 with hhdef
  have hn2 : n = h + (1 + h) := by
    change n = Nat.succ (2 * h) at hodd
    omega
  have hh31 : h ≤ 31 := by omega
  have hW : W < 256 ^ (h + (1 + h)) := by rw [← hn2, ← two_pow_eight_mul]; exact hWlt
  set F := W % 256 ^ h with hFdef
  set S := W / 256 ^ (h + 1) with hSdef
  have hF : F < 256 ^ h := Nat.mod_lt _ (by positivity)
  have hS : S < 256 ^ h := by
    rw [hSdef, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc W < 256 ^ (h + (1 + h)) := hW
      _ = 256 ^ (h + (h + 1)) := by ring_nf
  have hmid' : W / 256 ^ h % 256 = 0 := by rw [← byte_eq]; exact hmid
  have hdec : W = F + (0 + S * 256 ^ 1) * 256 ^ h := by
    have h1 := Nat.mod_add_div W (256 ^ h)
    have h2 := Nat.mod_add_div (W / 256 ^ h) 256
    have h3 : W / 256 ^ h / 256 = S := by
      rw [hSdef, Nat.div_div_eq_div_mul, pow_succ]
    rw [hmid', h3] at h2
    rw [pow_one]
    calc W = F + 256 ^ h * (W / 256 ^ h) := h1.symm
      _ = F + (0 + S * 256) * 256 ^ h := by rw [← h2]; ring
  have hI : HSK.sigInv GW k = 4 * h + F <<< 12 := by
    unfold HSK.sigInv
    rw [sliceEnt_eq, hgh, pow_zero, Nat.div_one]
  have hSg : HSK.sigma GW k = 4 * h + S <<< 12 := by
    unfold HSK.sigma
    have hS' : wWord (GW k) / 256 ^ (Nat.succ h) < 256 ^ h := hS
    rw [sliceEnt_eq, hgh, Nat.mod_eq_of_lt hS']
  have hh' : h < 1024 := by omega
  have hletF : ∀ i < h, wLet F i < 254 := by
    intro i hi
    have := hl i (by omega)
    rw [wLet_eq] at this ⊢
    rw [hdec, byte_add_high hi] at this
    omega
  have hletS : ∀ i < h, wLet S i < 254 := by
    intro i hi
    have := hl (h + 1 + i) (by omega)
    rw [wLet_eq] at this ⊢
    rw [hSdef, Nat.div_div_eq_div_mul, ← pow_add]
    omega
  have hIok : entOK (HSK.sigInv GW k) 254 31 = true := by
    rw [hI, entOK_iff, wLen_mk _ _ hh', wWord_mk _ _ hh', two_pow_eight_mul]
    exact ⟨hF, hh31, hletF⟩
  have hSok : entOK (HSK.sigma GW k) 254 31 = true := by
    rw [hSg, entOK_iff, wLen_mk _ _ hh', wWord_mk _ _ hh', two_pow_eight_mul]
    exact ⟨hS, hh31, hletS⟩
  have hsig' : HSK.sigInv GW k = invEnt (HSK.sigma GW k) := hsig
  have hinvS : bval gen (wWord (HSK.sigInv GW k)) (wLen (HSK.sigInv GW k)) =
      (bval gen (wWord (HSK.sigma GW k)) (wLen (HSK.sigma GW k)))⁻¹ := by
    rw [hsig', (Co2Kill.invEnt_spec gen hSok (by norm_num)).2.2]
  refine ⟨hSok, hIok, hinvS, ?_⟩
  rw [← hinvS, hI, hSg, wLen_mk _ _ hh', wWord_mk _ _ hh', wLen_mk _ _ hh', wWord_mk _ _ hh',
    hn2, hdec, bval_concat gen hF, bval_concat gen (by norm_num : (0 : ℕ) < 256 ^ 1),
    bval_one gen (by norm_num : (0 : ℕ) < 256)]
  simp [letV, mul_assoc]

theorem gwOK_spec {GW : ℕ → ℕ} {ng : ℕ} (h : gwOK GW ng = true) :
    ∀ k, 1 ≤ k → k ≤ ng → conjOK (GW k) = true ∧ entOK (GW k) (nat_lit 4) (nat_lit 63) = true := by
  induction ng with
  | zero => intro k h1 h0; omega
  | succ n ih =>
    have e : gwOK GW (n + 1) = andB (gwOK GW n)
        (andB (conjOK (GW (n + 1))) (entOK (GW (n + 1)) (nat_lit 4) (nat_lit 63))) := rfl
    rw [e] at h
    simp only [andB_eq, Bool.and_eq_true] at h
    intro k h1 hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with hk' | rfl
    · exact ih h.1 k h1 (by omega)
    · exact h.2

theorem letInvAB_spec {G : Type*} [Group G] (gen : ℕ → G) {GW : ℕ → ℕ} {ng : ℕ} (hng : ng < 128)
    (hGW : ∀ k, 1 ≤ k → k ≤ ng → conjOK (GW k) = true ∧ entOK (GW k) (nat_lit 4) (nat_lit 63) = true)
    {x : ℕ} (hx : x < 2 * ng) :
    entOK (HSK.letInvAB GW x) 254 63 = true ∧
      bval gen (wWord (HSK.letInvAB GW x)) (wLen (HSK.letInvAB GW x)) =
        (letV (fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1)))) x)⁻¹ := by
  have hs : Nat.shiftRight x 1 = x / 2 := by
    change x >>> 1 = x / 2
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  have hm : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
  have e : HSK.letInvAB GW x = Bool.rec (motive := fun _ => ℕ) (GW (x / 2 + 1))
      (invEnt (GW (x / 2 + 1))) (Nat.beq (x % 2) 0) := by
    unfold HSK.letInvAB
    rw [hs, hm]
  have hg := hGW (x / 2 + 1) (by omega) (by omega)
  have hent : entOK (GW (x / 2 + 1)) 254 63 = true := Co2Kill.entOK_mono hg.2 (by norm_num) le_rfl
  rw [e]
  have h255 : x ≠ 255 := by omega
  rcases Nat.mod_two_eq_zero_or_one x with h2 | h2
  · rw [h2]
    change entOK (invEnt (GW (x / 2 + 1))) 254 63 = true ∧
      bval gen (wWord (invEnt (GW (x / 2 + 1)))) (wLen (invEnt (GW (x / 2 + 1)))) = _
    obtain ⟨i1, -, i3⟩ := Co2Kill.invEnt_spec gen hent (by norm_num)
    refine ⟨i1, ?_⟩
    rw [i3]
    simp [letV, h255, h2]
  · rw [h2]
    change entOK (GW (x / 2 + 1)) 254 63 = true ∧
      bval gen (wWord (GW (x / 2 + 1))) (wLen (GW (x / 2 + 1))) = _
    refine ⟨hent, ?_⟩
    simp [letV, h255, h2]

theorem piInv_spec {G : Type*} [Group G] (gen : ℕ → G) {GW : ℕ → ℕ} {ng : ℕ} (hng : ng < 128)
    (hGW : ∀ k, 1 ≤ k → k ≤ ng → conjOK (GW k) = true ∧ entOK (GW k) (nat_lit 4) (nat_lit 63) = true)
    {w : ℕ} (hw : entOK w (2 * ng) 8 = true) :
    entOK (HSK.piInv GW w) 254 504 = true ∧
      bval gen (wWord (HSK.piInv GW w)) (wLen (HSK.piInv GW w)) =
        (bval (fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1)))) (wWord w) (wLen w))⁻¹ := by
  set gen' := fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1)))
  obtain ⟨-, hn, hl⟩ := (entOK_iff _ _ _).1 hw
  set n := wLen w
  set W := wWord w
  set P : ℕ → ℕ := fun k => Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => CFSG.KC.Loop.strictN acc (fun a =>
      HSK.catEnt a (HSK.letInvAB GW (CFSG.KC.HOrb.byte W (Nat.sub (Nat.sub n 1) k))))) k
    with hPdef
  have hp : HSK.piInv GW w = P n := rfl
  have key : ∀ k ≤ n, entOK (P k) 254 (63 * k) = true ∧ bval gen (wWord (P k)) (wLen (P k)) =
      ((List.range k).map fun t => (letV gen' (wLet W (n - 1 - t)))⁻¹).prod := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 : wLen 0 = 0 := by decide
      refine ⟨Co2Kill.entOK_zero 254, ?_⟩
      change bval gen (wWord 0) (wLen 0) = _
      rw [h0, bval_zero]
      rfl
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      have e : P (k + 1) = HSK.catEnt (P k)
          (HSK.letInvAB GW (CFSG.KC.HOrb.byte W (n - 1 - k))) := by
        change CFSG.KC.Loop.strictN (P k) _ = _
        rw [Co2Kill.strictN_eq]
        rfl
      have hx : CFSG.KC.HOrb.byte W (n - 1 - k) < 2 * ng := hl _ (by omega)
      obtain ⟨l1, l2⟩ := letInvAB_spec gen hng hGW hx
      obtain ⟨c1, -, c3⟩ := catEnt_spec gen h1 l1 (by omega)
      rw [e, c3, h2, l2, List.range_succ, List.map_append, List.prod_append]
      exact ⟨by rw [Nat.mul_succ]; exact c1, by simp; rfl⟩
  obtain ⟨k1, k2⟩ := key n le_rfl
  refine ⟨by rw [hp]; exact Co2Kill.entOK_mono k1 le_rfl (by omega), ?_⟩
  rw [hp, k2, bval, List.prod_inv_reverse, List.map_map]
  rw [← map_range_rev ((fun x => x⁻¹) ∘ fun i => letV gen' (wLet W i)) n]
  rfl

theorem hWord_spec {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G) {sub : ℕ → ℕ}
    (hsub : ∀ j, entOK (sub j) (nat_lit 4) (nat_lit 18) = true ∧
      bval gen (wWord (sub j)) (wLen (sub j)) ∈ H) (hl : ℕ) :
    ∀ k ≤ 32, entOK (HSK.hWord sub hl k) 254 (18 * k) = true ∧
      bval gen (wWord (HSK.hWord sub hl k)) (wLen (HSK.hWord sub hl k)) ∈ H := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : wLen 0 = 0 := by decide
    refine ⟨Co2Kill.entOK_zero 254, ?_⟩
    change bval gen (wWord 0) (wLen 0) ∈ H
    rw [h0, bval_zero]
    exact H.one_mem
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    set x := CFSG.KC.HOrb.byte hl k
    set q := Bool.rec (motive := fun _ => ℕ) (invEnt (sub (Nat.shiftRight x 1)))
      (sub (Nat.shiftRight x 1)) (Nat.beq (Nat.land x 1) 0) with hq
    have e : HSK.hWord sub hl (k + 1) = HSK.catEnt (HSK.hWord sub hl k) q := by
      have e0 : HSK.hWord sub hl (k + 1) =
          CFSG.KC.Loop.strictN (HSK.hWord sub hl k) (fun a => HSK.catEnt a q) := rfl
      rw [e0, Co2Kill.strictN_eq]
    obtain ⟨s1, s2⟩ := hsub (Nat.shiftRight x 1)
    have s1' : entOK (sub (Nat.shiftRight x 1)) 254 18 = true :=
      Co2Kill.entOK_mono s1 (by norm_num) le_rfl
    have hq1 : entOK q 254 18 = true ∧ bval gen (wWord q) (wLen q) ∈ H := by
      rw [hq]
      cases Nat.beq (Nat.land x 1) 0
      · obtain ⟨i1, -, i3⟩ := Co2Kill.invEnt_spec gen s1' (by norm_num)
        exact ⟨i1, by rw [i3]; exact H.inv_mem s2⟩
      · exact ⟨s1', s2⟩
    obtain ⟨c1, -, c3⟩ := catEnt_spec gen h1 hq1.1 (by omega)
    rw [e, c3]
    exact ⟨by rw [Nat.mul_succ]; exact c1, H.mul_mem h2 hq1.2⟩

theorem pairOK_sound {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G) (rep : ℕ → G)
    {blk : ℕ → ℕ} {nf : ℕ} (hrep : rep 0 = 1)
    (hwalk : ∀ w x R y, x < 2 ^ 20 → walkTo blk nf w x R y = true →
      rep x * bval gen (wWord w) (wLen w) * (rep y)⁻¹ ∈ H)
    {sub : ℕ → ℕ} (hsub : ∀ j, entOK (sub j) (nat_lit 4) (nat_lit 18) = true ∧
      bval gen (wWord (sub j)) (wLen (sub j)) ∈ H)
    (hcent : ∀ x ∈ H, x * gen 0 = gen 0 * x) (ha : gen 0 * gen 0 = 1)
    {GW : ℕ → ℕ} {ng : ℕ} (hGW : gwOK GW ng = true) (hng : ng < 128)
    (hU : ∀ ρ, 1 ≤ ρ → ρ ≤ 4 → entOK (rootWord ρ) (nat_lit 4) (nat_lit 16) = true ∧
      ((gen 0)⁻¹ * (bval gen (wWord (rootWord ρ)) (wLen (rootWord ρ)))⁻¹ * gen 0 *
        bval gen (wWord (rootWord ρ)) (wLen (rootWord ρ))) ^ rootExp ρ = 1)
    {XRk i j m w R1 c ρ hl hn R2 : ℕ} (hargs : pairArgsOK ng w hn m = true)
    (h : pairOK blk GW sub ng nf XRk i j m w R1 c ρ hl hn R2 = true) :
    bval (fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1)))) (wWord XRk) (wLen XRk) = 1 := by
  set gen' : ℕ → G := fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1))) with hgen'
  have hGW' := gwOK_spec hGW
  simp only [pairArgsOK, andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hargs
  obtain ⟨hw, hhn, hm⟩ := hargs
  have hw' : entOK w (2 * ng) 8 = true := hw
  have hm' : (2 * wLen w + 2) * m < 1024 := hm
  have hw254 : entOK w 254 8 = true := Co2Kill.entOK_mono hw' (by omega) le_rfl
  unfold pairOK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨hi1, hi5⟩, ⟨hj1, hj5⟩, -⟩, hX, hw1, hcase⟩ := h
  obtain ⟨si1, si2, si3, si4⟩ := gw_spec gen (hGW' i hi1 hi5)
  obtain ⟨sj1, -, -, sj4⟩ := gw_spec gen (hGW' j hj1 hj5)
  set a := gen 0
  set σi := bval gen (wWord (HSK.sigma GW i)) (wLen (HSK.sigma GW i))
  set σj := bval gen (wWord (HSK.sigma GW j)) (wLen (HSK.sigma GW j))
  set πw := bval gen' (wWord w) (wLen w)
  obtain ⟨p1, p2⟩ := piInv_spec gen hng hGW' hw'
  obtain ⟨c1, -, c3⟩ := catEnt_spec gen p1 si2 (by norm_num)
  obtain ⟨-, -, d3⟩ := catEnt_spec gen sj1 c1 (by norm_num)
  have hPv : bval gen (wWord (HSK.pairWord GW i j w)) (wLen (HSK.pairWord GW i j w)) =
      σj * (πw⁻¹ * σi⁻¹) := by
    unfold HSK.pairWord
    rw [d3, c3, p2, si3]
  have hwk1 := hwalk _ 0 R1 c (by norm_num) hw1
  rw [bval_withSent, hPv, hrep, one_mul] at hwk1
  have hlet : ∀ t, 1 ≤ t → t ≤ ng →
      letV gen' (2 * (t - 1)) = bval gen (wWord (GW t)) (wLen (GW t)) := by
    intro t h1 h5
    have e1 : 2 * (t - 1) ≠ 255 := by omega
    have e2 : 2 * (t - 1) % 2 = 0 := by omega
    have e3 : 2 * (t - 1) / 2 + 1 = t := by omega
    simp only [letV, e1, e2, ite_false, ite_true]
    change bval gen (wWord (GW (2 * (t - 1) / 2 + 1))) (wLen (GW (2 * (t - 1) / 2 + 1))) = _
    rw [e3]
  obtain ⟨ej1, ej2, ej3⟩ := letEnt_spec gen' (c := 2 * (j - 1)) (by omega)
  obtain ⟨ewj1, ewj2, ewj3⟩ := catEnt_spec gen' hw254 ej1 (by norm_num)
  obtain ⟨ei1, ei2, ei3⟩ := letEnt_spec gen' (c := 2 * (i - 1)) (by omega)
  obtain ⟨eiwj1, eiwj2, eiwj3⟩ := catEnt_spec gen' ei1 ewj1 (by norm_num)
  obtain ⟨ev1, ev2, ev3⟩ := Co2Kill.invEnt_spec gen' hw254 (by norm_num)
  obtain ⟨ea1, ea2, ea3⟩ := catEnt_spec gen' ev1 eiwj1 (by norm_num)
  obtain ⟨eW, -, -⟩ := (entOK_iff _ _ _).1 ea1
  have hcase' : (m = HSK.rootExp ρ ∧ ρ ≤ 4 ∧ walkTo blk nf (withSent (HSK.catEnt
      (HSK.rootWord ρ) (HSK.hWord sub hl hn))) 0 R2 c = true ∧ 1 ≤ ρ) ∨
      (c = 0 ∧ m = 1) := by
    cases hρ : Nat.beq ρ 0 <;> rw [hρ] at hcase <;> dsimp only at hcase <;>
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcase
    · refine Or.inl ⟨hcase.1, hcase.2.1, hcase.2.2, ?_⟩
      rcases Nat.eq_zero_or_pos ρ with h0 | h0
      · rw [h0] at hρ
        exact absurd hρ (by decide)
      · exact h0
    · exact Or.inr hcase
  have hXv : bval gen' (wWord XRk) (wLen XRk) =
      (πw⁻¹ * ((σi⁻¹ * a * σi) * (πw * (σj⁻¹ * a * σj)))) ^ m := by
    have hX' : HSK.xrelOf i j m w = powEnt (HSK.catEnt (invEnt w) (HSK.catEnt
        (HSK.letEnt (2 * (i - 1))) (HSK.catEnt w (HSK.letEnt (2 * (j - 1)))))) m := rfl
    have hlen : m * wLen (HSK.catEnt (invEnt w) (HSK.catEnt
        (HSK.letEnt (2 * (i - 1))) (HSK.catEnt w (HSK.letEnt (2 * (j - 1)))))) < 1024 := by
      rw [ea2, ev2, eiwj2, ei2, ewj2, ej2]
      calc m * (wLen w + (1 + (wLen w + 1))) = (2 * wLen w + 2) * m := by ring
        _ < 1024 := hm'
    rw [← hX, hX', bval_powEnt gen' eW hlen, ea3, ev3, eiwj3, ei3, ewj3, ej3, hlet i hi1 hi5,
      hlet j hj1 hj5, si4, sj4]
  rw [hXv]
  have hre : πw⁻¹ * ((σi⁻¹ * a * σi) * (πw * (σj⁻¹ * a * σj))) =
      (σi * πw)⁻¹ * a * (σi * πw) * σj⁻¹ * a * σj := by group
  have hvu : σj * (πw⁻¹ * σi⁻¹) = σj * (σi * πw)⁻¹ := by group
  rw [hre]
  rw [hvu] at hwk1
  rcases hcase' with ⟨hm, hρ4, hw2, hρ1⟩ | ⟨hc0, hm1⟩
  ·
    obtain ⟨u1, u2⟩ := hU ρ hρ1 hρ4
    obtain ⟨hh1, hh2⟩ := hWord_spec gen H hsub hl hn hhn
    obtain ⟨-, -, f3⟩ := catEnt_spec gen (Co2Kill.entOK_mono u1 (by norm_num) le_rfl)
      (Co2Kill.entOK_mono hh1 le_rfl (n' := 576) (by omega)) (by norm_num)
    have hwk2 := hwalk _ 0 R2 c (by norm_num) hw2
    rw [bval_withSent, f3, hrep, one_mul] at hwk2
    rw [hm]
    refine Co2Kill.pair_group H ha hcent (H.mul_mem hwk1 (H.inv_mem hwk2)) hh2 ?_ u2
    group
  ·
    rw [hc0, hrep, inv_one, mul_one] at hwk1
    rw [hm1]
    refine Co2Kill.pair_group H ha hcent (U := 1) hwk1 H.one_mem ?_ (by group)
    group

private noncomputable def d2 (X : ℕ) : Multiplicative (ZMod 2) := Multiplicative.ofAdd (X : ZMod 2)

private theorem d2_zero : d2 0 = 1 := by
  simp [d2]

private theorem d2_inv (X : ℕ) : (d2 X)⁻¹ = d2 X := by
  unfold d2
  rw [← ofAdd_neg, ZMod.neg_eq_self_mod_two]

private theorem xor_sound {a b : ℕ} (ha : a < 2) (hb : b < 2) :
    Nat.xor a b < 2 ∧ d2 (Nat.xor a b) = d2 a * d2 b := by
  interval_cases a <;> interval_cases b <;> exact ⟨by decide, by decide⟩

private noncomputable def jList (WT : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, J => J :: jList WT k (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight J (nat_lit 1))
      (Nat.shiftRight J (jLen J (WT (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))

private noncomputable def wOf (WT : ℕ → ℕ) (J : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
    (WT (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))
    (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))

private noncomputable def jAll (WT : ℕ → ℕ) (Cs : List ℕ) : List ℕ :=
  Cs.flatMap fun C => jList WT (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8))

private theorem chunkRec_eq (blk WT : ℕ → ℕ) (INV nC L : ℕ) : ∀ k J S,
    LceP.chunkRec blk WT INV nC L k J S =
      (jList WT k J).foldl (fun S J => factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J)) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ)
      (LceP.chunkRec blk WT INV nC L k (Nat.shiftRight J (nat_lit 1))
        (factStep blk INV nC L J S (fct blk (sI S)) (nat_lit 0)))
      (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
        (nat_lit 65535)) WT)
        (fun w => LceP.chunkRec blk WT INV nC L k (Nat.shiftRight J (jLen J w))
          (factStep blk INV nC L J S (fct blk (sI S)) w)))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, wOf, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> exact chunkRec_eq blk WT INV nC L k _ _

private theorem runFacts_eq (blk WT : ℕ → ℕ) (INV nC L : ℕ) : ∀ Cs S,
    runFacts blk WT INV nC L Cs S =
      (jAll WT Cs).foldl (fun S J => factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J)) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (LceP.chunkRec blk WT INV nC L (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (runFacts blk WT INV nC L Cs) = _
    rw [LceP.strictN_eq, runFacts_eq blk WT INV nC L Cs, chunkRec_eq]
    simp only [jAll, List.flatMap_cons, List.foldl_append]

private noncomputable def labRec (WT LB LETs : ℕ → ℕ) (Hs : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (CFSG.KC.Loop.strictN (labStep LB LETs Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
        (nat_lit 65535)) WT) (fun w =>
        CFSG.KC.Loop.strictN (labStep LB LETs Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

private theorem labRec_eq (WT LB LETs : ℕ → ℕ) (Hs : ℕ) : ∀ k J S,
    labRec WT LB LETs Hs k J S =
      (jList WT k J).foldl (fun S J => labStep LB LETs Hs J S (wOf WT J)) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ)
      (CFSG.KC.Loop.strictN (labStep LB LETs Hs J S (nat_lit 0))
        (labRec WT LB LETs Hs k (Nat.shiftRight J (nat_lit 1))))
      (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
        (nat_lit 65535)) WT)
        (fun w => CFSG.KC.Loop.strictN (labStep LB LETs Hs J S w)
          (labRec WT LB LETs Hs k (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, wOf, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> exact labRec_eq WT LB LETs Hs k _ _

private theorem runLab_eq (WT LB LETs : ℕ → ℕ) (Hs : ℕ) : ∀ Cs S,
    runLab WT LB LETs Hs Cs S = (jAll WT Cs).foldl (fun S J => labStep LB LETs Hs J S (wOf WT J)) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (labRec WT LB LETs Hs (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (runLab WT LB LETs Hs Cs) = _
    rw [LceP.strictN_eq, runLab_eq WT LB LETs Hs Cs, labRec_eq]
    simp only [jAll, List.flatMap_cons, List.foldl_append]

private noncomputable def idsF (m I J : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) I
    (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) I
      (Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) m))
    (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))

private noncomputable def idsRec (WT : ℕ → ℕ) (m : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight J (nat_lit 1)) S)
      (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun id =>
        CFSG.KC.Loop.strictN (WT id) (fun w =>
          ih (Nat.shiftRight J (jLen J w))
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S (Nat.blt id m)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

private theorem idsRec_eq (WT : ℕ → ℕ) (m : ℕ) : ∀ k J S,
    idsRec WT m k J S = (jList WT k J).foldl (idsF m) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ) (idsRec WT m k (Nat.shiftRight J (nat_lit 1)) S)
      (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun id =>
        CFSG.KC.Loop.strictN (WT id) (fun w => idsRec WT m k (Nat.shiftRight J (jLen J w))
          (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) S (Nat.blt id m)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, idsF, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> exact idsRec_eq WT m k _ _

private theorem runIds_eq (WT : ℕ → ℕ) (m : ℕ) : ∀ Cs S,
    CFSG.KC.LceSR.runIds WT m Cs S = (jAll WT Cs).foldl (idsF m) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (idsRec WT m (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (CFSG.KC.LceSR.runIds WT m Cs) = _
    rw [LceP.strictN_eq, runIds_eq WT m Cs, idsRec_eq]
    simp only [jAll, List.flatMap_cons, List.foldl_append]

section Lab

variable {G X : Type*} [Group G] [Group X] (gen : ℕ → G) (π : X →* G)
  (ψ : X →* Multiplicative (ZMod 2))

private noncomputable def LabHolds (rep : ℕ → G) (R L : ℕ) : Prop :=
  ∃ l : X, π l = LceP.el gen rep R ∧ ψ l = d2 L

private noncomputable def LRefs (blk LB : ℕ → ℕ) (INV nC : ℕ) (rep : ℕ → G) (i : ℕ) : Prop :=
  ∀ h < i, recOK INV nC (fct blk h) = true ∧ LB h < 2 ∧ LabHolds gen π ψ rep (fct blk h) (LB h)

private noncomputable def WL (rep : ℕ → G) (s W ft : ℕ) (u : G) (M : Multiplicative (ZMod 2))
    (p st acc : ℕ) : Prop :=
  st / 1048576 = 0 ∨ ∃ cur < 1048576, st = cur + 1048576 * (W / 256 ^ p) ∧ acc < 2 ∧
    ((p ≤ ft ∧ ∃ a : X, π a = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧ ψ a = d2 acc) ∨
      (ft < p ∧ ∃ a b : X, π a * u * π b = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧
        ψ a * M * ψ b = d2 acc))

private theorem WL_start (rep : ℕ → G) {s : ℕ} (W ft : ℕ) (u : G) (M : Multiplicative (ZMod 2))
    (hs : s < 1048576) : WL gen π ψ rep s W ft u M 0 (wStart s W) 0 := by
  right
  refine ⟨s, hs, ?_, by norm_num, Or.inl ⟨Nat.zero_le _, 1, ?_, ?_⟩⟩
  · unfold wStart
    rw [LceP.lor20 _ hs, pow_zero, Nat.div_one]
    ring
  · rw [map_one, LceP.bv_zero, mul_one, mul_inv_cancel]
  · rw [map_one, d2_zero]

private theorem WL_ext {rep : ℕ → G} {s W ft : ℕ} {u : G} {M : Multiplicative (ZMod 2)}
    {p acc cur cur' B : ℕ} {c : X} (hp : p ≠ ft) (hacc : acc < 2) (hB : B < 2)
    (hX : (p ≤ ft ∧ ∃ a : X, π a = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧ ψ a = d2 acc) ∨
      (ft < p ∧ ∃ a b : X, π a * u * π b = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧
        ψ a * M * ψ b = d2 acc))
    (hc : π c = rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹) (hcB : ψ c = d2 B) :
    Nat.xor acc B < 2 ∧
    ((p + 1 ≤ ft ∧ ∃ a : X, π a = rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ ∧
        ψ a = d2 (Nat.xor acc B)) ∨
      (ft < p + 1 ∧ ∃ a b : X, π a * u * π b = rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ ∧
        ψ a * M * ψ b = d2 (Nat.xor acc B))) := by
  obtain ⟨hw, hd⟩ := xor_sound hacc hB
  have e : rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ =
      (rep s * LceP.bv gen W p * (rep cur)⁻¹) * (rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹) := by
    rw [LceP.bv_succ]
    group
  refine ⟨hw, ?_⟩
  rcases hX with ⟨hp', a, ha, haψ⟩ | ⟨hp', a, b, hab, habψ⟩
  · refine Or.inl ⟨by omega, a * c, ?_, ?_⟩
    · rw [map_mul, ha, hc, e]
    · rw [map_mul, haψ, hcB, hd]
  · refine Or.inr ⟨by omega, a, b * c, ?_, ?_⟩
    · rw [map_mul, e, ← hab, hc]
      group
    · rw [map_mul, hd, ← habψ, hcB]
      simp only [mul_assoc]

private theorem sF_cases (R st : ℕ) :
    sF R st = 0 ∨ (st % 268435456 = fxc R ∧ sF R st = fy R + st / 268435456 * 1048576) := by
  rw [LceP.sF_eq]
  split_ifs with h
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl rfl

private theorem sB_cases (R st : ℕ) :
    sB R st = 0 ∨ (st % 268435456 = fyic R ∧ sB R st = fx R + st / 268435456 * 1048576) := by
  rw [LceP.sB_eq]
  split_ifs with h
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl rfl

private theorem fwd_arith {R st cur W p : ℕ} (hcur : cur < 1048576)
    (hst : st = cur + 1048576 * (W / 256 ^ p)) (hm : st % 268435456 = fxc R) :
    cur = fx R ∧ wLet W p = fc R ∧
      fy R + st / 268435456 * 1048576 = fy R + 1048576 * (W / 256 ^ (p + 1)) := by
  rw [LceP.fxc_eq] at hm
  have hfx := LceP.fx_lt R
  have hfc := LceP.fc_lt R
  have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
    rw [← LceP.div256_succ]
    omega
  refine ⟨by omega, ?_, by rw [h3]; ring⟩
  rw [LceP.wLet_eq]
  omega

private theorem bwd_arith {R st cur W p : ℕ} (hcur : cur < 1048576)
    (hst : st = cur + 1048576 * (W / 256 ^ p)) (hm : st % 268435456 = fyic R)
    (hic : fic R < 256) :
    cur = fy R ∧ wLet W p = fic R ∧
      fx R + st / 268435456 * 1048576 = fx R + 1048576 * (W / 256 ^ (p + 1)) := by
  rw [LceP.fyic_eq] at hm
  have hfy := LceP.fy_lt R
  have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
    rw [← LceP.div256_succ]
    omega
  refine ⟨by omega, ?_, by rw [h3]; ring⟩
  rw [LceP.wLet_eq]
  omega

private theorem WL_ref {blk LB : ℕ → ℕ} {INV INV8 L nC i : ℕ} (hinv : invOK INV INV8 L = true)
    {rep : ℕ → G} {s W ft : ℕ} {u : G} {M : Multiplicative (ZMod 2)} {p st acc : ℕ}
    (e : ℕ) (hrefs : LRefs gen π ψ blk LB INV nC rep i) (hp : p ≠ ft)
    (hI : WL gen π ψ rep s W ft u M p st acc) :
    WL gen π ψ rep s W ft u M (p + 1) (refStep blk i e st)
      (Nat.xor acc (LB (Nat.shiftRight e (nat_lit 1)))) := by
  unfold refStep
  rw [LceP.brec_eq]
  split_ifs with hh
  · rw [Nat.blt_eq] at hh
    simp only [LceP.strictN_eq]
    obtain ⟨hrec, hwX, l, hl, hlψ⟩ := hrefs _ hh
    set R := fct blk (Nat.shiftRight e (nat_lit 1))
    have hlv := (LceP.lv_fic gen blk hinv hrec).1
    rw [LceP.brec_eq]
    split_ifs with hd
    ·
      rcases hI with hdead | ⟨cur, hcur, hst, hacc, hX⟩
      · left
        rcases sB_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := LceP.fx_lt R
          omega
      · rcases sB_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := bwd_arith hcur hst hm (LceP.fic_lt blk _)
          refine ⟨fx R, LceP.fx_lt R, by rw [h1, hs], ?_⟩
          refine WL_ext gen π ψ hp hacc hwX hX (c := l⁻¹) ?_ (by rw [map_inv, hlψ, d2_inv])
          have hlv' : LceP.lv gen (fic R) = (LceP.lv gen (fc R))⁻¹ := hlv
          rw [map_inv, hl, hw, hlv', hc]
          unfold LceP.el
          group
    ·
      rcases hI with hdead | ⟨cur, hcur, hst, hacc, hX⟩
      · left
        rcases sF_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := LceP.fy_lt R
          omega
      · rcases sF_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := fwd_arith hcur hst hm
          refine ⟨fy R, LceP.fy_lt R, by rw [h1, hs], ?_⟩
          refine WL_ext gen π ψ hp hacc hwX hX (c := l) ?_ hlψ
          rw [hl, hw, hc]
          rfl
  · left
    rfl

private theorem WL_own {rep : ℕ → G} {s W ft Ri Li p st acc : ℕ} (hp : p = ft) (hLi : Li < 2)
    (hI : WL gen π ψ rep s W ft (LceP.el gen rep Ri) (d2 Li) p st acc) :
    WL gen π ψ rep s W ft (LceP.el gen rep Ri) (d2 Li) (p + 1) (sF Ri st) (Nat.xor acc Li) := by
  rcases hI with hdead | ⟨cur, hcur, hst, hacc, hX⟩
  · left
    rcases sF_cases Ri st with h0 | ⟨hm, h1⟩
    · rw [h0]
    · rw [h1]
      have := LceP.fy_lt Ri
      omega
  · rcases sF_cases Ri st with h0 | ⟨hm, h1⟩
    · left
      rw [h0]
    · right
      obtain ⟨hc, hw, hs⟩ := fwd_arith hcur hst hm
      obtain ⟨hw2, hd⟩ := xor_sound hacc hLi
      refine ⟨fy Ri, LceP.fy_lt Ri, by rw [h1, hs], hw2, Or.inr ⟨by omega, ?_⟩⟩
      rcases hX with ⟨-, a, ha, haψ⟩ | ⟨hlt, -⟩
      · refine ⟨a, 1, ?_, ?_⟩
        · rw [map_one, mul_one, ha, LceP.bv_succ, hw, hc]
          unfold LceP.el
          group
        · rw [map_one, mul_one, haψ, hd]
      · omega

private theorem walk_lab {blk LB : ℕ → ℕ} {INV INV8 L nC i : ℕ} (hinv : invOK INV INV8 L = true)
    {rep : ℕ → G} {s W Ri Li ft n : ℕ} (hrefs : LRefs gen π ψ blk LB INV nC rep i) (hLi : Li < 2) :
    ∀ k ≤ n, ∀ J st acc,
      WL gen π ψ rep s W ft (LceP.el gen rep Ri) (d2 Li) (n - k) st acc →
      WL gen π ψ rep s W ft (LceP.el gen rep Ri) (d2 Li) n
        (walkGo blk i Ri ft n k J st) (labGo LB Li ft n k J acc)
  | 0, _, J, st, acc, hI => by
    rw [Nat.sub_zero] at hI
    exact hI
  | k + 1, hk, J, st, acc, hI => by
    change WL gen π ψ rep s W ft (LceP.el gen rep Ri) (d2 Li) n
      (Bool.rec (motive := fun _ => ℕ)
        (walkGo blk i Ri ft n k (Nat.shiftRight J 32) (refStep blk i (Nat.land J 4294967295) st))
        (walkGo blk i Ri ft n k J (sF Ri st)) (Nat.beq (Nat.sub n (Nat.succ k)) ft))
      (Bool.rec (motive := fun _ => ℕ)
        ((fun e => CFSG.KC.Loop.strictN (Nat.xor acc (LB (Nat.shiftRight e 1)))
            (labGo LB Li ft n k (Nat.shiftRight J 32))) (Nat.land J 4294967295))
        (CFSG.KC.Loop.strictN (Nat.xor acc Li) (labGo LB Li ft n k J))
        (Nat.beq (Nat.sub n (Nat.succ k)) ft))
    have e : n - k = n - (k + 1) + 1 := by omega
    cases hb : Nat.beq (Nat.sub n (Nat.succ k)) ft
    · dsimp only
      rw [LceP.strictN_eq]
      apply walk_lab hinv hrefs hLi k (by omega)
      rw [e]
      have hp : n - (k + 1) ≠ ft := by
        intro h
        have h2 : Nat.beq (Nat.sub n (Nat.succ k)) ft = true := by
          rw [Nat.beq_eq]
          exact h
        rw [hb] at h2
        exact Bool.false_ne_true h2
      exact WL_ref gen π ψ hinv _ hrefs hp hI
    · dsimp only
      rw [LceP.strictN_eq]
      apply walk_lab hinv hrefs hLi k (by omega)
      rw [e]
      exact WL_own gen π ψ (Nat.eq_of_beq_eq_true hb) hLi hI

private theorem walk_cyc {blk LB : ℕ → ℕ} {INV INV8 L nC i : ℕ} (hinv : invOK INV INV8 L = true)
    {rep : ℕ → G} {s W n : ℕ} {u : G} {M : Multiplicative (ZMod 2)}
    (hrefs : LRefs gen π ψ blk LB INV nC rep i) :
    ∀ k ≤ n, ∀ J st acc, WL gen π ψ rep s W n u M (n - k) st acc →
      WL gen π ψ rep s W n u M n (cycWalk blk i k J st) (cycLab LB k J acc)
  | 0, _, J, st, acc, hI => by
    rw [Nat.sub_zero] at hI
    exact hI
  | k + 1, hk, J, st, acc, hI => by
    change WL gen π ψ rep s W n u M n
      (CFSG.KC.Loop.strictN (refStep blk i (Nat.land J 4294967295) st)
        (cycWalk blk i k (Nat.shiftRight J 32)))
      (CFSG.KC.Loop.strictN (Nat.xor acc (LB (Nat.shiftRight (Nat.land J 4294967295) 1)))
        (cycLab LB k (Nat.shiftRight J 32)))
    rw [LceP.strictN_eq, LceP.strictN_eq]
    apply walk_cyc hinv hrefs k (by omega)
    rw [show n - k = n - (k + 1) + 1 by omega]
    exact WL_ref gen π ψ hinv _ hrefs (by omega) hI

private noncomputable def LInv (blk LB : ℕ → ℕ) (INV nC i N : ℕ) : Prop :=
  ∃ rep : ℕ → G, rep 0 = 1 ∧ ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) →
    LRefs gen π ψ blk LB INV nC rep' i

private noncomputable def LGood (blk LB : ℕ → ℕ) (INV nC S T I : ℕ) : Prop :=
  S = 0 ∨ T = 0 ∨ I = 0 ∨ 4294967296 < T ∨
    (1 ≤ sN S ∧ T = sI S + 1 ∧ LInv gen π ψ blk LB INV nC (sI S) (sN S))

private theorem lab_of_walk {u : G} {M : Multiplicative (ZMod 2)} {a b t : X}
    (hab : π a * u * π b = π t) (hψ : ψ a * M * ψ b = ψ t) : ∃ l : X, π l = u ∧ ψ l = M := by
  refine ⟨a⁻¹ * t * b⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, map_inv, ← hab]
    group
  · rw [map_mul, map_mul, map_inv, map_inv, ← hψ]
    group

private theorem labStep_cases (LB LETs : ℕ → ℕ) (Hs J T w : ℕ) :
    labStep LB LETs Hs J T w = 0 ∨ labStep LB LETs Hs J T w = T + 1 := by
  unfold labStep
  cases Nat.blt (nat_lit 0) T
  · exact Or.inl rfl
  · dsimp only
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> dsimp only
    · cases Nat.beq (LB (Nat.sub T (nat_lit 1))) (nat_lit 0)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · cases labWalk LB LETs (Nat.sub T (nat_lit 1)) J w
        (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))
      · exact Or.inl rfl
      · exact Or.inr rfl

private theorem LGood_step {blk WT ST LB LETs : ℕ → ℕ} {INV INV8 L nC m Hs K : ℕ}
    (hinv : invOK INV INV8 L = true)
    (hW2 : ∀ id < m, wKind (WT id) = 2 → LceP.bv gen (wWord (WT id)) (wLen (WT id)) = 1)
    (hW3 : ∀ id < m, wKind (WT id) = 3 → hint Hs id < K ∧
      LceP.bv gen (wWord (WT id)) (wLen (WT id)) =
        LceP.bv gen (wWord (ST (hint Hs id))) (wLen (ST (hint Hs id))))
    (hLET : ∀ j < K, ∃ t : X, π t = LceP.bv gen (wWord (ST j)) (wLen (ST j)) ∧ ψ t = d2 (LETs j))
    {S T I : ℕ} (J : ℕ) (hG : LGood gen π ψ blk LB INV nC S T I) :
    LGood gen π ψ blk LB INV nC (factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J))
      (labStep LB LETs Hs J T (wOf WT J)) (idsF m I J) := by
  rcases hG with h0 | h0 | h0 | h0 | ⟨hN, hT, rep, hrep0, hrefs⟩
  · left
    rw [h0]
    rfl
  · right; left
    rw [h0]
    rfl
  · right; right; left
    rw [h0]
    unfold idsF
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;>
      cases Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) m <;> rfl
  · rcases labStep_cases LB LETs Hs J T (wOf WT J) with h | h
    · right; left
      exact h
    · right; right; right; left
      rw [h]
      omega
  set i := sI S with hidef
  set N := sN S with hNdef
  have hi32 : i < 4294967296 := LceP.sI_lt S
  have hS0 : Nat.blt (nat_lit 0) S = true := by
    rw [Nat.blt_eq]
    change 0 < S
    have : S / 4294967296 ≥ 1 := by rw [← LceP.sN_eq]; exact hN
    omega
  have hT0 : Nat.blt (nat_lit 0) T = true := by
    rw [Nat.blt_eq]
    change 0 < T
    omega
  have hT1 : Nat.sub T (nat_lit 1) = i := by
    change T - 1 = i
    omega
  have hnext : ∀ N' : ℕ, 1 ≤ N' → LInv gen π ψ blk LB INV nC (i + 1) N' → ∀ I' : ℕ,
      LGood gen π ψ blk LB INV nC (mkS (Nat.succ i) N') (T + 1) I' := by
    intro N' hN' hL I'
    rcases Nat.lt_or_ge (i + 1) 4294967296 with hlt | hge
    · right; right; right; right
      have e1 : sI (mkS (Nat.succ i) N') = i + 1 := by
        rw [LceP.sI_eq, LceP.mkS_eq N' hlt]
        omega
      have e2 : sN (mkS (Nat.succ i) N') = N' := by
        rw [LceP.sN_eq, LceP.mkS_eq N' hlt]
        omega
      rw [e1, e2]
      exact ⟨hN', by omega, hL⟩
    · right; right; right; left
      omega
  unfold factStep labStep idsF wOf
  rw [hS0, hT0, hT1]
  dsimp only
  cases hJ : Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)
  ·
    dsimp only
    cases hft : fTree INV nC L (fct blk i) N
    · left
      rfl
    cases hlb : Nat.beq (LB i) (nat_lit 0)
    · right; left
      rfl
    dsimp only
    refine hnext (N + 1) (by omega) ?_ _
    unfold fTree at hft
    simp only [LceP.andB_iff, Nat.beq_eq, Nat.blt_eq] at hft
    obtain ⟨hrR, hfy, hfx, -⟩ := hft
    have hLB : LB i = 0 := Nat.eq_of_beq_eq_true hlb
    set R := fct blk i
    refine ⟨Function.update rep N (rep (fx R) * LceP.lv gen (fc R)), ?_, fun rep' hag h hh => ?_⟩
    · rw [Function.update_of_ne (show (0 : ℕ) ≠ N by omega)]
      exact hrep0
    have hag' : ∀ k < N, rep' k = rep k := by
      intro k hk
      rw [hag k (by omega), Function.update_of_ne (show k ≠ N by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag' h hh
    · refine ⟨hrR, by rw [hLB]; norm_num, 1, ?_, ?_⟩
      · rw [map_one]
        unfold LceP.el
        rw [hfy, hag N (by omega), Function.update_self, hag' _ hfx, mul_inv_cancel]
      · rw [map_one, hLB, d2_zero]
  ·
    dsimp only
    set id := Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535) with hiddef
    cases hid : Nat.blt id m
    · right; right; left
      rfl
    have hidm : id < m := LceP.blt_true hid
    set w := WT id
    set fs := Nat.land (Nat.shiftRight J (nat_lit 17)) (nat_lit 1048575)
    set ft := Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)
    cases hwk : walkOK blk INV nC i (fct blk i) w fs ft J
    · left
      rfl
    cases hlw : labWalk LB LETs i J w (hint Hs id)
    · right; left
      rfl
    dsimp only
    set R := fct blk i
    refine hnext N hN ⟨rep, hrep0, fun rep' hag h hh => ?_⟩ _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag h hh
    unfold walkOK at hwk
    simp only [LceP.andB_iff, LceP.orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at hwk
    obtain ⟨hrec, hft, hkind, hwalk⟩ := hwk
    unfold labWalk at hlw
    rw [LceP.letB_eq] at hlw
    simp only [LceP.andB_iff, Nat.beq_eq] at hlw
    obtain ⟨hwX, hlab⟩ := hlw
    have hwX' : LB i < 2 := LceP.blt_true hwX
    have hfs : fs < 1048576 := by
      change Nat.land (Nat.shiftRight J 17) 1048575 < 1048576
      rw [LceP.land20]
      omega
    have hrefs' := hrefs rep' hag
    have hstart := WL_start gen π ψ rep' (wWord w) ft (LceP.el gen rep' R) (d2 (LB i)) hfs
    have hW := walk_lab gen π ψ hinv hrefs' hwX' (wLen w) le_rfl (Nat.shiftRight J 53) _ _
      (by rw [Nat.sub_self]; exact hstart)
    rw [hwalk, hlab] at hW
    refine ⟨hrec, hwX', ?_⟩
    rcases hW with hdead | ⟨cur, hcur, hst, -, hX⟩
    · exfalso
      omega
    have hW1 : wWord w / 256 ^ wLen w = 1 := by omega
    have hc : cur = fs := by omega
    rcases hX with ⟨hle, -⟩ | ⟨-, a, b, hab, habψ⟩
    · exfalso
      omega
    rw [hc] at hab
    rcases hkind with hk2 | ⟨hk3, hfs0⟩
    ·
      have hbv := hW2 id hidm hk2
      have htg : target LETs w (hint Hs id) = 0 := by
        unfold target
        rw [show Nat.beq (wKind w) (nat_lit 3) = false by rw [hk2]; rfl]
      rw [htg, d2_zero] at habψ
      refine lab_of_walk π ψ (a := a) (b := b) (t := 1) ?_ ?_
      · rw [hab, hbv, mul_one, mul_inv_cancel, map_one]
      · rw [habψ, map_one]
    ·
      obtain ⟨hK, hbv⟩ := hW3 id hidm hk3
      obtain ⟨t, ht, htψ⟩ := hLET _ hK
      have htg : target LETs w (hint Hs id) = LETs (hint Hs id) := by
        unfold target
        rw [show Nat.beq (wKind w) (nat_lit 3) = true by rw [hk3]; rfl]
      rw [htg, ← htψ] at habψ
      have h0 : rep' 0 = 1 := by rw [hag 0 (by omega), hrep0]
      refine lab_of_walk π ψ (a := a) (b := b) ?_ habψ
      rw [hab, hfs0, h0, one_mul, inv_one, mul_one, hbv, ht]

end Lab

theorem lab_sound {G X : Type*} [Group G] [Group X] (gen : ℕ → G) (π : X →* G)
    (ψ : X →* Multiplicative (ZMod 2))
    {blk WT RT ST LB LETs : ℕ → ℕ} {INV INV8 L nC nf m Hs K S0 S1 T0 T1 : ℕ} {Cs : List ℕ}
    (h : coneOk blk WT RT ST LB LETs INV INV8 L nC nf m Hs K S0 S1 T0 T1 Cs = true)
    (hRT : ∀ r, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧ bval gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hLET : ∀ j < K, LETs j < 2 ∧ ∃ t : X,
      π t = bval gen (wWord (ST j)) (wLen (ST j)) ∧ ψ t = Multiplicative.ofAdd (LETs j : ZMod 2))
    {nf' c wid R V : ℕ} (hnf : nf' = nf) (hc : c < 2 ^ 20) (hwid : wid < m)
    (hcyc : cycOK blk WT LB nf' c wid R V = true) :
    ∃ ν : X, π ν = 1 ∧ ψ ν = Multiplicative.ofAdd (V : ZMod 2) := by
  subst nf'
  unfold coneOk at h
  obtain ⟨hwords, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hinv, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hnf, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hS0, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hS1, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hT0, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hT1, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hhints, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hids, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hrun, hlab⟩ := (LceP.andB_iff _ _).1 h
  have hnf' : nf < 4294967296 := LceP.blt_true hnf
  have hw : ∀ j < m, (wKind (WT j) = 2 → LceP.bv gen (wWord (WT j)) (wLen (WT j)) = 1) ∧
      (wKind (WT j) = 3 → hint Hs j < K ∧ LceP.bv gen (wWord (WT j)) (wLen (WT j)) =
        LceP.bv gen (wWord (ST (hint Hs j))) (wLen (ST (hint Hs j)))) := by
    intro j hj
    have hl := LceP.hintLoop (fun j H => (fun w r => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true
          (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r))) (Nat.beq (wKind w) (nat_lit 3)))
        (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
        (Nat.beq (wKind w) (nat_lit 2))) (WT j) (Nat.land H (nat_lit 65535)))
      m (nat_lit 16) m le_rfl Hs hwords j hj
    rw [Nat.sub_self, Nat.zero_add] at hl
    obtain ⟨hw2, hw3⟩ := LceP.word_check hl
    have hlt := (LceP.allRec_iff (fun k => Bool.rec (motive := fun _ => Bool) true
      (Nat.blt (hint Hs k) K) (Nat.beq (wKind (WT k)) (nat_lit 3))) m).1 hhints j hj
    refine ⟨fun hk => LceP.wRel_sound gen hinv (hw2 hk) (hRT _).1 (hRT _).2, fun hk => ⟨?_, ?_⟩⟩
    · have hb : Nat.beq (wKind (WT j)) (nat_lit 3) = true := by rw [hk]; rfl
      rw [hb] at hlt
      exact LceP.blt_true hlt
    · exact LceP.wSub_sound gen (hw3 hk)
  have hstep := fun (J : ℕ) {S T I : ℕ} => LGood_step gen π ψ (blk := blk) (WT := WT) (ST := ST)
    (LB := LB) (LETs := LETs) (L := L) (nC := nC) (m := m) (Hs := Hs) (K := K) (S := S) (T := T)
    (I := I) hinv (fun id hid => (hw id hid).1) (fun id hid => (hw id hid).2)
    (fun j hj => (hLET j hj).2) J
  have hfold : ∀ (l : List ℕ) (S T I : ℕ), LGood gen π ψ blk LB INV nC S T I →
      LGood gen π ψ blk LB INV nC
        (l.foldl (fun S J => factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J)) S)
        (l.foldl (fun S J => labStep LB LETs Hs J S (wOf WT J)) T) (l.foldl (idsF m) I) := by
    intro l
    induction l with
    | nil => intro S T I hG; exact hG
    | cons J l ih =>
      intro S T I hG
      simp only [List.foldl_cons]
      exact ih _ _ _ (hstep J hG)
  have hS0' : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  have hT0' : T0 = 1 := Nat.eq_of_beq_eq_true hT0
  have hG0 : LGood gen π ψ blk LB INV nC S0 T0 1 := by
    right; right; right; right
    have e1 : sI S0 = 0 := by rw [hS0', LceP.sI_eq, LceP.mkS_eq 1 (by norm_num)]
    have e2 : sN S0 = 1 := by rw [hS0', LceP.sN_eq, LceP.mkS_eq 1 (by norm_num)]
    rw [e1, e2, hT0']
    exact ⟨le_rfl, rfl, fun _ => 1, rfl, fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩
  have hG1 := hfold (jAll WT Cs) S0 T0 1 hG0
  rw [← runFacts_eq, ← runLab_eq, ← runIds_eq, Nat.eq_of_beq_eq_true hrun,
    Nat.eq_of_beq_eq_true hlab, Nat.eq_of_beq_eq_true hids, Nat.eq_of_beq_eq_true hS1,
    Nat.eq_of_beq_eq_true hT1] at hG1
  have hL : ∃ rep : ℕ → G, LRefs gen π ψ blk LB INV nC rep nf := by
    rcases hG1 with h0 | h0 | h0 | h0 | ⟨-, -, rep, -, hrefs⟩
    · rw [LceP.mkS_eq nC hnf'] at h0
      have h0' : nf = 0 := by omega
      exact ⟨fun _ => 1, fun h hh => absurd hh (by omega)⟩
    · exact absurd h0 (Nat.succ_ne_zero nf)
    · exact absurd h0 one_ne_zero
    · exfalso
      change 4294967296 < nf + 1 at h0
      omega
    · have e1 : sI (mkS nf nC) = nf := by
        rw [LceP.sI_eq, LceP.mkS_eq nC hnf']
        omega
      rw [e1] at hrefs
      exact ⟨rep, hrefs rep fun _ _ => rfl⟩
  obtain ⟨rep, hrefs⟩ := hL
  unfold cycOK at hcyc
  rw [LceP.letB_eq] at hcyc
  simp only [LceP.andB_iff, Nat.beq_eq, Nat.add_eq] at hcyc
  obtain ⟨hk2, hwalk, hlab'⟩ := hcyc
  have hc' : c < 1048576 := by simpa using hc
  have hstart := WL_start gen π ψ rep (wWord (WT wid)) (wLen (WT wid)) 1 1 hc'
  have hW := walk_cyc gen π ψ hinv hrefs (wLen (WT wid)) le_rfl R _ _
    (by rw [Nat.sub_self]; exact hstart)
  rw [hwalk, hlab'] at hW
  rcases hW with hdead | ⟨cur, hcur, hst, -, hX⟩
  · exfalso
    omega
  have hc0 : cur = c := by omega
  rcases hX with ⟨-, a, ha, haψ⟩ | ⟨hlt, -⟩
  · refine ⟨a, ?_, haψ⟩
    rw [ha, hc0, (hw wid hwid).1 hk2, mul_one, mul_inv_cancel]
  · exact absurd hlt (lt_irrefl _)

end CFSG.Certificates.HSKill

end
