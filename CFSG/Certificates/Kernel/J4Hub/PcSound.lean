module

public import CFSG.Certificates.Kernel.J4Hub.BlockSound
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

theorem nbeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem nbeq_ne {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem nblt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp e) h

theorem pw_pow (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {q n PR PW : Nat} (hpr : regsIn PR n nreg = true)
    (hpw : pwOK RB (mulR p w S d T L H CM RM) PR PW n q nreg = true) {k : Nat} (hk : k < n) :
    ∀ e < q, Canon p d w (RB (at16 PW (k * q + e))) ∧
      ordMat p d w S (RB (at16 PW (k * q + e))) = pcMat p d w S RB PR k ^ (e + 1) := by
  have hkk := rec_and' (f := fun k => andB (Nat.beq (at16 PW (Nat.mul k q)) (at16 PR k))
      (Nat.rec (motive := fun _ => Bool) true (fun e ih2 => andB ih2
        (andB (regBelow (at16 PW (Nat.add (Nat.mul k q) e)) nreg)
          (Bool.rec (motive := fun _ => Bool)
            (Nat.beq (RB (at16 PW (Nat.add (Nat.mul k q) e)))
              (mulR p w S d T L H CM RM (RB (at16 PW (Nat.sub (Nat.add (Nat.mul k q) e) (nat_lit 1))))
                (RB (at16 PR k))))
            true (Nat.beq e (nat_lit 0))))) q)) n hpw k hk
  obtain ⟨h0, hrest⟩ := andT' hkk
  have hfld := rec_and' q hrest
  obtain ⟨cpc, -⟩ := pc_reg hnb hc hR hpr hk
  intro e he
  induction e with
  | zero =>
    have e0 : at16 PW (k * q + 0) = at16 PR k := Nat.eq_of_beq_eq_true h0
    rw [e0, zero_add, pow_one]
    exact ⟨cpc, rfl⟩
  | succ e ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨hb, hm⟩ := andT' (hfld (e + 1) he)
    have hm' : RB (at16 PW (k * q + (e + 1))) = mulR p w S d T L H CM RM
        (RB (at16 PW (k * q + e))) (RB (at16 PR k)) := Nat.eq_of_beq_eq_true hm
    obtain ⟨c1, e1⟩ := mulR_sound hc ih1 cpc
    rw [hm']
    refine ⟨c1, ?_⟩
    rw [e1, ih2, pow_succ]
    rfl

theorem rhs_mem (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {q n PR PW pb i x : Nat} (hpr : regsIn PR n nreg = true)
    (hpw : pwOK RB (mulR p w S d T L H CM RM) PR PW n q nreg = true)
    (hx : ∀ k < n, Bool.rec (motive := fun _ => Bool) (Nat.blt (bitsN x (Nat.mul pb k) pb) q)
        (Nat.beq (bitsN x (Nat.mul pb k) pb) (nat_lit 0)) (Nat.ble k i) = true) :
    ∀ m ≤ n, Canon p d w (rhsPc RB (mulR p w S d T L H CM RM) ONE PW m q pb x) ∧
      ∃ h ∈ pcSub p d w S RB PR (i + 1) n, ((h : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) =
        ordMat p d w S (rhsPc RB (mulR p w S d T L H CM RM) ONE PW m q pb x) := by
  obtain ⟨hO1, hO2⟩ := CFSG.KS.Ord.one_sound hc
  intro m
  induction m with
  | zero => intro _; exact ⟨hO1, 1, one_mem _, Units.val_one.trans hO2.symm⟩
  | succ m ih =>
    intro hm
    obtain ⟨c0, h, hh, eh⟩ := ih (by omega)
    have e : rhsPc RB (mulR p w S d T L H CM RM) ONE PW (m + 1) q pb x =
        Bool.rec (motive := fun _ => Nat)
          (mulR p w S d T L H CM RM (rhsPc RB (mulR p w S d T L H CM RM) ONE PW m q pb x)
            (RB (at16 PW (Nat.sub (Nat.add (Nat.mul m q) (bitsN x (Nat.mul pb m) pb)) (nat_lit 1)))))
          (rhsPc RB (mulR p w S d T L H CM RM) ONE PW m q pb x)
          (Nat.beq (bitsN x (Nat.mul pb m) pb) (nat_lit 0)) := rfl
    rw [e]
    have hxm := hx m (by omega)
    cases hb : Nat.beq (bitsN x (Nat.mul pb m) pb) (nat_lit 0)
    case true => exact ⟨c0, h, hh, eh⟩
    dsimp only
    have hX0 : 0 < bitsN x (Nat.mul pb m) pb := Nat.pos_of_ne_zero (nbeq_ne hb)
    have hmi : ¬ m ≤ i := by
      intro hmi
      rw [Nat.ble_eq_true_of_le hmi] at hxm
      change Nat.beq (bitsN x (Nat.mul pb m) pb) (nat_lit 0) = true at hxm
      rw [hb] at hxm
      exact absurd hxm (by decide)
    cases hle : Nat.ble m i
    case true => exact absurd (Nat.le_of_ble_eq_true hle) hmi
    rw [hle] at hxm
    have hXq : bitsN x (Nat.mul pb m) pb < q := Nat.blt_eq.mp hxm
    generalize bitsN x (Nat.mul pb m) pb = X at hX0 hXq ⊢
    obtain ⟨cp, ep⟩ := pw_pow hc hnb hR hpr hpw (k := m) (by omega) (X - 1) (by omega)
    have eidx : Nat.sub (Nat.add (Nat.mul m q) X) (nat_lit 1) = m * q + (X - 1) := by
      change m * q + X - 1 = _
      omega
    rw [eidx]
    obtain ⟨c1, e1⟩ := mulR_sound hc c0 cp
    obtain ⟨-, u, -, eu⟩ := pc_reg hnb hc hR hpr (k := m) (by omega)
    refine ⟨c1, h * u ^ X, mul_mem hh (pow_mem (mem_pcSub (by omega) (by omega) eu) _), ?_⟩
    rw [e1, ep, Units.val_mul, eh, Units.val_pow_eq_pow_val, eu, Nat.sub_add_cancel hX0]

theorem pcRel_spec (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {q n PR PW pb i j x : Nat} (hq : 0 < q)
    (hpr : regsIn PR n nreg = true)
    (hpw : pwOK RB (mulR p w S d T L H CM RM) PR PW n q nreg = true) (hij : i ≤ j) (hj : j < n)
    (h : pcRelOK RB (mulR p w S d T L H CM RM) ONE PR PW n q pb i j x = true)
    {ui uj : GL (Fin d) (ZMod p)}
    (hui : ((ui : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = pcMat p d w S RB PR i)
    (huj : ((uj : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = pcMat p d w S RB PR j) :
    ∃ g ∈ pcSub p d w S RB PR (i + 1) n, (i = j → ui ^ q = g) ∧ (i < j → uj * ui = ui * g) := by
  obtain ⟨hx, hr⟩ := andT' h
  obtain ⟨cR, g, hg, eg⟩ := rhs_mem hc hnb hR hpr hpw (i := i) (pb := pb)
    (rec_and' (f := fun k => Bool.rec (motive := fun _ => Bool)
      (Nat.blt (bitsN x (Nat.mul pb k) pb) q)
      (Nat.beq (bitsN x (Nat.mul pb k) pb) (nat_lit 0)) (Nat.ble k i)) n hx) n le_rfl
  refine ⟨g, hg, fun hij' => ?_, fun hij' => ?_⟩
  · subst hij'
    rw [Nat.beq_refl] at hr
    have e := Nat.eq_of_beq_eq_true hr
    obtain ⟨-, ep⟩ := pw_pow hc hnb hR hpr hpw (k := i) hj (q - 1) (by omega)
    have eidx : Nat.sub (Nat.add (Nat.mul i q) q) (nat_lit 1) = i * q + (q - 1) := by
      change i * q + q - 1 = _
      omega
    rw [eidx] at e
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hui, eg, ← e, ep, Nat.sub_add_cancel hq]
  · rw [nbeq_false (by omega : i ≠ j)] at hr
    have e := Nat.eq_of_beq_eq_true hr
    obtain ⟨ci, -⟩ := pc_reg hnb hc hR hpr (k := i) (by omega)
    obtain ⟨cj, -⟩ := pc_reg hnb hc hR hpr hj
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hui, huj, eg]
    unfold pcMat
    rw [← (mulR_sound hc cj ci).2, ← (mulR_sound hc ci cR).2, e]

noncomputable def pcChunk (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE PR PW n q pb : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih2 J S => (fun i j => CFSG.KC.Loop.strictN
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Bool.rec (motive := fun _ => Nat) (Nat.add S (nat_lit 256))
            (Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 1) n)
              (Nat.add (nat_lit 1) (Nat.add (Nat.succ i) (Nat.shiftLeft (Nat.succ i) (nat_lit 8))))
              (Nat.blt (Nat.succ i) n))
            (Nat.beq (Nat.succ j) n))
          (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt i n) (andB (Nat.blt j n)
            (pcRelOK RB mul ONE PR PW n q pb i j (bitsN J (nat_lit 0) (Nat.mul n pb)))))))
        (ih2 (Nat.shiftRight J (Nat.mul n pb))))
      (Nat.land (Nat.sub S (nat_lit 1)) (nat_lit 255)) (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 8)))

theorem runPc_cons (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE PR PW n q pb C : Nat)
    (Cs : List Nat) (s : Nat) :
    runPc RB mul ONE PR PW n q pb (C :: Cs) s =
      runPc RB mul ONE PR PW n q pb Cs (pcChunk RB mul ONE PR PW n q pb (Nat.land C (nat_lit 255))
        (Nat.shiftRight C (nat_lit 8)) s) :=
  strictN_eq' _ _

def PcDone (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE PR PW n q pb i j : Nat) : Prop :=
  ∃ x, pcRelOK RB mul ONE PR PW n q pb i j x = true

def PcInv (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE PR PW n q pb s : Nat) : Prop :=
  s = 0 ∨ (s = 1 + n ∧ ∀ i j, i ≤ j → j < n → PcDone RB mul ONE PR PW n q pb i j) ∨
    ∃ i j, s = 1 + i + 256 * j ∧ i ≤ j ∧ j < n ∧
      ∀ i' j', i' ≤ j' → j' < n → (i' < i ∨ (i' = i ∧ j' < j)) → PcDone RB mul ONE PR PW n q pb i' j'

theorem pcChunk_inv (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE PR PW n q pb : Nat)
    (hn : n < 256) :
    ∀ m J s, PcInv RB mul ONE PR PW n q pb s → PcInv RB mul ONE PR PW n q pb (pcChunk RB mul ONE PR PW n q pb m J s)
  | 0, _, _, h => h
  | m + 1, J, s, h => by
    have e : pcChunk RB mul ONE PR PW n q pb (m + 1) J s = pcChunk RB mul ONE PR PW n q pb m
        (Nat.shiftRight J (Nat.mul n pb))
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Bool.rec (motive := fun _ => Nat) (Nat.add s (nat_lit 256))
            (Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 1) n)
              (Nat.add (nat_lit 1) (Nat.add (Nat.succ (Nat.land (Nat.sub s 1) 255))
                (Nat.shiftLeft (Nat.succ (Nat.land (Nat.sub s 1) 255)) (nat_lit 8))))
              (Nat.blt (Nat.succ (Nat.land (Nat.sub s 1) 255)) n))
            (Nat.beq (Nat.succ (Nat.shiftRight (Nat.sub s 1) 8)) n))
          (andB (Nat.blt (nat_lit 0) s) (andB (Nat.blt (Nat.land (Nat.sub s 1) 255) n)
            (andB (Nat.blt (Nat.shiftRight (Nat.sub s 1) 8) n)
            (pcRelOK RB mul ONE PR PW n q pb (Nat.land (Nat.sub s 1) 255)
              (Nat.shiftRight (Nat.sub s 1) 8) (bitsN J (nat_lit 0) (Nat.mul n pb))))))) :=
      strictN_eq' _ _
    rw [e]
    apply pcChunk_inv RB mul ONE PR PW n q pb hn
    refine brec_zero (Q := PcInv RB mul ONE PR PW n q pb) (Or.inl rfl) fun hc => ?_
    obtain ⟨h0, hc⟩ := andT' hc
    obtain ⟨hi, hc⟩ := andT' hc
    obtain ⟨-, hrel⟩ := andT' hc
    have hi' := Nat.blt_eq.mp hi
    rcases h with rfl | ⟨rfl, -⟩ | ⟨i, j, rfl, hij, hjn, hdone⟩
    · exact absurd (Nat.blt_eq.mp h0) (Nat.lt_irrefl 0)
    · exfalso
      have e1 : Nat.land (Nat.sub (1 + n) 1) 255 = n := by
        change (1 + n - 1) &&& 255 = n
        rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
        omega
      rw [e1] at hi'
      omega
    have hi8 : i < 256 := by omega
    have e1 : Nat.land (Nat.sub (1 + i + 256 * j) 1) 255 = i := by
      change (1 + i + 256 * j - 1) &&& 255 = i
      rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have e2 : Nat.shiftRight (Nat.sub (1 + i + 256 * j) 1) 8 = j := by
      change (1 + i + 256 * j - 1) >>> 8 = j
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [e1, e2] at hrel ⊢
    have hd : PcDone RB mul ONE PR PW n q pb i j := ⟨_, hrel⟩
    have hall : ∀ i' j', i' ≤ j' → j' < n → (i' < i ∨ (i' = i ∧ j' < j + 1)) →
        PcDone RB mul ONE PR PW n q pb i' j' := by
      intro i' j' h1 h2 h3
      rcases h3 with h3 | ⟨rfl, h3⟩
      · exact hdone i' j' h1 h2 (Or.inl h3)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 h3 with h3 | rfl
        · exact hdone i' j' h1 h2 (Or.inr ⟨rfl, h3⟩)
        · exact hd
    by_cases hjn' : j + 1 = n
    · have hb : Nat.beq (Nat.succ j) n = true := by
        rw [← hjn']
        exact Nat.beq_refl _
      rw [hb]
      by_cases hin : i + 1 < n
      · rw [Nat.blt_eq.mpr hin]
        refine Or.inr (Or.inr ⟨i + 1, i + 1, ?_, le_rfl, hin, fun i' j' h1 h2 h3 => ?_⟩)
        · change 1 + (i + 1 + (i + 1) <<< 8) = _
          rw [Nat.shiftLeft_eq]
          omega
        · rcases h3 with h3 | ⟨rfl, h3⟩
          · exact hall i' j' h1 h2 (by omega)
          · omega
      · rw [nblt_false hin]
        refine Or.inr (Or.inl ⟨rfl, fun i' j' h1 h2 => hall i' j' h1 h2 ?_⟩)
        omega
    · rw [nbeq_false hjn']
      refine Or.inr (Or.inr ⟨i, j + 1, ?_, by omega, by omega, fun i' j' h1 h2 h3 => hall i' j' h1 h2 h3⟩)
      change 1 + i + 256 * j + 256 = _
      omega

theorem runPc_inv (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE PR PW n q pb : Nat) (hn : n < 256) :
    ∀ (Cs : List Nat) s, PcInv RB mul ONE PR PW n q pb s →
      PcInv RB mul ONE PR PW n q pb (runPc RB mul ONE PR PW n q pb Cs s)
  | [], _, h => h
  | C :: Cs, s, h => by
    rw [runPc_cons]
    exact runPc_inv RB mul ONE PR PW n q pb hn Cs _ (pcChunk_inv RB mul ONE PR PW n q pb hn _ _ _ h)

theorem runPc_spec {RB : Nat → Nat} {mul : Nat → Nat → Nat} {ONE PR PW n q pb : Nat} {Cs : List Nat}
    (hn : n < 256)
    (h : Nat.beq (runPc RB mul ONE PR PW n q pb Cs 1) (Nat.add 1 n) = true) :
    ∀ i j, i ≤ j → j < n → PcDone RB mul ONE PR PW n q pb i j := by
  have h0 : PcInv RB mul ONE PR PW n q pb 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact Or.inr (Or.inl ⟨rfl, fun i j _ hj => absurd hj (Nat.not_lt_zero _)⟩)
    · exact Or.inr (Or.inr ⟨0, 0, rfl, le_rfl, hn0, fun i' j' _ _ h3 => by omega⟩)
  have hi := runPc_inv RB mul ONE PR PW n q pb hn Cs 1 h0
  rw [Nat.eq_of_beq_eq_true h] at hi
  rcases hi with hi | ⟨-, hi⟩ | ⟨i, j, e, hij, hjn, -⟩
  · change 1 + n = 0 at hi
    omega
  · exact hi
  · change 1 + n = 1 + i + 256 * j at e
    omega

theorem blocks_n_lt {BL nbl n : Nat} (h : blocksOK BL nbl n = true) : n < 256 := by
  obtain ⟨h1, h2⟩ := andT' h
  have hn : blkAcc BL nbl - 1 = n := Nat.eq_of_beq_eq_true h2
  have h0 : 0 < blkAcc BL nbl := Nat.blt_eq.mp h1
  cases nbl with
  | zero =>
    change 1 - 1 = n at hn
    omega
  | succ b =>
    obtain ⟨-, -, -, hacc⟩ := blkAcc_succ h0
    rw [hacc] at hn
    have : blkTo BL b < 256 := by
      unfold blkTo bitsN
      change (BL >>> (16 * b + 8)) &&& ((1 <<< 8) - 1) < 256
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    omega

theorem card_step {G : Type*} [Group G] [Finite G] (P N : Subgroup G) (u : G) (q : Nat) (hq : 0 < q)
    (hN : N ≤ P) (hu : u ∈ P) (hconj : ∀ g ∈ N, u⁻¹ * g * u ∈ N) (hpow : u ^ q ∈ N)
    (s : Set G) (hP : P = Subgroup.closure s)
    (hs : ∀ g ∈ s, g = u ∨ g ∈ N) :
    Nat.card P ≤ q * Nat.card N := by
  have hconjE : ∀ e : Nat, ∀ g ∈ N, (u ^ e)⁻¹ * g * u ^ e ∈ N := by
    intro e
    induction e with
    | zero => intro g hg; simpa using hg
    | succ e ih =>
      intro g hg
      have := hconj _ (ih g hg)
      rw [pow_succ, _root_.mul_inv_rev]
      simpa [mul_assoc] using this
  let X : Set G := {g | ∃ e < q, ∃ h ∈ N, g = u ^ e * h}
  have hX : ∀ x ∈ s, ∀ y ∈ X, x * y ∈ X := by
    rintro x hx y ⟨e, he, h, hh, rfl⟩
    rcases hs x hx with rfl | hxN
    · by_cases he' : e + 1 < q
      · exact ⟨e + 1, he', h, hh, by rw [pow_succ', mul_assoc]⟩
      · have heq : e + 1 = q := by omega
        refine ⟨0, hq, x ^ q * h, N.mul_mem hpow hh, ?_⟩
        rw [pow_zero, one_mul, ← heq, pow_succ', mul_assoc]
    · refine ⟨e, he, (u ^ e)⁻¹ * x * u ^ e * h, N.mul_mem (hconjE e x hxN) hh, ?_⟩
      simp [mul_assoc]
  let M : Subgroup G :=
    { carrier := {g | ∀ y ∈ X, g * y ∈ X}
      one_mem' := fun y hy => by simpa using hy
      mul_mem' := fun ha hb y hy => by rw [mul_assoc]; exact ha _ (hb y hy)
      inv_mem' := by
        intro g hg
        have hpow' : ∀ k : Nat, ∀ y ∈ X, g ^ k * y ∈ X := by
          intro k
          induction k with
          | zero => intro y hy; simpa using hy
          | succ k ih => intro y hy; rw [pow_succ', mul_assoc]; exact hg _ (ih y hy)
        intro y hy
        have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
          refine (eq_inv_of_mul_eq_one_left ?_).symm
          rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
        rw [hinv]
        exact hpow' _ y hy }
  have hPM : P ≤ M := by
    rw [hP]
    exact (Subgroup.closure_le M).2 fun x hx => hX x hx
  have h1X : (1 : G) ∈ X := ⟨0, hq, 1, N.one_mem, by simp⟩
  let f : Fin q × N → P := fun eh => ⟨u ^ (eh.1 : Nat) * eh.2,
    P.mul_mem (P.pow_mem hu _) (hN eh.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨e, he, h, hh, rfl⟩ : g ∈ X := by simpa using hPM hg 1 h1X
    exact ⟨(⟨e, he⟩, ⟨h, hh⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin q), Fintype.card_fin] at this

theorem pc_card_le (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {q n pb PR PW : Nat} (hq : 0 < q)
    (hpr : regsIn PR n nreg = true) (hpw : pwOK RB (mulR p w S d T L H CM RM) PR PW n q nreg = true)
    (hdone : ∀ i j, i ≤ j → j < n → PcDone RB (mulR p w S d T L H CM RM) ONE PR PW n q pb i j) :
    Nat.card (pcSub p d w S RB PR 0 n) ≤ q ^ n := by
  obtain ⟨hp, -⟩ := consts_facts hc
  have := finite_GL (d := d) hp
  have hu : ∀ k < n, ∃ u : GL (Fin d) (ZMod p),
      ((u : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = pcMat p d w S RB PR k := by
    intro k hk
    obtain ⟨-, u, -, eu⟩ := pc_reg hnb hc hR hpr hk
    exact ⟨u, eu⟩
  have key : ∀ t i, i + t = n → Nat.card (pcSub p d w S RB PR i n) ≤ q ^ t := by
    intro t
    induction t with
    | zero =>
      intro i hi
      have hbot : pcSub p d w S RB PR i n = ⊥ := by
        unfold pcSub
        rw [Subgroup.closure_eq_bot_iff]
        rintro g ⟨k, h1, h2, -⟩
        omega
      rw [hbot, Subgroup.card_bot]
      simp
    | succ t ih =>
      intro i hi
      obtain ⟨u, eu⟩ := hu i (by omega)
      have hcard := card_step (pcSub p d w S RB PR i n) (pcSub p d w S RB PR (i + 1) n) u q hq
        (pcSub_anti (Nat.le_succ i)) (mem_pcSub le_rfl (by omega) eu) ?_ ?_
        {g | ∃ k, i ≤ k ∧ k < n ∧
          ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = pcMat p d w S RB PR k}
        rfl ?_
      · calc Nat.card (pcSub p d w S RB PR i n) ≤ q * Nat.card (pcSub p d w S RB PR (i + 1) n) := hcard
          _ ≤ q * q ^ t := Nat.mul_le_mul_left _ (ih (i + 1) (by omega))
          _ = q ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
      · intro g hg
        have hle : pcSub p d w S RB PR (i + 1) n ≤
            (pcSub p d w S RB PR (i + 1) n).comap (MulAut.conj u⁻¹).toMonoidHom := by
          refine (Subgroup.closure_le _).2 ?_
          rintro y ⟨k, h1, h2, ey⟩
          obtain ⟨x, hx⟩ := hdone i k (by omega) h2
          obtain ⟨g', hg', -, hrel⟩ := pcRel_spec hc hnb hR hq hpr hpw (by omega) h2 hx eu ey
          have e2 := hrel (by omega)
          change u⁻¹ * y * u⁻¹⁻¹ ∈ pcSub p d w S RB PR (i + 1) n
          rw [inv_inv, mul_assoc, e2, ← mul_assoc, inv_mul_cancel, one_mul]
          exact hg'
        have := hle hg
        simpa using this
      · obtain ⟨x, hx⟩ := hdone i i le_rfl (by omega)
        obtain ⟨g', hg', hpow, -⟩ := pcRel_spec hc hnb hR hq hpr hpw le_rfl (by omega) hx eu eu
        rw [hpow rfl]
        exact hg'
      · rintro g ⟨k, h1, h2, eg⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact Or.inl (Units.ext (eg.trans eu.symm))
        · exact Or.inr (mem_pcSub h1 h2 eg)
  simpa using key n 0 (Nat.zero_add n)

theorem sylowPc_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {q n pb PR PW nbl BL : Nat} (hq : q.Prime)
    (hpr : regsIn PR n nreg = true) (hpw : pwOK RB (mulR p w S d T L H CM RM) PR PW n q nreg = true)
    {Cs : List Nat}
    (hpc : Nat.beq (runPc RB (mulR p w S d T L H CM RM) ONE PR PW n q pb Cs 1) (Nat.add 1 n) = true)
    (hbl : BlocksOK p d w S T RM LV HV RB PR n q nbl BL) :
    q ^ n ∣ Nat.card G := by
  obtain ⟨hp, -⟩ := consts_facts hc
  have := finite_GL (d := d) hp
  have hn := blocks_n_lt hbl.1
  have hup := pc_card_le hc hnb hR hq.pos hpr hpw (runPc_spec hn hpc)
  have hlo := blocks_le hc hnb hR hpr hbl
  have he : Nat.card (pcSub p d w S RB PR 0 n) = q ^ n := le_antisymm hup hlo
  rw [← he]
  exact Subgroup.card_dvd_of_le (pcSub_le hnb hc hR hpr 0)

end CFSG.KS.J4Hub

end
