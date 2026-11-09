module

public import CFSG.Certificates.Kernel.SporSch.PairHeCntSound
public import CFSG.Certificates.Kernel.SporSch.PairHeOrbPack

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative

theorem heoMask (w : Nat) : mask w = 2 ^ w - 1 := by
  simp [mask, Nat.shiftLeft_eq]

theorem heoFld (V o w : Nat) : fld(V, o, mask w) = V / 2 ^ o % 2 ^ w := by
  change (V >>> o) &&& mask w = _
  rw [heoMask, Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem heoFld_lt (V o w : Nat) : fld(V, o, mask w) < 2 ^ w := by
  rw [heoFld]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem heoPack_eq (L w : Nat) (f : Nat → Nat) :
    heoPack L w f = ∑ m ∈ Finset.range L, f m * 2 ^ (w * m) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change heoPack L w f + (f L <<< (w * L)) = _
    rw [Finset.sum_range_succ, ← ih, Nat.shiftLeft_eq]

theorem heoPack_fld {L w : Nat} {f : Nat → Nat} (hf : ∀ m < L, f m < 2 ^ w) {m : Nat}
    (hm : m < L) : fld(heoPack L w f, Nat.mul w m, mask w) = f m := by
  rw [heoFld, heoPack_eq]
  exact OrbCount.pack_digit w f L hf m hm

theorem keyL_congr' (n : Nat) {f g : Nat → Nat} :
    ∀ {bs : List Nat}, (∀ b ∈ bs, f b = g b) → keyL n f bs = keyL n g bs
  | [], _ => rfl
  | b :: bs, h => by
    change strictN (keyL n f bs) (fun r => Nat.add (f b) (Nat.mul n r)) =
      strictN (keyL n g bs) (fun r => Nat.add (g b) (Nat.mul n r))
    rw [strictN_val, strictN_val, keyL_congr' n fun c hc => h c (List.mem_cons_of_mem b hc),
      h b List.mem_cons_self]

theorem heoIx_lt {L t k c : Nat} (hL : 0 < L) (hc : c < L * t) : heoIx L k c < L * t := by
  change c - c % L + (c % L + (L - k)) % L < L * t
  have h1 := Nat.mod_add_div c L
  have h2 := Nat.mod_lt (c % L + (L - k)) hL
  have h3 : c / L < t := Nat.div_lt_of_lt_mul hc
  have h4 : L * (c / L) + L ≤ L * t := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left L h3
  omega

theorem heoIx_one {L k c : Nat} (hc : c < L) : heoIx L k c = (c + (L - k)) % L := by
  change c - c % L + (c % L + (L - k)) % L = _
  rw [Nat.mod_eq_of_lt hc, Nat.sub_self, Nat.zero_add]

theorem heoLoop_spec {n L N w mw MB : Nat} {bs : List Nat} {Z KS R : Nat → Nat} {j : Nat}
    (hZ : ∀ x, Z x < 2 ^ w)
    (hIx : ∀ b ∈ bs, ∀ k < L, heoIx L k fld(MB, Nat.mul mw b, mask mw) < N) :
    ∀ fuel k V, (∀ m < N, fld(V, Nat.mul w m, mask w) = powF Z k (R m)) →
      heoLoop n L N w mw MB bs Z KS j fuel k V = true → ∀ k', k ≤ k' → k' < k + fuel → k' < L →
      KS (Nat.add (Nat.mul j L) k') = keyL n (fun b =>
        powF Z k' (R (heoIx L k' fld(MB, Nat.mul mw b, mask mw)))) bs := by
  intro fuel
  induction fuel with
  | zero =>
    intro k V _ _ k' h1 h2 _
    omega
  | succ fuel ih =>
    intro k V hV h k' hk1 hk2 hL
    have h' : bAnd(Nat.beq (KS (Nat.add (Nat.mul j L) k))
        (keyL n (fun b => heoRd L w V k fld(MB, Nat.mul mw b, mask mw)) bs),
      strictB (heoMap N w Z V) (fun V' => heoLoop n L N w mw MB bs Z KS j fuel (Nat.succ k) V')) =
        true := h
    rw [bAnd_iff, strictB_val] at h'
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hlt
    · rw [Nat.eq_of_beq_eq_true h'.1]
      refine keyL_congr' n fun b hb => ?_
      unfold heoRd
      exact hV _ (hIx b hb k hL)
    · refine ih (Nat.succ k) _ (fun m hm => ?_) h'.2 k' hlt (by omega) hL
      unfold heoMap
      rw [heoPack_fld (fun m _ => hZ _) hm, hV m hm]
      exact (powF_succ Z k (R m)).symm

theorem heoAt_spec {w NR NL lv n L N mw MB OP : Nat} {LT PT X Z KS : Nat → Nat} {bs : List Nat}
    {j : Nat} (hZ : ∀ x, Z x < 2 ^ w)
    (hIx : ∀ b ∈ bs, ∀ k < L, heoIx L k fld(MB, Nat.mul mw b, mask mw) < N)
    (hR : ∀ m < N, nfPtT w NR NL LT PT lv (nfX lv (X j)) fld(OP, Nat.mul w m, mask w) < 2 ^ w)
    (h : heoAt w NR NL LT PT lv n L N mw MB OP bs X Z KS j = true) {k : Nat} (hk : k < L) :
    KS (Nat.add (Nat.mul j L) k) = keyL n (fun b => powF Z k (nfPtT w NR NL LT PT lv (nfX lv (X j))
      fld(OP, Nat.mul w (heoIx L k fld(MB, Nat.mul mw b, mask mw)), mask w))) bs := by
  unfold heoAt at h
  rw [strictB_val, strictB_val] at h
  exact heoLoop_spec (R := fun m => nfPtT w NR NL LT PT lv (nfX lv (X j)) fld(OP, Nat.mul w m, mask w))
    hZ hIx L 0 _ (fun m hm => heoPack_fld hR hm) h k (Nat.zero_le k) (by omega) hk

end CFSG.KS.SporSch

end
