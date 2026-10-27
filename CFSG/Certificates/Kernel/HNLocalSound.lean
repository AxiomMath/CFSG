module

public import CFSG.Certificates.Kernel.HNLocal.Defs
import CFSG.Certificates.Kernel.HNLocal.Mat
import CFSG.Certificates.Kernel.HNLocal.Cen
import CFSG.Certificates.Kernel.HNLocal.Row
import CFSG.Certificates.Kernel.HNLocal.Tree

public section

namespace CFSG.KS.HNLocal

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord Matrix

variable {L H CM RM ONE LV HV CM3 M MS : Nat}

theorem treeLeaf_sound {XC TD MSF : Nat → Nat} {N GA GB GFC j : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hms : masksOK MS = true)
    (hmsf : msfOK MS MSF = true) (hcm : cmOK CM3 M = true) (hGA : Canon 5 133 13 GA)
    (hGB : Canon 5 133 13 GB) (hGF : Canon 5 133 13 GFC)
    (h : treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC j < 2 ^ 50) :
    TD j % 2 ^ 21 + TD j / 2 ^ 21 % 512 = TD (j + 1) % 2 ^ 21 ∧
      ((∀ i < TD (j + 1) % 2 ^ 21 / 133, XC i < 2 ^ 53200) →
        (∀ t < TD j / 2 ^ 21 % 512, 0 < recX XC M (TD j % 2 ^ 21 + t)) →
        ∀ t < TD j / 2 ^ 21 % 512, ∃ r < 133, 133 * j + r < TD j % 2 ^ 21 + t ∧
        CCanon (recX XC M (TD j % 2 ^ 21 + t)) ∧
        (cvec (recX XC M (TD j % 2 ^ 21 + t)) = (OM GA)ᵀ *ᵥ cvec (recX XC M (133 * j + r)) ∨
          cvec (recX XC M (TD j % 2 ^ 21 + t)) = (OM GB)ᵀ *ᵥ cvec (recX XC M (133 * j + r)))) ∧
      treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC j =
        ((Finset.range (min (N - 133 * j) 133)).filter fun r => ∀ i : Fin 133, i.val < 56 →
            ((OM GFC)ᵀ *ᵥ cvec (recX XC M (133 * j + r))) i = 0).card +
          2 ^ 24 * ((Finset.range (min (N - 133 * j) 133)).filter fun r => ∀ i : Fin 133,
            56 ≤ i.val → i.val < 120 → ((OM GFC)ᵀ *ᵥ cvec (recX XC M (133 * j + r))) i = 0).card :=
  TreePf.treeLeaf_sound' hc hms hmsf hcm hGA hGB hGF h

theorem actLeaf_sound {XC PI : Nat → Nat} {nW G c nr : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hms : masksOK MS = true)
    (hcm : cmOK CM3 M = true) (hG : Canon 5 133 13 G) (hnr : nr ≤ 133)
    (h : actLeaf XC PI M MS L H CM3 RM nW G c nr = true) :
    ∀ r < nr, PI (133 * c + r) < nW ∧ CCanon (recX XC M (PI (133 * c + r))) ∧
      cvec (recX XC M (PI (133 * c + r))) = (OM G)ᵀ *ᵥ cvec (recX XC M (133 * c + r)) :=
  RowPf.actLeaf_sound' hc hms hcm hG hnr h

theorem fixVec_sound {G x : Nat} (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hms : masksOK MS = true) (hcm : cmOK CM3 M = true) (hG : Canon 5 133 13 G) (hx : x < 2 ^ 399)
    (h : fixVec MS L H CM3 RM G x = true) : CCanon x ∧ (OM G)ᵀ *ᵥ cvec x = cvec x :=
  RowPf.fixVec_sound' hc hms hcm hG hx h

theorem cenAt_sound {PC RP TG : Nat → Nat} {np m k n : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hPC : ∀ i < k + n, Canon 5 133 13 (PC i)) (hRP : ∀ a < np, Canon 5 133 13 (RP a))
    (hm : m < 2 ^ k)
    (h : cenAt (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) PC RP TG np ONE RM
      m k n = true) :
    ∀ e : Nat → Nat, (∀ i, e i < 2) → (∀ i < k, e i = m / 2 ^ i % 2) →
      nfE PC (k + n) e = 1 ∨ nfE PC (k + n) e * nfE PC (k + n) e ≠ 1 ∨
      ∃ a < np, ∃ q, q % 2 = 1 ∧ (nfE PC (k + n) e * OM (RP a)) ^ q = 1 :=
  CenPf.cenAt_sound' hc hPC hRP hm h

theorem trM_sound {X : Nat} (hX : Canon 5 133 13 X) : Canon 5 133 13 (trM X) ∧ OM (trM X) = (OM X)ᵀ :=
  MatPf.trM_sound' hX

theorem traceL_sound {X : Nat} (hX : Canon 5 133 13 X) : ((traceL X : Nat) : ZMod 5) = (OM X).trace :=
  MatPf.traceL_sound' hX

theorem subOne_sound {X : Nat} (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hX : Canon 5 133 13 X) :
    Canon 5 133 13 (redP 13 L H 5 9 (X + 4 * ONE)) ∧ OM (redP 13 L H 5 9 (X + 4 * ONE)) = OM X - 1 :=
  MatPf.subOne_sound' hc hX

theorem rows_sound {X m n : Nat} (hX : Canon 5 133 13 X) :
    Canon 5 133 13 (Nat.land (Nat.shiftRight X (1729 * m)) (2 ^ (1729 * n) - 1)) ∧
      ∀ i j : Fin 133, OM (Nat.land (Nat.shiftRight X (1729 * m)) (2 ^ (1729 * n) - 1)) i j =
        if h : i.val < n ∧ m + i.val < 133 then OM X ⟨m + i.val, h.2⟩ j else 0 :=
  MatPf.rows_sound' hX

private theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem bIf_true {c t : Bool} (h : bIf(c, t, true) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

private theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem sig_eq {SD : Nat → Nat} {m u : Nat} (hu : u < 133) :
    sig SD (133 * m + u) = Nat.land (Nat.shiftRight (SD m) (21 * u)) 2097151 := by
  unfold sig
  have h1 : (133 * m + u) / 133 = m := by omega
  have h2 : (133 * m + u) % 133 = u := by omega
  change Nat.land (Nat.shiftRight (SD ((133 * m + u) / 133)) (21 * ((133 * m + u) % 133))) 2097151 = _
  rw [h1, h2]

theorem sortGo_spec {XC SD : Nat → Nat} {N m : Nat} : ∀ f t pk,
    sortGo XC N M (SD m) (SD (m + 1)) m f t pk = true → t + f = 133 →
      pk = recX XC M (sig SD (133 * m + t)) → ∀ u, t ≤ u → u < 133 → 133 * m + u + 1 < N →
      sig SD (133 * m + u + 1) < N ∧
        recX XC M (sig SD (133 * m + u)) < recX XC M (sig SD (133 * m + u + 1)) := by
  intro f
  induction f with
  | zero => intro t pk _ hf _ u hu hu' _; omega
  | succ f ih =>
    intro t pk h hf hpk u hu hu' hN
    have hN' : 133 * m + t + 1 < N := by omega
    have hb : Nat.blt (Nat.succ (Nat.add (Nat.mul 133 m) t)) N = true := Nat.blt_eq.mpr hN'
    have e : sortGo XC N M (SD m) (SD (m + 1)) m (f + 1) t pk =
        bIf(Nat.blt (Nat.succ (Nat.add (Nat.mul (nat_lit 133) m) t)) N,
          letB (nIf(Nat.blt t (nat_lit 132),
              Nat.land (Nat.shiftRight (SD m) (Nat.mul (nat_lit 21) (Nat.succ t))) (nat_lit 2097151),
              Nat.land (SD (m + 1)) (nat_lit 2097151))) (fun b =>
          letB (recX XC M b) (fun kb =>
            bAnd(Nat.blt b N, bAnd(Nat.blt pk kb,
              sortGo XC N M (SD m) (SD (m + 1)) m f (Nat.succ t) kb)))),
          true) := rfl
    rw [e] at h
    have h' := bIf_true h hb
    have hsig : (nIf(Nat.blt t (nat_lit 132),
        Nat.land (Nat.shiftRight (SD m) (Nat.mul (nat_lit 21) (Nat.succ t))) (nat_lit 2097151),
        Nat.land (SD (m + 1)) (nat_lit 2097151))) = sig SD (133 * m + t + 1) := by
      by_cases ht : t < 132
      · have : Nat.blt t 132 = true := Nat.blt_eq.mpr ht
        rw [this]
        rw [show 133 * m + t + 1 = 133 * m + (t + 1) by omega, sig_eq (by omega)]
        rfl
      · have : Nat.blt t 132 = false := by
          cases e2 : Nat.blt t 132
          · rfl
          · exact absurd (Nat.blt_eq.mp e2) ht
        rw [this]
        have ht' : t = 132 := by omega
        subst ht'
        rw [show 133 * m + 132 + 1 = 133 * (m + 1) + 0 by omega, sig_eq (by norm_num)]
        simp
    rw [hsig, letB_eq, letB_eq] at h'
    obtain ⟨h1, h2⟩ := bAnd_true h'
    obtain ⟨h2, h3⟩ := bAnd_true h2
    rcases Nat.eq_or_lt_of_le hu with rfl | hu
    · refine ⟨Nat.blt_eq.mp h1, ?_⟩
      rw [← hpk]
      exact Nat.blt_eq.mp h2
    · have := ih (t + 1) _ h3 (by omega) (by rw [show 133 * m + (t + 1) = 133 * m + t + 1 by omega])
        u hu hu' hN
      exact this

theorem sortLeaf_spec {XC SD : Nat → Nat} {N m : Nat} (h : sortLeaf XC SD N M m = true) :
    (133 * m < N → sig SD (133 * m) < N) ∧
      ∀ u < 133, 133 * m + u + 1 < N → sig SD (133 * m + u + 1) < N ∧
        recX XC M (sig SD (133 * m + u)) < recX XC M (sig SD (133 * m + u + 1)) := by
  unfold sortLeaf at h
  rw [letB_eq, letB_eq, letB_eq] at h
  have hs0 : Nat.land (SD m) 2097151 = sig SD (133 * m) := by
    rw [show 133 * m = 133 * m + 0 by omega, sig_eq (by norm_num)]
    simp
  refine ⟨fun hm => ?_, fun u hu hN => ?_⟩
  · have hb : Nat.blt (Nat.mul 133 m) N = true := Nat.blt_eq.mpr hm
    obtain ⟨h1, -⟩ := bAnd_true (bIf_true h hb)
    rw [← hs0]
    exact Nat.blt_eq.mp h1
  · have hb : Nat.blt (Nat.mul 133 m) N = true := Nat.blt_eq.mpr (show 133 * m < N by omega)
    obtain ⟨-, h2⟩ := bAnd_true (bIf_true h hb)
    rw [hs0] at h2
    exact sortGo_spec 133 0 _ h2 rfl (by simp) u (Nat.zero_le _) hu hN

theorem allBelow_spec {m hi : Nat} {f : Nat → Bool} (h : CFSG.KC.Loop.allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  have inner : ∀ (hh : Nat) (n : Nat), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl hlm
      obtain ⟨h1, h2⟩ := bAnd_true hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact ih h2 l hl hlm
      · have hb : Nat.blt (Nat.add (Nat.shiftLeft hh 6) l) m = true := Nat.blt_eq.mpr hlm
        exact bIf_true h1 hb
  have outer : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun hh ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64,
        ih)) n = true → ∀ hh < n, ∀ l < 64, Nat.add (Nat.shiftLeft hh 6) l < m →
          f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ hh hhh; omega
    | succ n ih =>
      intro hn hh hhh l hl hlm
      obtain ⟨h1, h2⟩ := bAnd_true hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhh with hhh | rfl
      · exact ih h2 hh hhh l hl hlm
      · exact inner _ 64 h1 l hl hlm
  intro i him hih
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have := outer hi h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by norm_num)) (by rw [e]; exact him)
  rwa [e] at this

theorem sortRange_spec {XC SD : Nat → Nat} {N lo n : Nat} (h : sortRange XC SD N M lo n = true) :
    ∀ i < n, sortLeaf XC SD N M (lo + i) = true := by
  intro i hi
  exact allBelow_spec h i hi (show i < 64 * (n / 64 + 1) by omega)

end CFSG.KS.HNLocal

end
