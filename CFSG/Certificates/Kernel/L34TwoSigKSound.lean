module

public import Certificates.Data.Kernel.L34TwoSigK
public import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34Two

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.KLie.CT (andB orB notB)

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sigSl_spec {n w B1 B2 nb L K N : Nat} {BT BTI T W : Nat → Nat} (hN : N = L * K)
    (hL : 0 < L) (h : ∀ s < K, sigSl n w B1 B2 BT BTI nb T W L s = true) :
    ∀ i < N, sigK n w B1 B2 BT BTI nb (pidn n w) (T i) (W i) = true := by
  intro i hi
  have hs : i / L < K := by
    rw [hN] at hi
    exact (Nat.div_lt_iff_lt_mul hL).2 (by rw [Nat.mul_comm]; exact hi)
  have h1 := h (i / L) hs
  unfold sigSl at h1
  rw [strictB_eq] at h1
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h1 (i % L) (Nat.mod_lt _ hL)
  rw [strictB_eq] at h'
  have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
  rw [e, strictB_eq, strictB_eq] at h'
  exact h'

theorem tabRep_iter : ∀ (k : Nat) {t : Tab} {g : Equiv.Perm (Fin 42)}, TabRep t g →
    TabRep ((fun t => comp 42 t t)^[k] t) (g ^ 2 ^ k)
  | 0, t, g, h => by simpa using h
  | k + 1, t, g, h => by
    rw [Function.iterate_succ_apply', pow_succ, pow_mul, sq]
    exact (tabRep_iter k h).comp (tabRep_iter k h)

theorem pow_beq_iff {x : Nat} {g : Equiv.Perm (Fin 42)}
    (hx : canonK 42 6 (mask 6) (42 * 6) x = true) (h : TabRep (unpack 42 6 x) g) :
    Nat.beq (pow2K 42 6 8 x) (pidn 42 6) = true ↔ g ^ 256 = 1 := by
  rw [← beq_unpack (pow2K_canon hx 8) (canon_pidn hsz42), pow2K_unpack hx,
    ← idTab_unpack' hsz42]
  exact (tabRep_iter 8 h).beq_iff TabRep.idTab

variable {nb : Nat} {BT BTI : Nat → Nat} {B₀ : Subgroup (Equiv.Perm (Fin 42))}

@[expose] def ConjOK (nb : Nat) (BT BTI : Nat → Nat) (B₀ : Subgroup (Equiv.Perm (Fin 42))) :
    Prop :=
  0 < nb ∧ ∀ j < nb, canonK 42 6 (mask 6) (42 * 6) (BT j) = true ∧
    canonK 42 6 (mask 6) (42 * 6) (BTI j) = true ∧
    pcomp 42 6 (mask 6) (BTI j) (BT j) = pidn 42 6 ∧ ∃ c ∈ B₀, TabRep (unpack 42 6 (BT j)) c

theorem conjK_rep (hB : ConjOK nb BT BTI B₀) {d x : Nat} {g : Equiv.Perm (Fin 42)}
    (hx : canonK 42 6 (mask 6) (42 * 6) x = true) (hg : TabRep (unpack 42 6 x) g) :
    canonK 42 6 (mask 6) (42 * 6) (conjK 42 6 BT BTI nb d x) = true ∧
      ∃ c ∈ B₀, TabRep (unpack 42 6 (conjK 42 6 BT BTI nb d x)) (c * g * c⁻¹) := by
  unfold conjK
  rw [strictN_eq]
  obtain ⟨c1, c2, ce, c, hc, hrep⟩ := hB.2 _ (Nat.mod_lt _ hB.1)
  have hinv : TabRep (unpack 42 6 (BTI ((d - 1) % nb))) c⁻¹ :=
    hrep.inv (size_unpack _) (by rw [comp_unpack' c2 c1, ce, ← idTab_unpack' hsz42])
  refine ⟨canonK_pcomp (canonK_pcomp c1 hx) c2, c, hc, ?_⟩
  have hr := (hrep.comp hg).comp hinv
  rw [comp_unpack' c1 hx, comp_unpack' (canonK_pcomp c1 hx) c2] at hr
  exact hr

theorem wordK_rep (hB : ConjOK nb BT BTI B₀) {x : Nat} {g : Equiv.Perm (Fin 42)}
    (hx : canonK 42 6 (mask 6) (42 * 6) x = true) (hg : TabRep (unpack 42 6 x) g) :
    ∀ f wd, canonK 42 6 (mask 6) (42 * 6) (wordK 42 6 BT BTI nb x f wd) = true ∧
      ∃ v ∈ Subgroup.closure {y | ∃ c ∈ B₀, y = c * g * c⁻¹},
        TabRep (unpack 42 6 (wordK 42 6 BT BTI nb x f wd)) v
  | 0, _ => ⟨canon_pidn hsz42, 1, Subgroup.one_mem _, by
      change TabRep (unpack 42 6 (pidn 42 6)) 1
      rw [← idTab_unpack' hsz42]
      exact TabRep.idTab⟩
  | f + 1, wd => by
    have e : wordK 42 6 BT BTI nb x (f + 1) wd = strictN (Nat.land wd 15) fun d =>
        nIf(Nat.beq d 0, pidn 42 6,
          pcomp 42 6 (mask 6) (conjK 42 6 BT BTI nb d x)
            (wordK 42 6 BT BTI nb x f (Nat.shiftRight wd 4))) := rfl
    rw [e, strictN_eq]
    cases Nat.beq (Nat.land wd 15) 0
    · obtain ⟨cc, c, hc, hcr⟩ := conjK_rep hB (d := Nat.land wd 15) hx hg
      obtain ⟨cw, v, hv, hvr⟩ := wordK_rep hB hx hg f (Nat.shiftRight wd 4)
      refine ⟨canonK_pcomp cc cw, c * g * c⁻¹ * v,
        Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c, hc, rfl⟩) hv, ?_⟩
      change TabRep (unpack 42 6 (pcomp 42 6 (mask 6) (conjK 42 6 BT BTI nb (Nat.land wd 15) x)
        (wordK 42 6 BT BTI nb x f (Nat.shiftRight wd 4)))) _
      rw [← comp_unpack' cc cw]
      exact hcr.comp hvr
    · exact ⟨canon_pidn hsz42, 1, Subgroup.one_mem _, by
        change TabRep (unpack 42 6 (pidn 42 6)) 1
        rw [← idTab_unpack' hsz42]
        exact TabRep.idTab⟩

theorem commPt_rep {x b : Nat} {g h : Equiv.Perm (Fin 42)}
    (hx : canonK 42 6 (mask 6) (42 * 6) x = true) (hb : canonK 42 6 (mask 6) (42 * 6) b = true)
    (hg : TabRep (unpack 42 6 x) g) (hh : TabRep (unpack 42 6 b) h) (hc : commPt 42 6 x b = true) :
    h * g = g * h :=
  (((hg.comp hh).eq_iff (hh.comp hg)).1 ((commPt_iff hx hb).1 hc)).symm

theorem pg_pow2K {n w x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    ∀ k, ∀ i < n, pg w (mask w) (pow2K n w k x) i = (pg w (mask w) x)^[2 ^ k] i
  | 0, i, _ => by
    rw [pow_zero, Function.iterate_one]
    rfl
  | k + 1, i, hi => by
    have hc := pow2K_canon hx k
    rw [pow2K_succ, pg_pcomp' hc hi,
      pg_pow2K hx k _ ((CFSG.KS.PF.canon_facts hc).2.2.2 i hi), pg_pow2K hx k i hi, pow_succ,
      mul_two, Function.iterate_add_apply]

theorem cycL_spec {w x p : Nat} : ∀ fu q c, cycL w x p fu q c ≠ 0 →
    q = (pg w (mask w) x)^[c] p → (∀ j, 0 < j → j < c → (pg w (mask w) x)^[j] p ≠ p) →
    (pg w (mask w) x)^[cycL w x p fu q c] p = p ∧
      ∀ j, 0 < j → j < cycL w x p fu q c → (pg w (mask w) x)^[j] p ≠ p
  | 0, _, _, h, _, _ => (h rfl).elim
  | fu + 1, q, c, h, hq, hm => by
    have e : cycL w x p (fu + 1) q c = Bool.rec (motive := fun _ => Nat)
        (cycL w x p fu (pg w (mask w) x q) (Nat.succ c)) c (Nat.beq q p) := rfl
    rw [e] at h ⊢
    cases hb : Nat.beq q p
    · rw [hb] at h
      have hqp : q ≠ p := Nat.ne_of_beq_eq_false hb
      refine cycL_spec fu _ _ h ?_ fun j hj hj' => ?_
      · rw [hq]
        exact (Function.iterate_succ_apply' _ c p).symm
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hlt | rfl
        · exact hm j hj hlt
        · rw [← hq]
          exact hqp
    · refine ⟨?_, hm⟩
      change (pg w (mask w) x)^[c] p = p
      rw [← hq]
      exact Nat.eq_of_beq_eq_true hb

theorem badP_spec {n w x p : Nat} (h : badP n w x p = true) :
    (pg w (mask w) x)^[256] p ≠ p := by
  intro h256
  unfold badP at h
  rw [strictB_eq] at h
  simp only [andB_iff, notB_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hpos := Nat.blt_eq.mp h1
  obtain ⟨hl, hmin⟩ := cycL_spec n (pg w (mask w) x p) 1 (Nat.pos_iff_ne_zero.1 hpos) rfl
    fun j hj hj' => by omega
  have hP : Function.IsPeriodicPt (pg w (mask w) x) (cycL w x p n (pg w (mask w) x p) 1) p := hl
  have hmp : Function.minimalPeriod (pg w (mask w) x) p = cycL w x p n (pg w (mask w) x p) 1 := by
    by_contra hne
    exact hmin _ (hP.minimalPeriod_pos hpos) (lt_of_le_of_ne (hP.minimalPeriod_le hpos) hne)
      (Function.isPeriodicPt_minimalPeriod _ p)
  have h256' : Function.IsPeriodicPt (pg w (mask w) x) 256 p := h256
  have hd := h256'.minimalPeriod_dvd
  rw [hmp] at hd
  exact Nat.ne_of_beq_eq_false h2 (Nat.mod_eq_zero_of_dvd hd)

theorem cycNP_spec {n w x : Nat} : ∀ k p, cycNP n w x k p = true → p + k ≤ n →
    ¬ ∀ i < n, (pg w (mask w) x)^[256] i = i
  | 0, _, h, _, _ => Bool.false_ne_true h
  | k + 1, p, h, hk, hall => by
    have e : cycNP n w x (k + 1) p = orB (badP n w x p) (cycNP n w x k (Nat.succ p)) := rfl
    rw [e, orB_iff] at h
    rcases h with h | h
    · exact badP_spec h (hall p (by omega))
    · exact cycNP_spec k (p + 1) h (by omega) hall

theorem fix256 {x : Nat} {g : Equiv.Perm (Fin 42)} (hx : canonK 42 6 (mask 6) (42 * 6) x = true)
    (h : TabRep (unpack 42 6 x) g) (h2 : g ^ 256 = 1) :
    ∀ i < 42, (pg 6 (mask 6) x)^[256] i = i := by
  intro i hi
  have e := Nat.eq_of_beq_eq_true ((pow_beq_iff hx h).2 h2)
  have hp := pg_pow2K hx 8 i hi
  rw [e, pg_pidn' hsz42 hi] at hp
  exact hp.symm

theorem twoSig_of {N B1 B2 : Nat} {T W : Nat → Nat} {R : Subgroup (Equiv.Perm (Fin 42))}
    {b₁ b₂ : Equiv.Perm (Fin 42)} (hR : Enumerates R (pts 42 6 N T).toList)
    (hT : ∀ i < N, canonK 42 6 (mask 6) (42 * 6) (T i) = true) (hB : ConjOK nb BT BTI B₀)
    (hB1 : canonK 42 6 (mask 6) (42 * 6) B1 = true) (hB2 : canonK 42 6 (mask 6) (42 * 6) B2 = true)
    (hb₁ : TabRep (unpack 42 6 B1) b₁) (hb₂ : TabRep (unpack 42 6 B2) b₂)
    (hB₀ : B₀ = Subgroup.closure {b₁, b₂})
    (h : ∀ i < N, sigK 42 6 B1 B2 BT BTI nb (pidn 42 6) (T i) (W i) = true) :
    ∀ r ∈ R, r ^ 256 = 1 → (∀ b ∈ B₀, b * r = r * b) ∨
      ∃ v ∈ Subgroup.closure {x | ∃ c ∈ B₀, x = c * r * c⁻¹}, v ^ 256 ≠ 1 := by
  intro r hr h2
  obtain ⟨t, ht, hrt⟩ := hR.complete r hr
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
  rw [size_pts] at hi
  rw [pts_get' hi] at hrt
  have hx := hT i hi
  have hk := h i hi
  unfold sigK at hk
  rw [strictB_eq] at hk
  simp only [orB_iff, notB_iff, andB_iff] at hk
  rcases hk with h1 | ⟨c1, c2⟩ | h3 | h3
  · exact (cycNP_spec 7 0 h1 (by norm_num) (fix256 hx hrt h2)).elim
  · left
    have hle : B₀ ≤ Subgroup.centralizer {r} := by
      rw [hB₀, Subgroup.closure_le]
      rintro a (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (commPt_rep hx hB1 hrt hb₁ c1)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (commPt_rep hx hB2 hrt hb₂ c2)
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hb)
  · right
    obtain ⟨cw, v, hv, hvr⟩ := wordK_rep hB hx hrt 8 (W i)
    exact ⟨v, hv, fun hv2 => cycNP_spec 3 0 h3 (by norm_num) (fix256 cw hvr hv2)⟩
  · right
    obtain ⟨cw, v, hv, hvr⟩ := wordK_rep hB hx hrt 8 (W i)
    refine ⟨v, hv, fun hv2 => ?_⟩
    rw [(pow_beq_iff cw hvr).2 hv2] at h3
    exact absurd h3 (by decide)

end CFSG.KC.L34Two

end
