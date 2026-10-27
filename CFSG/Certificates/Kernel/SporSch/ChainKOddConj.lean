module

public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
public import Certificates.Data.Kernel.SporSch.OddConj

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Certificates CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Mathieu

variable {n w : Nat}

@[expose] noncomputable def witP (n w : Nat) (p : Nat × Nat) : Equiv.Perm (Fin n) :=
  permOfArr n (unpack n w p.1)

theorem pbK_cons (n w m p : Nat) (b : Bool) (eb : List Bool) :
    pbK n w m p (b :: eb) = if b = true then pcomp n w m p (pcomp n w m (pbK n w m p eb)
      (pbK n w m p eb)) else pcomp n w m (pbK n w m p eb) (pbK n w m p eb) := by
  have e : pbK n w m p (b :: eb) = strictN (pcomp n w m (pbK n w m p eb) (pbK n w m p eb))
      (fun s => nIf(b, pcomp n w m p s, s)) := rfl
  rw [e, Orb.strictN_eq, Orb.nIf_eq]

theorem prep_pbK {P : Nat} {g : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32) (hw : 0 < w)
    (hP : PRep n w P g) (sP : P >>> (n * w) = 0) :
    ∀ eb, PRep n w (pbK n w (mask w) P eb) (g ^ bval eb) ∧ pbK n w (mask w) P eb >>> (n * w) = 0
  | [] => by
    have e : pbK n w (mask w) P [] = P := rfl
    rw [e, show bval [] = 1 from rfl, pow_one]
    exact ⟨hP, sP⟩
  | b :: eb => by
    obtain ⟨h1, -⟩ := prep_pbK hn hw hP sP eb
    have hs := prep_pcomp hn h1 h1
    rw [pbK_cons]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, bval, cond_false, Nat.add_zero]
      refine ⟨?_, PF.pcomp_shr _ _ hn hw⟩
      rw [two_mul, pow_add]
      exact hs
    · simp only [↓reduceIte, bval, cond_true]
      refine ⟨?_, PF.pcomp_shr _ _ hn hw⟩
      rw [pow_succ', two_mul, pow_add]
      exact prep_pcomp hn hP hs

theorem anyWitK_cons (n w m idn : Nat) (eb : List Bool) (c ci : Nat) (ws : List (Nat × Nat))
    (y : Nat) : anyWitK n w m idn eb ((c, ci) :: ws) y =
      (!Nat.beq (pbK n w m (pcomp n w m y (pcomp n w m c (pcomp n w m y ci))) eb) idn ||
        anyWitK n w m idn eb ws y) := by
  have e : anyWitK n w m idn eb ((c, ci) :: ws) y =
      bIf(Nat.beq (pbK n w m (pcomp n w m y (pcomp n w m c (pcomp n w m y ci))) eb) idn,
        anyWitK n w m idn eb ws y, true) := rfl
  rw [e, Orb.bIf_eq]
  cases Nat.beq (pbK n w m (pcomp n w m y (pcomp n w m c (pcomp n w m y ci))) eb) idn <;> simp

theorem allPairsK_cons (f : Nat → Nat → Bool) (c ci : Nat) (ws : List (Nat × Nat)) :
    allPairsK f ((c, ci) :: ws) = (f c ci && allPairsK f ws) := by
  have e : allPairsK f ((c, ci) :: ws) = bAnd(f c ci, allPairsK f ws) := rfl
  rw [e, Orb.bAnd_eq]

theorem allPairsK_spec {f : Nat → Nat → Bool} :
    ∀ {ws : List (Nat × Nat)}, allPairsK f ws = true → ∀ p ∈ ws, f p.1 p.2 = true
  | [], _, _, hp => absurd hp List.not_mem_nil
  | (c, ci) :: ws, h, p, hp => by
    rw [allPairsK_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact allPairsK_spec h.2 p hp

theorem prep_witP {p : Nat × Nat} (h : permOK n w (mask w) (n * w) p.1 p.2 = true) :
    PRep n w p.1 (witP n w p) ∧ PRep n w p.2 (witP n w p)⁻¹ := by
  have := rep_permOfArr (isInvA_unpack h)
  exact ⟨prep_of_rep this.1, prep_of_rep this.2⟩

section Facts

variable (hsz : szOK n w = true) {eb : List Bool} {Y : Nat} {y : Equiv.Perm (Fin n)}
  (pY : PRep n w Y y) (sY : Y >>> (n * w) = 0)
include hsz pY sY

theorem anyWitK_eq : ∀ {ws : List (Nat × Nat)},
    (∀ p ∈ ws, permOK n w (mask w) (n * w) p.1 p.2 = true) →
      anyWitK n w (mask w) (pidn n w) eb ws Y =
        ws.any fun p => !decide ((y * (witP n w p * (y * (witP n w p)⁻¹))) ^ bval eb = 1)
  | [], _ => rfl
  | (c, ci) :: ws, hws => by
    have hf := szOK_facts hsz
    have hn := szOK_lt hsz
    have hw := PF.w_pos hf.2
    rw [anyWitK_cons, List.any_cons, anyWitK_eq fun p hp => hws p (List.mem_cons_of_mem _ hp)]
    obtain ⟨p1, p2⟩ : PRep n w c (witP n w (c, ci)) ∧ PRep n w ci (witP n w (c, ci))⁻¹ :=
      prep_witP (hws (c, ci) List.mem_cons_self)
    have pX := prep_pcomp hn pY (prep_pcomp hn p1 (prep_pcomp hn pY p2))
    have pw := prep_pbK hn hw pX (PF.pcomp_shr _ _ hn hw) eb
    rw [beq_prep hw pw.1 (prep_pidn hf.1 hf.2) pw.2 (PF.pidn_shr hf.1 hf.2)]

theorem oddBadK_eq {ws : List (Nat × Nat)}
    (hws : ∀ p ∈ ws, permOK n w (mask w) (n * w) p.1 p.2 = true) :
    oddBadK n w (mask w) (pidn n w) eb ws Y = (!decide (y = 1) && decide (y ^ bval eb = 1) &&
      !(ws.any fun p => !decide ((y * (witP n w p * (y * (witP n w p)⁻¹))) ^ bval eb = 1))) := by
  have hf := szOK_facts hsz
  have hn := szOK_lt hsz
  have hw := PF.w_pos hf.2
  have pid := prep_pidn hf.1 hf.2
  have sid := PF.pidn_shr hf.1 hf.2
  have pw := prep_pbK hn hw pY sY eb
  unfold oddBadK
  rw [Orb.bIf_eq, Orb.bIf_eq, Orb.bIf_eq, beq_prep hw pY pid sY sid,
    beq_prep hw pw.1 pid pw.2 sid, anyWitK_eq hsz pY sY hws]
  by_cases h1 : y = 1 <;> by_cases h2 : y ^ bval eb = 1 <;> simp [h1, h2]

end Facts

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem chainK_oddConj (hk : 2 ≤ k) {eb : List Bool} {ws : List (Nat × Nat)}
    (hws : allPairsK (fun c ci => permOK n w (mask w) (n * w) c ci) ws = true)
    (hc : ∀ k₀ < rcnt (LR 0), ∀ k₁ < rcnt (LR 1),
      cntOddBad2K n w (mask w) (n * w) (pidn n w) LR TR k eb ws k₀ k₁ = 0)
    {y : Equiv.Perm (Fin n)} (hy : y ∈ (certificate hn gens words bv hbs).originalSubgroup)
    (hy1 : y ≠ 1) (hye : y ^ bval eb = 1) :
    ∃ p ∈ ws, (y * (witP n w p * y * (witP n w p)⁻¹)) ^ bval eb ≠ 1 := by
  have hn32 := chainK_h32 hQ
  have hw := PF.w_pos hQ.2.1
  have hsz := chainK_szOK hQ
  have hf := szOK_facts hsz
  have hws' := allPairsK_spec hws
  set q : Equiv.Perm (Fin n) → Bool := fun x => !decide (x = 1) && decide (x ^ bval eb = 1) &&
    !(ws.any fun p => !decide ((x * (witP n w p * (x * (witP n w p)⁻¹))) ^ bval eb = 1))
    with hq
  have hzero : ((enumeration (certificate hn gens words bv hbs)).map (1 * ·)).countP q = 0 := by
    rw [countP_coset2 hQ hn hbs hk]
    refine List.sum_eq_zero fun s hs => ?_
    obtain ⟨k₀, hk₀, rfl⟩ := List.mem_map.1 hs
    refine List.sum_eq_zero fun s' hs' => ?_
    obtain ⟨k₁, hk₁, rfl⟩ := List.mem_map.1 hs'
    refine Eq.trans ?_ (hc k₀ (List.mem_range.1 hk₀) k₁ (List.mem_range.1 hk₁))
    obtain ⟨t0, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hk₀)
    obtain ⟨t1, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hk₁)
    have e1 : cntOddBad2K n w (mask w) (n * w) (pidn n w) LR TR k eb ws k₀ k₁ =
        enumFrom n w (mask w) (n * w) LR TR (oddBadK n w (mask w) (pidn n w) eb ws) (k - 2) 2
          (pcomp n w (mask w) (pcomp n w (mask w) (pidn n w) (TR (roff n (n * w) (LR 0) + k₀)))
            (TR (roff n (n * w) (LR 1) + k₁))) 0 := by
      unfold cntOddBad2K start2
      rw [Orb.strictN_eq, Orb.strictN_eq]
      rfl
    rw [e1, enumFrom_spec hQ (q := q) (fun P x hP sP => oddBadK_eq hsz hP sP hws') (k - 2) 2
      (by omega) _ _ 0 (prep_pcomp hn32 (prep_pcomp hn32 (prep_pidn hf.1 hf.2) t0) t1)
      (PF.pcomp_shr _ _ hn32 hw), Nat.zero_add]
  simp only [one_mul, List.map_id'] at hzero
  have hmem := (mem_enumeration_iff _ (chainK_valid hQ hn hbs) y).2 hy
  have h1 := List.countP_eq_zero.1 hzero y hmem
  have h2 : (ws.any fun p => !decide ((y * (witP n w p * (y * (witP n w p)⁻¹))) ^ bval eb = 1)) =
      true := by
    simpa [hq, hy1, hye] using h1
  obtain ⟨p, hp, hne⟩ := List.any_eq_true.1 h2
  refine ⟨p, hp, ?_⟩
  simpa [mul_assoc] using hne

end Chain

end CFSG.KS.SporSch.MOC

end
