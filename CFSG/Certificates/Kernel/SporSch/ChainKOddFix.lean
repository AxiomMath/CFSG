module

public import CFSG.Certificates.Kernel.SporSch.ChainKOddConj
public import Certificates.Data.Kernel.SporSch.OddFix

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Certificates CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Mathieu

variable {n w : Nat}

theorem oFpow_mod {y : Equiv.Perm (Fin n)} {x : Fin n} {L : Nat} (hL : (y ^ L) x = x) (e : Nat) :
    (y ^ e) x = (y ^ (e % L)) x := by
  conv_lhs => rw [← Nat.mod_add_div e L, pow_add, pow_mul, Equiv.Perm.mul_apply,
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hL]

section Pt

variable {Y : Nat} {y : Equiv.Perm (Fin n)} (pY : PRep n w Y y)
include pY

theorem oFpw_eq {x : Nat} (hx : x < n) :
    ∀ k, oFpw w (mask w) Y k x = ((y ^ k) ⟨x, hx⟩ : Nat)
  | 0 => by rw [pow_zero, Equiv.Perm.one_apply]; rfl
  | k + 1 => by
    have e : oFpw w (mask w) Y (k + 1) x = pg w (mask w) Y (oFpw w (mask w) Y k x) := rfl
    rw [e, oFpw_eq hx k, pY ((y ^ k) ⟨x, hx⟩), pow_succ', Equiv.Perm.mul_apply]

theorem oFwalk_spec {x : Nat} (hx : x < n) :
    ∀ f k, oFwalk w (mask w) Y x f (k + 1) ((y ^ k) ⟨x, hx⟩) ≠ 0 →
      (y ^ oFwalk w (mask w) Y x f (k + 1) ((y ^ k) ⟨x, hx⟩)) ⟨x, hx⟩ = ⟨x, hx⟩
  | 0, _, h => absurd rfl h
  | f + 1, k, h => by
    have es : oFwalk w (mask w) Y x (f + 1) (k + 1) ((y ^ k) ⟨x, hx⟩) =
        strictN (pg w (mask w) Y ((y ^ k) ⟨x, hx⟩)) fun nx =>
          nIf(Nat.beq nx x, k + 1, oFwalk w (mask w) Y x f (k + 1 + 1) nx) := rfl
    have e : oFwalk w (mask w) Y x (f + 1) (k + 1) ((y ^ k) ⟨x, hx⟩) =
        nIf(Nat.beq ((y ^ (k + 1)) ⟨x, hx⟩ : Nat) x, k + 1,
          oFwalk w (mask w) Y x f (k + 1 + 1) ((y ^ (k + 1)) ⟨x, hx⟩)) := by
      rw [es, Orb.strictN_eq, pY, pow_succ', Equiv.Perm.mul_apply]
    rw [e, Orb.nIf_eq] at h ⊢
    by_cases hb : Nat.beq ((y ^ (k + 1)) ⟨x, hx⟩ : Nat) x = true
    · simp only [hb, ↓reduceIte]
      exact Fin.ext (Nat.eq_of_beq_eq_true hb)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact oFwalk_spec hx f (k + 1) h

theorem oFfix_eq (e : Nat) {x : Nat} (hx : x < n) :
    oFfix n w (mask w) Y e x = decide ((y ^ e) ⟨x, hx⟩ = ⟨x, hx⟩) := by
  have hs : ∀ (L : Nat) (k : Nat → Bool), strictB L k = k L := fun L k => by cases L <;> rfl
  have h0 : oFwalk w (mask w) Y x n 1 x = oFwalk w (mask w) Y x n (0 + 1) ((y ^ 0) ⟨x, hx⟩) := by
    rw [pow_zero, Equiv.Perm.one_apply]
  have hw := oFwalk_spec pY hx n 0
  rw [← h0] at hw
  rw [oFfix, hs, Orb.nIf_eq]
  generalize oFwalk w (mask w) Y x n 1 x = L at hw
  by_cases hL : Nat.beq L 0 = true
  · simp only [hL, ↓reduceIte]
    rw [oFpw_eq pY hx, Orb.beq_dec]
    simp only [Fin.ext_iff]
  · simp only [hL, Bool.false_eq_true, ↓reduceIte]
    rw [oFpw_eq pY hx, Orb.beq_dec, oFpow_mod (hw fun h => hL (by rw [h]; rfl)) e]
    simp only [Fin.ext_iff]
    rfl

theorem oFone_eq (e : Nat) : oFone n w (mask w) Y e = decide (y ^ e = 1) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, oFone, allN_iff]
  constructor
  · intro h
    ext x
    have := h x x.2
    rw [oFfix_eq pY e x.2, decide_eq_true_iff] at this
    rw [this, Equiv.Perm.one_apply]
  · intro h i hi
    rw [oFfix_eq pY e hi, h]
    simp

end Pt

section Facts

variable (hsz : szOK n w = true) {Y : Nat} {y : Equiv.Perm (Fin n)}
  (pY : PRep n w Y y) (sY : Y >>> (n * w) = 0)
include hsz pY sY

omit sY in
theorem oFanyWit_eq (e : Nat) : ∀ {ws : List (Nat × Nat)},
    (∀ p ∈ ws, permOK n w (mask w) (n * w) p.1 p.2 = true) →
      oFanyWit n w (mask w) e ws Y =
        ws.any fun p => !decide ((y * (witP n w p * (y * (witP n w p)⁻¹))) ^ e = 1)
  | [], _ => rfl
  | (c, ci) :: ws, hws => by
    have hn := szOK_lt hsz
    have e1 : oFanyWit n w (mask w) e ((c, ci) :: ws) Y =
        bIf(oFone n w (mask w) (pcomp n w (mask w) Y (pcomp n w (mask w) c
          (pcomp n w (mask w) Y ci))) e, oFanyWit n w (mask w) e ws Y, true) := rfl
    obtain ⟨p1, p2⟩ : PRep n w c (witP n w (c, ci)) ∧ PRep n w ci (witP n w (c, ci))⁻¹ :=
      prep_witP (hws (c, ci) List.mem_cons_self)
    have pX := prep_pcomp hn pY (prep_pcomp hn p1 (prep_pcomp hn pY p2))
    rw [e1, Orb.bIf_eq, oFone_eq pX e, List.any_cons,
      oFanyWit_eq e fun p hp => hws p (List.mem_cons_of_mem _ hp)]
    by_cases h : (y * (witP n w (c, ci) * (y * (witP n w (c, ci))⁻¹))) ^ e = 1 <;> simp [h]

theorem oFbad_eq (e : Nat) {ws : List (Nat × Nat)}
    (hws : ∀ p ∈ ws, permOK n w (mask w) (n * w) p.1 p.2 = true) :
    oFbad n w (mask w) (pidn n w) e ws Y = (!decide (y = 1) && decide (y ^ e = 1) &&
      !(ws.any fun p => !decide ((y * (witP n w p * (y * (witP n w p)⁻¹))) ^ e = 1))) := by
  have hf := szOK_facts hsz
  have hw := PF.w_pos hf.2
  have pid := prep_pidn hf.1 hf.2
  have sid := PF.pidn_shr hf.1 hf.2
  unfold oFbad
  rw [Orb.bIf_eq, Orb.bIf_eq, Orb.bIf_eq, beq_prep hw pY pid sY sid, oFone_eq pY e,
    oFanyWit_eq hsz pY e hws]
  by_cases h1 : y = 1 <;> by_cases h2 : y ^ e = 1 <;> simp [h1, h2]

end Facts

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem chainK_oddConjF (hk : 2 ≤ k) {e : Nat} {ws : List (Nat × Nat)}
    (hws : allPairsK (fun c ci => permOK n w (mask w) (n * w) c ci) ws = true)
    (hc : ∀ k₀ < rcnt (LR 0), ∀ k₁ < rcnt (LR 1),
      cntOddFixK n w (mask w) (n * w) (pidn n w) LR TR k e ws k₀ k₁ = 0)
    {y : Equiv.Perm (Fin n)} (hy : y ∈ (certificate hn gens words bv hbs).originalSubgroup)
    (hy1 : y ≠ 1) (hye : y ^ e = 1) :
    ∃ p ∈ ws, (y * (witP n w p * y * (witP n w p)⁻¹)) ^ e ≠ 1 := by
  have hn32 := chainK_h32 hQ
  have hw := PF.w_pos hQ.2.1
  have hsz := chainK_szOK hQ
  have hf := szOK_facts hsz
  have hws' := allPairsK_spec hws
  set q : Equiv.Perm (Fin n) → Bool := fun x => !decide (x = 1) && decide (x ^ e = 1) &&
    !(ws.any fun p => !decide ((x * (witP n w p * (x * (witP n w p)⁻¹))) ^ e = 1))
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
    have e1 : cntOddFixK n w (mask w) (n * w) (pidn n w) LR TR k e ws k₀ k₁ =
        enumFrom n w (mask w) (n * w) LR TR (oFbad n w (mask w) (pidn n w) e ws) (k - 2) 2
          (pcomp n w (mask w) (pcomp n w (mask w) (pidn n w) (TR (roff n (n * w) (LR 0) + k₀)))
            (TR (roff n (n * w) (LR 1) + k₁))) 0 := by
      unfold cntOddFixK start2
      rw [Orb.strictN_eq, Orb.strictN_eq]
      rfl
    rw [e1, enumFrom_spec hQ (q := q) (fun P x hP sP => oFbad_eq hsz hP sP e hws') (k - 2) 2
      (by omega) _ _ 0 (prep_pcomp hn32 (prep_pcomp hn32 (prep_pidn hf.1 hf.2) t0) t1)
      (PF.pcomp_shr _ _ hn32 hw), Nat.zero_add]
  simp only [one_mul, List.map_id'] at hzero
  have hmem := (mem_enumeration_iff _ (chainK_valid hQ hn hbs) y).2 hy
  have h1 := List.countP_eq_zero.1 hzero y hmem
  have h2 : (ws.any fun p => !decide ((y * (witP n w p * (y * (witP n w p)⁻¹))) ^ e = 1)) =
      true := by
    simpa [hq, hy1, hye] using h1
  obtain ⟨p, hp, hne⟩ := List.any_eq_true.1 h2
  refine ⟨p, hp, ?_⟩
  simpa [mul_assoc] using hne

end Chain

end CFSG.KS.SporSch.MOC

end
