module

public import Certificates.Data.Kernel.Co2R3K
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.Co2Rank3.CheckInputs
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Co2R3KSnd.OrbReplay

public section

namespace CFSG.KC.Co2R3.Snd

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Sporadic.Co2Rank3
  CFSG.Sporadic.Co2Rank3.Native
open CFSG.Monster.B.Co2 (allLt_iff)

private theorem anyRootK_spec : ∀ (roots : List (Nat × Nat)) {v : Nat},
    anyRootK roots v = true → ∃ r ∈ roots, (r.1 == v) = true
  | [], v, h => by
    have e : anyRootK [] v = false := rfl
    rw [e] at h
    cases h
  | r :: rs, v, h => by
    have e : anyRootK (r :: rs) v =
        Bool.rec (motive := fun _ => Bool) (anyRootK rs v) true (Nat.beq r.1 v) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := bif_true h
    cases hb : Nat.beq r.1 v
    · obtain ⟨r', hr', e'⟩ := anyRootK_spec rs (h2 hb)
      exact ⟨r', List.mem_cons_of_mem _ hr', e'⟩
    · exact ⟨r, List.mem_cons_self .., beq_iff_eq.2 (beq_t hb)⟩

private theorem rootsK_spec {L : Nat} : ∀ {roots : List (Nat × Nat)}, rootsK L roots = true →
    ∀ r ∈ roots, r.1 < 2300 ∧ at12 L r.1 = r.1 ∧
      cntK 2300 (fun w => Nat.beq (at12 L w) r.1) = r.2
  | [], _, _, hr => by cases hr
  | r :: rs, h, r', hr' => by
    have e : rootsK L (r :: rs) = Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false (rootsK L rs)
            (Nat.beq (cntK 2300 fun w => Nat.beq (at12 L w) r.1) r.2))
          (Nat.beq (at12 L r.1) r.1))
        (Nat.blt r.1 2300) := rfl
    rw [e] at h
    obtain ⟨h1, h'⟩ := band_true h
    obtain ⟨h2, h''⟩ := band_true h'
    obtain ⟨h3, h4⟩ := band_true h''
    rcases List.mem_cons.1 hr' with e' | hm
    · subst e'
      exact ⟨blt_t h1, beq_t h2, beq_t h3⟩
    · exact rootsK_spec h4 r' hm

private theorem foldr_cnt (f : Nat → Bool) : ∀ (n s : Nat),
    (List.range n).foldr (fun w a => Bool.rec (motive := fun _ => Nat) a (Nat.add a 1) (f w)) s =
      s + ((Finset.range n).filter fun w => f w = true).card
  | 0, s => by simp
  | n + 1, s => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_cnt f n,
      Finset.range_add_one, Finset.filter_insert]
    cases hf : f n
    · rw [if_neg Bool.false_ne_true]
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      change s + 1 + _ = _
      omega

theorem cntK_card (n : Nat) (f : Nat → Bool) :
    cntK n f = ((Finset.range n).filter fun w => f w = true).card := by
  unfold cntK
  rw [foldN_eq]
  have := foldr_cnt f n 0
  rw [Nat.zero_add] at this
  exact this

theorem card_fin_eq (N : Nat) (p : Nat → Prop) [DecidablePred p] :
    (Finset.univ.filter fun w : Fin N => p w.val).card = ((Finset.range N).filter p).card := by
  rw [Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun k => if p k then 1 else 0)]

theorem recOK_of_recK {m : Nat} {gens : Array (Array Nat)} {G : Nat → Nat} {L D P V : Nat}
    {roots : List (Nat × Nat)} (hgs : gens.size = m)
    (hG : ∀ k < m, gens[k]! = unpack 2300 12 (G k)) (h : recK m G L D P V roots = true) :
    recOK gens (unpack 2300 12 L, unpack 2300 12 D, unpack 2300 12 P, unpack 2300 12 V) roots =
      true := by
  unfold recK at h
  obtain ⟨h1, h'⟩ := band_true h
  obtain ⟨h2, h''⟩ := band_true h'
  obtain ⟨h3, h4⟩ := band_true h''
  unfold recOK
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold orbitsOK
    rw [Bool.and_eq_true, allLt_iff, allLt_iff]
    refine ⟨fun k hk => ?_, fun x hx => ?_⟩
    · rw [hgs] at hk
      rw [allLt_iff]
      intro x hx
      have e := allN_iff.1 (allN_iff.1 h1 k hk) x hx
      rw [strictB_eq] at e
      obtain ⟨e1, e2⟩ := band_true e
      have hy : at12 (G k) x < 2300 := blt_t e1
      rw [hG k hk, unpack12_get (G k) hx, unpack12_get L hy, unpack12_get L hx,
        Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨hy, beq_t e2⟩
    · obtain ⟨e1, e2⟩ := band_true (allN_iff.1 h2 x hx)
      rw [unpack12_get L hx, unpack12_get D hx, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨blt_t e1, ?_⟩
      by_cases hd : at12 D x = 1
      · rw [if_pos (beq_iff_eq.2 hd), beq_iff_eq]
        exact beq_t ((bif_true e2).1 (beq_true hd))
      · rw [if_neg (fun h' => hd (beq_iff_eq.1 h'))]
        obtain ⟨f1, f'⟩ := band_true ((bif_true e2).2 (beq_false hd))
        obtain ⟨f2, f''⟩ := band_true f'
        obtain ⟨f3, f4⟩ := band_true f''
        have hp : at12 P x < 2300 := blt_t f1
        have hv : at12 V x < m := blt_t f3
        rw [unpack12_get P hx, unpack12_get V hx, unpack12_get D hp, hG _ hv,
          unpack12_get (G (at12 V x)) hp, hgs]
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨⟨⟨hp, beq_t f2⟩, hv⟩, beq_t f4⟩
  · unfold labelsOK
    rw [Bool.and_eq_true, allLt_iff, List.all_eq_true]
    refine ⟨fun x hx => ?_, fun r hr => ?_⟩
    · rw [unpack12_get L hx, List.any_eq_true]
      exact anyRootK_spec roots (allN_iff.1 h3 x hx)
    · obtain ⟨r1, r2, -⟩ := rootsK_spec h4 r hr
      rw [unpack12_get L r1, beq_iff_eq]
      exact r2
  · rw [List.all_eq_true]
    intro r hr
    obtain ⟨-, -, hc⟩ := rootsK_spec h4 r hr
    rw [beq_iff_eq, ← hc, cntK_card]
    unfold labCount
    rw [card_fin_eq 2300 (fun v => (unpack 2300 12 L)[v]! = r.1)]
    exact congrArg Finset.card (Finset.filter_congr fun w hw => by
      rw [unpack12_get L (Finset.mem_range.1 hw), Nat.beq_eq])

end CFSG.KC.Co2R3.Snd

end
