module

public import Certificates.Data.Kernel.W4Row.CentPairK
public import Certificates.Data.W4RowJ2Cent
public import CFSG.Certificates.Kernel.W4Row.E25KSound

public section

namespace CFSG.KC.W4C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.TCP CFSG.KC.LQT.TCK
  CFSG.KC.LQT.JX CFSG.KC.W4E CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

theorem cpK_of {n w : ℕ} {G GI : List ℕ} {Z X : ℕ} {wz wx : List ℤ} {prog : List (ℤ × ℤ)}
    {targets : List ℕ} (h : cpK n w G GI Z X wz wx prog targets = true) :
    centPairCheck n (unpackP n w G GI) (unpack n w Z) (unpack n w X) wz wx prog
      (targets.map (unpack n w)) = true := by
  unfold cpK at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨ht, h⟩ := bAnd_true h
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  obtain ⟨-, tz⟩ := gensTc_sound [Z, X] [Z, X] ht
  have hZ := rr_of_prp (prp_of_permOK (tz (Z, Z) (by simp)))
  have hX := rr_of_prp (prp_of_permOK (tz (X, X) (by simp)))
  obtain ⟨U, UI, h, hU⟩ := wordP_sound hn hnw hidn hl hz wz _ h
  obtain ⟨V, VI, h, hV⟩ := wordP_sound hn hnw hidn hl hz wx _ h
  replace hU : PrP n w (pWord n (unpackP n w G GI) wz) U UI := hU
  replace hV : PrP n w (pWord n (unpackP n w G GI) wx) V VI := hV
  obtain ⟨h1, h⟩ := bAnd_true h
  obtain ⟨h2, h⟩ := bAnd_true h
  have hR : RelP n w [pWord n (unpackP n w G GI) wz, pWord n (unpackP n w G GI) wx]
      [(U, UI), (V, VI)] := List.Forall₂.cons hU (List.Forall₂.cons hV List.Forall₂.nil)
  obtain ⟨Ps', hR', hk'⟩ := runP_sound hn hnw hidn _ prog _ _ hR h
  have hu := (rr_of_prp hU).1
  have hv := (rr_of_prp hV).1
  simp only [centPairCheck, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [RR.eqA (hu.comp hn hnw hZ.1) (hZ.1.comp hn hnw hu)]
    exact h1
  · rw [RR.eqA (hv.comp hn hnw hX.1) (hX.1.comp hn hnw hv)]
    exact h2
  · have htarg := targTc_sound targets (R1 Ps') hk'
    rw [List.all_eq_true]
    intro A' hA'
    obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA'
    have hAP := htarg A hA
    unfold R1 at hAP
    obtain ⟨pq, hpq, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hAP)
    obtain ⟨r, hr, g, hg1, hg2, -⟩ := exists_of_mem_right hR' hpq
    rw [List.any_eq_true]
    exact ⟨r, hr, (eqA_iff hg1.1 (CFSG.KS.Raw.Orb.rep_unpack hg2.1)).2 rfl⟩

theorem anyBlk_spec {b : ℕ} {f : ℕ → Bool} : ∀ {len : ℕ}, anyBlk b f len = true →
    ∃ l < len, f (Nat.add b l) = true
  | 0, h => absurd (h : false = true) Bool.false_ne_true
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) (anyBlk b f len) true (f (Nat.add b len)) = true
      at h
    cases hf : f (Nat.add b len)
    · rw [hf] at h
      obtain ⟨l, hl, hl'⟩ := anyBlk_spec h
      exact ⟨l, by omega, hl'⟩
    · exact ⟨len, by omega, hf⟩

theorem zcK_spec {b N z : ℕ} {MR : ℕ → ℕ} (h : zcK b N z MR = true) :
    isInvJ b MR z = true ∧ ∀ k < N, mtJ b MR z k = mtJ b MR k z := by
  unfold zcK at h
  obtain ⟨h1, h2⟩ := bAnd_true h
  exact ⟨h1, fun k hk => Nat.eq_of_beq_eq_true (allN_spec h2 k hk)⟩

theorem covK_spec {b N z : ℕ} {MR IT : ℕ → ℕ} {reps : List ℕ} (h : covK b N z MR IT reps = true) :
    ∀ k < N, isInvJ b MR k = true → k ≠ z → ∃ s < N, conjJ b MR IT s k ∈ reps := by
  intro k hk hinv hkz
  unfold covK at h
  have h' := allN_spec h k hk
  change Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool)
    (anyBlk 0 (fun s => memTc (conjJ b MR IT s k) reps) N) true (Nat.beq k z))
    (isInvJ b MR k) = true at h'
  have hb : Nat.beq k z = false := by
    cases hh : Nat.beq k z
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hh) hkz
  rw [hinv, hb] at h'
  obtain ⟨s, hs, hm⟩ := anyBlk_spec h'
  simp only [Nat.add_eq, Nat.zero_add] at hm
  exact ⟨s, hs, memTc_iff _ _ hm⟩

end CFSG.KC.W4C

end
