module

public import Certificates.Data.Kernel.LocalQT.Cov
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck

import CFSG.Certificates.Kernel.LocalQTCovPerm
import CFSG.Certificates.Kernel.LocalQTCovParse
import CFSG.Certificates.Kernel.LocalQTCovEqns
import CFSG.Certificates.Kernel.LocalQTCovGe
import CFSG.Certificates.Kernel.LocalQTBaseWProved

namespace CFSG.KC.LQT.Cov.Pf

open CFSG.KC.LQT.Cov

private theorem syl_eqL_iff : ∀ l m : List ℕ, CFSG.KC.LQT.Syl.eqL l m = true ↔ l = m
  | [], [] => by simp [CFSG.KC.LQT.Syl.eqL]
  | [], _ :: _ => by simp [CFSG.KC.LQT.Syl.eqL]
  | _ :: _, [] => by simp [CFSG.KC.LQT.Syl.eqL]
  | x :: l, y :: m => by
    change CFSG.KC.Ord.andB (Nat.beq x y) (CFSG.KC.LQT.Syl.eqL l m) = true ↔ _
    rw [CFSG.KC.LQT.BW.Pf.andB_eq, Bool.and_eq_true, Nat.beq_eq, syl_eqL_iff l m,
      List.cons.injEq]

private theorem xorK_eq (F : List ℕ) : ∀ ks : List ℕ,
    xorK F ks = ks.foldr (fun k acc => F.getD k 0 ^^^ acc) 0
  | [] => rfl
  | k :: ks => by
    change Nat.xor (CFSG.KC.LQT.Syl.getK F k 0) (xorK F ks) = _
    rw [CFSG.KC.LQT.Cov.Perm.sgetK_eq, xorK_eq F ks, List.foldr_cons]
    rfl

private theorem flags_spec : ∀ Q : List (Bool × ℕ),
    (List.rec (motive := fun _ => Bool) true (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) Q : Bool) =
      true → ∀ q ∈ Q, q.1 = true
  | [], _, q, hq => absurd hq List.not_mem_nil
  | q :: Q, h, q', hq' => by
    change CFSG.KC.Ord.andB q.1 (List.rec (motive := fun _ => Bool) true
      (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) Q) = true at h
    rw [CFSG.KC.LQT.BW.Pf.andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact h.1
    · exact flags_spec Q h.2 q' hq'

end CFSG.KC.LQT.Cov.Pf

public section

namespace CFSG.KC.LQT.Cov

open CFSG.QuasithinUnique.Ch1.M22Cover CFSG.KC.LQT.W CFSG.Sporadic.Mathieu CFSG.KC.LQT.Cov.Pf
open CFSG.QuasithinUnique.Ch1.TitsCover (reduceF gePivots)

theorem cov_sound_proved (cs : List Char) (H : List (List ℕ)) (nV0 : ℕ) (free0 : List ℕ)
    {cA cB : ℕ} (hA : codeP m22gA = cA) (hB : codeP m22gB = cB)
    (h : covK 22 cA cB cs H nV0 free0 = true) :
    covCheck (parseData (String.ofList cs)) = true ∧ (parseData (String.ofList cs)).nV = nV0 ∧
      (parseData (String.ofList cs)).free = free0 := by
  have hA' : CFSG.KC.LQT.P.code m22gA = cA := hA
  have hB' : CFSG.KC.LQT.P.code m22gB = cB := hB
  rw [covK] at h
  cases hp : parseCov cs with
  | none =>
    rw [hp] at h
    exact absurd h Bool.false_ne_true
  | some D =>
    rw [hp] at h
    simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, CFSG.KC.LQT.BW.Pf.allBs_nil, Bool.and_true,
      Bool.and_eq_true] at h
    obtain ⟨-, -, hnv, hfree, hgood, hblk, hval, hforms, -, hhint⟩ := h
    obtain ⟨hxw, hwl, hw3, hpd⟩ := Parse.parseCov_sound hp
    have hpd' : parseData (String.ofList cs) = Eqns.ofCD D := hpd
    rw [hpd']
    have hn0 : 0 < D.nV := by
      have h' := hgood
      rw [goodK] at h'
      simp only [CFSG.KC.LQT.BW.Pf.allBs_cons, Bool.and_eq_true, Nat.blt_eq] at h'
      exact h'.1
    refine ⟨?_, Nat.beq_eq.mp hnv, (syl_eqL_iff _ _).1 hfree⟩
    rw [covCheck]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨CFSG.KC.LQT.Cov.Perm.goodK_sound hA' hB' hxw rfl rfl rfl rfl rfl rfl rfl hgood,
      ?_⟩, Eqns.eqnsK_valid hw3 hn0 (flags_spec _ hval)⟩, ?_⟩
    · rw [List.all_eq_true]
      intro bl hbl
      simp only [Eqns.ofCD, List.mem_map] at hbl
      obtain ⟨b, hb, rfl⟩ := hbl
      exact CFSG.KC.LQT.Cov.Perm.blkK_sound hA' hB' hxw rfl rfl rfl rfl rfl hwl b
        ((CFSG.KC.LQT.Cov.Perm.allT_iff _ _).1 hblk b hb)
    · rw [geFinal, CFSG.Monster.B.Co2.allLt_iff]
      intro e he
      have hM : (Eqns.ofCD D).M = 3 * D.nV + 32 * D.blocks.length := by
        simp [CovData.M, Eqns.ofCD]
      have hfs : ∀ f ∈ (Eqns.ofCD D).forms, f < 2 ^ (Eqns.ofCD D).M := by
        rw [← Eqns.eqnsK_forms hw3, hM]
        intro f hf
        have := (CFSG.KC.LQT.P.allL_iff _ _).1 hforms f hf
        rw [Nat.blt_eq, CFSG.KC.LQT.Cov.Perm.slenK_eq] at this
        exact this
      have he' : e < 3 * D.nV := by simpa [Eqns.ofCD] using he
      have hh := (CFSG.KC.LQT.Cov.Perm.allLtK_iff _ _).1 hhint e he'
      rw [Nat.beq_eq, xorK_eq, Eqns.eqnsK_forms hw3] at hh
      have hh' : List.foldr (fun k acc => (Eqns.ofCD D).forms.getD k 0 ^^^ acc) 0
          (CFSG.KC.LQT.Syl.getK H e []) = 2 ^ e := hh
      rw [beq_iff_eq, ← hh']
      exact Ge.reduceF_gePivots_xor hfs (by omega) _

end CFSG.KC.LQT.Cov

end
