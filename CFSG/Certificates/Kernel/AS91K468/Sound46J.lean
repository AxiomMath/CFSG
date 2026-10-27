module

public import Certificates.Data.Kernel.AS91K468.K46J
public import CFSG.Certificates.Kernel.AS91K468.Sound46

public section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
  CFSG.GF2Type.Smith1979.GammaU.Enum

theorem foldl_stepN_mem : ∀ (L l : List ℕ) (t : NT ℕ), ∃ new : List ℕ,
    (L.foldl stepN (l, t)).1 = new ++ l ∧
      ∀ q, memP (L.foldl stepN (l, t)).2 q = (new.contains q || memP t q)
  | [], l, t => ⟨[], rfl, fun q => by simp⟩
  | x :: L, l, t => by
    rw [List.foldl_cons]
    by_cases hm : memP t x = true
    · have e : stepN (l, t) x = (l, t) := by simp only [stepN, hm, if_true]
      rw [e]
      exact foldl_stepN_mem L l t
    · have hm' : memP t x = false := by simpa using hm
      have e : stepN (l, t) x = (x :: l, insP t x) := by
        simp only [stepN, hm', Bool.false_eq_true, if_false]
      rw [e]
      obtain ⟨new, h1, h2⟩ := foldl_stepN_mem L (x :: l) (insP t x)
      refine ⟨new ++ [x], by rw [h1, List.append_assoc, List.singleton_append], fun q => ?_⟩
      rw [h2, memP_insP, List.contains_append, List.contains_cons, List.contains_nil,
        Bool.or_false, HJ12K.beq_symm x q, Bool.or_assoc]

section

variable {σ κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
  (enc : ℕ → σ) (key : σ → κ) (D : ℕ → Prop)

theorem bfsClosure_L (hk : ∀ a b, D a → D b → (key (enc a) == key (enc b)) = (a == b))
    (fs : List (σ → σ)) (fsQ : List (ℕ → ℕ))
    (hf : ∀ q, D q → fs.map (fun f => f (enc q)) = (fsQ.map fun f => f q).map enc)
    (hd : ∀ q, D q → ∀ f ∈ fsQ, D (f q)) :
    ∀ (fuel : ℕ) (fr vis : List ℕ) (h : Std.HashSet κ) (S : List ℕ), (∀ q ∈ fr, D q) →
      (∀ q ∈ vis, D q) → SRel enc key D h (ofListP S) →
      bfsClosure key fs fuel (fr.map enc) h (vis.map enc) = (closL fsQ fuel fr S vis).map enc ∧
        ∀ q ∈ closL fsQ fuel fr S vis, D q
  | 0, fr, vis, h, S, hfr, hvis, _ => by
    refine ⟨by rw [bfsClosure, closL, List.map_append], fun q hq => ?_⟩
    rw [closL] at hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hfr q hq
    · exact hvis q hq
  | fuel + 1, fr, vis, h, S, hfr, hvis, hr => by
    have e1 : bfsRound key fs (fr.map enc) h =
        ((fr.flatMap fun s => fsQ.map fun f => f s).map enc).foldl (stepH key)
          (([] : List ℕ).map enc, h) := by
      rw [bfsRound, flat_encN enc D fs fsQ hf fr hfr]
      rfl
    have e2 : roundN fsQ fr (ofListP S) =
        (fr.flatMap fun s => fsQ.map fun f => f s).foldl stepN ([], ofListP S) := rfl
    obtain ⟨r1, r2, r3⟩ := foldl_stepN enc key D hk _ (flat_D D fsQ hd fr hfr) [] h (ofListP S)
      (by simp) hr
    obtain ⟨new, n1, n2⟩ := foldl_stepN_mem (fr.flatMap fun s => fsQ.map fun f => f s) []
      (ofListP S)
    rw [List.append_nil] at n1
    have hr' : SRel enc key D (((fr.flatMap fun s => fsQ.map fun f => f s).map enc).foldl
        (stepH key) (([] : List ℕ).map enc, h)).2
        (ofListP (((fr.flatMap fun s => fsQ.map fun f => f s).foldl stepN ([], ofListP S)).1 ++
          S)) := by
      intro q hq
      rw [r2 q hq, n2, n1, memP_ofListP, memP_ofListP, List.contains_append]
    have hfv : ∀ q ∈ fr ++ vis, D q := fun q hq => by
      rcases List.mem_append.1 hq with hq | hq
      · exact hfr q hq
      · exact hvis q hq
    simp only [bfsClosure, closL]
    rw [e1, e2, r1, List.isEmpty_map]
    split_ifs with he
    · exact ⟨by rw [List.map_append], hfv⟩
    · rw [← List.map_append]
      exact bfsClosure_L hk fs fsQ hf hd fuel _ _ _ _ r3 hfv hr'

end

theorem closL_step (fs : List (ℕ → ℕ)) (n : ℕ) (fr S vis fr' : List ℕ)
    (h1 : (roundN fs fr (ofListP S)).1 = fr') (h2 : fr'.isEmpty = false) :
    closL fs (n + 1) fr S vis = closL fs n fr' (fr' ++ S) (fr ++ vis) := by
  simp only [closL]
  rw [h1, h2, if_neg Bool.false_ne_true]

theorem closL_end (fs : List (ℕ → ℕ)) (n : ℕ) (fr S vis : List ℕ)
    (h : (roundN fs fr (ofListP S)).1.isEmpty = true) : closL fs (n + 1) fr S vis = fr ++ vis := by
  simp only [closL]
  rw [if_pos h]

theorem roundOK_iff {PF : List (ℕ × ℕ)} {fr S fr' : List ℕ} (h : roundOK PF fr S fr' = true) :
    (roundN (fsOf PF) fr (ofListP S)).1 = fr' ∧ fr'.isEmpty = false := by
  rw [roundOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, by simpa using h.2⟩

theorem closL_five (PF : List (ℕ × ℕ)) (f0 f1 f2 f3 f4 : List ℕ)
    (r0 : roundOK PF f0 f0 f1 = true) (r1 : roundOK PF f1 (f1 ++ f0) f2 = true)
    (r2 : roundOK PF f2 (f2 ++ (f1 ++ f0)) f3 = true)
    (r3 : roundOK PF f3 (f3 ++ (f2 ++ (f1 ++ f0))) f4 = true)
    (r4 : roundEnd PF f4 (f4 ++ (f3 ++ (f2 ++ (f1 ++ f0)))) = true) :
    closL (fsOf PF) 100 f0 f0 [] = f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ [])))) := by
  have e : (100 : ℕ) = 95 + 1 + 1 + 1 + 1 + 1 := rfl
  obtain ⟨a0, b0⟩ := roundOK_iff r0
  obtain ⟨a1, b1⟩ := roundOK_iff r1
  obtain ⟨a2, b2⟩ := roundOK_iff r2
  obtain ⟨a3, b3⟩ := roundOK_iff r3
  rw [roundEnd] at r4
  rw [e, closL_step _ _ _ _ _ _ a0 b0, closL_step _ _ _ _ _ _ a1 b1, closL_step _ _ _ _ _ _ a2 b2,
    closL_step _ _ _ _ _ _ a3 b3, closL_end _ _ _ _ _ r4]

theorem fixClosure_eqL (P : List ℕ) (EP : enumGrp (pQ.map unpackA) = P.map unpackA)
    (BP : ∀ q ∈ P, q < 2 ^ 144) (hn : nodupP P = true) :
    CFSG.Quasithin.H13.AS91.Two.fixClosure () = closL (fsOf (pfOf P)) 100 [fullM] [fullM] [] := by
  have hfs : ((pfOf P).map fun p => (unpackA p.1, p.2)).map
      (fun (rf : Array ℕ × ℕ) (F : ℕ) => F &&& rf.2) = fsOf (pfOf P) := by
    rw [List.map_map]
    rfl
  have hk : ∀ a b : ℕ, True → True →
      (CFSG.Quasithin.H13.AS91.Two.mkey ((fun q => q) a) ==
        CFSG.Quasithin.H13.AS91.Two.mkey ((fun q => q) b)) = (a == b) :=
    fun a b _ _ => mkey_beq a b
  have hs : SRel (fun q => q) CFSG.Quasithin.H13.AS91.Two.mkey (fun _ => True)
      ((∅ : Std.HashSet (ℕ × ℕ)).insert (CFSG.Quasithin.H13.AS91.Two.mkey fullM))
      (ofListP [fullM]) := by
    intro q _
    rw [Std.HashSet.contains_insert, memP_ofListP, Std.HashSet.contains_empty, List.contains_cons,
      List.contains_nil, hk fullM q trivial trivial, HJ12K.beq_symm]
  have := bfsClosure_L (fun q => q) CFSG.Quasithin.H13.AS91.Two.mkey (fun _ => True) hk
    (fsOf (pfOf P)) (fsOf (pfOf P)) (fun q _ => by rw [List.map_id'])
    (fun _ _ _ _ => trivial) 100 [fullM] [] _ [fullM] (fun _ _ => trivial) (fun _ _ => trivial) hs
  rw [CFSG.Quasithin.H13.AS91.Two.fixClosure, fixPairs_eq P EP BP hn, hfs, fullMask_eq]
  simp only [List.map_id', List.map_nil] at this
  exact this.1

theorem j_soundL (P : List ℕ) (EP : enumGrp (pQ.map unpackA) = P.map unpackA)
    (BP : ∀ q ∈ P, q < 2 ^ 144) (hn : nodupP P = true) (PF : List (ℕ × ℕ)) (hPF : pfOf P = PF)
    (f0 f1 f2 f3 f4 : List ℕ) (hf0 : f0 = [fullM])
    (r0 : roundOK PF f0 f0 f1 = true) (r1 : roundOK PF f1 (f1 ++ f0) f2 = true)
    (r2 : roundOK PF f2 (f2 ++ (f1 ++ f0)) f3 = true)
    (r3 : roundOK PF f3 (f3 ++ (f2 ++ (f1 ++ f0))) f4 = true)
    (r4 : roundEnd PF f4 (f4 ++ (f3 ++ (f2 ++ (f1 ++ f0)))) = true)
    (a0 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f0 = true)
    (a1 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f1 = true)
    (a2 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f2 = true)
    (a3 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f3 = true)
    (a4 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f4 = true)
    (b0 : jAll2 PF f0 = true) (b1 : jAll2 PF f1 = true) (b2 : jAll2 PF f2 = true)
    (b3 : jAll2 PF f3 = true) (b4 : jAll2 PF f4 = true) :
    CFSG.Quasithin.H13.AS91.Two.jOK46 () = true := by
  have hcl : CFSG.Quasithin.H13.AS91.Two.fixClosure () =
      f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ [])))) := by
    rw [fixClosure_eqL P EP BP hn, hPF, ← hf0]
    exact closL_five PF f0 f1 f2 f3 f4 r0 r1 r2 r3 r4
  have BPF := pfOf_lt P BP
  rw [hPF] at BPF
  simp only [CFSG.Quasithin.H13.AS91.Two.jOK46]
  rw [fixPairs_eq P EP BP hn, hcl, w1Mask_eq, hPF]
  refine (jAt_eq PF BPF _).trans ?_
  rw [jAll1] at a0 a1 a2 a3 a4
  rw [jAll2] at b0 b1 b2 b3 b4
  rw [jAt, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_append, List.all_append, List.all_append, List.all_append, List.all_append,
      List.all_nil, a0, a1, a2, a3, a4]
    rfl
  · rw [List.all_append, List.all_append, List.all_append, List.all_append, List.all_append,
      List.all_nil, b0, b1, b2, b3, b4]
    rfl

theorem ok46_ofL (hw : wordsOK46 = true) (h1 : w1OK46Q = true) (h2 : eb46Q = true)
    (h3 : trans46Q = true) (hn : pNodup46Q = true) (PF : List (ℕ × ℕ))
    (hPF : (pfOf (enumQ pQ) == PF) = true) (f0 f1 f2 f3 f4 : List ℕ) (hf0 : (f0 == [fullM]) = true)
    (r0 : roundOK PF f0 f0 f1 = true) (r1 : roundOK PF f1 (f1 ++ f0) f2 = true)
    (r2 : roundOK PF f2 (f2 ++ (f1 ++ f0)) f3 = true)
    (r3 : roundOK PF f3 (f3 ++ (f2 ++ (f1 ++ f0))) f4 = true)
    (r4 : roundEnd PF f4 (f4 ++ (f3 ++ (f2 ++ (f1 ++ f0)))) = true)
    (a0 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f0 = true)
    (a1 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f1 = true)
    (a2 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f2 = true)
    (a3 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f3 = true)
    (a4 : jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) f4 = true)
    (b0 : jAll2 PF f0 = true) (b1 : jAll2 PF f1 = true) (b2 : jAll2 PF f2 = true)
    (b3 : jAll2 PF f3 = true) (b4 : jAll2 PF f4 = true) :
    CFSG.Quasithin.H13.AS91.Two.ok46 () = true := by
  have e2 := eb_sound _ _ _ (enumS st1Q) (enumS pQ) (enumS ebQ) (enumS_lt _) (enumS_lt _)
    (enumS_lt _) (stab1Gens_eq hw) (g13Gens_eq hw) h2
  have e3 := trans_sound _ (enumS ebQ) (enumS_lt _) (g13Gens_eq hw) h3
  have e4 := j_soundL _ (enumS pQ) (enumS_lt _) hn PF (beq_iff_eq.1 hPF) f0 f1 f2 f3 f4
    (beq_iff_eq.1 hf0) r0 r1 r2 r3 r4 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  rw [CFSG.Quasithin.H13.AS91.Two.ok46, w1OK46_eq, h1, e2, e3, e4]
  rfl

end Certificates.Kernel.AS91K468
