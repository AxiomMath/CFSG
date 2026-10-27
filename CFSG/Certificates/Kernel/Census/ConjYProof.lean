module

public import CFSG.Certificates.Kernel.Census.ConjProof

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native

theorem mem_of_inXL {n : Nat} {Xs : Array Nat} {w : Nat} {a : Array Nat}
    (h : inXL n (Xs.map (unpackP n w)) a = true) :
    ∃ P ∈ Xs.toList, eqA n a (unpackP n w P) = true := by
  unfold inXL at h
  rw [Array.toList_map, List.any_map, List.any_eq_true] at h
  obtain ⟨P, hP, h⟩ := h
  exact ⟨P, hP, h⟩

theorem conjCensusY_of_packed {n w : Nat} {ps : List Nat} {testP : Array Nat → Bool}
    {u : Array Nat} {uP : Nat} {inP : Nat → Bool} {d : ConjDataP} {Xs : Array Nat}
    (h24 : n ≤ 2 ^ 24) (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcongr : ∀ a b g, Rep n a g → Rep n b g → testP a = testP b)
    (hinP : ∀ P, canon1 n w P = true → pvalid n w P = true → inP P = testP (unpackP n w P))
    (hu : u = unpackP n w uP) (huc : canon1 n w uP = true) (huv : pvalid n w uP = true)
    (hc : canonC n w d = true)
    (hX : Xs.toList.all (fun P => canon1 n w P && pvalid n w P && inP P) = true)
    (hW : d.xs.all (fun P => canon1 n w P && pvalid n w P && (inP P || inP (pc n w uP P))) = true)
    (hpc : ppcOK n w d.xs d.rs d.cjs d.bs = true) (hinv : pinvOK n w d.xs d.us d.im d.wt = true)
    (htab : ptabOK n w d.xs d.cm d.cs d.ci = true)
    (hrl : Nat.beq d.roots.length d.us.size = true)
    (hR : (d.us.toList.zip d.roots).all
      (fun ur => prootOKC n w (d.nodes.map NodeP.basis) (pcN n w d.nodes) d.cs d.ci ur.1 ur.2) =
        true)
    (hN : ∀ i < d.nodes.size, pnodeOKC n w ps (pinXL Xs) (fun _ => true) (pinXL d.xs.toArray)
      false false false d (pcN n w d.nodes) #[] i = true) :
    ∃ (inX inW : Array Nat → Bool) (D : ConjData),
      (∀ a, validA n a = true → inX a = true → testP a = true) ∧
      (∀ a, validA n a = true → inW a = true → (testP a || testP (compA n u a)) = true) ∧
      conjCensusOKW n ps inX (fun _ => true) inW false false false D #[] = true ∧
      D.xs.all inW = true ∧ D.xs.length = d.xs.length := by
  have hX' : ∀ P ∈ Xs.toList, canon1 n w P = true ∧ pvalid n w P = true ∧ inP P = true := by
    intro P hP
    have := List.all_eq_true.1 hX P hP
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hW' : ∀ P ∈ d.xs, canon1 n w P = true ∧ pvalid n w P = true ∧
      (inP P || inP (pc n w uP P)) = true := by
    intro P hP
    have := List.all_eq_true.1 hW P hP
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hurep : Rep n u (permOfArr n u) := by
    rw [hu]
    exact rep_of_validA ((SP.validA_unpack hw huc).trans huv)
  have hpt : ∀ a P, validA n a = true → eqA n a (unpackP n w P) = true →
      testP a = testP (unpackP n w P) := fun a P hv he =>
    hcongr _ _ _ (rep_of_validA hv) (rep_of_eqA (rep_of_validA hv) he)
  have hptu : ∀ a P, validA n a = true → eqA n a (unpackP n w P) = true →
      testP (compA n u a) = testP (compA n u (unpackP n w P)) := fun a P hv he =>
    hcongr _ _ _ (rep_compA hurep (rep_of_validA hv))
      (rep_compA hurep (rep_of_eqA (rep_of_validA hv) he))
  refine ⟨inXL n (Xs.map (unpackP n w)), inXL n (d.xs.toArray.map (unpackP n w)), d.toMain n w,
    fun a hv h => ?_, fun a hv h => ?_, ?_, ?_, by simp [ConjDataP.toMain]⟩
  · obtain ⟨P, hP, he⟩ := mem_of_inXL h
    obtain ⟨hPc, hPv, hPi⟩ := hX' P hP
    rw [hpt a P hv he, ← hinP P hPc hPv, hPi]
  · obtain ⟨P, hP, he⟩ := mem_of_inXL h
    obtain ⟨hPc, hPv, hPi⟩ := hW' P (by simpa using hP)
    rw [hpt a P hv he, hptu a P hv he]
    simp only [Bool.or_eq_true] at hPi ⊢
    rcases hPi with h1 | h1
    · left
      rw [← hinP P hPc hPv, h1]
    · right
      rw [hu, ← unpackP_pc hn hw huc, ← hinP _ (SP.canon_pc hn hw)
        (pvalid_pc hn hw huc huv hPc hPv), h1]
  · have hXc : Xs.toList.all (canon1 n w) = true :=
      List.all_eq_true.2 fun P hP => (hX' P hP).1
    have hxc : d.xs.toArray.toList.all (canon1 n w) = true :=
      List.all_eq_true.2 fun P hP => (hW' P (by simpa using hP)).1
    have h := pconjCensus_sound_proved (inX := inXL n (Xs.map (unpackP n w)))
      (outX := fun _ => true) (inW := inXL n (d.xs.toArray.map (unpackP n w))) h24 hn hw hc
      (e0 := #[]) rfl (fun P hP _ => pinXL_eq hP hXc) (fun _ _ _ => rfl)
      (fun P hP _ => pinXL_eq hP hxc) hpc hinv htab hrl hR hN
    rwa [Array.map_empty] at h
  · rw [List.all_eq_true]
    intro x hx
    simp only [ConjDataP.toMain, List.mem_map] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    unfold inXL
    rw [List.any_eq_true]
    exact ⟨unpackP n w P, by simpa using ⟨P, hP, rfl⟩, by
      unfold eqA
      rw [allLt_iff]
      intro i _
      simp⟩

end CFSG.KC.Census
