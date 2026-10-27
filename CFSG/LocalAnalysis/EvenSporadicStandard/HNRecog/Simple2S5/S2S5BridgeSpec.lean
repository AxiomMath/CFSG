module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec
public import Certificates.Certificate442201

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HNRecog

theorem elemW_apply_of_ap (hgens : gensOK = true) {w : List ℕ} (hw : wordOK w = true)
    {p q : Fin 1408} (h : ap (tabW w) (p : ℕ) = (q : ℕ)) : elemW w p = q := by
  have hr := rep_elemW_of_gensOK hgens hw (p : ℕ) p.2
  rw [idx_of_lt _ p.2] at hr
  exact Fin.ext (by rw [← h, hr]; rfl)

@[expose] def bridgePt (l : Fin 50) : Fin 1408 := Fin.ofNat 1408 bridgePts[(l : ℕ)]!

@[expose] noncomputable def bridgeGen (k : Fin 6) : ↥P1408 :=
  ⟨elemW bridgeWords[(k : ℕ)]!, elemW_mem _⟩

section Cert


private theorem bridgeOK_parts :
    ((((((gensOK = true ∧ (∀ w, w ∈ bridgeWords → wordOK w = true)) ∧ bridgeWords.length = 6) ∧
        bridgePts.length = 50) ∧ bridgePts.Nodup) ∧ (∀ p, p ∈ bridgePts → p < 1408)) ∧
      (∀ k, k < 6 → bridgeWordOK bridgeWords[k]! HNUnitaryBridge.smallPerms[k]! = true)) := by
  have h : bridgeOK = true := Certificates.certificate442201
  simp only [bridgeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact h

private lemma bridgeGen_smul_eq (k : Fin 6) (p : Fin 1408) :
    bridgeGen k • p = elemW bridgeWords[(k : ℕ)]! p := by
  simp only [bridgeGen, Subgroup.smul_def, Equiv.Perm.smul_def]

theorem bridgePt_val (l : Fin 50) : ((bridgePt l : Fin 1408) : ℕ) = bridgePts[(l : ℕ)]! := by
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hlen50⟩, -⟩, hlt⟩, -⟩ := bridgeOK_parts
  have hl : (l : ℕ) < bridgePts.length := by rw [hlen50]; exact l.2
  have hmem : bridgePts[(l : ℕ)]! ∈ bridgePts := by
    rw [getElem!_pos bridgePts (l : ℕ) hl]; exact List.getElem_mem hl
  have h := hlt _ hmem
  unfold bridgePt
  rw [Fin.ofNat_eq_cast, Fin.coe_natCast_eq_mod, Nat.mod_eq_of_lt h]

theorem bridgePt_injective : Function.Injective bridgePt := by
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hlen50⟩, hnd⟩, -⟩, -⟩ := bridgeOK_parts
  intro l₁ l₂ heq
  have h1 : (l₁ : ℕ) < bridgePts.length := by rw [hlen50]; exact l₁.2
  have h2 : (l₂ : ℕ) < bridgePts.length := by rw [hlen50]; exact l₂.2
  have heq' : ((bridgePt l₁ : Fin 1408) : ℕ) = ((bridgePt l₂ : Fin 1408) : ℕ) :=
    congrArg (fun x : Fin 1408 => (x : ℕ)) heq
  rw [bridgePt_val l₁, bridgePt_val l₂] at heq'
  rw [getElem!_pos bridgePts (l₁ : ℕ) h1, getElem!_pos bridgePts (l₂ : ℕ) h2] at heq'
  exact Fin.ext (hnd.getElem_inj_iff.mp heq')

theorem bridgeGen_smul_zero (k : Fin 6) : bridgeGen k • (0 : Fin 1408) = 0 := by
  obtain ⟨⟨⟨⟨⟨⟨hgens, hwords⟩, hlen6⟩, -⟩, -⟩, -⟩, hk⟩ := bridgeOK_parts
  have hk' := hk (k : ℕ) k.2
  simp only [bridgeWordOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hk'
  obtain ⟨h0, -⟩ := hk'
  have hklen : (k : ℕ) < bridgeWords.length := by rw [hlen6]; exact k.2
  have hw : wordOK bridgeWords[(k : ℕ)]! = true := by
    apply hwords
    rw [getElem!_pos bridgeWords (k : ℕ) hklen]
    exact List.getElem_mem hklen
  rw [bridgeGen_smul_eq]
  exact elemW_apply_of_ap hgens hw (p := 0) (q := 0) (by simpa using h0)

theorem bridgeGen_smul_pt (k : Fin 6) (l m : Fin 50)
    (h : (m : ℕ) = (HNUnitaryBridge.smallPerms[(k : ℕ)]!)[(l : ℕ)]!) :
    bridgeGen k • bridgePt l = bridgePt m := by
  obtain ⟨⟨⟨⟨⟨⟨hgens, hwords⟩, hlen6⟩, -⟩, -⟩, -⟩, hk⟩ := bridgeOK_parts
  have hk' := hk (k : ℕ) k.2
  simp only [bridgeWordOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hk'
  obtain ⟨-, hall⟩ := hk'
  have hklen : (k : ℕ) < bridgeWords.length := by rw [hlen6]; exact k.2
  have hw : wordOK bridgeWords[(k : ℕ)]! = true := by
    apply hwords
    rw [getElem!_pos bridgeWords (k : ℕ) hklen]
    exact List.getElem_mem hklen
  have hap : ap (tabW bridgeWords[(k : ℕ)]!) (bridgePt l : ℕ) = (bridgePt m : ℕ) := by
    rw [bridgePt_val l, bridgePt_val m, h]
    exact hall (l : ℕ) l.2
  rw [bridgeGen_smul_eq]
  exact elemW_apply_of_ap hgens hw hap

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
