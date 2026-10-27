module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXCert
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXPerm
public import Certificates.Certificate25296

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section


theorem fullGen_mem_T0 {k : ℕ} (hk : k < 9) : fi22ExtFullGen k ∈ fi22ExtT0 := by
  rw [fi22ExtT0_eq_closure, fi22ExtFullGen_eq hk]
  exact Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem sigma_mem_T0 {l : ℕ × Bool} (hl : l.1 < 9) :
    axSigma fi22ExtFullGen l ∈ fi22ExtT0 := by
  unfold axSigma
  split_ifs
  · exact fi22ExtT0.inv_mem (fullGen_mem_T0 hl)
  · exact fullGen_mem_T0 hl

theorem signedProd_mem_T0 (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < 9) :
    (w.map (axSigma fi22ExtFullGen)).prod ∈ fi22ExtT0 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact sigma_mem_T0 (hw l hl)

theorem prod_mem_T0 (w : List ℕ) (hw : ∀ k ∈ w, k < 9) :
    (w.map fi22ExtFullGen).prod ∈ fi22ExtT0 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact fullGen_mem_T0 (hw k hk)

theorem prod_mem_S (w : List ℕ) (hw : ∀ k ∈ w, k < 10) :
    (w.map fi22ExtFullGen).prod ∈ fi22ExtS :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact fi22ExtFullGen_mem (hw k hk)

end

theorem permFacts_data :
    PermFacts fi22ExtFullGen axBasWords axGc := by
  have h := Certificates.certificate25296
  simp only [axPermCertificate] at h
  refine axPermCheckT_sound (fun k hk => ?_) h
  have hk' : k < ((Array.range 10).map fun k => fi22ExtArr (11 + k)).size := by simpa using hk
  rw [getElem!_pos _ k hk', Array.getElem_map, Array.getElem_range]
  exact rep_fi22ExtFullGen hk

theorem extSRank_proved :
    ExtSRank := by
  intro A hAS hsq hAP
  have hP := permFacts_data
  have hW := axWords_data
  have hM := axMs_parts
  have hgc : axGc.size = 10 := rfl
  have hD : AbsX (Equiv.Perm (Fin 3510)) fi22ExtS fi22ExtT0 (axB fi22ExtFullGen axBasWords)
      (fun j => ((axWs[j]!).map fi22ExtFullGen).prod) axMs (fun k => axQs[k]!) := by
    refine ⟨?_, fi22ExtT0_le_S, fun i hi => ?_, hP.b_sq, hP.b_comm, hP.phi_inj, hM.1,
      fun k hk => ?_, fun k hk hq => ?_, hM.2.1, hM.2.2, fun k hk i hi => ?_, axSpec_data⟩
    · rw [card_fi22ExtS]
      norm_num
    · exact signedProd_mem_T0 _ (hP.letters i hi)
    · refine prod_mem_S _ fun l hl => ?_
      have := (hW.2.2 k hk).1 l hl
      omega
    · exact prod_mem_T0 _ ((hW.2.2 k hk).2.2 hq)
    · have hmem := (hW.2.2 k hk).1
      have := axWordCols_act hP.b_comm hP.b_sq fi22ExtFullGen axGc
        (fun k' hk' i' hi' => hP.act k' (by omega) i' hi') (axWs[k]!) hmem i hi
      rw [(hW.2.2 k hk).2.1 i hi] at this
      exact this
  exact hD.card_le hAS hsq (fun h => hAP (h.trans fi22ExtT0_le_P))

end CFSG.EvenSporadicStandard.TwoFi22.DS81
