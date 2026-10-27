module

public import CFSG.RankThree.PartTwo.Census.DoubleCoverLift
public import CFSG.Sporadic.SmallOddCore.HS
public import Certificates.Certificate25552

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HSStd
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift (E8Datum)

noncomputable abbrev coverGenPerm (l : ℤ) : Equiv.Perm (Fin 3850) := hsGen l.toNat

theorem coverWords_letters : ∀ l ∈ coverXWord ++ coverNWord, l = 0 ∨ l = 1 := by
  decide

noncomputable abbrev coverXPerm : Equiv.Perm (Fin 3850) := wordG coverGenPerm coverXWord

noncomputable abbrev coverNPerm : Equiv.Perm (Fin 3850) := wordG coverGenPerm coverNWord

theorem coverPermOK_spec {T : Table} (h : coverPermOK T = true) :
    Rep 3850 T (tp 3850 T) ∧ Rep 3850 (invT 3850 T) (tp 3850 T)⁻¹ := by
  simp only [coverPermOK, Bool.and_eq_true] at h
  have hr := rep_tp h.1
  exact ⟨hr, rep_invT hr h.2⟩

section Spec


theorem rep_coverWord {w : List ℤ} (hw : ∀ l ∈ w, l = 0 ∨ l = 1) :
    Rep 3850 (wordT 3850 coverGen w) (wordG coverGenPerm w) := by
  refine Rep.wordT (by norm_num) w fun l hl => ?_
  have hlt : l.toNat < hsPGTbls.size := by
    have hsz : hsPGTbls.size = 2 := rfl
    rcases hw l hl with rfl | rfl <;> simp [hsz]
  exact hs_groupData.rep l.toNat hlt

theorem wordG_mem_hsP {w : List ℤ} (hw : ∀ l ∈ w, l = 0 ∨ l = 1) : wordG coverGenPerm w ∈ hsP := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hlt : l.toNat < hsPGTbls.size := by
    have hsz : hsPGTbls.size = 2 := rfl
    rcases hw l hl with rfl | rfl <;> simp [hsz]
  exact hs_groupData.mem hlt

theorem rep_coverX : Rep 3850 coverX coverXPerm :=
  rep_coverWord fun l hl => coverWords_letters l (List.mem_append_left _ hl)

theorem rep_coverN : Rep 3850 coverN coverNPerm :=
  rep_coverWord fun l hl => coverWords_letters l (List.mem_append_right _ hl)

theorem coverXPerm_mem : coverXPerm ∈ hsP :=
  wordG_mem_hsP fun l hl => coverWords_letters l (List.mem_append_left _ hl)

theorem coverNPerm_mem : coverNPerm ∈ hsP :=
  wordG_mem_hsP fun l hl => coverWords_letters l (List.mem_append_right _ hl)

theorem coverMemOK_spec {T : Table} (h : coverMemOK T = true) :
    Rep 3850 T (tp 3850 T) ∧ Rep 3850 (invT 3850 T) (tp 3850 T)⁻¹ ∧ tp 3850 T ∈ hsP := by
  simp only [coverMemOK, Bool.and_eq_true] at h
  obtain ⟨hr, hi⟩ := coverPermOK_spec h.1
  exact ⟨hr, hi, (hs_groupData.sift T _ hr).1 h.2⟩

theorem coverWitness {l c ρ : Table} (hl : coverMemOK l = true) (hc : coverMemOK c = true)
    (hρ : coverPermOK ρ = true) (h : coverConjEqOK l c ρ = true) :
    ∃ l' c' : hsP, (l' : Equiv.Perm (Fin 3850)) * tp 3850 ρ * (l' : Equiv.Perm (Fin 3850))⁻¹ *
      (tp 3850 ρ)⁻¹ =
        (c' : Equiv.Perm (Fin 3850)) * coverXPerm * (c' : Equiv.Perm (Fin 3850))⁻¹ := by
  obtain ⟨rl, rli, hlP⟩ := coverMemOK_spec hl
  obtain ⟨rc, rci, hcP⟩ := coverMemOK_spec hc
  obtain ⟨rρ, rρi⟩ := coverPermOK_spec hρ
  exact ⟨⟨tp 3850 l, hlP⟩, ⟨tp 3850 c, hcP⟩, (tblEq_iff_eq
    (Rep.compT (Rep.compT (Rep.compT rl rρ) rli) rρi) (rep_conjT rc rci rep_coverX)).1 h⟩

end Spec

section Datum


theorem coverE8Datum :
    E8Datum coverXPerm (coverNPerm * coverXPerm * coverNPerm⁻¹)
      (coverNPerm * (coverNPerm * coverXPerm * coverNPerm⁻¹) * coverNPerm⁻¹) coverNPerm := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, -⟩ := Certificates.certificate25552
  have hX := rep_coverX
  have hN := rep_coverN
  have hNi : Rep 3850 coverNInv coverNPerm⁻¹ := Rep.inv_of_invOK hN h1
  have hX2 : Rep 3850 coverX2 (coverNPerm * coverXPerm * coverNPerm⁻¹) :=
    rep_conjT hN hNi hX
  have hX3 : Rep 3850 coverX3
      (coverNPerm * (coverNPerm * coverXPerm * coverNPerm⁻¹) * coverNPerm⁻¹) :=
    rep_conjT hN hNi hX2
  have hXX : Rep 3850 (compT 3850 coverX coverX) (coverXPerm * coverXPerm) := Rep.compT hX hX
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro h
    have h' := (tblEq_idT_iff (by norm_num) hX).2 h
    simp [coverXNeOK, h'] at h2
  · rw [pow_two]
    exact (tblEq_iff_eq hXX (Rep.idT (by norm_num))).1 h3
  · exact (commTT_iff hX hX2).1 h4
  · exact (commTT_iff hX hX3).1 h5
  · exact (tblEq_iff_eq (rep_conjT hN hNi hX3) (Rep.compT hX hX2)).1 h6

theorem cover_datum :
    ∃ a₁ a₂ a₃ n : hsP, E8Datum a₁ a₂ a₃ n ∧
      (∃ l c : hsP, (l : Equiv.Perm (Fin 3850)) * tp 3850 rho2 * (l : Equiv.Perm (Fin 3850))⁻¹ *
        (tp 3850 rho2)⁻¹ = (c : Equiv.Perm (Fin 3850)) * (a₁ : Equiv.Perm (Fin 3850)) *
          (c : Equiv.Perm (Fin 3850))⁻¹) ∧
      (∃ l c : hsP, (l : Equiv.Perm (Fin 3850)) * tp 3850 rho3 * (l : Equiv.Perm (Fin 3850))⁻¹ *
        (tp 3850 rho3)⁻¹ = (c : Equiv.Perm (Fin 3850)) * (a₁ : Equiv.Perm (Fin 3850)) *
          (c : Equiv.Perm (Fin 3850))⁻¹) := by
  obtain ⟨-, ⟨hl2, hc2, hρ2, he2⟩, ⟨hl3, hc3, hρ3, he3⟩⟩ := Certificates.certificate25552
  refine ⟨⟨coverXPerm, coverXPerm_mem⟩,
    ⟨coverNPerm, coverNPerm_mem⟩ * ⟨coverXPerm, coverXPerm_mem⟩ * ⟨coverNPerm, coverNPerm_mem⟩⁻¹,
    ⟨coverNPerm, coverNPerm_mem⟩ * (⟨coverNPerm, coverNPerm_mem⟩ * ⟨coverXPerm, coverXPerm_mem⟩ *
      ⟨coverNPerm, coverNPerm_mem⟩⁻¹) * ⟨coverNPerm, coverNPerm_mem⟩⁻¹,
    ⟨coverNPerm, coverNPerm_mem⟩, ?_, coverWitness hl2 hc2 hρ2 he2, coverWitness hl3 hc3 hρ3 he3⟩
  exact E8Datum.of_map hsP.subtype Subtype.val_injective coverE8Datum

end Datum

end CFSG.EvenSporadicStandard.TwoHS
