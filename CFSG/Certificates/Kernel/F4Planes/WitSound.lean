module

public import Certificates.Data.Kernel.F4PlanesWit
public import CFSG.Certificates.Kernel.F4Planes.RowSound
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Wit3

public section

namespace CFSG.KC.F4Planes

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.F4Syl3 CFSG.LieType.Ree
  CFSG.RankThree.PartTwo.Sec4.RonanK432 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley

variable {K : Type} [Field K]
  [CharP K 2]

theorem witG_sound {s : Fin 4 → adjointGroup ReeTag.F4.tag K}
    {g4 g5 : adjointGroup ReeTag.F4.tag K} {S : List ℕ} {G4 G5 : ℕ} {ww : List W4}
    {wk reps : List ℕ} (hs : ∀ i : Fin 4, HasBitsS K (s i) (S.getD i 0))
    (h4 : HasBitsS K g4 G4) (h5 : HasBitsS K g5 G5) (h : witG S G4 G5 ww wk reps = true)
    {k : ℕ} (hk : k < 48) (h3 : phi s g4 g5 (reps.getD k 0) ^ 3 = 1) :
    Wit3 (⊤ : Subgroup (adjointGroup ReeTag.F4.tag K)) (phi s g4 g5 (reps.getD k 0)) := by
  simp only [witG, Bool.and_eq_true] at h
  have hk' := allN_spec h.2 k hk
  simp only [Bool.and_eq_true, strictB_eq, lenL_eq] at hk'
  obtain ⟨hlt, hw⟩ := hk'
  have hlt' : wk.getD k 0 < ww.length := by simpa using hlt
  set e := ww.getD (wk.getD k 0) (0, 0, 0, 0) with he_def
  have he : e ∈ ww := by
    rw [he_def, List.getD_eq_getElem _ _ hlt']
    exact List.getElem_mem _
  have hpin := allL_spec h.1 e he
  simp only [witPin, Bool.and_eq_true] at hpin
  have hY : HasBitsS K (wordE K e.1 e.2.1) e.2.2.1 := hasBitsS_of_eqS (hasBitsS_wordS _ _) hpin.1
  have hYi := hasBitsS_inv_of hY hpin.2
  set a := phi s g4 g5 (reps.getD k 0)
  have hU : HasBitsS K a (phiS S G4 G5 (reps.getD k 0)) := hasBitsS_phiS' hs h4 h5 _
  have hC := (hY.mul hU).mul hYi
  simp only [witOne, strictB_eq, Bool.and_eq_true, Bool.not_eq_true'] at hw
  obtain ⟨⟨⟨hc, hn1⟩, hn2⟩, hn3⟩ := hw
  refine wit3_of_conj_ne (Subgroup.mem_top (wordE K e.1 e.2.1)) h3 ?_ ?_ ?_ ?_
  · exact ((hC.mul hU).eq_iff (hU.mul hC)).2 hc
  · intro heq
    rw [(hC.eq_iff hasBitsS_one).1 heq] at hn1
    exact Bool.noConfusion hn1
  · intro heq
    rw [(hC.eq_iff hU).1 heq] at hn2
    exact Bool.noConfusion hn2
  · intro heq
    have hinv : a⁻¹ = a * a := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_three']
      exact h3
    rw [hinv] at heq
    rw [(hC.eq_iff (hU.mul hU)).1 heq] at hn3
    exact Bool.noConfusion hn3

theorem witP_sound {s : Fin 4 → adjointGroup ReeTag.F4.tag K}
    {g4 g5 : adjointGroup ReeTag.F4.tag K} {pS : List ℕ} {ww : List W4} {wk reps : List ℕ}
    (hs : ∀ i : Fin 4, HasBitsS K (s i) (pS.getD i 0))
    (h4 : HasBitsS K g4 (pS.getD 4 0)) (h5 : HasBitsS K g5 (pS.getD 5 0))
    (h : witP pS ww wk reps = true) {k : ℕ} (hk : k < 48)
    (h3 : phi s g4 g5 (reps.getD k 0) ^ 3 = 1) :
    Wit3 (⊤ : Subgroup (adjointGroup ReeTag.F4.tag K)) (phi s g4 g5 (reps.getD k 0)) := by
  simp only [witP, strictB_eq] at h
  refine witG_sound (S := [pS.getD 0 0, pS.getD 1 0, pS.getD 2 0, pS.getD 3 0]) (fun i => ?_)
    h4 h5 h hk h3
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3
  · omega

end CFSG.KC.F4Planes

end
