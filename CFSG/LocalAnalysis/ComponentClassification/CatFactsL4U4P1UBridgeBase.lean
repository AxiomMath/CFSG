
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UTabs
public import CFSG.Sporadic.SmallOddCore.CentSpec

@[expose] public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43

open CFSG.LieType.Multipliers.U43 Matrix Subgroup CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

noncomputable def uChainQ : RawSchreierDatum 820 :=
  RawSchreierDatum.ofArrays 820 (by norm_num) chainS 2 (by decide) chainBase (by decide) chainW

theorem uChainArrays : ChainArrays uChainQ (chainS.extract 0 2) chainS uBase chainW :=
  chainArrays_ofArrays (chainCheckFacts chain_check).strong_inv

theorem uChainQ_eq : uChainQ.originalSubgroup = Subgroup.closure {psi xElt, psi yElt} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [uChainQ, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  have h0 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 0 (by decide))).1
  have h1 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 1 (by decide))).1
  have e0 : permOfArr 820 chainS[0]! = psi xElt := h0.unique rep_tabA
  have e1 : permOfArr 820 chainS[1]! = psi yElt := h1.unique rep_tabB
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩

theorem range_psi : psi.range = Subgroup.closure {psi xElt, psi yElt} := by
  rw [MonoidHom.range_eq_map, ← closure_xy, MonoidHom.map_closure, Set.image_pair]

theorem uPg_zero : uPg[0]! = toTable tabA := by
  simp only [uPg, List.getElem!_toArray, List.getElem!_cons_zero]

theorem uPg_one : uPg[1]! = toTable tabB := by
  simp only [uPg, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

noncomputable def uGens (l : ℕ) : Equiv.Perm (Fin 820) :=
  if l = 0 then psi xElt else psi yElt

theorem u43_groupData : GroupData 820 psi.range uPg uGens uSift where
  lt := by norm_num
  rep l hl := by
    have hl2 : l < 2 := hl
    interval_cases l
    · rw [uPg_zero]
      exact rep_toTable rep_tabA
    · rw [uPg_one]
      exact rep_toTable rep_tabB
  gen := by
    have himg : uGens '' {l | l < uPg.size} = {psi xElt, psi yElt} := by
      ext g
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨l, hl, rfl⟩
        have hl2 : l < 2 := hl
        interval_cases l
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
    rw [himg, range_psi]
  sift T g hT := by
    rw [range_psi, ← uChainQ_eq]
    exact siftA_iff_mem_originalSubgroup uChainArrays (by norm_num) chain_check
      (co2Rep_natArr_iff.mpr hT)

end CFSG.ComponentClassification.HarrisLit.P1.U43
