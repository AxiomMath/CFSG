module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM23Model
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensusW2
public import CFSG.Certificates.Kernel.Census.ToMain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M23

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.KC.Census

@[expose] def m23DW : List (List ℤ) :=
  [[-2, -2, 1, 2, 2], [-1, -2, 3, 2, 1], [-4, 3, 4], [-1, 5, 1], [-5, 6, 5], [-4, 7, 4],
    [-6, -3, -5, 8, 3], [-9, -8, -9, -1, 8, 1], [-7, -9, -10, -5, 10, 9, 5], [-8, -9, 11, 9],
    [-10, -11, 12, 10]]

@[expose] def m23SW : Array (Array ℕ) := CFSG.EvenSmallLie.OmegaEight.pushWords 23 m23Gens m23DW

@[expose] def m23BaseWL : List (Fin 23) := [0, 1, 2, 5, 3, 4]

@[expose] def m23BaseW : Array ℕ := (m23BaseWL.map Fin.val).toArray

@[expose] def m23InXW (t : Array ℕ) : Bool := siftA 23 (rawLevels 23 m23SW m23BaseW) m23BaseW 0 t

theorem m23SW_getElem! {i : ℕ} (hi : i < 2) : m23SW[i]! = m23Gens[i]! :=
  CFSG.EvenSmallLie.OmegaEight.pushWords_getElem! _ _ (by simp [m23Gens]; omega)

@[expose] noncomputable def m23QW : RawSchreierDatum 23 :=
  RawSchreierDatum.ofArrays 23 (by norm_num) m23SW 2 (by simp [m23SW, m23Gens,
    CFSG.EvenSmallLie.OmegaEight.size_pushWords, m23DW]) m23BaseWL (by decide)
    (CFSG.EvenSmallLie.OmegaEight.wordsOf 2 m23DW)

theorem m23QW_originalSubgroup : m23QW.originalSubgroup = Blueprint.NativeSporadic.M23 := by
  rw [m23QW, J2Cover.ofArrays_originalSubgroup, ← closure_m23Gens]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi2 : i < 2 := by simpa using hi
    refine ⟨i, by simpa [m23Gens] using hi2, ?_⟩
    rw [m23SW_getElem! hi2]
  · rintro ⟨i, hi, rfl⟩
    have hi2 : i < 2 := by simpa [m23Gens] using hi
    refine ⟨i, by simpa using hi2, ?_⟩
    rw [m23SW_getElem! hi2]

theorem m23InXW_iff (hch : rawChainOK 23 (m23SW.extract 0 2) m23SW m23BaseW
      (CFSG.EvenSmallLie.OmegaEight.wordsOf 2 m23DW) 4 = true)
    (a : Array ℕ) (g : Equiv.Perm (Fin 23)) (h : Rep 23 a g) :
    m23InXW a = true ↔ g ∈ Blueprint.NativeSporadic.M23 := by
  rw [← m23QW_originalSubgroup]
  exact J2Cover.ofArrays_mem_iff (by norm_num) hch h

@[expose] noncomputable def m23CheckW2 (sG roots : Array ℕ) (nodes : Array NodeP)
    (cS : ArrCertP) (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP) : Bool :=
  rawChainOK 23 (m23SW.extract 0 2) m23SW m23BaseW
      (CFSG.EvenSmallLie.OmegaEight.wordsOf 2 m23DW) 4 &&
    censusOKW2 23 m23PS m23InXW M24.allA true false false (sG.map (unpackP 23 5)) roots
      (nodes.map (NodeP.toMain 23 5)) (cS.toMain 23 5)
      (wcs.map fun cs => cs.map (ArrCertP.toMain 23 5)) (pfs.map PerfWP.toMain) &&
    (allLt (sG.map (unpackP 23 5)).size fun k => m23InXW (sG.map (unpackP 23 5))[k]!) &&
    (cS.toMain 23 5).pts.size == 128

theorem census_of_m23CheckW2
    {sG roots : Array ℕ} {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)}
    {pfs : Array PerfWP} (h : m23CheckW2 sG roots nodes cS wcs pfs = true) :
    YCensus17 (⊤ : Subgroup ↥Blueprint.NativeSporadic.M23) (fun _ => False) := by
  simp only [m23CheckW2, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hch, hc⟩, hgen⟩, hsize⟩ := h
  exact yCensus17_top_of_checkW2 (k := 7) (m := 79695) m23PS_lt
    (fun a hv ha => (m23InXW_iff hch a _ (rep_of_validA hv)).1 ha) hc hgen hsize
    (by rw [card_m23]; norm_num) (by decide)

end CFSG.ComponentClassification.RankTwoSporadic.M23
