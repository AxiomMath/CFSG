module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Fact218
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109CInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelInv
public import Certificates.Certificate442017

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace MoInv

theorem fixCnt_of_invCent_1440
    {t : P45} (h : InvCent 1440 t) : Certificates.OmegaInv.fixCnt t = 15 := by
  obtain ⟨ht, hsq, hne, hc⟩ := h
  rcases class_cases ht hsq hne with ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ |
    ⟨-, -, -, h1⟩
  · omega
  · omega
  · omega
  · exact h1

end MoInv

namespace Ty

theorem swapChk_of_invCent_1440
    {u : P45} (hu : InvCent 1440 u)
    (hc : u * Pk.tA = Pk.tA * u) : Certificates.OmegaTypes.swapChk KAl KBl u = true := by
  have hf := MoInv.fixCnt_of_invCent_1440 hu
  have h := Certificates.certificate442017
  simp only [Certificates.OmegaSwap.check, Certificates.OmegaSwap.swapAll, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    mem_elemsT QA45 QA45_ok] at h
  rcases h u hu.1 with ((((h1 | h1) | h1) | h1) | h1)
  · exact absurd hu.2.1 h1
  · exact absurd h1 hu.2.2.1
  · exact absurd hc h1
  · exact absurd hf h1
  · exact h1

end Ty

theorem asc82FactCSw_of_cert :
    Asc82FactCSw := by
  intro G _ _ L hL z K1 K2 hz hK1 hK2 hne r hrz hty
  obtain ⟨F, hzL, hψz⟩ := Pk.exists_frame_tA hL hz
  have hXY := Ty.pockets_cases F hzL hψz hK1 hK2 hne
  obtain ⟨hrN, hinv⟩ := (TyDict.inducesTypeSome_four_minus_iff hL F r).1 hty
  have hzN : z ∈ normalizer (L : Set G) := Subgroup.le_normalizer hzL
  have hc : F.φ ⟨r, hrN⟩ * Pk.tA = Pk.tA * F.φ ⟨r, hrN⟩ := by
    have h1 : F.φ ⟨z, hzN⟩ = Pk.tA := by rw [← hψz]; rfl
    rw [← h1, ← map_mul, ← map_mul]
    exact congrArg F.φ (Subtype.ext hrz)
  have hsw := Ty.swapChk_of_invCent_1440 hinv hc
  have huu := hinv.2.1
  have hKA := (Ty.swapChk_iff_KA huu).1 hsw
  have hKB := (Ty.swapChk_iff_KB huu).1 hsw
  have hK1L := PspFrame.le_of_sl23PocketIn hK1
  have hK2L := PspFrame.le_of_sl23PocketIn hK2
  have hcL : CFSG.conjugate K1 r ≤ L := by
    intro y hy
    rw [mem_conjugate_iff'] at hy
    exact (Subgroup.mem_normalizer_iff.1 hrN y).2 (hK1L hy)
  refine (F.img_inj hcL hK2L).1 ?_
  rw [F.img_conjugate_phi ⟨r, hrN⟩]
  rcases hXY with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact hKA
  · rw [h1, h2]
    exact hKB

end CFSG.OddStandard.SmallF3.Omega
