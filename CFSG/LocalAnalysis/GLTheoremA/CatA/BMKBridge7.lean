module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKSporFalseK

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.BMRows (kRows_of_isKGroup isKGroup_pSimple)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.GLTheoremA.AltDown
open scoped commutatorElement

section BMKBridge7


theorem i1415Seven_of_sporK
    (h : I1415SevenSporSK) (G : Type) [Group G] [Finite G] : I1415SevenAt G := by
  intro X K J y hX hK hyN hyp hJ hA
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  by_cases hCM : CentMod 3 K y
  · left
    obtain ⟨φ⟩ := up7a8_pQuot_iso_of_top hJK (up7a8_top_of_centMod hK hyN hyp hJ hCM)
    obtain ⟨eA⟩ := hA
    exact ⟨0, ⟨φ.symm.trans eA⟩⟩
  · have hcat : IsCatalogGroup (PSimple 3 K) :=
      CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' ((hX.of_le hK.1).quotient _)
        (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK)
    obtain ⟨i, ⟨e⟩⟩ := hcat
    cases i with
    | cyclic r hr =>
      exfalso
      obtain ⟨a, b, hab⟩ := (chev_pSimple_simple_nonabelian Nat.prime_three hK).2
      apply hab
      apply e.injective
      simp only [map_mul]
      exact mul_comm _ _
    | alternating n hn =>
      left
      obtain ⟨m, k, hm5, hk0, hnk, ⟨eJ⟩⟩ := up7a8_psimple_root hn hK hyN hyp hCM hJ e
      obtain ⟨eA⟩ := hA
      obtain ⟨eP7⟩ := up7a8_psimple_iso_of_pQuot (by norm_num) eA
      have hm7 : m = 7 := up7a8_alt_iso_eq hm5 (by norm_num) (eJ.symm.trans eP7)
      subst hm7
      have hn8 : 8 ≤ n := by omega
      obtain ⟨eK⟩ := up7a8_pQuot_alt_of_center hK hn8 e
      subst hnk
      exact ⟨k, ⟨eK⟩⟩
    | sporadic s =>
      exact (up7a8_spor_falseK (m := 7) h (by norm_num) hK hyN hyp hCM hJ s e hA (isKGroup_pSimple hX hK)).elim
    | lie d =>
      have hr : d.1.characteristic.Prime := up7a8_char_prime d.1
      have hKr : IsChevSimple d.1.characteristic (PSimple 3 K) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie d, by simp [onLie], ⟨e⟩⟩
      have hJr := up7a8_closure hr hX hK hyN hyp hKr hJ
      obtain ⟨eA⟩ := hA
      obtain ⟨eP7⟩ := up7a8_psimple_iso_of_pQuot (by norm_num) eA
      exact (up7a8_not_chev_alt7 hr eP7 hJr).elim

end BMKBridge7

end CFSG.LocalAnalysis.GLTheoremA
