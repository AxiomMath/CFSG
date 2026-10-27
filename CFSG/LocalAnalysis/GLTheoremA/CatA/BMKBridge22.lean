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

section BMKBridge22


theorem i1422At_of_sporK
    (h : I1422SporSK) (G : Type) [Group G] [Finite G] (hc2 : I1422Char2At G) :
    I1422At G := by
  intro X K J y hX hK hyN hyp hJ hA
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  by_cases hCM : CentMod 3 K y
  · obtain ⟨φ⟩ := up7a8_pQuot_iso_of_top hJK (up7a8_top_of_centMod hK hyN hyp hJ hCM)
    obtain ⟨eA⟩ := hA
    rw [up7a8_top_of_centMod hK hyN hyp hJ hCM]
    exact ⟨Subgroup.topEquiv.trans (φ.symm.trans eA)⟩
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
      obtain ⟨m, k, hm5, hk0, hnk, ⟨eJ⟩⟩ := up7a8_psimple_root hn hK hyN hyp hCM hJ e
      obtain ⟨eA⟩ := hA
      obtain ⟨eP8⟩ := up7a8_psimple_iso_of_pQuot (by norm_num) eA
      have hm8 : m = 8 := up7a8_alt_iso_eq hm5 (by norm_num) (eJ.symm.trans eP8)
      subst hm8
      have hn8 : 8 ≤ n := by omega
      obtain ⟨eK⟩ := up7a8_pQuot_alt_of_center hK hn8 e
      obtain ⟨m', hm'5, ⟨eI⟩⟩ := up7a8_imageMod_alt hn hK hyN hyp hCM hJ eK
      have hJA : IsAltPType 3 J m' := isAltPType_of_imageMod hJK hm'5 ⟨eI⟩
      obtain ⟨eJ2⟩ := hJA
      have hm'8 : m' = 8 := up7a8_alt_iso_eq hm'5 (by norm_num) (eJ2.symm.trans eA)
      subst hm'8
      exact ⟨eI⟩
    | sporadic s =>
      exact (up7a8_spor_falseK (m := 8) h (by norm_num) hK hyN hyp hCM hJ s e hA (isKGroup_pSimple hX hK)).elim
    | lie d =>
      have hr : d.1.characteristic.Prime := up7a8_char_prime d.1
      have hKr : IsChevSimple d.1.characteristic (PSimple 3 K) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie d, by simp [onLie], ⟨e⟩⟩
      have hJr := up7a8_closure hr hX hK hyN hyp hKr hJ
      by_cases hr2 : d.1.characteristic = 2
      · rw [hr2] at hKr
        exact hc2 X K J y hX hK hyN hyp hCM hJ hA hKr
      · obtain ⟨eA⟩ := hA
        obtain ⟨eP8⟩ := up7a8_psimple_iso_of_pQuot (by norm_num) eA
        exact (up7a8_not_chev_alt8_odd hr hr2 eP8 hJr).elim

end BMKBridge22

end CFSG.LocalAnalysis.GLTheoremA
