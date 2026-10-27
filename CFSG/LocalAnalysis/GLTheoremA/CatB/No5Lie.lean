module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Co1Chev
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.No5

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

section Lie


theorem kdChevDownQ_five (q : ℕ) : KDChevDownQ 5 q := by
  have hp5 : Nat.Prime 5 := by norm_num
  have hLQ : YS08.LieQ.LieQConstrainedInner 5 := YS08.LieQ.lieQConstrainedInner_odd hp5 (by norm_num)
  have hA : KDAmbSolv 5 := kdAmbSolv_holds hp5 (by norm_num) u42_fixSubgroup_solvable
  have hI : KDChevInner 5 :=
    kdChevInner_of hp5 (by norm_num) (kdCharP_of_lieQConstrainedInner hp5 hLQ) hA
  exact kdChevDownQ_of_lieComps hp5 (lieCompsOn_holds hp5 (by norm_num)) (fun _ => hI)
    (kdAmbDownQ_holds hp5 (by norm_num) hI hA)

theorem no5_lie {Y : Type} [Group Y] [Finite Y] (hY : IsSimpleGroup Y)
    (hnab : ∃ a b : Y, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (e : Y ≃* (TauCeti.CFSGIndex.lie idx).Group) {y : Y} (hy : orderOf y = 5)
    {J : Subgroup Y} (hJ : GLAPComponent 5 (S8.cx y) J)
    (hC : Nonempty (PSimple 5 J ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group)) : False := by
  have hq : idx.1.characteristic.Prime := TauCeti.ValidLieTypeIndex.characteristic_prime idx
  have hchev : IsChevSimple idx.1.characteristic Y := Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨e⟩⟩
  have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hα : (MulAut.conj y) ^ 5 = 1 := by rw [← map_pow, hy5, map_one]
  have hI : GLAPComponent 5 (fixSubgroup (MulAut.conj y)) J := by
    rw [fixSubgroup_conj_eq_cx]
    exact hJ
  have hres := kdChevDownQ_five idx.1.characteristic Y hY hnab hchev (MulAut.conj y) hα J hI
  obtain ⟨eC⟩ := hC
  exact co1_not_chev_of_prime hq eC hres

end Lie

end CFSG.LocalAnalysis.GLTheoremA.No5
