module

public import CFSG.Sporadic.Schreier.Co3Sp6
public import Certificates.Data.Sp6Insp443
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace CFSG.SectionRank.QTK.Insp443.Sp6

open Equiv CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier.Co3 CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem hn36 : 36 < 2 ^ 32 := by norm_num


theorem valid : ValidSchreier co3Sp36Chain :=
  (validSchreier_of_chainOK co3Sp36Arrays (by norm_num) co3Sp36_check.1).1

theorem levelTables_eq_lv : levelTables co3Sp36Chain = lv () :=
  levelTables_eq co3Sp36Arrays (chainCheckFacts co3Sp36_check.1) rfl

theorem orderTables_eq_invs : orderTables co3Sp36Chain 2 = invs () := by
  rw [orderTables, levelTables_eq_lv]
  rfl

theorem getElem!_map_toNat (T : Table) (i : ℕ) : (T.map UInt32.toNat)[i]! = (T[i]!).toNat := by
  by_cases hi : i < T.size
  · rw [getElem!_pos (T.map UInt32.toNat) i (by simpa using hi), getElem!_pos T i hi,
      Array.getElem_map]
  · rw [getElem!_neg (T.map UInt32.toNat) i (by simpa using hi), getElem!_neg T i hi]
    rfl

theorem mem_of_siftOK {T : Table} {g : Perm (Fin 36)} (hT : Rep 36 T g)
    (h : siftOK T = true) : g ∈ co3X36 := by
  have hG : CFSG.Monster.B.Co2.Rep 36 (T.map UInt32.toNat) g := fun x => by
    have h1 := hT x x.2
    rw [idx_of_lt _ x.2] at h1
    rw [getElem!_map_toNat]
    exact h1
  exact (siftA_iff_mem_originalSubgroup co3Sp36Arrays (by norm_num) co3Sp36_check.1 hG).1 h

end CFSG.SectionRank.QTK.Insp443.Sp6

end
