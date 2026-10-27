module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermKit

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

variable {n : ℕ}

theorem card_subtype_mem_list {L : List (Perm (Fin n))} (hnd : L.Nodup) :
    Nat.card {g : Perm (Fin n) // g ∈ L} = L.length := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun g => (List.mem_toFinset (l := L) (a := g)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe]

theorem mem_of_count_list (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {ts : List Table} (hts : tabsOK n ts = true) (hnd : (ts.map (tabPerm n)).Nodup)
    (hcnt : countProducts n (inSp n ts) (levelTables Q) (idT n) = ts.length) {T : Table}
    (hT : T ∈ ts) : tabPerm n T ∈ Q.originalSubgroup := by
  classical
  have hts' := hts
  unfold tabsOK at hts'
  rw [List.all_eq_true] at hts'
  have hfP : ∀ S g, Rep n S g → (inSp n ts S = true ↔ g ∈ ts.map (tabPerm n)) := by
    intro S g hS
    unfold inSp
    rw [List.any_eq_true, List.mem_map]
    refine exists_congr fun u => and_congr_right fun hu => ?_
    exact tblEq_iff_eq (rep_tabPerm (hts' u hu)) hS
  have h1 := card_subtype_eq_countProducts hn Q hQ hfP
  rw [hcnt] at h1
  have h2 := card_subtype_mem_list hnd
  rw [List.length_map] at h2
  let ι : {x : Q.originalSubgroup // (x : Perm (Fin n)) ∈ ts.map (tabPerm n)} →
      {g : Perm (Fin n) // g ∈ ts.map (tabPerm n)} := fun x => ⟨x.1, x.2⟩
  have hι : Function.Injective ι := by
    intro x y hxy
    have h : ((x.1 : Q.originalSubgroup) : Perm (Fin n)) = ((y.1 : Q.originalSubgroup) :
        Perm (Fin n)) := congrArg (fun z : {g : Perm (Fin n) // g ∈ ts.map (tabPerm n)} =>
          (z : Perm (Fin n))) hxy
    exact Subtype.ext (Subtype.ext h)
  have hbij := hι.bijective_of_nat_card_le (by rw [h1, h2])
  obtain ⟨x, hx⟩ := hbij.2 ⟨tabPerm n T, List.mem_map.mpr ⟨T, hT, rfl⟩⟩
  have : (x.1 : Perm (Fin n)) = tabPerm n T := congrArg Subtype.val hx
  rw [← this]
  exact x.1.2

end CFSG.SectionRank.QTK.Insp443.PermKit

end
