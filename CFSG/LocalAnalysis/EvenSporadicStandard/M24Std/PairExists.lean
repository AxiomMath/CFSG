module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TCheck
public import Certificates.Certificate24850

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Setup.X1

variable {G : Type} [Group G]

theorem exists_listImage_pair
    {L : Subgroup G} (e : L ≃* NativeSporadic.M24) :
    ∃ A B : Subgroup G, ListImage L e A m24E1l ∧ ListImage L e B m24B0l := by
  obtain ⟨-, -, h1, hmul, -⟩ := m24_e1_check
  obtain ⟨-, -, h1', hmul', -⟩ := Certificates.certificate24850
  obtain ⟨A, hA⟩ := exists_listImage e h1 hmul
  obtain ⟨B, hB⟩ := exists_listImage e h1' hmul'
  exact ⟨A, B, hA, hB⟩

theorem exists_pairType
    {L : Subgroup G} (hL : IsSporadic L .M24) : ∃ A B : Subgroup G, PairType L A B := by
  obtain ⟨e⟩ := hL
  obtain ⟨A, B, hA, hB⟩ := exists_listImage_pair (L := L) e
  exact ⟨A, B, pairType_of_listImage hA hB⟩

end CFSG.EvenSporadicStandard.M24Std
