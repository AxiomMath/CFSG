module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

theorem not_isDelta5_perfectCore_tits
    {G : Type} [Group G] [Finite G] (L P : Subgroup G)
    (hT : IsTits ↥L) (hP : IsMaxParabolic2 L P) : ¬ IsDelta5Group ↥(perfectCore P) := by
  obtain ⟨⟨hPL, S, hS, hN⟩, hPne, -⟩ := hP
  have hU : IsSylowTwoOf (S.subgroupOf L) (⊤ : Subgroup ↥L) := isSylowTwoOf_top_subgroupOf hS
  obtain ⟨H, N, -, hUH, hUN, -, -, hlat, hHs, hNs⟩ := titsSylowOvergroupLattice ↥L hT _ hU
  have hSP : S ≤ P := fun x hx => hN ⟨hS.1 hx, Subgroup.le_normalizer hx⟩
  have hUP : S.subgroupOf L ≤ P.subgroupOf L := fun x hx => hSP hx
  have hsolv : Group.IsSolvable ↥(P.subgroupOf L) := by
    rcases hlat _ hUP with h | h | h | h
    · rw [h]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 ↥(S.subgroupOf L) := hU.2.1
      have : Group.IsNilpotent ↥(S.subgroupOf L) := hp.isNilpotent
      infer_instance
    · rw [h]; exact hHs
    · rw [h]; exact hNs
    · exfalso
      apply hPne
      refine le_antisymm hPL fun x hx => ?_
      have : (⟨x, hx⟩ : ↥L) ∈ P.subgroupOf L := h ▸ Subgroup.mem_top _
      exact this
  have hPs : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hPL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPL).symm.injective
  rw [(isSolvable_iff_perfectCore_eq_bot P).mp hPs]
  exact not_isDelta5_bot

end CFSG.QuasithinUnique.A5.G3
