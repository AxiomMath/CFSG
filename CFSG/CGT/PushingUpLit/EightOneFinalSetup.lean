module

public import CFSG.CGT.PushingUpLit.EightOneWindow
public import CFSG.CGT.PushingUpLit.EightOneBlocksBasic

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open CFSG.Assembly (KProper InCatalog)

namespace EightOneFinal

section Blocks

variable {G : Type} [Group G] [Finite G]

@[expose] def BlockAbove (X N' L : Subgroup G) : Prop :=
  X ≤ L ∧ L ≤ N' ∧ (L.subgroupOf N').IsSubnormal ∧ InClassX ↥L ∧ Arrow X L ∧ L ≠ X

namespace BlockAbove

variable {X N' L : Subgroup G}

theorem le (h : BlockAbove X N' L) : X ≤ L :=
  h.1

theorem isSubnormal (h : BlockAbove X N' L) : (L.subgroupOf N').IsSubnormal :=
  h.2.2.1

theorem inClassX (h : BlockAbove X N' L) : InClassX ↥L :=
  h.2.2.2.1

theorem arrow (h : BlockAbove X N' L) : Arrow X L :=
  h.2.2.2.2.1

theorem ne (h : BlockAbove X N' L) : X ≠ L :=
  fun e => h.2.2.2.2.2 e.symm

theorem isBlockOfInX (h : BlockAbove X N' L) : IsBlockOfInX N' L :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem mem_normalizer (hN : IsCharacteristicP 2 ↥N') (hX : InClassX ↥X) (h : BlockAbove X N' L)
    {g : G} (hgN : g ∈ N') (hgX : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have hconj : conjugate L g = L := conjugate_block_eq hN hX h.isBlockOfInX h.le hgN hgX
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← ThreeFromEight.mem_conjugate_iff, hconj]

end BlockAbove

end Blocks

section Pair

variable {G : Type} [Group G] [Finite G]

theorem exists_maximal_pair {X D : Subgroup G} (hex : ∃ N', AnchoredWitness X D N')
    (hL : ∀ N', AnchoredWitness X D N' → ∃ L, BlockAbove X N' L) :
    ∃ N L : Subgroup G, AnchoredWitness X D N ∧ BlockAbove X N L ∧
      ∀ N' L' : Subgroup G, AnchoredWitness X D N' → BlockAbove X N' L' →
        Nat.card ↥L' ≤ Nat.card ↥L := by
  obtain ⟨N₁, hN₁⟩ := hex
  obtain ⟨L₁, hL₁⟩ := hL N₁ hN₁
  obtain ⟨⟨N, L⟩, ⟨hN, hLB⟩, hmax⟩ := Set.exists_max_image
    {p : Subgroup G × Subgroup G | AnchoredWitness X D p.1 ∧ BlockAbove X p.1 p.2}
    (fun p => Nat.card ↥p.2) (Set.toFinite _) ⟨(N₁, L₁), hN₁, hL₁⟩
  exact ⟨N, L, hN, hLB, fun N' L' hN' hL' => hmax (N', L') ⟨hN', hL'⟩⟩

end Pair

end EightOneFinal

end CFSG.CGT.PushingUpLit
