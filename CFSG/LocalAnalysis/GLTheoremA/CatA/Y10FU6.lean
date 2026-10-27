module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def U6Center : Prop :=
  ∀ (L : Type) [Group L] [Finite L], HasLabel L (fun lab : GLALabel => lab = ⟨.twA, 5, 2⟩) →
    Subgroup.center L = ⊥

@[expose] def U6Rank : Prop :=
  ∀ (L : Type) [Group L] [Finite L], HasLabel L (fun lab : GLALabel => lab = ⟨.twA, 5, 2⟩) →
    ∃ F : Subgroup L, IsElemAbelian 5 F ∧ Nat.card F = 5 ^ 5

@[expose] def U6Mem : Prop :=
  ∀ (L : Type) [Group L] [Finite L], HasLabel L (fun lab : GLALabel => lab = ⟨.twA, 5, 2⟩) →
    ∀ (y : L) (J : Subgroup L), orderOf y = 5 → GLALayer (Subgroup.centralizer ({y} : Set L)) = J →
      HasLabel ↥J (fun lab : GLALabel => lab = ⟨.twA, 4, 2⟩) → y ∈ J

@[expose] def U6Cent : Prop :=
  ∀ (L : Type) [Group L] [Finite L], HasLabel L (fun lab : GLALabel => lab = ⟨.twA, 5, 2⟩) →
    ∀ (y : L) (J : Subgroup L), orderOf y = 5 → GLALayer (Subgroup.centralizer ({y} : Set L)) = J →
      HasLabel ↥J (fun lab : GLALabel => lab = ⟨.twA, 4, 2⟩) →
        ∀ α : MulAut L, (∀ j ∈ J, α j = j) → ∃ a ∈ Subgroup.zpowers y, ∀ l : L, α l = a⁻¹ * l * a

variable {G : Type} [Group G] [Finite G]

theorem layer_centralizer_subgroupOf {L J : Subgroup G} {y : G} (hy : y ∈ L)
    (hJ : GLALayer (L ⊓ Subgroup.centralizer ({y} : Set G)) = J) :
    GLALayer (Subgroup.centralizer ({(⟨y, hy⟩ : L)} : Set L)) = J.subgroupOf L := by
  have h1 := glaLayer_map L.subtype_injective (Subgroup.centralizer ({(⟨y, hy⟩ : L)} : Set L))
  rw [map_centralizer_singleton_subtype] at h1
  rw [hJ] at h1
  rw [subgroupOf_eq_comap, h1, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

theorem layer_le_of_layer {L J : Subgroup G} {y : G}
    (hJ : GLALayer (L ⊓ Subgroup.centralizer ({y} : Set G)) = J) : J ≤ L := by
  rw [← hJ]
  exact (glaLayer_le _).trans inf_le_left

theorem u6StructAt_of_four_facts (hc : U6Center) (hr : U6Rank) (hm : U6Mem) (ht : U6Cent) :
    U6StructAt G where
  center L hL := hc ↥L hL
  rank L hL := by
    obtain ⟨F', hF', hcard⟩ := hr ↥L hL
    exact ⟨F'.map L.subtype, map_subtype_le F', (isElemAbelian_map_subtype_iff F').2 hF',
      by rw [card_map_subtype]; exact hcard⟩
  mem L J y hL hyL hord hJ hJlab := by
    have hJL := layer_le_of_layer hJ
    have hlay := layer_centralizer_subgroupOf hyL hJ
    have := hm ↥L hL ⟨y, hyL⟩ (J.subgroupOf L) (by rw [← orderOf_subtype] at *; exact hord) hlay
      ((hasLabel_subgroupOf_iff hJL _).1 hJlab)
    exact Subgroup.mem_subgroupOf.1 this
  cent L J y g hL hyL hord hJ hJlab hgN hgC := by
    have hJL := layer_le_of_layer hJ
    have hlay := layer_centralizer_subgroupOf hyL hJ
    obtain ⟨a, ha, hα⟩ := ht ↥L hL ⟨y, hyL⟩ (J.subgroupOf L)
      (by rw [← orderOf_subtype] at *; exact hord) hlay ((hasLabel_subgroupOf_iff hJL _).1 hJlab)
      (conjAut L g hgN) (by
        intro j hj
        apply Subtype.ext
        rw [coe_conjAut]
        have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
        have := Subgroup.mem_centralizer_iff.1 hgC (j : G) hjJ
        calc g⁻¹ * (j : G) * g = g⁻¹ * (g * (j : G)) := by rw [← this]; group
          _ = j := by group)
    refine ⟨(a : G), ?_, fun l hl => ?_⟩
    · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
    · have := congrArg Subtype.val (hα ⟨l, hl⟩)
      rw [coe_conjAut] at this
      simpa using this.symm

end CFSG.LocalAnalysis.GLTheoremA.Y10F
