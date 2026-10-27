module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5EightB
public import CFSG.CGT.PushingUpLit.CGT6.Emb5CompZ

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

omit [Finite V] in
theorem conj_mem_map_subtype {g : MulAut V} (hg : g ∈ G) {x : ↥G} (N : Subgroup ↥G)
    (h : (⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹ : ↥G) ∈ N) : g * (x : MulAut V) * g⁻¹ ∈ N.map G.subtype :=
  Subgroup.mem_map.mpr ⟨_, h, by simp⟩

structure Emb5Layer (G Y L : Subgroup (MulAut V)) : Prop where
  le : L ≤ G
  normal : ∀ g ∈ G, ∀ x ∈ L, g * x * g⁻¹ ∈ L
  quasi : CFSG.IsQuasisimple ↥L
  le_conj : L ≤ conjClosure Y G
  noncentral : ∃ y ∈ Y, ∃ x ∈ L, x * y ≠ y * x

theorem Emb5Cfg.exists_layer (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1)
    (hself : (Y.subgroupOf G).IsSubnormal → Lift5 G Y Y) : ∃ L, Emb5Layer G Y L := by
  obtain ⟨Lg, y, hy, l, hL, hl, hne⟩ := cfg.exists_component hV hself
  have hnorm : Lg.Normal := cfg.normal_of_component hV hL hy hl hne
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hNG : conjClosure Y G ≤ G := conjClosure_le hYG
  have hNn : ((conjClosure Y G).subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).2 le_normalizer_conjClosure
  refine ⟨Lg.map G.subtype, ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact conj_mem_map_subtype hg Lg (hnorm.conj_mem x hx ⟨g, hg⟩)
  · exact isQuasisimple_of_mulEquiv (Lg.equivMapOfInjective G.subtype G.subtype_injective) hL.1
  · have hy' : (⟨y, hYG hy⟩ : ↥G) ∈ (conjClosure Y G).subgroupOf G :=
      Subgroup.mem_subgroupOf.mpr (le_conjClosure hy)
    rcases le_or_commute_of_normal (L := Lg) (P := (conjClosure Y G).subgroupOf G) hL.1 hy' with
      h | h
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
    · exact absurd (h l hl) hne
  · refine ⟨y, hy, (l : MulAut V), ⟨l, hl, rfl⟩, fun h => hne (Subtype.ext h)⟩

omit [Finite V] in
theorem Emb5Layer.conjClosure_eq {L : Subgroup (MulAut V)} (h : Emb5Layer G Y L) (hYL : Y ≤ L) :
    conjClosure Y G = L := by
  apply le_antisymm _ h.le_conj
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  exact h.normal g hg y (hYL hy)

theorem Emb5Cfg.sup_eq_of_le (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} (h : Emb5Layer G Y L) (hYL : Y ≤ L) : L ⊔ T = G := by
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hKG : L ⊔ T ≤ G := sup_le h.le cfg.adm.hTG
  by_contra hne
  have hlt : L ⊔ T < G := lt_of_le_of_ne hKG hne
  have hNK : conjClosure Y G ≤ L ⊔ T := (h.conjClosure_eq hYL).le.trans le_sup_left
  obtain ⟨X, hX⟩ := cfg.lift_sub hV hlt
    (cfg.adm.restrict le_sup_right hKG (hYL.trans le_sup_left))
  exact cfg.nolift ⟨X, Lift5.up hYG cfg.not_isPGroup_Y hNK hKG hX⟩

end CFSG.CGT.PushingUpLit.CGT6
