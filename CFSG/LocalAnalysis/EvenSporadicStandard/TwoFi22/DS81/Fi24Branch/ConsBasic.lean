module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotC

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G]

@[expose] def czInv (z : G) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : CInv ↥(Cz z) where
  z := ⟨z, mem_Cz.mpr rfl⟩
  central := fun g => Subtype.ext (mem_Cz.mp g.2)
  sq := Subtype.ext (by simpa using hz2)
  ne := fun h => hz1 (congrArg Subtype.val h)

theorem mem_zpowers_czInv (z : G) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (x : ↥(Cz z)) :
    x ∈ zpowers (czInv z hz2 hz1).z ↔ (x : G) ∈ zpowers z := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa [czInv] using congrArg Subtype.val hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa [czInv] using hk)⟩

theorem mem_Cz_of_comm {t z : G} (h : t * z = z * t) : t ∈ Cz z := mem_Cz.mpr h

theorem card_subgroupOf' {S D : Subgroup G} (h : S ≤ D) :
    Nat.card ↥(S.subgroupOf D) = Nat.card ↥S := by
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem perfect_subgroupOf {S D : Subgroup G} (h : S ≤ D) (hS : ⁅S, S⁆ = S) :
    ⁅S.subgroupOf D, S.subgroupOf D⁆ = S.subgroupOf D := by
  apply Subgroup.map_injective D.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h, hS]

theorem closure_pair_subgroupOf {D : Subgroup G} {t z : G} (ht : t ∈ D) (hz : z ∈ D) :
    closure {(⟨t, ht⟩ : ↥D), (⟨z, hz⟩ : ↥D)} = (closure {t, z}).subgroupOf D := by
  apply Subgroup.map_injective D.subtype_injective
  have hle : closure ({t, z} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    exacts [ht, hz]
  rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le hle, Set.image_pair]
  rfl

theorem quot_subgroupOf {X : Type} [Group X] {T S D : Subgroup G} (hTD : T ≤ D)
    (π : ↥T →* X) (hπ : Function.Surjective π) (hker : π.ker = S.subgroupOf T) :
    ∃ π' : ↥(T.subgroupOf D) →* X, Function.Surjective π' ∧
      π'.ker = (S.subgroupOf D).subgroupOf (T.subgroupOf D) := by
  let φ : ↥(T.subgroupOf D) →* ↥T := (Subgroup.subgroupOfEquivOfLe hTD).toMonoidHom
  let π' : ↥(T.subgroupOf D) →* X := π.comp φ
  refine ⟨π', hπ.comp (Subgroup.subgroupOfEquivOfLe hTD).surjective, ?_⟩
  ext x
  simp only [Subgroup.mem_subgroupOf]
  change π (φ x) = 1 ↔ ((x : ↥D) : G) ∈ S
  rw [← MonoidHom.mem_ker, hker]
  rfl

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
