module

public import CFSG.LargeExtraspecial.Setting
public import CFSG.LargeExtraspecial.O62Transport
public import CFSG.LargeExtraspecial.O62Model

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

variable {G : Type*} [Group G] [Finite G] (S : Setting G) (L : S.Qt ≃ₗ[ZMod 2] V₀)

@[expose] noncomputable def mbarModel : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  (S.Mbar.map S.O.subtype).map (conjL L).toMonoidHom

theorem mem_mbarModel_iff {g : V₀ ≃ₗ[ZMod 2] V₀} :
    g ∈ mbarModel S L ↔ ∃ m : S.M, conjL L (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) = g := by
  constructor
  · rintro ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, rfl⟩
    exact ⟨m, rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, rfl⟩

theorem conjL_ρ_mem_mbarModel (m : S.M) :
    conjL L (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ mbarModel S L :=
  (mem_mbarModel_iff S L).mpr ⟨m, rfl⟩

theorem card_mbarModel : Nat.card (mbarModel S L) = Nat.card S.Mbar := by
  rw [mbarModel, card_map_conjL, Subgroup.card_map_of_injective S.O.subtype_injective]

theorem mbarModel_le_O₀ {minus : Bool} (hL : ∀ v, qModel minus (L v) = S.q v) :
    mbarModel S L ≤ O₀ minus := by
  rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
  exact (mem_orthogonalGroup_conjL hL).mpr u.2

end CFSG.GF2Type.Smith1979W3

end
