module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_isSylowOf_pElementSubgroup {p : ℕ} [Fact p.Prime] {X P : Subgroup G}
    (hP : IsSylowOf p P (CFSG.RankThree.PartOne.pElementSubgroup p X)) : IsSylowOf p P X := by
  have hPX : P ≤ X := hP.le.trans ((Subgroup.closure_le X).2 fun _ hx => hx.1)
  obtain ⟨Q, hQ⟩ := (hP.isPGroup.comap_subtype (K := X)).exists_le_sylow
  have hT : IsSylowOf p ((Q : Subgroup X).map X.subtype) X := ⟨Q, rfl⟩
  have hPT : P ≤ (Q : Subgroup X).map X.subtype := fun y hy => ⟨⟨y, hPX hy⟩, hQ hy, rfl⟩
  have hTO := CFSG.le_pElementSubgroup_of_isPGroup Fact.out hT.isPGroup hT.le
  rwa [← hP.eq_of_le hPT hTO hT.isPGroup]

theorem isSylowOf_inf_of_commutator_le {K₁ K₂ O : Subgroup G} (hO : IsPGroup 2 O)
    (hO₁ : O ≤ K₁) (hO₂ : O ≤ K₂) (hc : ⁅K₁, K₂⁆ ≤ O)
    (hcore : CFSG.Open.pCoreOf 2 K₁ ≤ O) : IsSylowOf 2 O (K₁ ⊓ K₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hO.comap_subtype (K := K₁ ⊓ K₂)).exists_le_sylow
  set T := (Q : Subgroup ↥(K₁ ⊓ K₂)).map (K₁ ⊓ K₂).subtype
  have hT : IsSylowOf 2 T (K₁ ⊓ K₂) := ⟨Q, rfl⟩
  have hOT : O ≤ T := fun y hy => ⟨⟨y, le_inf hO₁ hO₂ hy⟩, hQ hy, rfl⟩
  have hTn : K₁ ≤ normalizer (T : Set G) := by
    rw [le_normalizer_iff_commutator_le_right]
    exact (commutator_mono le_rfl (hT.le.trans inf_le_right)).trans (hc.trans hOT)
  have hTO : T ≤ O := (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hT.le.trans inf_le_left) hTn hT.isPGroup).trans hcore
  rwa [le_antisymm hTO hOT] at hT

end CFSG.GroupTheory
