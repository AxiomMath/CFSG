module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Iso
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabCert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Cert

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.NativeSporadic HeSylow
open CFSG.Sporadic.HeldB

theorem centralizer_heP_eq_bot :
    centralizer ((heP.subgroupOf heAutGroup : Subgroup ↥heAutGroup) : Set ↥heAutGroup) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  refine Subtype.ext (CFSG.RankThree.PartOne.heAutModel.inj y y.2 fun p hp => ?_)
  have h := mem_centralizer_iff.mp hy ⟨p, heP_le_heAutGroup hp⟩ hp
  exact (congrArg Subtype.val h).symm

theorem step44_sylow_of
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}
    (hset : Sec4Setting G A R g E F) (S₁ : Subgroup G)
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    (Nat.card S₁ = 2 ^ 10 ∧ ∃ P : Sylow 2 (Carrier .He), Nonempty (S₁ ≃* P)) ∨
      (Nat.card S₁ = 2 ^ 11 ∧
        ∃ (H : Type) (_ : Group H) (_ : Finite H) (K : Subgroup H), K.Normal ∧
          IsSporadic K .He ∧ K.index = 2 ∧ centralizer (K : Set H) = ⊥ ∧
          ∃ P : Sylow 2 H, Nonempty (S₁ ≃* P)) := by
  rcases sylow_equiv_model Hexa.hexa_check Hexa.hexaStab_check Hexa.step44_check
      (planeData_of hE16 h11 hset.frame hset.even)
      (planeData_of hE16 h11 hset.frame.swap hset.even) hS₁ with ⟨hc, ⟨e⟩⟩ | ⟨hc, ⟨e⟩⟩
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (Carrier .He)))
    obtain ⟨e₀⟩ := nonempty_sylow_he_equiv P
    exact Or.inl ⟨hc, P, ⟨e.trans e₀.symm⟩⟩
  · have hK : IsSporadic (heP.subgroupOf heAutGroup) .He :=
      ⟨(subgroupOfEquivOfLe heP_le_heAutGroup).trans
        (heEquivP : Blueprint.NativeSporadic.Carrier .He ≃* ↥heP).symm⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥heAutGroup))
    obtain ⟨e₀⟩ := nonempty_sylow_aut_equiv heP_normal_heAutGroup hK heP_relIndex_heAutGroup
      centralizer_heP_eq_bot P
    exact Or.inr ⟨hc, ↥heAutGroup, inferInstance, inferInstance, heP.subgroupOf heAutGroup,
      heP_normal_heAutGroup, hK, heP_relIndex_heAutGroup, centralizer_heP_eq_bot, P,
      ⟨e.trans e₀.symm⟩⟩


theorem step44ii_of
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) : Step44ii :=
  fun _ _ _ _ _ _ _ _ hset S₁ hS₁ => step44_sylow_of hE16 h11 hset S₁ hS₁

end CFSG.ComponentClassification.AS81
