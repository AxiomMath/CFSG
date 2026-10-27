module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chains
public import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Conj

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

section StdBare

variable {A B : Type} [Group A] [Group B]

theorem centralizer_map_mulEquiv (e : A ≃* B) (K : Subgroup A) :
    centralizer ((K.map e.toMonoidHom : Subgroup B) : Set B) =
      (centralizer (K : Set A)).map e.toMonoidHom :=
  CFSG.StandardSubgroupAPI.centralizer_map_mulEquiv e K

end StdBare

section Components

variable {H : Type} [Group H]

theorem isCompIn_of_le {M X Z : Subgroup H} (h : IsCompIn M X) (hMZ : M ≤ Z) (hZX : Z ≤ X) :
    IsCompIn M Z := by
  refine ⟨hMZ, ?_⟩
  have hq : CFSG.IsQuasisimple ↥(M.subgroupOf Z) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMZ).symm
      h.isQuasisimple
  refine ⟨hq, ?_⟩
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hZX h.2.2

theorem isCompIn_subgroupOf {M X Y : Subgroup H} (h : IsCompIn M X) (hXY : X ≤ Y) :
    IsCompIn (M.subgroupOf Y) (X.subgroupOf Y) := by
  refine ⟨fun x hx => h.1 hx, ?_⟩
  let e : ↥(X.subgroupOf Y) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXY
  have hc := CFSG.LocalCores.isComponent_map_mulEquiv e.symm h.2
  have heq : (M.subgroupOf X).map e.symm.toMonoidHom =
      (M.subgroupOf Y).subgroupOf (X.subgroupOf Y) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨e z, hz, by simp⟩
  rwa [heq] at hc

theorem inL_subgroupOf {K P Y : Subgroup H} (hK : IsCompIn K (centralizer (P : Set H)))
    (hKY : K ≤ Y) (hPY : P ≤ Y) (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P) : InL (K.subgroupOf Y) := by
  refine ⟨P.subgroupOf Y, ?_, ?_, ?_⟩
  · intro hb
    apply hP
    rw [eq_bot_iff]
    intro p hp
    have : (⟨p, hPY hp⟩ : ↥Y) ∈ P.subgroupOf Y := hp
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · exact hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
  · have hcen : centralizer ((P.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) =
        (centralizer (P : Set H) ⊓ Y).subgroupOf Y := by
      ext x
      simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hx
        refine ⟨fun p hp => ?_, x.2⟩
        have := hx ⟨p, hPY hp⟩ hp
        exact congrArg Subtype.val this
      · rintro ⟨hx, -⟩ p hp
        exact Subtype.ext (hx p hp)
    rw [hcen]
    have hKX : K ≤ centralizer (P : Set H) ⊓ Y := le_inf hK.1 hKY
    exact isCompIn_subgroupOf (isCompIn_of_le hK hKX inf_le_left) inf_le_right

theorem stdBare_subgroupOf_of_stdModulo {Y Z K : Subgroup H} (hZ : Z = ⊥) (h : StdModulo Y Z K) :
    StdBare (K.subgroupOf Y) := by
  subst hZ
  obtain ⟨hN, hstd⟩ := h
  have hbot : (⊥ : Subgroup H).subgroupOf Y = ⊥ := Subgroup.bot_subgroupOf Y
  let e : (↥Y ⧸ (⊥ : Subgroup H).subgroupOf Y) ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have he : ∀ y : ↥Y, e (QuotientGroup.mk y) = y := fun y => rfl
  have h1 := stdBare_map_mulEquiv e hstd
  have hmap : ((K.subgroupOf Y).map (QuotientGroup.mk' ((⊥ : Subgroup H).subgroupOf Y))).map
      e.toMonoidHom = K.subgroupOf Y := by
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa [he] using hy
    · intro hx
      exact ⟨_, ⟨x, hx, rfl⟩, he x⟩
  rwa [hmap] at h1

end Components

end CFSG.EvenSporadicStandard.Induction
