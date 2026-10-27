module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusBalance
public import CFSG.LocalAnalysis.OddStandard.Solomon75Balance

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

variable {G : Type} [Group G]

theorem LPlusIn_map_of_injective {A : Type} [Group A] [Finite A] (K : Subgroup A) (f : A →* G)
    (hf : Function.Injective f) : (LPlusIn K).map f = LPlusIn (K.map f) := by
  let e := Subgroup.equivMapOfInjective K f hf
  have hmap : (LPlus ↥K).map e.toMonoidHom = LPlus ↥(K.map f) := LPlus_map_equiv e
  have hcomp : (K.map f).subtype.comp e.toMonoidHom = f.comp K.subtype := by
    ext x
    rfl
  unfold LPlusIn
  rw [Subgroup.map_map, ← hmap, Subgroup.map_map, hcomp]

theorem map_oTwoPrimeOf_le {A : Type} [Group A] (S : Subgroup A) (f : A →* G) :
    (oTwoPrimeOf S).map f ≤ oTwoPrimeOf (S.map f) := by
  rw [Subgroup.map_le_iff_le_comap, oTwoPrimeOf_le_iff]
  intro x hx h2
  exact mem_oTwoPrimeOf_of_twoElt ⟨x, hx, rfl⟩ (h2.map f)

theorem oTwoPrimeOf_map_le {A : Type} [Group A] (S : Subgroup A) (f : A →* G)
    (hf : Function.Injective f) : oTwoPrimeOf (S.map f) ≤ (oTwoPrimeOf S).map f := by
  rw [oTwoPrimeOf_le_iff]
  rintro _ ⟨a, ha, rfl⟩ h2
  exact ⟨a, mem_oTwoPrimeOf_of_twoElt ha (TwoElt.of_injective hf h2), rfl⟩

theorem map_centralizer_subgroupOf (H B : Subgroup G) (hBH : B ≤ H) :
    (centralizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H)).map H.subtype =
      H ⊓ centralizer (B : Set G) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro b hb
    have := Subgroup.mem_centralizer_iff.mp hc ⟨b, hBH hb⟩ hb
    exact congrArg Subtype.val this
  · rintro ⟨hxH, hx⟩
    refine ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
    intro b hb
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (b : G) hb)

theorem lPlus_balance [Finite G] (H B : Subgroup G) (hBH : B ≤ H) (hB : IsPGroup 2 B) :
    oTwoPrimeOf (LPlusIn (H ⊓ centralizer (B : Set G))) ≤
      oTwoPrimeOf (LPlusIn H) ⊔ oddTwoCoreOf H := by
  have hB' : IsPGroup 2 (B.subgroupOf H) := hB.comap_subtype
  have h := lPlus_balance_top (G := ↥H) (B.subgroupOf H) hB'
  have h1 := Subgroup.map_mono (f := H.subtype) h
  rw [Subgroup.map_sup] at h1
  rw [← map_centralizer_subgroupOf H B hBH,
    ← LPlusIn_map_of_injective _ H.subtype H.subtype_injective]
  refine (oTwoPrimeOf_map_le _ _ H.subtype_injective).trans (h1.trans ?_)
  refine sup_le_sup ?_ le_rfl
  have := map_oTwoPrimeOf_le (LPlus ↥H) H.subtype
  exact this

theorem le_normalizer_LPlusIn [Finite G] (Y : Subgroup G) :
    Y ≤ normalizer ((LPlusIn Y : Subgroup G) : Set G) :=
  Subgroup.le_normalizer.trans
    (normalizer_le_normalizer_map_subtype Y (LPlus ↥Y) fun φ => LPlus_map_aut φ)

theorem layer_balance [Finite G] (B : Subgroup G) (hB : IsPGroup 2 B) :
    (pLayer (centralizer (B : Set G)) 2).map (centralizer (B : Set G)).subtype ≤ pLayer G 2 :=
  ClassicalInvolution.l2PrimeBalance G B hB

end CFSG.OddStandard.Solomon75
