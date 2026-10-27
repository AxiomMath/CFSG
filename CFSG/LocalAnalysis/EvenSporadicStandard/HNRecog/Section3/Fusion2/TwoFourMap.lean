module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup
open scoped commutatorElement

private lemma derivedOf_map_of_injective {H G : Type} [Group H] [Group G]
    (ι : H →* G) (K : Subgroup H) :
    derivedOf (K.map ι) = (derivedOf K).map ι := by
  rw [show derivedOf (K.map ι) = ⁅K.map ι, K.map ι⁆ from
        Subgroup.map_subtype_commutator (K.map ι),
      show derivedOf K = ⁅K, K⁆ from Subgroup.map_subtype_commutator K,
      Subgroup.map_commutator]

private lemma pCoreOf_map_of_injective {H G : Type} [Group H] [Group G]
    (ι : H →* G) (hι : Function.Injective ι) (K : Subgroup H) :
    CFSG.Open.pCoreOf 2 (K.map ι) = (CFSG.Open.pCoreOf 2 K).map ι := by
  let e : ↥K ≃* ↥(K.map ι) := Subgroup.equivMapOfInjective K ι hι
  have he : (K.map ι).subtype.comp e.toMonoidHom = ι.comp K.subtype := by
    ext x; rfl
  rw [CFSG.Open.pCoreOf, CFSG.Open.pCoreOf, Subgroup.map_map,
    ← CFSG.pCore_map_iso 2 e, Subgroup.map_map, he]

private lemma natCard_derivedOf_map {H G : Type} [Group H] [Group G]
    (ι : H →* G) (hι : Function.Injective ι) (K : Subgroup H) :
    Nat.card ↥(derivedOf (K.map ι)) = Nat.card ↥(derivedOf K) := by
  rw [derivedOf_map_of_injective ι K]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective (derivedOf K) ι hι).toEquiv).symm

theorem Gxy_eq_map_Gx {G : Type} [Group G] {a : G} (u : ↥(Gx a)) :
    Gxy a (u : G) = (Gx u).map (Gx a).subtype := by
  ext g
  rw [mem_Gxy]
  constructor
  · rintro ⟨hga, hgu⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, hga⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : (u : G) * g = g * (u : G) := mem_Gx.mp hgu
      exact Subtype.ext hcomm.symm, rfl⟩
  · intro hg
    obtain ⟨h, hh, hhg⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hh
    refine ⟨?_, ?_⟩
    · rw [← hhg]; exact h.2
    · rw [mem_Gx, ← hhg]
      exact (congrArg Subtype.val hh).symm

theorem twoFourData_Gxy {G : Type} [Group G] {a : G} {u : ↥(Gx a)} (h : TwoFourData (Gx u)) :
    TwoFourData (Gxy a (u : G)) := by
  rw [Gxy_eq_map_Gx u]
  refine ⟨?_, ?_, ?_⟩
  · rw [natCard_derivedOf_map (Gx a).subtype Subtype.coe_injective (Gx u), h.card_derived]
  · rw [derivedOf_map_of_injective (Gx a).subtype (Gx u),
        pCoreOf_map_of_injective (Gx a).subtype Subtype.coe_injective (derivedOf (Gx u))]
    exact isElemTwo_map (Gx a).subtype Subtype.coe_injective h.elem_two
  · intro S hS hSinv
    have hSle_X : S ≤ (Gx u).map (Gx a).subtype := by
      refine hS.trans ?_
      exact (Subgroup.map_subtype_le
        (pCore 2 ↥(derivedOf ((Gx u).map (Gx a).subtype)))).trans
          (derivedOf_le ((Gx u).map (Gx a).subtype))
    let S' : Subgroup ↥(Gx a) := S.comap (Gx a).subtype
    have hS'map : S'.map (Gx a).subtype = S :=
      Subgroup.map_comap_eq_self
        (hSle_X.trans (Subgroup.map_le_range (Gx a).subtype (Gx u)))
    have hSle : S ≤ (CFSG.Open.pCoreOf 2 (derivedOf (Gx u))).map (Gx a).subtype := by
      rw [← pCoreOf_map_of_injective (Gx a).subtype Subtype.coe_injective (derivedOf (Gx u)),
        ← derivedOf_map_of_injective (Gx a).subtype (Gx u)]
      exact hS
    have hS'le : S' ≤ CFSG.Open.pCoreOf 2 (derivedOf (Gx u)) := by
      have h1 : S' ≤ ((CFSG.Open.pCoreOf 2 (derivedOf (Gx u))).map
          (Gx a).subtype).comap (Gx a).subtype := Subgroup.comap_mono hSle
      rwa [Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective] at h1
    have hS'inv : ∀ g ∈ Gx u, ∀ s ∈ S', g * s * g⁻¹ ∈ S' := by
      intro g hg s hs
      rw [Subgroup.mem_comap] at hs ⊢
      have hgX : (g : G) ∈ (Gx u).map (Gx a).subtype :=
        Subgroup.mem_map_of_mem (Gx a).subtype hg
      simpa using hSinv (g : G) hgX (s : G) hs
    rcases h.irreducible S' hS'le hS'inv with hbot | htop
    · left
      rw [← hS'map, hbot, Subgroup.map_bot]
    · right
      rw [← hS'map, htop,
        ← pCoreOf_map_of_injective (Gx a).subtype Subtype.coe_injective (derivedOf (Gx u)),
        ← derivedOf_map_of_injective (Gx a).subtype (Gx u)]

end CFSG.EvenSporadicStandard.HNRecog.Section3
