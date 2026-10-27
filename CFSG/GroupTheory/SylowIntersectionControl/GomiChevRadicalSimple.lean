module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.PCoreOfCentralQuotient
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.GroupTheory.OppositeRadicals
import CFSG.LieType.BorelTits.CentralQuotient

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)

private theorem map_subtype_centralizer_eq_inf {G : Type} [Group G] (H : Subgroup G)
    (A : Subgroup H) : (centralizer (A : Set H)).map H.subtype =
      H ⊓ centralizer ((A.map H.subtype : Subgroup G) : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx a ha)
  · rintro x ⟨hxH, hx⟩
    refine ⟨⟨x, hxH⟩, mem_centralizer_iff.mpr fun a ha => ?_, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.mp hx a ⟨a, ha, rfl⟩)

private theorem twoResidual_map_le_map {G G' : Type} [Group G] [Group G'] [Finite G]
    (f : G →* G') (H : Subgroup G) : twoResidual (H.map f) ≤ (twoResidual H).map f :=
  twoResidual_le_of_isTwoQuotient (map_mono (twoResidual_le H))
    ((map_mono (le_normalizer_twoResidual H)).trans (le_normalizer_map f)) (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H x hx
      exact ⟨k, by rw [← map_pow]; exact mem_map_of_mem f hk⟩)

@[expose] def ChevParabolicRadicalSimple (K : Type) [Group K] : Prop :=
  ∀ (S : Sylow 2 K) (P : Subgroup K), normalizer ((S : Subgroup K) : Set K) ≤ P → P ≠ ⊤ →
    pCoreOf 2 P ≠ ⊥ ∧ centralizer (pCoreOf 2 P : Set K) ≤ pCoreOf 2 P

@[expose] def GomiChevRadicalTop (X : Type) [Group X] : Prop :=
  ∀ (S : Sylow 2 X) (P : Subgroup X), normalizer ((S : Subgroup X) : Set X) ≤ P → P ≠ ⊤ →
    pCoreOf 2 P ≠ ⊥ ∧ twoResidual (centralizer (pCoreOf 2 P : Set X)) ≤ center X

theorem gomiChevRadical_of_top
    (h : ∀ (X : Type) [Group X] [Finite X], IsGomiChevTwo X → GomiChevRadicalTop X) :
    GomiChevRadical := by
  intro G _ _ L U P hL hU hUP hPL
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
  have hN : normalizer ((Q : Subgroup L) : Set L) ≤ P.subgroupOf L := by
    rw [hQ, ← subgroupOf_normalizer_eq hU.le]
    exact fun x hx => mem_subgroupOf.2 (hUP ⟨x.2, mem_subgroupOf.1 hx⟩)
  have hPt : P.subgroupOf L ≠ ⊤ := fun h' => hPL.not_ge (subgroupOf_eq_top.1 h')
  obtain ⟨h1, h2⟩ := h L hL Q (P.subgroupOf L) hN hPt
  have hO : pCoreOf 2 P = (pCoreOf 2 (P.subgroupOf L)).map L.subtype := by
    rw [← pCoreOf_map_of_injective 2 L.subtype L.subtype_injective (P.subgroupOf L),
      subgroupOf_map_subtype, inf_of_le_left hPL.le]
  refine ⟨?_, ?_⟩
  · rw [hO, Ne, map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact h1
  · rw [hO, ← map_subtype_centralizer_eq_inf, ← CFSG.center_map_subtype_eq_inf_centralizer]
    exact (twoResidual_map_le_map _ _).trans (map_mono h2)

theorem gomiChevRadicalTop_of_quotient_center {X : Type} [Group X] [Finite X]
    (hZ : Nat.Coprime (Nat.card (center X)) 2)
    (h : ChevParabolicRadicalSimple (X ⧸ center X)) : GomiChevRadicalTop X := by
  intro S P hSP hP
  have hπ := QuotientGroup.mk'_surjective (center X)
  have hZP : center X ≤ P := (center_le_normalizer _).trans hSP
  have hN : normalizer (((S.mapSurjective hπ : Sylow 2 (X ⧸ center X)) :
      Subgroup (X ⧸ center X)) : Set (X ⧸ center X)) ≤
      P.map (QuotientGroup.mk' (center X)) := by
    rw [Sylow.coe_mapSurjective, ← map_comap_eq_self_of_surjective hπ (normalizer _),
      ← LieType.BorelTits.normalizer_eq_comap_normalizer_map (center X) le_rfl hZ S.isPGroup']
    exact map_mono hSP
  have hPt : P.map (QuotientGroup.mk' (center X)) ≠ ⊤ := by
    intro h'
    apply hP
    rw [← comap_map_eq_self ((QuotientGroup.ker_mk' _).le.trans hZP), h', comap_top]
  obtain ⟨h1, h2⟩ := h _ _ hN hPt
  rw [pCoreOf_map_mk'_eq_of_le le_rfl hZ hZP] at h1 h2
  refine ⟨fun h0 => h1 (by rw [h0, Subgroup.map_bot]), ?_⟩
  exact twoResidual_centralizer_le_of_isPGroup_centralizer_map (center X)
    (((LieType.BorelTits.pCoreOf_isPGroup 2 P).map _).to_le h2)

theorem gomiChevRadical_of_simple
    (h : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → IsChevTwo K →
      ChevParabolicRadicalSimple K) :
    GomiChevRadical :=
  gomiChevRadical_of_top fun _ _ _ hX => gomiChevRadicalTop_of_quotient_center
    hX.coprime_card_center (h _ hX.isSimpleGroup hX.isChevTwo)

end CFSG.GroupTheory
