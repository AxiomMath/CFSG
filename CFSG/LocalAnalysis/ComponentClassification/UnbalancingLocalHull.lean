module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSection
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalCoreSurvival
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def oddCentralizerMeet (x y : G) : Subgroup G :=
  (pPrimeCore 2 (centralizer ({y} : Set G))).map (centralizer ({y} : Set G)).subtype ⊓
    centralizer ({x} : Set G)

@[expose] def hull (L : Subgroup G) (y : G) (D : Subgroup G) : Subgroup G :=
  L ⊔ zpowers y ⊔ D

theorem le_hull_left (L : Subgroup G) (y : G) (D : Subgroup G) : L ≤ hull L y D :=
  le_sup_left.trans le_sup_left

theorem mem_hull_elem (L : Subgroup G) (y : G) (D : Subgroup G) : y ∈ hull L y D :=
  mem_sup_left (mem_sup_right (mem_zpowers y))

theorem le_hull_right (L : Subgroup G) (y : G) (D : Subgroup G) : D ≤ hull L y D :=
  le_sup_right

theorem le_normalizer_of_commutator_le {L X : Subgroup G} (h : ⁅L, X⁆ ≤ L) :
    X ≤ normalizer (L : Set G) := by
  refine SmallLocal.le_normalizer_of_conj_mem fun g hg l hl => ?_
  have hc : ⁅l⁻¹, g⁆ ∈ L := h (commutator_mem_commutator (inv_mem hl) hg)
  have heq : g * l * g⁻¹ = l * ⁅l⁻¹, g⁆ := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact mul_mem hl hc

theorem hull_normal {L D : Subgroup G} {y : G} (hLy : ⁅L, zpowers y⁆ ≤ L)
    (hLD : ⁅L, D⁆ ≤ L) : (L.subgroupOf (hull L y D)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (le_hull_left L y D)).mpr
    (sup_le (sup_le le_normalizer (le_normalizer_of_commutator_le hLy))
      (le_normalizer_of_commutator_le hLD))

abbrev hullSection (L H : Subgroup G) : Type _ :=
  L.subgroupOf H ⧸ centralPreimage (pPrimeCore 2 (L.subgroupOf H))

@[expose] def hullAction (L : Subgroup G) (y : G) (D : Subgroup G) (hLy : ⁅L, zpowers y⁆ ≤ L)
    (hLD : ⁅L, D⁆ ≤ L) : hull L y D →* MulAut (hullSection L (hull L y D)) :=
  haveI := hull_normal hLy hLD
  conjQuotAction (L.subgroupOf (hull L y D))
    (centralPreimage (pPrimeCore 2 (L.subgroupOf (hull L y D))))

theorem commutator_eq_of_map_subtype {H : Subgroup G} {A B : Subgroup H}
    (h : ⁅A.map H.subtype, B.map H.subtype⁆ = A.map H.subtype) : ⁅A, B⁆ = A := by
  apply map_injective H.subtype_injective
  rw [map_commutator, h]

theorem map_subtype_subgroupOf {L H : Subgroup G} (h : L ≤ H) :
    (L.subgroupOf H).map H.subtype = L := by
  rw [subgroupOf_map_subtype, inf_eq_left.mpr h]

theorem hull_commutator_elem {L D : Subgroup G} {y : G} (hLy : ⁅L, zpowers y⁆ = L) :
    ⁅L.subgroupOf (hull L y D), zpowers (⟨y, mem_hull_elem L y D⟩ : hull L y D)⁆ =
      L.subgroupOf (hull L y D) := by
  apply commutator_eq_of_map_subtype
  rw [map_subtype_subgroupOf (le_hull_left L y D), MonoidHom.map_zpowers]
  exact hLy

theorem hull_commutator_right {L D : Subgroup G} {y : G} (hLD : ⁅L, D⁆ = L) :
    ⁅L.subgroupOf (hull L y D), D.subgroupOf (hull L y D)⁆ = L.subgroupOf (hull L y D) := by
  apply commutator_eq_of_map_subtype
  rw [map_subtype_subgroupOf (le_hull_left L y D), map_subtype_subgroupOf (le_hull_right L y D)]
  exact hLD

theorem mem_centralizer_singleton {g h : G} : h ∈ centralizer ({g} : Set G) ↔ h * g = g * h :=
  mem_centralizer_singleton_iff

theorem hull_le_centralizer {x y : G} (hxy : x * y = y * x) {L : Subgroup G}
    (hLx : L ≤ centralizer ({x} : Set G)) :
    hull L y (oddCentralizerMeet x y) ≤ centralizer ({x} : Set G) :=
  sup_le (sup_le hLx (zpowers_le.mpr (mem_centralizer_singleton.mpr hxy.symm))) inf_le_right

theorem centralizer_lt_top {x : G} (hxZ : x ∉ center G) : centralizer ({x} : Set G) < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun htop => hxZ (mem_center_iff.mpr fun g => ?_)
  have hg : g ∈ centralizer ({x} : Set G) := htop ▸ mem_top g
  exact mem_centralizer_singleton.mp hg

theorem oddCentralizerMeet_le (x y : G) : oddCentralizerMeet x y ≤ centralizer ({y} : Set G) :=
  inf_le_left.trans (map_subtype_le _)

theorem coprime_card_oddCentralizerMeet [Finite G] (x y : G) :
    Nat.Coprime 2 (Nat.card (oddCentralizerMeet x y)) := by
  have h1 : Nat.card (oddCentralizerMeet x y) ∣
      Nat.card (pPrimeCore 2 (centralizer ({y} : Set G))) := by
    rw [← card_map_of_injective (centralizer ({y} : Set G)).subtype_injective]
    exact card_dvd_of_le inf_le_left
  exact (pPrimeCore_coprime_card (p := 2) (G := centralizer ({y} : Set G))).coprime_dvd_right h1

theorem conj_mem_oddCentralizerMeet {x y g d : G} (hgx : g ∈ centralizer ({x} : Set G))
    (hgy : g ∈ centralizer ({y} : Set G)) (hd : d ∈ oddCentralizerMeet x y) :
    g * d * g⁻¹ ∈ oddCentralizerMeet x y := by
  obtain ⟨hdD, hdx⟩ := mem_inf.mp hd
  obtain ⟨d', hd', rfl⟩ := hdD
  refine mem_inf.mpr ⟨⟨⟨g, hgy⟩ * d' * ⟨g, hgy⟩⁻¹, ?_, rfl⟩, ?_⟩
  · exact (pPrimeCore_normal (p := 2) (G := centralizer ({y} : Set G))).conj_mem d' hd' _
  · exact mul_mem (mul_mem hgx hdx) (inv_mem hgx)

theorem hull_quasisimple [Finite G] {x : G} {L H : Subgroup G} (hLx : L ≤ centralizer ({x} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set G)))) (hLH : L ≤ H) :
    IsQuasisimple (L.subgroupOf H ⧸ pPrimeCore 2 (L.subgroupOf H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hL
  exact CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2
    ((subgroupOfEquivOfLe hLx).trans (subgroupOfEquivOfLe hLH).symm) h

end CFSG.ComponentClassification.UnbalancingLocal
