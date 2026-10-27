module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

private lemma map_zpowers_subtype_GxSelf {G : Type} [Group G] (z : G) :
    (Subgroup.zpowers (GxSelf z)).map (Gx z).subtype = Subgroup.zpowers z := by
  rw [MonoidHom.map_zpowers]
  rfl

private lemma mem_zpowers_GxSelf_iff {G : Type} [Group G] {z : G} (y : ↥(Gx z)) :
    y ∈ Subgroup.zpowers (GxSelf z) ↔ (y : G) ∈ Subgroup.zpowers z := by
  rw [← map_zpowers_subtype_GxSelf z]
  exact (Subgroup.mem_map_iff_mem (Gx z).subtype_injective).symm

theorem card_centQtilde_eq {G : Type} [Group G] {a z : G} (h : IsF5Type a z) (x : ↥(Gx z)) :
    Nat.card (centQtilde z (x : G)) =
      Nat.card {q : ↥(Gx z) // q ∈ CFSG.pCore 2 ↥(Gx z) ∧
        ⁅q, x⁆ ∈ centerOf (CFSG.pCore 2 ↥(Gx z))} := by
  have hQ := isExtraspecialPlusByA5WrTwoWith_pCore (z := z) h.cent_z
  have hcenter := centerOf_eq_zpowers h.orderOf_z hQ
  let T : Set ↥(Gx z) :=
    {q | q ∈ CFSG.pCore 2 ↥(Gx z) ∧ ⁅q, x⁆ ∈ centerOf (CFSG.pCore 2 ↥(Gx z))}
  have hset : centQtilde z (x : G) = T.image (Gx z).subtype := by
    ext g
    constructor
    · intro hg
      obtain ⟨q, hq, hqg⟩ := Subgroup.mem_map.mp hg.1
      have hqg' : (q : G) = g := hqg
      refine (Set.mem_image (Gx z).subtype T g).mpr ⟨q, ⟨hq, ?_⟩, hqg⟩
      rw [hcenter]
      refine (mem_zpowers_GxSelf_iff ⁅q, x⁆).mpr ?_
      have hcoe : ((⁅q, x⁆ : ↥(Gx z)) : G) = ⁅g, (x : G)⁆ := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hqg']
      rw [hcoe]
      exact hg.2
    · intro hg
      obtain ⟨q, ⟨hq, hcomm⟩, hqg⟩ := (Set.mem_image (Gx z).subtype T g).mp hg
      refine ⟨Subgroup.mem_map.mpr ⟨q, hq, hqg⟩, ?_⟩
      rw [← hqg]
      have hmem := (mem_zpowers_GxSelf_iff ⁅q, x⁆).mp (hcenter ▸ hcomm)
      have hcoe : ((⁅q, x⁆ : ↥(Gx z)) : G) = ⁅(q : G), (x : G)⁆ := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rwa [hcoe] at hmem
  change Nat.card (centQtilde z (x : G)) = Nat.card ↥T
  rw [hset]
  simpa using Set.ncard_image_of_injective T (Gx z).subtype_injective

theorem card_commute_Qz_eq {G : Type} [Group G] {z : G} (x : ↥(Gx z)) :
    Nat.card {q : G // q ∈ Qz z ∧ q * (x : G) = (x : G) * q} =
      Nat.card {q : ↥(Gx z) // q ∈ CFSG.pCore 2 ↥(Gx z) ∧ q * x = x * q} := by
  let T : Set ↥(Gx z) := {q | q ∈ CFSG.pCore 2 ↥(Gx z) ∧ q * x = x * q}
  have hset : {q : G | q ∈ Qz z ∧ q * (x : G) = (x : G) * q} = T.image (Gx z).subtype := by
    ext g
    constructor
    · intro hg
      obtain ⟨q, hq, hqg⟩ := Subgroup.mem_map.mp hg.1
      have hqg' : (q : G) = g := hqg
      refine (Set.mem_image (Gx z).subtype T g).mpr ⟨q, ⟨hq, ?_⟩, hqg⟩
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hqg']
      exact hg.2
    · intro hg
      obtain ⟨q, ⟨hq, hcomm⟩, hqg⟩ := (Set.mem_image (Gx z).subtype T g).mp hg
      refine ⟨Subgroup.mem_map.mpr ⟨q, hq, hqg⟩, ?_⟩
      rw [← hqg]
      simpa [Subgroup.coe_mul] using congrArg (fun t : ↥(Gx z) => (t : G)) hcomm
  change Nat.card ↥{q : G | q ∈ Qz z ∧ q * (x : G) = (x : G) * q} = Nat.card ↥T
  rw [hset]
  simpa using Set.ncard_image_of_injective T (Gx z).subtype_injective

theorem card_Gx_inf_eq {G : Type} [Group G] {z c : G} (hc : c ∈ Gx z) :
    Nat.card ↥(Gx z ⊓ Gx c) =
      Nat.card ↥(Subgroup.centralizer ({(⟨c, hc⟩ : ↥(Gx z))} : Set ↥(Gx z))) := by
  have hset : Gx z ⊓ Gx c =
      (Subgroup.centralizer ({(⟨c, hc⟩ : ↥(Gx z))} : Set ↥(Gx z))).map
        (Gx z).subtype := by
    ext g
    constructor
    · intro hg
      refine Subgroup.mem_map.mpr ⟨⟨g, hg.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact (mem_Gx.mp hg.2).symm
    · intro hg
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← hyg]
        exact y.2
      · rw [mem_Gx]
        have hy' := congrArg (fun t : ↥(Gx z) => (t : G))
          (Subgroup.mem_centralizer_singleton_iff.mp hy)
        rw [← hyg]
        exact hy'.symm
  rw [hset, Subgroup.card_map_of_injective (Gx z).subtype_injective]

theorem commutatorElement_mem_zpowers_of_mem_Qz {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) {y w : G} (hy : y ∈ Qz z) (hw : w ∈ Qz z) :
    ⁅y, w⁆ ∈ Subgroup.zpowers z := by
  obtain ⟨y', hy'Q, hy'eq⟩ := Subgroup.mem_map.mp hy
  obtain ⟨w', hw'Q, hw'eq⟩ := Subgroup.mem_map.mp hw
  have hy'' : (y' : G) = y := hy'eq
  have hw'' : (w' : G) = w := hw'eq
  have hQ := isExtraspecialPlusByA5WrTwoWith_pCore (z := z) h.cent_z
  have hcenter := centerOf_eq_zpowers h.orderOf_z hQ
  have hcomm := commutatorElement_mem_centerOf hQ.plus hy'Q hw'Q
  rw [hcenter] at hcomm
  have hmem := (mem_zpowers_GxSelf_iff ⁅y', w'⁆).mp hcomm
  have hcoe : ((⁅y', w'⁆ : ↥(Gx z)) : G) = ⁅y, w⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hy'', hw'']
  rwa [hcoe] at hmem

end CFSG.EvenSporadicStandard.HNRecog.Section3
