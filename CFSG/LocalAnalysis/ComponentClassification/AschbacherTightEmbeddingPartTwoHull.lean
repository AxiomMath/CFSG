module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoData
public import CFSG.LocalAnalysis.ComponentClassification.OddIndexSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoStrongEmbedding

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G] [Finite G]

theorem involution_conjugate_into_odd_index_subgroup (Q L : Subgroup G)
    (hQL : Q ≤ L) (hindex : Odd (Q.subgroupOf L).index)
    (v : G) (hvL : v ∈ L) (hv : orderOf v = 2) :
    ∃ a : L, (a : G) * v * (a : G)⁻¹ ∈ Q := by
  let vL : L := ⟨v, hvL⟩
  have hvLorder : orderOf vL = 2 := (Subgroup.orderOf_coe vL).symm.trans hv
  have htwo : IsPGroup 2 (Subgroup.zpowers vL) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hvLorder, pow_one])
  obtain ⟨P, hP⟩ := htwo.exists_le_sylow
  let D : Sylow 2 Q := default
  obtain ⟨S, hS⟩ := OddIndexSylow.nested Q L hQL hindex D
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq L P S
  have hvS : (MulAut.conj a) vL ∈ (S : Subgroup L) := by
    rw [← ha]
    exact Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom
      (hP (Subgroup.mem_zpowers vL))
  have hmem : ((MulAut.conj a) vL : G) ∈ (S : Subgroup L).map L.subtype :=
    Subgroup.mem_map_of_mem L.subtype hvS
  rw [hS] at hmem
  exact ⟨a, sylowImage_le Q D hmem⟩

theorem hull_involution_mem_normalizer_iff_mem_Q (Q L : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hQL : Q ≤ L)
    (hindex : Odd (Q.subgroupOf L).index) (v : G)
    (hvL : v ∈ L) (hv : orderOf v = 2) :
    v ∈ Subgroup.normalizer (Q : Set G) ↔ v ∈ Q := by
  constructor
  · intro hvH
    obtain ⟨a, ha⟩ := involution_conjugate_into_odd_index_subgroup Q L hQL hindex v hvL hv
    let w : G := (a : G) * v * (a : G)⁻¹
    have hw : orderOf w = 2 := ((MulAut.conj (a : G)).orderOf_eq v).trans hv
    have hback : (a : G)⁻¹ * w * (a : G) = v := by
      dsimp only [w]
      group
    have haH : (a : G) ∈ Subgroup.normalizer (Q : Set G) :=
      (involution_conjugate_mem_normalizer_iff Q hodd w ha hw a).mp (hback ▸ hvH)
    have hbackQ := (involution_conjugate_mem_Q_iff Q hodd w ha hw a).mpr haH
    rwa [hback] at hbackQ
  · intro hvQ
    exact Subgroup.le_normalizer hvQ

theorem normal_hull_normalizer_proper (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) :
    (Subgroup.normalizer (Q : Set G)).subgroupOf (Subgroup.normalClosure (Q : Set G)) ≠ ⊤ := by
  let H := Subgroup.normalizer (Q : Set G)
  let L := Subgroup.normalClosure (Q : Set G)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2
    (even_iff_two_dvd.mp htight.1)
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  intro htop
  apply hnormal
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  have hzL : (z : G) ∈ L := Subgroup.le_normalClosure z.property
  have hconjL : g⁻¹ * (z : G) * g ∈ L := by
    simpa only [inv_inv] using (inferInstance : L.Normal).conj_mem (z : G) hzL g⁻¹
  have hconjH : g⁻¹ * (z : G) * g ∈ H := by
    have hmem : (⟨g⁻¹ * (z : G) * g, hconjL⟩ : L) ∈ H.subgroupOf L :=
      htop ▸ Subgroup.mem_top _
    exact hmem
  exact (involution_conjugate_mem_normalizer_iff Q hodd z z.property hzG g).mp hconjH

theorem normal_hull_strong_embedding_of_odd_relative_index (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal)
    (hindex : Odd (Q.subgroupOf (Subgroup.normalClosure (Q : Set G))).index) :
    fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (Subgroup.normalClosure (Q : Set G))) := by
  let H := Subgroup.normalizer (Q : Set G)
  let L := Subgroup.normalClosure (Q : Set G)
  let B : Subgroup L := H.subgroupOf L
  have hQL : Q ≤ L := Subgroup.le_normalClosure
  let D : Sylow 2 Q := default
  obtain ⟨S, hS⟩ := OddIndexSylow.nested Q L hQL hindex D
  have hSQ : (S : Subgroup L).map L.subtype ≤ Q := by
    rw [hS]
    exact sylowImage_le Q D
  have hSB : (S : Subgroup L) ≤ B := fun _ hs => Subgroup.le_normalizer
    (hSQ (Subgroup.mem_map_of_mem L.subtype hs))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2
    (even_iff_two_dvd.mp htight.1)
  have hzL : (z : G) ∈ L := hQL z.property
  let zL : L := ⟨z, hzL⟩
  have hzLorder : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans
    ((Subgroup.orderOf_coe z).trans hz)
  have heven : Even (Nat.card B) := even_iff_two_dvd.mpr
    (hzLorder ▸ Subgroup.orderOf_dvd_natCard B (Subgroup.le_normalizer z.property : zL ∈ B))
  have hNS : Subgroup.normalizer (S : Set L) ≤ B := by
    intro a ha
    obtain ⟨v, hvorder⟩ := exists_prime_orderOf_dvd_card' (G := (D : Subgroup Q)) 2
      (D.dvd_card_of_dvd_card (even_iff_two_dvd.mp htight.1))
    have hvQ : ((v : Q) : G) ∈ Q := (v : Q).property
    have hvGorder : orderOf ((v : Q) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hvorder]
    have hvmap : ((v : Q) : G) ∈ (S : Subgroup L).map L.subtype := by
      rw [hS]
      exact Subgroup.mem_map_of_mem Q.subtype v.property
    obtain ⟨vL, hvS, hvval⟩ := Subgroup.mem_map.mp hvmap
    have hvconj : a⁻¹ * vL * a ∈ (S : Subgroup L) := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem ha) vL).mp hvS
    have hvconjQ : (a : G)⁻¹ * ((v : Q) : G) * (a : G) ∈ Q := by
      rw [← hvval]
      exact hSQ (Subgroup.mem_map_of_mem L.subtype hvconj)
    exact (involution_conjugate_mem_Q_iff Q hodd ((v : Q) : G) hvQ hvGorder a).mp hvconjQ
  have hcentral : ∀ v ∈ B, orderOf v = 2 → Subgroup.centralizer ({v} : Set L) ≤ B := by
    intro v hv hvorder c hc
    have hvGorder : orderOf (v : G) = 2 := (Subgroup.orderOf_coe v).trans hvorder
    have hvQ := (hull_involution_mem_normalizer_iff_mem_Q Q L hodd hQL hindex v
      v.property hvGorder).mp hv
    apply involution_centralizer_le_normalizer Q hodd v hvQ hvGorder
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))
  exact CFSG.ProperTwoGeneratedCore.sylow_normalizer_involution_centralizer_strong_embedding
    B (normal_hull_normalizer_proper Q htight hodd hnormal) heven S hSB hNS hcentral

end CFSG.ComponentClassification.AschbacherTightEmbedding
