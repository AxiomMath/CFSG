module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoNormalHullClass
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoNormalHullData

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem involution_mem_normal_subgroup_of_odd_index (L : Subgroup G) [L.Normal]
    (hindex : Odd L.index) (x : G) (hx : orderOf x = 2) : x ∈ L := by
  let q := QuotientGroup.mk' L
  have hodd : Odd (Nat.card (G ⧸ L)) := by
    rw [← L.index_eq_card]
    exact hindex
  have hdiv : orderOf (q x) ∣ 2 := hx ▸ orderOf_map_dvd q x
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
  · exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hone)
  · exact (hodd.not_two_dvd_nat (htwo ▸ orderOf_dvd_natCard (q x))).elim

theorem strong_embedding_of_normal_odd_index_factorization
    (H L : Subgroup G) [L.Normal] (hindex : Odd L.index)
    (hfactor : ∀ g : G, ∃ h ∈ H, ∃ l ∈ L, g = h * l)
    (hM : fusionStronglyEmbedded (H.subgroupOf L)) : fusionStronglyEmbedded H := by
  let M := H.subgroupOf L
  have hproper : H ≠ ⊤ := by
    intro htop
    apply hM.1
    ext x
    change (x : G) ∈ H ↔ True
    rw [htop]
    simp
  have hmap : M.map L.subtype ≤ H := by
    rintro x ⟨l, hl, rfl⟩
    exact hl
  have heven : Even (Nat.card H) := even_iff_two_dvd.mpr (by
    have hcard : Nat.card (M.map L.subtype) = Nat.card M :=
      Subgroup.card_map_of_injective L.subtype_injective
    exact (hcard ▸ hM.2.1.two_dvd).trans (Subgroup.card_dvd_of_le hmap))
  refine ⟨hproper, heven, ?_⟩
  intro g hg
  apply Nat.not_even_iff_odd.mp
  intro hEven
  let I := H ⊓ rightConjugate H g
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 hEven.two_dvd
  have hwG : orderOf (w : G) = 2 := (Subgroup.orderOf_coe w).trans hw
  have hwL : (w : G) ∈ L := involution_mem_normal_subgroup_of_odd_index L hindex w hwG
  obtain ⟨h, hh, l, hl, hgl⟩ := hfactor g
  let lL : L := ⟨l, hl⟩
  let wL : L := ⟨w, hwL⟩
  have hloutside : lL ∉ M := by
    intro hlH
    apply hg
    rw [hgl]
    exact H.mul_mem hh hlH
  have hwback : g * (w : G) * g⁻¹ ∈ H :=
    (mem_rightConjugate_iff H g w).mp w.property.2
  have hwconj : l * (w : G) * l⁻¹ ∈ H := by
    have hmem := H.mul_mem (H.mul_mem (H.inv_mem hh) hwback) hh
    rw [hgl] at hmem
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hmem
  have hwI : wL ∈ M ⊓ rightConjugate M lL := by
    refine ⟨w.property.1, ?_⟩
    apply (mem_rightConjugate_iff M lL wL).mpr
    exact hwconj
  have horder : orderOf wL = 2 := (Subgroup.orderOf_coe wL).symm.trans hwG
  exact (hM.2.2 lL hloutside).not_two_dvd_nat
    (horder ▸ Subgroup.orderOf_dvd_natCard (M ⊓ rightConjugate M lL) hwI)

theorem normalizer_index_odd (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q) :
    Odd (Subgroup.normalizer (Q : Set G)).index := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, _z, _hzQ, _hz, hPH, _hcenter, _hNP⟩ :=
    exists_central_sylow_involution_in_Q Q htight hodd
  have hPindex : Odd (P : Subgroup G).index :=
    Nat.not_even_iff_odd.mp (fun hEven => P.not_dvd_index hEven.two_dvd)
  exact hPindex.of_dvd_nat (Subgroup.index_dvd_of_le hPH)

theorem normal_hull_normalizer_index_odd (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q) :
    Odd ((Subgroup.normalizer (Q : Set G)).subgroupOf
      (Subgroup.normalClosure (Q : Set G))).index := by
  rw [← normal_hull_Q_normalizer Q htight hodd]
  exact normalizer_index_odd
    (Q.subgroupOf (Subgroup.normalClosure (Q : Set G)))
    (normal_hull_Q_tightly_embedded Q htight hodd)
    (normal_hull_Q_odd_normalizer_overlaps Q htight hodd)

theorem normal_hull_strong_embedding_of_point_hull_odd_index
    (Q : Subgroup G) (_htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (hindex :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      Odd (involutionPointHull zJ).index)
    (hM :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      fusionStronglyEmbedded
        (((Subgroup.normalizer (Q : Set G)).subgroupOf J).subgroupOf
          (involutionPointHull zJ))) :
    fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf
        (Subgroup.normalClosure (Q : Set G))) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let L := involutionPointHull zJ
  let H := (Subgroup.normalizer (Q : Set G)).subgroupOf J
  let : L.Normal := by
    dsimp only [L]
    rw [tightly_embedded_point_hull_eq_normalClosure]
    infer_instance
  have hfactor : ∀ g : J, ∃ h ∈ H, ∃ l ∈ L, g = h * l := by
    intro g
    have hg := g.property
    change (g : G) ∈ (Subgroup.normalClosure (Q : Set G) : Set G) at hg
    rw [normalClosure_eq_Q_mul_point_hull Q hodd z hzQ hz] at hg
    obtain ⟨q, hq, l, hl, hql⟩ := Set.mem_mul.mp hg
    let qJ : J := ⟨q, Subgroup.le_normalClosure hq⟩
    let lJ : J := ⟨l, point_hull_le_normal_hull Q z hzQ hl⟩
    have hlL : lJ ∈ L := by
      rw [show L = (involutionPointHull z).subgroupOf J from
        normal_hull_point_hull_eq Q hodd hnormal z hzQ hz]
      exact hl
    exact ⟨qJ, Subgroup.le_normalizer hq, lJ, hlL, Subtype.ext hql.symm⟩
  exact strong_embedding_of_normal_odd_index_factorization H L hindex hfactor hM

end CFSG.ComponentClassification.AschbacherTightEmbedding
