module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStarFactorization

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def triplePointStabilizer (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) : Subgroup G :=
  pairPointStabilizer H beta ⊓ rightCosetStabilizer H (rightCosetTranslate H beta z)

theorem rightCosetTranslate_injective (H : Subgroup G) (g : G) :
    Function.Injective (fun omega : rightCosetSpace H => rightCosetTranslate H omega g) := by
  intro a b hab
  have h := congrArg (fun omega => rightCosetTranslate H omega g⁻¹) hab
  simpa only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] using h

theorem rightCosetTranslate_distinguished_fixed_iff
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (omega : rightCosetSpace H) :
    rightCosetTranslate H omega z = omega ↔ omega = rightCosetMk H 1 := by
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  have hzfix := point_fixed_coset_unique h (e omega)
  have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two h.distinguished_order
  have hbase : e (rightCosetMk H 1) = (QuotientGroup.mk 1 : G ⧸ H) := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  constructor
  · intro hfix
    have hleft := congrArg e hfix
    rw [rightCosetTranslate_inversion, hzinv] at hleft
    apply e.injective
    exact (hzfix.mp hleft).trans hbase.symm
  · intro homega
    apply e.injective
    rw [rightCosetTranslate_inversion, hzinv]
    apply hzfix.mpr
    rw [homega, hbase]

theorem triple_point_cosets_distinct
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1) :
    beta ≠ rightCosetMk H 1 ∧
      rightCosetTranslate H beta z ≠ beta ∧
      rightCosetTranslate H beta z ≠ rightCosetMk H 1 := by
  refine ⟨hbeta, fun hfix => hbeta ((rightCosetTranslate_distinguished_fixed_iff h beta).mp hfix),
    ?_⟩
  intro hbase
  apply hbeta
  apply rightCosetTranslate_injective H z
  exact hbase.trans ((rightCosetTranslate_distinguished_fixed_iff h
    (rightCosetMk H 1)).mpr rfl).symm

theorem pair_z_centralizer_le_triple
    (H : Subgroup G) (z : G) (beta : rightCosetSpace H) :
    pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) ≤
      triplePointStabilizer H z beta := by
  intro c hc
  refine ⟨hc.1, (mem_rightCosetStabilizer_iff H (rightCosetTranslate H beta z) c).mpr ?_⟩
  have hfix : rightCosetTranslate H beta c = beta :=
    (mem_rightCosetStabilizer_iff H beta c).mp hc.1.2
  have hcomm : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  rw [rightCosetTranslate_mul, ← hcomm, ← rightCosetTranslate_mul, hfix]

theorem pair_stabilizer_eq_z_centralizer_mul_odd_core [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (pairPointStabilizer H beta : Set G) =
      (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
        (pairOddCore H beta : Set G) := by
  have hfactor := point_subgroup_eq_centralizer_mul_inverted_set h S hzS hzcenter hbeta ht
  have hJB := (pairOddCore_le H beta t).1
  ext b
  constructor
  · intro hb
    have hbH : b ∈ (H : Set G) := pairPointStabilizer_le_point H beta hb
    rw [hfactor] at hbH
    obtain ⟨c, hc, i, hi, hci⟩ := Set.mem_mul.mp hbH
    have hiJ : i ∈ pairOddCore H beta := hi.1
    have hcB : c ∈ pairPointStabilizer H beta := by
      have hmem := (pairPointStabilizer H beta).mul_mem hb
        ((pairPointStabilizer H beta).inv_mem (hJB hiJ))
      rw [← hci] at hmem
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hmem
    exact Set.mem_mul.mpr ⟨c, ⟨hcB, hc⟩, i, hiJ, hci⟩
  · intro hb
    obtain ⟨c, hc, j, hj, rfl⟩ := Set.mem_mul.mp hb
    exact (pairPointStabilizer H beta).mul_mem hc.1 (hJB hj)

theorem pair_stabilizer_eq_odd_core_mul_triple [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (pairPointStabilizer H beta : Set G) =
      (pairOddCore H beta : Set G) * (triplePointStabilizer H z beta : Set G) := by
  have hfactor := pair_stabilizer_eq_z_centralizer_mul_odd_core h S hzS hzcenter hbeta ht
  have hJB := (pairOddCore_le H beta t).1
  ext b
  constructor
  · intro hb
    have hbinv : b⁻¹ ∈ (pairPointStabilizer H beta : Set G) :=
      (pairPointStabilizer H beta).inv_mem hb
    rw [hfactor] at hbinv
    obtain ⟨c, hc, j, hj, hprod⟩ := Set.mem_mul.mp hbinv
    refine Set.mem_mul.mpr ⟨j⁻¹, (pairOddCore H beta).inv_mem hj,
      c⁻¹, (triplePointStabilizer H z beta).inv_mem
        (pair_z_centralizer_le_triple H z beta hc), ?_⟩
    have h := congrArg Inv.inv hprod
    simpa only [mul_inv_rev, inv_inv] using h
  · intro hb
    obtain ⟨j, hj, e, he, rfl⟩ := Set.mem_mul.mp hb
    exact (pairPointStabilizer H beta).mul_mem (hJB hj) he.1

theorem odd_core_image_le_of_full_odd_core_cover [Finite G]
    (E : Subgroup G) (hcover : oddCore G ⊔ E = ⊤) :
    (oddCore E).map E.subtype ≤ oddCore G := by
  let V : Subgroup G := (oddCore E).map E.subtype
  let : (oddCore E).Normal := inferInstance
  have hEV : E ≤ Subgroup.normalizer (V : Set G) := by
    intro e he
    apply Subgroup.le_normalizer_map E.subtype
    apply Subgroup.mem_map_of_mem E.subtype (x := (⟨e, he⟩ : E))
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hEN : E ≤ Subgroup.normalizer ((V ⊔ oddCore G : Subgroup G) : Set G) :=
    hEV.trans Subgroup.normalizer_le_normalizer_sup_normal
  have hJN : oddCore G ≤ Subgroup.normalizer ((V ⊔ oddCore G : Subgroup G) : Set G) :=
    le_sup_right.trans Subgroup.le_normalizer
  have hnormal : (V ⊔ oddCore G).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hcover]
    exact sup_le hJN hEN
  have hVodd : Odd (Nat.card V) := by
    change Odd (Nat.card ((oddCore E).map E.subtype))
    rw [Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card E
  have hodd : Odd (Nat.card (V ⊔ oddCore G : Subgroup G)) := by
    rw [sup_comm]
    exact CFSG.ComponentClassification.OddCore.odd_card_sup _ _
      (CFSG.ComponentClassification.OddCore.odd_card G) hVodd
  exact le_sup_left.trans
    (CFSG.ComponentClassification.OddCore.maximal G _ hnormal hodd)

theorem triple_odd_core_le_pair_odd_core [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype ≤ pairOddCore H beta := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let EB := E.subgroupOf B
  have hEB : E ≤ B := inf_le_left
  let e : EB ≃* E := Subgroup.subgroupOfEquivOfLe hEB
  have hcover : oddCore B ⊔ EB = ⊤ := by
    apply top_unique
    intro b _
    have hb : (b : G) ∈ (pairPointStabilizer H beta : Set G) := b.property
    rw [pair_stabilizer_eq_odd_core_mul_triple h S hzS hzcenter hbeta ht] at hb
    obtain ⟨j, hj, a, ha, hja⟩ := Set.mem_mul.mp hb
    obtain ⟨jB, hjB, hjval⟩ := Subgroup.mem_map.mp hj
    change (jB : G) = j at hjval
    let aB : B := ⟨a, hEB ha⟩
    have haEB : aB ∈ EB := ha
    have hbprod : b = jB * aB := by
      apply Subtype.ext
      change (b : G) = (jB : G) * a
      rw [hjval]
      exact hja.symm
    rw [hbprod]
    exact (oddCore B ⊔ EB).mul_mem
      ((show oddCore B ≤ oddCore B ⊔ EB from le_sup_left) hjB)
      ((show EB ≤ oddCore B ⊔ EB from le_sup_right) haEB)
  have hcore := odd_core_image_le_of_full_odd_core_cover EB hcover
  have hmap : (oddCore EB).map e.toMonoidHom = oddCore E :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hhom : B.subtype.comp EB.subtype = E.subtype.comp e.toMonoidHom := by
    ext a
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom, e]
      using (Subgroup.subgroupOfEquivOfLe_apply_coe hEB a).symm
  have hambient := Subgroup.map_mono (f := B.subtype) hcore
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hmap] at hambient
  exact hambient

theorem involution_point_three_point_odd_core [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    beta ≠ rightCosetMk H 1 ∧
      rightCosetTranslate H beta z ≠ beta ∧
      rightCosetTranslate H beta z ≠ rightCosetMk H 1 ∧
      (pairPointStabilizer H beta : Set G) =
        (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
          (pairOddCore H beta : Set G) ∧
      (pairPointStabilizer H beta : Set G) =
        (pairOddCore H beta : Set G) * (triplePointStabilizer H z beta : Set G) ∧
      (oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype ≤ pairOddCore H beta := by
  have hdistinct := triple_point_cosets_distinct h hbeta
  exact ⟨hdistinct.1, hdistinct.2.1, hdistinct.2.2,
    pair_stabilizer_eq_z_centralizer_mul_odd_core h S hzS hzcenter hbeta ht,
    pair_stabilizer_eq_odd_core_mul_triple h S hzS hzcenter hbeta ht,
    triple_odd_core_le_pair_odd_core h S hzS hzcenter hbeta ht⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
