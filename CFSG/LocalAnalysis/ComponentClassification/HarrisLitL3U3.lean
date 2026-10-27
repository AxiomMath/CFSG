module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL3U3Core
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL3U3Inputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

namespace L3U3

theorem eq_one_of_mem_center_of_pow_three {R : Type*} [CommRing R]
    {x : Matrix.SpecialLinearGroup (Fin 2) R}
    (hx : x ∈ center (Matrix.SpecialLinearGroup (Fin 2) R)) (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  rw [Fintype.card_fin] at hr2
  have hx3 : ((x : Matrix (Fin 2) (Fin 2) R)) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, h3, Matrix.SpecialLinearGroup.coe_one]
  rw [← hr, ← map_pow] at hx3
  have hr3 : r ^ 3 = 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) hx3
    simpa [Matrix.scalar_apply] using this
  have hr1 : r = 1 := by
    have h1 : r ^ 3 = r ^ 2 * r := by ring
    rw [hr3, hr2, one_mul] at h1
    exact h1.symm
  apply Subtype.ext
  rw [← hr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

section PSU

open Assembly.LowTwoRank RankThree.CentralCover GH74.GLS.IVK.Proofs2 RankThree.Classical
  LocalAnalysis.ComponentInitial ClassicalGroups.UnitaryFlag RankThree.SubgroupLists

variable {p n : ℕ} {K : Type} [Field K]

theorem statedSU_two_le_GU2 (h : UnitaryFieldData p n K) :
    StatedSU 2 (p ^ n) K ≤ GU2Stated (p ^ n) K := fun _ hA =>
  (Lemma41aU3.mem_GU2Stated_iff h).mpr ((mem_unitarySU_iff h).mp hA).2

theorem statedSU_two_normal (h : UnitaryFieldData p n K) :
    ((StatedSU 2 (p ^ n) K).subgroupOf (GU2Stated (p ^ n) K)).Normal := by
  constructor
  rintro ⟨A, hA⟩ hAS ⟨g, hg⟩
  rw [mem_subgroupOf] at hAS ⊢
  have hA' := (mem_unitarySU_iff h).mp hAS
  have hmem : g * A * g⁻¹ ∈ GU2Stated (p ^ n) K := mul_mem (mul_mem hg hA) (inv_mem hg)
  refine (mem_unitarySU_iff h).mpr ⟨?_, (Lemma41aU3.mem_GU2Stated_iff h).mp hmem⟩
  show ((g * A * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj, hA'.1]

theorem neg_one_mem_statedSU_two (h : UnitaryFieldData p n K) :
    (-1 : GL (Fin 2) K) ∈ StatedSU 2 (p ^ n) K := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · simp [Matrix.det_fin_two]
  · simp [Matrix.map_neg, Matrix.map_one]

theorem blk_neg_one : (Lemma41aL3.blk (-1 : GL (Fin 2) K) : GL (Fin 3) K) = negNegOneGL K := by
  apply Units.ext
  rw [Lemma41aL3.coe_blk, coe_negNegOneGL, negNegOneDiag]
  have hdet : ((-1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two]
  rw [hdet, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]

variable [Finite K] [Fact p.Prime] [CharP K p]

theorem psu_case (h : UnitaryFieldData p n K) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ n) ^ 2)
    {w : StatedProj (StatedSU 3 (p ^ n) K)} (hw : orderOf w = 2) :
    ∃ Y : Subgroup (StatedProj (StatedSU 3 (p ^ n) K)), Y ≤ centralizer ({w} : Set _) ∧
      (Y.subgroupOf (centralizer ({w} : Set (StatedProj (StatedSU 3 (p ^ n) K))))).Normal ∧
      Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2)
        ↥(LieType.Steinberg.fixedSubfield K p n)) ∧ w ∈ Y := by
  have hw1 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSU 3 (p ^ n) K))
    (statedProjMk_surjective _) (fun z hz => Lemma41aU3.ker_pow_three h z hz) hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 ha_ord)
  set φ := Lemma41aU3.phi h c with hφdef
  have hrange : φ.range = centralizer ({a} : Set _) := by
    rw [hφdef, Lemma41aU3.phi_range h hp2 c, hc]
  set T := (StatedSU 2 (p ^ n) K).subgroupOf (GU2Stated (p ^ n) K) with hTdef
  let eT : ↥T ≃* Matrix.SpecialLinearGroup (Fin 2) ↥(LieType.Steinberg.fixedSubfield K p n) :=
    (subgroupOfEquivOfLe (statedSU_two_le_GU2 h)).trans
      (nonempty_sl2_mulEquiv_statedSU_two (r := p) (f := n) hK).some.symm
  have hneg : (-1 : GL (Fin 2) K) ∈ GU2Stated (p ^ n) K :=
    statedSU_two_le_GU2 h (neg_one_mem_statedSU_two h)
  have ht₀ : (⟨-1, hneg⟩ : ↥(GU2Stated (p ^ n) K)) ∈ T := by
    rw [hTdef, mem_subgroupOf]
    exact neg_one_mem_statedSU_two h
  have hφt₀ : φ ⟨-1, hneg⟩ = a := by
    rw [← hc, hφdef]
    show c * Lemma41aU3.blkU h ⟨-1, hneg⟩ * c⁻¹ = c * unitaryInvT h * c⁻¹
    congr 2
    exact Subtype.ext blk_neg_one
  have hinj : ∀ t ∈ T, statedProjMk (StatedSU 3 (p ^ n) K) (φ t) = 1 → t = 1 := by
    intro t ht htk
    have htk' : φ t ∈ (statedProjMk (StatedSU 3 (p ^ n) K)).ker := htk
    have htc := mem_center_iff.mp (ker_statedProjMk_le_center _ htk')
    have ht3 : t ^ 3 = 1 :=
      Lemma41aU3.phi_injective h c (by rw [map_pow, Lemma41aU3.ker_pow_three h _ htk', map_one])
    have htcen : (⟨t, ht⟩ : ↥T) ∈ center ↥T := by
      rw [mem_center_iff]
      intro s
      apply Subtype.ext
      apply Lemma41aU3.phi_injective h c
      simp only [Subgroup.coe_mul, map_mul]
      exact htc (φ s)
    have hcen : eT ⟨t, ht⟩ ∈ center (Matrix.SpecialLinearGroup (Fin 2)
        ↥(LieType.Steinberg.fixedSubfield K p n)) := by
      rw [mem_center_iff]
      intro B
      obtain ⟨s, rfl⟩ := eT.surjective B
      rw [← map_mul, ← map_mul, mem_center_iff.mp htcen s]
    have h3' : eT ⟨t, ht⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨t, ht⟩ : ↥T) ^ 3 = 1 := Subtype.ext ht3
      rw [this, map_one]
    have h1 := eq_one_of_mem_center_of_pow_three hcen h3'
    have h2 : (⟨t, ht⟩ : ↥T) = 1 := eT.injective (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  obtain ⟨Y, hYC, hYn, ⟨hYT⟩, hwY⟩ := exists_normal_of_param
    (statedProjMk (StatedSU 3 (p ^ n) K)) (statedProjMk_surjective _)
    (ker_statedProjMk_le_center _) (fun z hz => Lemma41aU3.ker_pow_three h z hz) ha φ hrange T
    (statedSU_two_normal h) ht₀ hφt₀ hinj
  exact ⟨Y, hYC, hYn, ⟨hYT.trans eT⟩, hwY⟩

end PSU

end L3U3

open Assembly.LowTwoRank LocalAnalysis.ComponentInitial

theorem EndB.l3u3InvolutionSL2Fact : EndB.L3U3InvolutionSL2Fact := by
  intro G _ _ E p m hp hp2 hm hE e he he2
  rcases hE with hE | hE
  · obtain ⟨-, -, K, _, _, hK, ⟨ι⟩⟩ := GH74.Generic.lieModel_psl_data hE
    have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
    have hw : orderOf (ι ⟨e, he⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact he2
    obtain ⟨Y, hYC, hYn, ⟨eY⟩, hwY⟩ := L3U3.psl_case hodd hw
    obtain ⟨Y', hY'le, hY'n, ⟨eY'⟩, heY'⟩ := L3U3.transport E ι he hYC hYn hwY
    have : Fintype K := Fintype.ofFinite K
    exact ⟨Y', hY'le, hY'n.isSubnormal, ⟨K, inferInstance, inferInstance,
      by rw [← Nat.card_eq_fintype_card, hK], ⟨eY'.trans eY⟩⟩, heY'⟩
  · obtain ⟨-, -, K, _, _, hK, ⟨ι⟩⟩ := GH74.Generic.lieModel_psu_data hE
    have h : UnitaryFieldData p m K := ⟨hp, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := h.charP
    have hw : orderOf (ι ⟨e, he⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact he2
    obtain ⟨Y, hYC, hYn, ⟨eY⟩, hwY⟩ := L3U3.psu_case h hp2 hK hw
    obtain ⟨Y', hY'le, hY'n, ⟨eY'⟩, heY'⟩ := L3U3.transport E ι he hYC hYn hwY
    have : Fintype ↥(LieType.Steinberg.fixedSubfield K p m) := Fintype.ofFinite _
    exact ⟨Y', hY'le, hY'n.isSubnormal, ⟨↥(LieType.Steinberg.fixedSubfield K p m), inferInstance,
      inferInstance, by rw [← Nat.card_eq_fintype_card, LieType.Steinberg.card_fixedSubfield hK],
      ⟨eY'.trans eY⟩⟩, heY'⟩

end CFSG.ComponentClassification.HarrisLit
