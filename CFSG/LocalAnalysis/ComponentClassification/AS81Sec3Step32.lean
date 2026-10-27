module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Model
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

noncomputable def slTwoMapEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    ext i j
    simp
  right_inv A := by
    ext i j
    simp
  map_mul' := map_mul _

open Sec3 in
theorem step32_of :
    Step32 := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y hSz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, hK, f, hM⟩ := exists_sec3Model hSz.setting
  have hfinj := hM.inj
  have hEA' := hM.E_eq
  have hFA' := hM.F_eq
  have hxA' := hM.x_eq
  have hI := hM.I_eq
  have hD₀C : g2ShortParabolicRadical K ≤ adjointGroup .G2 K :=
    G2.g2ShortParabolicRadical_le_adjointGroup
  have hLaC : g2RankOne K g2ia ≤ adjointGroup .G2 K := g2RankOne_le_adjointGroup g2ia
  have hHrC : g2TorusR K ≤ adjointGroup .G2 K := G2.g2TorusR_le_adjointGroup
  have hZ₀C : g2BCGroup K ≤ adjointGroup .G2 K :=
    G2.g2BCGroup_le_g2ShortParabolicRadical.trans hD₀C
  have hXvC : rootSubgroup .G2 K g2v ≤ adjointGroup .G2 K :=
    G2.rootSubgroup_v_le_g2ShortParabolicRadical.trans hD₀C
  have hPC : G2.g2Para K ≤ adjointGroup .G2 K := sup_le (sup_le hD₀C hLaC) hHrC
  have hXaL : rootSubgroup .G2 K g2a ≤ g2RankOne K g2ia := by
    intro g hg
    obtain ⟨s, rfl⟩ := mem_rootSubgroup.mp hg
    rw [← xUnit_g2ia]
    exact xUnit_mem_g2RankOne g2ia s
  have hXaAC : rootSubgroup .G2 K g2a ≤ G2.g2ACGroup K := by
    intro g hg
    obtain ⟨s, rfl⟩ := mem_rootSubgroup.mp hg
    exact ⟨s, 0, by rw [pinnedX_a_eq_g2N]⟩
  obtain ⟨-, -, -, -, -, -, -, ⟨ρ, -, -, hρrange, hρinj⟩, -⟩ :=
    even_G2_highest_short_root_centralizer K
  let eρ : LieType.Chevalley.SL2 K ≃* ↥(g2RankOne K g2ia) :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)
  have hLa60 : Nat.card (g2RankOne K g2ia) = 60 := by
    rw [← Nat.card_congr eρ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  have hXa4 : Nat.card (rootSubgroup .G2 K g2a) = 4 := by
    have hinj : Function.Injective (pinnedHom .G2 K g2a) := fun s t h =>
      Multiplicative.toAdd.injective (pinnedX_injective .G2 K g2a h)
    rw [rootSubgroup_eq_range, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, hK]
  have hXaSyl : IsSylowOf 2 (rootSubgroup .G2 K g2a) (g2RankOne K g2ia) := by
    refine isSylowOf_of_card hXaL ?_
    rw [hXa4, hLa60]
    have h1 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
    norm_num
  have hXaSylG : IsSylowOf 2 (((rootSubgroup .G2 K g2a).subgroupOf (adjointGroup .G2 K)).map f)
      (((g2RankOne K g2ia).subgroupOf (adjointGroup .G2 K)).map f) := by
    refine AschbacherTheorem3.IsSylowOf.map ?_ f
    rw [← isSylowOf_map_subtype_iff (adjointGroup .G2 K), map_subgroupOf_eq (hXaL.trans hLaC),
      map_subgroupOf_eq hLaC]
    exact hXaSyl
  refine ⟨((g2ShortParabolicRadical K).subgroupOf (adjointGroup .G2 K)).map f,
    ((g2RankOne K g2ia).subgroupOf (adjointGroup .G2 K)).map f,
    ((rootSubgroup .G2 K g2v).subgroupOf (adjointGroup .G2 K)).map f,
    ⟨hSz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    rw [hI, tr_pCoreOf hfinj hPC, G2.pCoreOf_g2Para hK]
  ·
    rw [hI]
    exact tr_mono (le_sup_right.trans le_sup_left)
  ·
    let _ : Fintype K := Fintype.ofFinite K
    let _ : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    have hcard : Fintype.card K = Fintype.card (GaloisField 2 2) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card 2 2
        (by norm_num)]
      norm_num
    exact ⟨((((g2RankOne K g2ia).subgroupOf (adjointGroup .G2 K)).equivMapOfInjective f
      hfinj).symm.trans (subgroupOfEquivOfLe hLaC)).trans (eρ.symm.trans
        (slTwoMapEquiv (FiniteField.ringEquivOfCardEq hcard)))⟩
  ·
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hx2 : x ∈ ((g2TorusR K).subgroupOf (adjointGroup .G2 K)).map f := by
      rw [hxA']
      exact mem_zpowers x
    obtain ⟨h, hh, rfl⟩ := hx2
    have hc := mem_centralizer_iff.mp (G2.g2TorusR_le_centralizer_g2RankOne hK
      (mem_subgroupOf.mp hh)) _ (mem_subgroupOf.mp hl)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  ·
    have hXaT : ((rootSubgroup .G2 K g2a).subgroupOf (adjointGroup .G2 K)).map f ≤ T :=
      (tr_mono hXaAC).trans (by rw [hFA']; exact inf_le_left.trans hSz.F_le)
    have h1 := hXaSylG.eq_of_le (le_inf hXaT (tr_mono hXaL)) inf_le_right
      (hSz.T_two.to_le inf_le_left)
    rw [h1]
    exact hXaSylG
  ·
    rw [hI, ← hxA', G2.g2Para, tr_sup (sup_le hD₀C hLaC) hHrC, tr_sup hD₀C hLaC, sup_assoc]
  ·
    rw [← hEA', tr_centerIn hfinj hD₀C]
    exact congrArg (fun Y => (Y.subgroupOf (adjointGroup .G2 K)).map f)
      (G2.centerIn_g2ShortParabolicRadical (K := K)).symm
  ·
    rw [← hEA']
    rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩
    obtain ⟨h1, h2⟩ := G2.g2ShortParabolicRadical_elem (mem_subgroupOf.mp hq)
      (mem_subgroupOf.mp hq')
    refine ⟨⟨q * q, mem_subgroupOf.mpr h1, map_mul f q q⟩,
      ⟨q * q' * q⁻¹ * q'⁻¹, mem_subgroupOf.mpr h2, by simp⟩⟩
  ·
    rw [← hEA', tr_relIndex hfinj hD₀C, G2.relIndex_g2BCGroup, hK]
  ·
    exact tr_mono G2.rootSubgroup_v_le_g2ShortParabolicRadical
  ·
    rw [← tr_sup hD₀C hLaC, ← hEA', ← tr_sup hXvC hZ₀C]
    rintro _ ⟨d, hd, rfl⟩
    have key := G2.center_mod_g2BCGroup hK (mem_subgroupOf.mp hd)
    constructor
    · intro hc
      rw [mem_map_iff_mem hfinj, mem_subgroupOf]
      refine key.mp fun j hj => ?_
      have hjC : j ∈ adjointGroup .G2 K := (sup_le hD₀C hLaC) hj
      have h1 := hc (f ⟨j, hjC⟩) ⟨⟨j, hjC⟩, mem_subgroupOf.mpr hj, rfl⟩
      rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul, mem_map_iff_mem hfinj,
        mem_subgroupOf] at h1
      exact h1
    · intro hd'
      rw [mem_map_iff_mem hfinj, mem_subgroupOf] at hd'
      rintro _ ⟨j, hj, rfl⟩
      have h1 := key.mpr hd' j (mem_subgroupOf.mp hj)
      rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul, mem_map_iff_mem hfinj,
        mem_subgroupOf]
      exact h1
  ·
    rw [← tr_commutator hD₀C hXvC, G2.commutator_g2ShortParabolicRadical_v, hEA']

end CFSG.ComponentClassification.AS81
