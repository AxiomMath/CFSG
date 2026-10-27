module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinGlue
public import CFSG.GH74.KGroups.CoverEven

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.Uniqueness.Bender FinGlue
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace FinBen

theorem isSolvable_sup {G : Type*} [Group G] {N T : Subgroup G}
    (hTN : T ≤ normalizer (N : Set G)) (hN : Group.IsSolvable N) (hT : Group.IsSolvable T) :
    Group.IsSolvable ↥(N ⊔ T) := by
  set V := N ⊔ T
  have hNV : N ≤ V := le_sup_left
  have hTV : T ≤ V := le_sup_right
  have hVN : V ≤ normalizer (N : Set G) := sup_le le_normalizer hTN
  have : (N.subgroupOf V).Normal := (normal_subgroupOf_iff_le_normalizer hNV).mpr hVN
  set π := QuotientGroup.mk' (N.subgroupOf V)
  set f : T →* V ⧸ N.subgroupOf V := π.comp (inclusion hTV)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hv : (v : G) ∈ ((T ⊔ N : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact v.2
    rw [coe_mul_of_left_le_normalizer_right T N hTN] at hv
    obtain ⟨t, ht, n, hn, htn⟩ := hv
    refine ⟨⟨t, ht⟩, ?_⟩
    change π (inclusion hTV ⟨t, ht⟩) = π v
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    have h : ((inclusion hTV ⟨t, ht⟩)⁻¹ * v : V) = (t⁻¹ * v : G) := rfl
    rw [h, ← htn, inv_mul_cancel_left]
    exact hn
  have hNVsol : Group.IsSolvable (N.subgroupOf V) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hNV).toMonoidHom)
      (subgroupOfEquivOfLe hNV).injective
  have hQsol : Group.IsSolvable (V ⧸ N.subgroupOf V) := Group.isSolvable_of_surjective hf
  refine Group.isSolvable_of_ker_le_range (N.subgroupOf V).subtype π ?_
  rw [QuotientGroup.ker_mk', range_subtype]


theorem isSolvable_centralizer {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) (y : K) (hy : orderOf y = 2) :
    Group.IsSolvable ↥(centralizer ({y} : Set K)) := by
  have hyp : IsPGroup 2 ↥(zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hQsol : Group.IsSolvable ↥(Q : Subgroup K) := by
    have := Q.isPGroup'.isNilpotent
    infer_instance
  have hDsol : Group.IsSolvable ↥(cartan (Q : Subgroup K) t) := by
    have := hc.isCyclic
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(cartan (Q : Subgroup K) t))
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hg a)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hg b)
    exact ((Commute.refl g).zpow_zpow i j).eq
  have hBsol : Group.IsSolvable ↥(borel (Q : Subgroup K)) := by
    rw [← hc.sup_eq]
    exact isSolvable_sup inf_le_left hQsol hDsol
  have hy1 : zpowers y ≠ ⊥ := fun hb => by
    rw [zpowers_eq_bot] at hb
    rw [hb, orderOf_one] at hy
    omega
  have hCle : centralizer ({y} : Set K) ≤ borel (Q : Subgroup K) := by
    intro g hg
    refine IsStronglyEmbedded.mem_of_conj_mem hc.strong (hQ.trans (le_borel _)) (fun v hv => ?_)
      hyp hy1
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    have hgy : Commute g y := mem_centralizer_singleton_iff.mp hg
    rw [(hgy.zpow_right k).eq, mul_inv_cancel_right]
    exact le_borel _ (hQ hv)
  exact Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hCle).toMonoidHom)
    (subgroupOfEquivOfLe hCle).surjective

end FinBen

open FinBen


theorem finCellB_l216 {Y : Type} [Group Y] (h : LieModel Y .PSL 2 2 4) : FinCellB Y := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even (by norm_num) h
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hB : BenderType Y 4 1 1 := .linear 4 (by norm_num) e
  exact finCellB_of (noFourPerf_mulAut_of_cyclic hB.center_eq_bot hB.outer_linear.1
    fun y hy => isSolvable_centralizer hB y hy)

theorem finCellB_u34 {Y : Type} [Group Y] (h : LieModel Y .PSU 3 2 2) : FinCellB Y := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even (S := Y) (f := 2) le_rfl h
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hmodel : CFSG.Theory.Comparator.PSU3Model 2 = CFSG.Open.PSU3 2 2 := by
    simp only [CFSG.Open.PSU3, CFSG.Theory.Comparator.PSU3Model]
  have hB : BenderType Y 2 3 ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1)) :=
    BenderType.unitary 2 le_rfl (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  have hcyc : IsCyclic (Outer Y) := by
    obtain ⟨Dd, _, -, hd, hq, -⟩ := hB.outer_unitary
    have hDd : Dd = ⊥ := (Subgroup.card_eq_one).mp (by rw [hd]; decide)
    let φ : Outer Y ⧸ Dd ≃* Outer Y :=
      (QuotientGroup.quotientMulEquivOfEq hDd).trans QuotientGroup.quotientBot
    exact isCyclic_of_surjective φ.toMonoidHom φ.surjective
  exact finCellB_of (noFourPerf_mulAut_of_cyclic hB.center_eq_bot hcyc
    fun y hy => isSolvable_centralizer hB y hy)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
