module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBSylowPowerCounts

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise

variable {H : Type*} [Group H]

theorem coe_sup_pPrimeCore_eq_mul (p : ℕ) {A L : Subgroup H} (hA : A ≤ L) :
    ((A ⊔ (pPrimeCore p L).map L.subtype : Subgroup H) : Set H) =
      (A : Set H) * ((pPrimeCore p L).map L.subtype : Set H) := by
  apply coe_mul_of_left_le_normalizer_right
  have hnormal : (((pPrimeCore p L).map L.subtype).subgroupOf L).Normal := by
    rw [← comap_subtype, comap_map_eq_self_of_injective L.subtype_injective]
    infer_instance
  exact hA.trans (le_normalizer_of_normal_subgroupOf (map_subtype_le _))

theorem component_recovery_from_covering_subgroup [Finite H] {p : ℕ} (hp : p.Prime)
    {L T : Subgroup H} (hL : IsPComponent p L) (hTL : T ≤ L)
    (hcover : (T : Set H) * ((pPrimeCore p L).map L.subtype : Set H) = L) :
    L ≤ pLayer H p ∧ (L.subgroupOf (pLayer H p)).Normal ∧
      (⨆ e ∈ pLayer H p, conjugate T e) = L ∧
      ∀ α : MulAut H, T.map α.toMonoidHom = T → L.map α.toMonoidHom = L := by
  have : Fact p.Prime := ⟨hp⟩
  set E := pLayer H p with hEdef
  have hLE : L ≤ E := le_sSup hL
  have hEnorm : E ≤ normalizer (L : Set H) := by
    apply sSup_le
    intro K hK
    by_cases hKL : K = L
    · rw [hKL]
      exact le_normalizer
    · exact ((CatalogueBPrimeJoin.distinct_p_components_core_commutation p hp L K hL hK).2
        (Ne.symm hKL)).1
  have hLnormal : (L.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hLE).mpr hEnorm
  obtain ⟨K, -, hLsub, hLK, hmin⟩ := hL
  set R₀ : Subgroup L := normalClosure ((T.subgroupOf L : Subgroup L) : Set L) with hR₀def
  have hTR : T ≤ R₀.map L.subtype := by
    intro t ht
    exact ⟨⟨t, hTL ht⟩, subset_normalClosure (show (⟨t, hTL ht⟩ : L) ∈ T.subgroupOf L from ht),
      rfl⟩
  have hRL : R₀.map L.subtype ≤ L := map_subtype_le _
  have hRsub : (R₀.map L.subtype).IsSubnormal :=
    (normalClosure_normal (s := ((T.subgroupOf L : Subgroup L) : Set L))).isSubnormal.trans'
      hLsub
  have hcoreL : ∀ o ∈ (pPrimeCore p L).map L.subtype, o ∈ pPrimeCore p H := by
    rintro _ ⟨o, ho, rfl⟩
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection p L hLsub] at ho
    exact ho
  have himage : (R₀.map L.subtype).map (QuotientGroup.mk' (pPrimeCore p H)) = K := by
    rw [← hLK]
    apply le_antisymm (map_mono hRL)
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l ∈ (T : Set H) * ((pPrimeCore p L).map L.subtype : Set H) := by
      rw [hcover]
      exact hl
    obtain ⟨t, ht, o, ho, rfl⟩ := Set.mem_mul.mp hl'
    refine ⟨t, hTR ht, ?_⟩
    have hone : (QuotientGroup.mk' (pPrimeCore p H)) o = 1 :=
      (QuotientGroup.eq_one_iff o).mpr (hcoreL o ho)
    rw [map_mul, hone, mul_one]
  have hRLeq : R₀.map L.subtype = L := by
    by_contra hne
    exact hmin _ (lt_of_le_of_ne hRL hne) hRsub himage
  have hconjle : ∀ e ∈ E, conjugate T e ≤ L := by
    intro e he x hx
    rw [mem_conjugate_iff_conj_mem] at hx
    have h := (mem_normalizer_iff''.mp (hEnorm he) _).mp (hTL hx)
    rwa [show e⁻¹ * (e * x * e⁻¹) * e = x by group] at h
  have hclosure : (⨆ e ∈ E, conjugate T e) = L := by
    apply le_antisymm (iSup₂_le hconjle)
    rw [← hRLeq, map_le_iff_le_comap]
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    have hc : ((c : H))⁻¹ ∈ E := hLE (inv_mem c.2)
    apply le_iSup₂ (f := fun e (_ : e ∈ E) => conjugate T e) ((c : H))⁻¹ hc
    rw [mem_conjugate_iff_conj_mem]
    have ha' : (a : H) ∈ T := ha
    convert ha' using 1
    simp only [subtype_apply, coe_mul, coe_inv, inv_inv]
    group
  refine ⟨hLE, hLnormal, hclosure, fun α hα => ?_⟩
  have hEα : E.map α.toMonoidHom = E :=
    characteristic_iff_map_eq.mp (CatalogueBPrimeJoin.pLayer_characteristic (G := H) (p := p)) α
  have hle : L.map α.toMonoidHom ≤ L := by
    conv_lhs => rw [← hclosure]
    rw [Subgroup.map_iSup]
    refine iSup_le fun e => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun he => ?_
    have hαe : α e ∈ E := by
      rw [← hEα]
      exact mem_map_of_mem _ he
    refine le_trans ?_ (hconjle (α e) hαe)
    rintro _ ⟨y, hy, rfl⟩
    have hy' : e * y * e⁻¹ ∈ T := mem_conjugate_iff_conj_mem.mp hy
    rw [MulEquiv.coe_toMonoidHom, mem_conjugate_iff_conj_mem]
    have hmem : α (e * y * e⁻¹) ∈ T.map α.toMonoidHom := mem_map_of_mem _ hy'
    rw [hα] at hmem
    simpa only [map_mul, map_inv] using hmem
  exact eq_of_le_of_card_ge hle
    (Nat.card_congr (α.subgroupMap L).toEquiv).le

end CFSG.ComponentClassification.UnbalancedGS
