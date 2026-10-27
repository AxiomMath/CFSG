module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingDefs

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_sylow_smul_iff {p : ℕ} (S : Sylow p G) (a v : G) :
    v ∈ ((a • S : Sylow p G) : Subgroup G) ↔ a⁻¹ * v * a ∈ (S : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]

theorem exists_conj_mem_commute [Finite G] {S : Sylow 2 G} {z : G}
    (hzS : z ∈ (S : Subgroup G)) (hzc : ∀ s ∈ (S : Subgroup G), Commute z s)
    {K : Subgroup G} (P : Sylow 2 G) (hPK : (P : Subgroup G) ≤ K) {x : G} (hxK : x ∈ K)
    (hx : IsPGroup 2 (Subgroup.zpowers x)) :
    ∃ y : G, y * z * y⁻¹ ∈ K ∧ Commute (y * z * y⁻¹) x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₁ : Sylow 2 K := P.subtype hPK
  have hQ : IsPGroup 2 ((Subgroup.zpowers x).comap K.subtype) := hx.comap_subtype
  obtain ⟨P', hQP'⟩ := hQ.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P₁ P'
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G S P
  have hxP' : (⟨x, hxK⟩ : K) ∈ (P' : Subgroup K) :=
    hQP' (by simp only [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_zpowers])
  rw [← hk, mem_sylow_smul_iff] at hxP'
  change ((k⁻¹ * ⟨x, hxK⟩ * k : K) : G) ∈ (P : Subgroup G) at hxP'
  rw [← ha, mem_sylow_smul_iff] at hxP'
  have hzP : a * z * a⁻¹ ∈ (P : Subgroup G) := by
    rw [← ha, mem_sylow_smul_iff]
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hzS
  refine ⟨(k : G) * a, ?_, ?_⟩
  · have hmem := K.mul_mem (K.mul_mem k.property (hPK hzP)) (K.inv_mem k.property)
    simpa only [mul_inv_rev, mul_assoc] using hmem
  · have hc := hzc _ hxP'
    have hc' := hc.map (MulAut.conj ((k : G) * a)).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at hc'
    convert hc' using 1
    group

theorem orderOf_mul_of_commute {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (hst : Commute s t) (hne : t ≠ s) : orderOf (s * t) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, mul_assoc, ← mul_assoc t, ← hst.eq, mul_assoc, ht, mul_one, hs]
  · intro h
    apply hne
    rw [← inv_eq_of_mul_eq_one_left hs]
    exact eq_inv_of_mul_eq_one_right h

theorem isPGroup_zpowers_of_orderOf_two {x : G} (hx : orderOf x = 2) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

variable {H : Subgroup G} {z : G}

theorem commute_of_mem_center {S : Sylow 2 G} {z : G} (hzS : z ∈ (S : Subgroup G))
    (hcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) :
    ∀ s ∈ (S : Subgroup G), Commute z s := by
  intro s hs
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcenter ⟨s, hs⟩) |>.symm

theorem productUniqueContainment_of_centralProductCentralizer [Finite G]
    (hz : orderOf z = 2) (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (h2 : CentralProductCentralizer H z) : ProductUniqueContainment H z := by
  obtain ⟨⟨S, hzS, hcenter⟩, hcent⟩ := h2
  have hzc := commute_of_mem_center hzS hcenter
  intro t ht hzt hne g
  have hC := hcent t ht hzt hne
  have hss : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
  have htt := class_mul_self hz ht
  have hzH : z ∈ H := hC (Subgroup.mem_centralizer_singleton_iff.mpr
    ((Commute.refl z).mul_right hzt).eq)
  have htH : t ∈ H := hC (Subgroup.mem_centralizer_singleton_iff.mpr
    (hzt.symm.mul_right (Commute.refl t)).eq)
  constructor
  · intro hmem
    by_contra hg
    have hfix : (z * t) • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g :=
      (smul_mk_eq_mk_iff _ _).mpr hmem
    let K := MulAction.stabilizer G (QuotientGroup.mk g : G ⧸ H)
    have hSH : (S : Subgroup G) ≤ H := fun s hs =>
      centralizer_le_of_unique huniq (Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs).eq.symm)
    have hPK : ((g • S : Sylow 2 G) : Subgroup G) ≤ K := by
      intro v hv
      rw [mem_sylow_smul_iff] at hv
      exact MulAction.mem_stabilizer_iff.mpr ((smul_mk_eq_mk_iff v g).mpr (hSH hv))
    have hx2 := isPGroup_zpowers_of_orderOf_two (orderOf_mul_of_commute hss htt hzt hne)
    obtain ⟨y, hyK, hycomm⟩ := exists_conj_mem_commute hzS hzc (g • S) hPK
      (MulAction.mem_stabilizer_iff.mpr hfix) hx2
    have hyH : y * z * y⁻¹ ∈ H := hC (Subgroup.mem_centralizer_singleton_iff.mpr hycomm.eq)
    have hbase : (y⁻¹⁻¹ * z * y⁻¹) • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 := by
      rw [inv_inv]
      exact class_mem_iff_fixes_base.mp hyH
    have hgfix : (y⁻¹⁻¹ * z * y⁻¹) • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g := by
      rw [inv_inv]
      exact MulAction.mem_stabilizer_iff.mp hyK
    rw [conj_smul_eq_iff_eq huniq] at hbase hgfix
    exact hg ((mk_eq_base_iff g).mp (hgfix.trans hbase.symm))
  · intro hg
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) (H.mul_mem hzH htH)) hg

end CFSG.ComponentClassification.AschbacherStrongEmbedding
