module

public import CFSG.GH74.GLS.C3.Layer1.St1Iv251B
public import CFSG.Dihedral.DisconnectedInvolutionGraph.PGroupNormalizerExtension

public section

namespace CFSG.GH74.GLS.C3.Layer1.Iv251

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
open scoped commutatorElement

section Top

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_isSylowOf_of_central {C Q : Subgroup G} (hQ : IsSylowOf 2 Q C) {x : G} (hxC : x ∈ C)
    (hx2 : orderOf x = 2) (hcen : ∀ c ∈ C, x * c = c * x) : x ∈ Q := by
  obtain ⟨S, rfl⟩ := hQ
  let x' : ↥C := ⟨x, hxC⟩
  have hx'2 : orderOf x' = 2 := by
    rw [← hx2, ← Subgroup.orderOf_coe]
  have hz : Subgroup.zpowers x' ≤ Subgroup.center ↥C := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcen g g.2).symm
  have : (Subgroup.zpowers x').Normal := Subgroup.normal_of_le_center hz
  have hp : IsPGroup 2 ↥(Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'2]; norm_num)
  exact ⟨x', hp.le_sylow_of_normal S (Subgroup.mem_zpowers x'), rfl⟩

omit [Finite G] in
theorem self_mem_CxK {x : G} {K : Subgroup G} (hK : K ≤ centralizer ({x} : Set G)) :
    x ∈ CxK x K := by
  have hcent : x ∈ centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => mem_centralizer_singleton_iff.mp (hK hk)
  have hN : x ∈ normalizer (K : Set G) := Subgroup.centralizer_le_normalizer (K : Set G) hcent
  refine ⟨mem_centralizer_singleton_iff.mpr rfl, hN, mem_normalizer_pPrimeCoreOf hN, fun k hk => ?_⟩
  have : ⁅k, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_singleton_iff.mp (hK hk))
  rw [this]
  exact one_mem _

theorem iv2_5_1
    {x : G} {K Q V : Subgroup G} (hP : IsILo 2 x K)
    (hQ : IsSylowOf 2 Q (CxK x K))
    (hV : IsPGroup 2 ↥V) (hVN : V ≤ NxK x K) (hVQ : V ≤ normalizer (Q : Set G))
    (hRank : ∀ z ∈ Q, orderOf z = 2 → (∀ q ∈ Q, z * q = q * z) →
      (∀ v ∈ V, z * v = v * z) →
      3 ≤ pRank 2 ↥(centralizer ({z} : Set G)))
    (hyp : ∀ z ∈ Q, orderOf z = 2 → (∀ q ∈ Q, z * q = q * z) → (∀ v ∈ V, z * v = v * z) →
      ∀ K' : Subgroup G, PumpUpLT 2 x K z K' →
        (x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K)) ∧ IsSylowOf 2 Q (CxK z K')) :
    ∀ z ∈ Q, orderOf z = 2 → (∀ q ∈ Q, z * q = q * z) →
      ∀ K' : Subgroup G, PumpUpLT 2 x K z K' →
        (x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K)) → IsSylowOf 2 Q (CxK z K') := by
  have hx2 : orderOf x = 2 := hP.1
  have hQC : Q ≤ CxK x K := hQ.le
  have hQ2 : IsPGroup 2 ↥Q := hQ.isPGroup
  have hKx : K ≤ centralizer ({x} : Set G) := hP.2.2.1
  have hxQ : x ∈ Q :=
    mem_of_isSylowOf_of_central hQ (self_mem_CxK hKx) hx2 fun c hc =>
      (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).1).symm
  have hVK : V ≤ normalizer (K : Set G) := fun v hv => (Subgroup.mem_inf.mp (hVN hv)).2
  obtain ⟨Q', hQ'S, hQQ', hVQ'⟩ :=
    exists_invariant_sylow (le_bigC : Q ≤ bigC K Q) hQ2 hV (le_normalizer_bigC hVK hVQ) hVQ
  have hQ'2 : IsPGroup 2 ↥Q' := hQ'S.isPGroup
  have hP2 : IsPGroup 2 ↥(Q' ⊔ V) := hQ'2.to_sup_of_normal_left' hV hVQ'
  have hPN : Q' ⊔ V ≤ normalizer (Q : Set G) :=
    sup_le (hQ'S.le.trans inf_le_left) hVQ
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hxQ
    exact ne_one_of_orderOf_eq_two hx2 hxQ
  obtain ⟨z₀, hz₀Q, hz₀2, hz₀c⟩ :=
    exists_central_involution hP2 (hQQ'.trans le_sup_left) hPN hQne
  have hz₀Qc : ∀ q ∈ Q, z₀ * q = q * z₀ := fun q hq =>
    hz₀c q ((le_sup_left : Q' ≤ Q' ⊔ V) (hQQ' hq))
  have hz₀V : ∀ v ∈ V, z₀ * v = v * z₀ := fun v hv =>
    hz₀c v ((le_sup_right : V ≤ Q' ⊔ V) hv)
  obtain ⟨K₀, hlt₀⟩ := PumpRigid.exists_pumpUpLT hP hz₀2 (hQC hz₀Q)
    (hRank z₀ hz₀Q hz₀2 hz₀Qc hz₀V)
  obtain ⟨htr₀, hS₀⟩ := hyp z₀ hz₀Q hz₀2 hz₀Qc hz₀V K₀ hlt₀
  obtain ⟨Λ₀, T₀⟩ := exists_trivData hlt₀ htr₀
  have hQ'le : Q' ≤ CxK z₀ K₀ := fun s hs' =>
    mem_CxK_of_mem_bigC T₀ hlt₀.2.1.2.2 hQC hQ2 hxQ hz₀Q hz₀Qc (hQ'S.le hs')
      (mem_centralizer_singleton_iff.mpr
        (hz₀c s ((le_sup_left : Q' ≤ Q' ⊔ V) hs')).symm)
  have hQ'eq : Q' = Q := hS₀.eq_of_le hQQ' hQ'le hQ'2
  have hQS : IsSylowOf 2 Q (bigC K Q) := hQ'eq ▸ hQ'S
  intro z hzQ hz2 hzc K' hlt htr
  obtain ⟨Λ, T⟩ := exists_trivData hlt htr
  have hQK' : Q ≤ CxK z K' := fun q hq => T.cent q (hQC hq) (hzc q hq)
  obtain ⟨R, hRS, hQR⟩ := exists_isSylowOf_ge hQK' hQ2
  have hRQ : R = Q := by
    by_contra hne
    obtain ⟨S, hQS', hS2, hSle⟩ :=
      CFSG.DisconnectedInvolutionGraph.Helpers.pgroup_strict_normalizer_extension 2 Q R
        hRS.isPGroup (lt_of_le_of_ne hQR (Ne.symm hne))
    have hSle' : S ≤ bigC K Q := fun s hs' =>
      mem_bigC_of_mem_CxK T hxQ hzQ (hRS.le (hSle hs').1) (hSle hs').2
    exact absurd (hQS.eq_of_le hQS'.le hSle' hS2) (ne_of_gt hQS')
  rw [hRQ] at hRS
  exact hRS

end Top

end CFSG.GH74.GLS.C3.Layer1.Iv251
