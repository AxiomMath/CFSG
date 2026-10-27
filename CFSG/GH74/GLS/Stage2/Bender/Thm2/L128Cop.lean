module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L129Grp
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der7
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Zstar

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L128

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Cop

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pPrimeCoreOf_le (N : Subgroup G) : pPrimeCoreOf 2 N ≤ N := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

omit [Finite G] in
theorem mem_pPrimeCoreOf_iff {N : Subgroup G} {n : ↥N} :
    (n : G) ∈ pPrimeCoreOf 2 N ↔ n ∈ pPrimeCore 2 ↥N :=
  Subgroup.mem_map_iff_mem N.subtype_injective

theorem exists_centralizer_mul {N : Subgroup G} {z n : G} (hz2 : z * z = 1) (hn : n ∈ N)
    (h : ⁅n, z⁆ ∈ pPrimeCoreOf 2 N) :
    ∃ c ∈ N ⊓ centralizer ({z} : Set G), ∃ o ∈ pPrimeCoreOf 2 N, n = c * o := by
  have hodd : Odd (orderOf ⁅n, z⁆) := L129.odd_orderOf_of_mem_pPrimeCoreOf h
  obtain ⟨y, hy, hyfix⟩ := L129.exists_fixed_of_twist (z := z) (r := n⁻¹) (x := ⁅n, z⁆) hz2
    (by simp only [commutatorElement_def, inv_inv]; group) hodd
  have hyO : y ∈ pPrimeCoreOf 2 N := (Subgroup.zpowers_le.mpr h) hy
  have hyN : y ∈ N := pPrimeCoreOf_le N hyO
  have hdN : n⁻¹ * y ∈ N := mul_mem (inv_mem hn) hyN
  have hdz : z * (n⁻¹ * y) = (n⁻¹ * y) * z := by
    have h1 : z * (n⁻¹ * y) * z⁻¹ = n⁻¹ * y := hyfix
    calc z * (n⁻¹ * y) = z * (n⁻¹ * y) * z⁻¹ * z := by group
      _ = (n⁻¹ * y) * z := by rw [h1]
  have hOnorm : N ≤ normalizer ((pPrimeCoreOf 2 N : Subgroup G) : Set G) := le_normalizer_pPrimeCoreOf N
  have hcC : (n⁻¹ * y)⁻¹ ∈ centralizer ({z} : Set G) := by
    have hcomm : z * (n⁻¹ * y)⁻¹ = (n⁻¹ * y)⁻¹ * z :=
      calc z * (n⁻¹ * y)⁻¹ = (n⁻¹ * y)⁻¹ * ((n⁻¹ * y) * z) * (n⁻¹ * y)⁻¹ := by group
        _ = (n⁻¹ * y)⁻¹ * (z * (n⁻¹ * y)) * (n⁻¹ * y)⁻¹ := by rw [hdz]
        _ = (n⁻¹ * y)⁻¹ * z := by group
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  refine ⟨(n⁻¹ * y)⁻¹, Subgroup.mem_inf.mpr ⟨inv_mem hdN, hcC⟩, (n⁻¹ * y) * y * (n⁻¹ * y)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hOnorm hdN) y).mp hyO, ?_⟩
  group

theorem pPrimeCoreOf_inf_le {M A : Subgroup G} (hAM : A ≤ M) :
    pPrimeCoreOf 2 M ⊓ A ≤ pPrimeCoreOf 2 A := by
  have hMO : M ≤ normalizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) := le_normalizer_pPrimeCoreOf M
  refine L129.le_pPrimeCoreOf_of_normal_of_odd (H := A) (K := pPrimeCoreOf 2 M ⊓ A) inf_le_right ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hMO (hAM hk)) h).mp hh.1,
      mul_mem (mul_mem hk hh.2) (inv_mem hk)⟩
  · refine L129.odd_card_of_forall_odd_orderOf fun x => ?_
    have h1 := L129.odd_orderOf_of_mem_pPrimeCoreOf (N := M) x.2.1
    rwa [Subgroup.orderOf_coe] at h1

theorem exists_centralizer_preimage {N : Subgroup G} {z : G} (hzN : z ∈ N) (hz2 : z * z = 1)
    (x : HBar N)
    (hx : (QuotientGroup.mk (⟨z, hzN⟩ : ↥N) : HBar N) * x = x * QuotientGroup.mk (⟨z, hzN⟩ : ↥N)) :
    ∃ c : ↥N, (c : G) ∈ centralizer ({z} : Set G) ∧ (QuotientGroup.mk c : HBar N) = x := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : ⁅n, (⟨z, hzN⟩ : ↥N)⁆ ∈ pPrimeCore 2 ↥N := by
    have h0 : (QuotientGroup.mk' (pPrimeCore 2 ↥N)) ⁅n, (⟨z, hzN⟩ : ↥N)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hx.symm
    exact (QuotientGroup.eq_one_iff _).mp h0
  have h2 : ⁅(n : G), z⁆ ∈ pPrimeCoreOf 2 N := by
    have := mem_pPrimeCoreOf_iff.mpr h1
    simpa [commutatorElement_def] using this
  obtain ⟨c, hc, o, ho, hco⟩ := exists_centralizer_mul hz2 n.2 h2
  refine ⟨⟨c, hc.1⟩, hc.2, ?_⟩
  have ho' : (⟨o, pPrimeCoreOf_le N ho⟩ : ↥N) ∈ pPrimeCore 2 ↥N := mem_pPrimeCoreOf_iff.mp ho
  have hn : n = (⟨c, hc.1⟩ : ↥N) * ⟨o, pPrimeCoreOf_le N ho⟩ := Subtype.ext hco
  rw [hn, QuotientGroup.mk_mul]
  have : (QuotientGroup.mk (⟨o, pPrimeCoreOf_le N ho⟩ : ↥N) : HBar N) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ho'
  rw [this, mul_one]

theorem surj_of_centMod {H : Subgroup G} {z : G} (hz2 : z * z = 1) (h : CentMod H z) (x : HBar H) :
    ∃ c : ↥H, (c : G) ∈ centralizer ({z} : Set G) ∧ (QuotientGroup.mk c : HBar H) = x := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨c, hc, o, ho, hco⟩ := exists_centralizer_mul hz2 n.2 (h n n.2)
  refine ⟨⟨c, hc.1⟩, hc.2, ?_⟩
  have ho' : (⟨o, pPrimeCoreOf_le H ho⟩ : ↥H) ∈ pPrimeCore 2 ↥H := mem_pPrimeCoreOf_iff.mp ho
  have hn : n = (⟨c, hc.1⟩ : ↥H) * ⟨o, pPrimeCoreOf_le H ho⟩ := Subtype.ext hco
  rw [hn, QuotientGroup.mk_mul]
  have : (QuotientGroup.mk (⟨o, pPrimeCoreOf_le H ho⟩ : ↥H) : HBar H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ho'
  rw [this, mul_one]

end Cop

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L128
