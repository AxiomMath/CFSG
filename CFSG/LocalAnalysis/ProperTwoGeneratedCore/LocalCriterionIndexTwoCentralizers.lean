module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoLocalHull
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStarFactorization

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem order_ne_two_of_mem_odd_subgroup (X : Subgroup G) (hX : Odd (Nat.card X))
    {x : G} (hx : x ∈ X) : orderOf x ≠ 2 := by
  intro hxorder
  have hdvd : 2 ∣ Nat.card X := hxorder ▸ Subgroup.orderOf_dvd_natCard X hx
  have hbad := hX.of_dvd_nat hdvd
  norm_num at hbad

omit [Finite G] in
theorem local_point_sylow_normalizer_le {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (S : Sylow 2 G)
    (hzS : z ∈ (S : Subgroup G)) (hSH : (S : Subgroup G) ≤ H) :
    Subgroup.normalizer (S : Set G) ≤ H := by
  intro g hg
  have hzconj : g⁻¹ * z * g ∈ (S : Subgroup G) :=
    (Subgroup.mem_normalizer_iff''.mp hg z).mp hzS
  exact (pointClass_conjugate_mem_iff h g).mp (hSH hzconj)

theorem local_point_not_sylow_weakly_closed_of_odd_core_free
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzcentral : ∀ s ∈ (S : Subgroup G), Commute z s)
    (hodd : oddCore G = ⊥)
    (hwc : ∀ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) → g⁻¹ * z * g = z) : False := by
  have hzCS : z ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun s hs => (hzcentral s hs).symm.eq)
  have hzz : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp h.distinguished_order).1
  have hisolated : ∀ g : G, Commute (g⁻¹ * z * g) z → g⁻¹ * z * g = z := by
    intro g hg
    simpa only [inv_inv] using CFSG.Adapters.isolated_of_weakClosure S hzCS hzz hwc g⁻¹
      (by simpa only [inv_inv] using hg.eq)
  have hfactor := (LocalCriterionGeometry.native_zStar_of_isolated_involution
    h.distinguished_order hisolated).2
  apply h.proper
  apply top_unique
  intro g _
  obtain ⟨c, hc, k, hk, hg⟩ := hfactor g
  rw [hodd] at hk
  have hkone := Subgroup.mem_bot.mp hk
  rw [hkone, mul_one] at hg
  exact hg ▸ point_centralizer_le h hc

theorem local_point_central_sylow_involution_centralizer_le
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcentral : ∀ s ∈ (S : Subgroup G), Commute z s)
    (hodd : oddCore G = ⊥) (M : Subgroup G) [M.Normal]
    (hindex : M.index = 2) (hzM : z ∉ M)
    {a : G} (ha : orderOf a = 2)
    (hacentral : ∀ s ∈ (S : Subgroup G), Commute a s) :
    Subgroup.centralizer ({a} : Set G) ≤ H := by
  by_contra hescape
  have haz := hacentral z hzS
  have hkernel := local_point_index_two_odd_kernel h M hindex hzM ha haz hescape
  let L := localInvolutionPointHull z a
  let X := L ⊓ M
  have hXodd : Odd (Nat.card X) := hkernel.1
  have hzL : z ∈ L := distinguished_mem_localInvolutionPointHull haz
  have hwc : ∀ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) → g⁻¹ * z * g = z := by
    intro g hdS
    let d := g⁻¹ * z * g
    have hdclass : d ∈ involutionPointClass z := ⟨g, rfl⟩
    have hdorder : orderOf d = 2 := order_two_of_mem_pointClass h.distinguished_order hdclass
    have hdL : d ∈ L := mem_localInvolutionPointHull hdclass (hacentral d hdS).symm
    have hdM : d ∉ M := point_class_not_mem_normal_of_point_not_mem M hzM hdclass
    by_contra hdz
    have hzd := hzcentral d hdS
    have hprodX : z * d ∈ X :=
      ⟨L.mul_mem hzL hdL, (Subgroup.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hzM hdM)⟩
    have hprodne : z * d ≠ 1 := by
      intro hprod
      have hdzeq : d = z := (mul_eq_one_iff_inv_eq.mp hprod).symm.trans
        (inv_eq_self_of_orderOf_eq_two h.distinguished_order)
      exact hdz hdzeq
    have hprodorder : orderOf (z * d) = 2 := by
      apply orderOf_eq_prime_iff.mpr
      refine ⟨?_, hprodne⟩
      rw [hzd.mul_pow, (orderOf_eq_prime_iff.mp h.distinguished_order).1,
        (orderOf_eq_prime_iff.mp hdorder).1, one_mul]
    exact order_ne_two_of_mem_odd_subgroup X hXodd hprodX hprodorder
  exact local_point_not_sylow_weakly_closed_of_odd_core_free h S hzcentral hodd hwc

end CFSG.ProperTwoGeneratedCore
