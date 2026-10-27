module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Facts
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_RankGrp
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairTwoCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G]

theorem eq_commutator_or_eq_commutator_of_exponent {z n e : G} (hz3 : z ^ 3 = 1)
    (hez : e * z = z * e) {b : ℕ} (hb : (b : ZMod 3) ≠ 0) (h : n * e * n⁻¹ = e * z ^ b) :
    z = n * e * n⁻¹ * e⁻¹ ∨ z = e * n * e⁻¹ * n⁻¹ := by
  have hcomm : e * z ^ b = z ^ b * e := (Commute.pow_right (show Commute e z from hez) b).eq
  have h1 : n * e * n⁻¹ * e⁻¹ = z ^ b := by
    rw [h, hcomm]
    group
  have hzb : z ^ b = z ^ (b % 3) := by
    conv_lhs => rw [← Nat.div_add_mod b 3, pow_add, pow_mul, hz3, one_pow, one_mul]
  have hb3 : ¬ 3 ∣ b := fun hdvd => hb ((ZMod.natCast_eq_zero_iff b 3).mpr hdvd)
  have hmod : b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hmod with hmod | hmod
  · left
    rw [h1, hzb, hmod, pow_one]
  · right
    have h2 : n * e * n⁻¹ * e⁻¹ = z⁻¹ := by
      rw [h1, hzb, hmod]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hz3])
    calc z = (n * e * n⁻¹ * e⁻¹)⁻¹ := by rw [h2, inv_inv]
      _ = e * n * e⁻¹ * n⁻¹ := by group

variable [Finite G]

theorem not_invariantTwoMaximalWithin_of_module {p : ℕ}
    (hS : Setting G) (hD1 : TheoremD1 G) (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D R T H V : Subgroup G} (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hd : MaximalRelativePair p P M D R T) (hfacts : OptimalRelPairFacts p M D H V)
    (hp3 : p = 3) {J₁ U : Subgroup G} (hdata : A7ModuleData D H V J₁ U)
    (hcard : Nat.card V = 4 * Nat.card (pCoreOf 2 H)) :
    ¬ invariantTwoMaximalWithin D M V := by
  intro hmax
  subst hp3
  have hprime : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, -, hCD, -⟩ :=
    hd.ext.transitivity_data hS hD1 hp hd.not_le_normalizer hR h13
  obtain ⟨hDe, hDc⟩ := hd.ext.isElemAbelian_of_isMulCommutative hprime hDab
  have hMmax := hd.ext.obstruction.1
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hMmax
  have hDM : D ≤ M := hd.ext.obstruction.2.1.trans hPM
  obtain ⟨n, hnP, hnN, hnC⟩ :=
    hd.ext.exists_mem_normalizer_not_mem_centralizer hS hD1 hp hd.not_le_normalizer hDab hCD
  have hnz : n * z = z * n := mem_centralizer_iff.mp hzc n hnP
  have hnord : ∃ k : ℕ, n ^ (3 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨e, heD, hez⟩ : ∃ e ∈ D, e ∉ zpowers z := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show D ≤ zpowers z from fun x hx => h x hx)
    rw [hDc, Nat.card_zpowers, orderOf_eq_prime hzp hz1] at this
    norm_num at this
  have hezc : e * z = z * e := congrArg Subtype.val (hDab.is_comm.comm ⟨e, heD⟩ ⟨z, hzD⟩)
  obtain ⟨b, hb0, hneb⟩ :=
    exists_transvection_exponent hDe hDc hzD hz1 hnord hnN hnz hnC heD hez
  obtain ⟨a, c, haM, hcM, hzac, hza, hzc'⟩ : ∃ a c : G, a ∈ M ∧ c ∈ M ∧
      z = a * c * a⁻¹ * c⁻¹ ∧ z * a = a * z ∧ z * c = c * z := by
    rcases eq_commutator_or_eq_commutator_of_exponent hzp hezc hb0 hneb with h | h
    · exact ⟨n, e, hPM hnP, hDM heD, h, hnz.symm, hezc.symm⟩
    · exact ⟨e, n, hDM heD, hPM hnP, h, hezc.symm, hnz.symm⟩
  have hX2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hMX : M ≤ normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 M
  have hznc : ∃ x ∈ pCoreOf 2 M, z * x ≠ x * z := by
    by_contra hcon
    push Not at hcon
    have hzC : z ∈ centralizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
      mem_centralizer_iff.mpr fun x hx => (hcon x hx).symm
    have hzX : z ∈ pCoreOf 2 M := hS.charTwo M hMmax.1.1 ⟨hDM hzD, hzC⟩
    obtain ⟨k, hk⟩ := hX2 ⟨z, hzX⟩
    have hzk : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact hz1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one hzk) (orderOf_dvd_of_pow_eq_one hzp)))
  have hXV : pCoreOf 2 M ≤ V := invariantTwoMaximalWithin_contains_normal_two_subgroup D M V
    (pCoreOf 2 M) hDM hmax (pCoreOf_le 2 M) (pCoreOf_normal 2 M) hX2
  have hVH : V ≤ H := hfacts.maximal.1
  have hHS : H ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H
  have hzJ : z ∈ J₁ := hdata.D_le hzD
  have hidx : (pCoreOf 2 H).relIndex (pCoreOf 2 M) ≤ 4 := by
    rw [← relIndex_eq_four_of_card hfacts.pCore_le hcard]
    exact Subgroup.relIndex_le_of_le_right hXV Subgroup.index_ne_zero_of_finite
  obtain ⟨hidx4, -, hcent⟩ := rank_step hX2 hMX (hDM hzD) haM hcM hzac hzp hza hzc' hznc
    (hHS (hdata.J₁_le hzJ)) hdata.U_le (fun s hs => hdata.comm s hs z hzJ) hidx hdata.card_U
    (fun x hx => hdata.U_normal (hVH (hXV hx)))
  have hVeq : pCoreOf 2 M ⊔ pCoreOf 2 H = V :=
    sup_eq_of_relIndex_eq hXV hfacts.pCore_le hcard hidx4
  have hVU : V ≤ centralizer (U : Set G) := by
    rw [← hVeq]
    refine sup_le (fun x hx => mem_centralizer_iff.mpr fun u hu => hcent x hx u hu)
      (fun s hs => mem_centralizer_iff.mpr fun u hu => ?_)
    exact (mem_centralizer_iff.mp (hdata.U_central hu) s hs).symm
  have hVS : V ≤ pCoreOf 2 H := hdata.cent ▸ le_inf le_rfl hVU
  have hle := Subgroup.card_le_of_le hVS
  have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
