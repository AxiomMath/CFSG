module

public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3URMembers

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups

section Ker

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ShapeUDict.kerInvolutionFree_three3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G}
    (hz : IsClassicalMember3 K z) (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    (d : ShapeUDict 3 1 3 Ω z) : Transfer.KerInvolutionFree d.ψ := by
  have h2 := two_ne_zero_gf9
  have hn : 2 ≤ 3 + 1 := by omega
  intro u hu hu2
  rcases eq_one_or_suMat_eq_neg_one3 (by omega : 3 ≤ 3 + 1) (d.ker_le hu) hu2 with h1 | h1
  · exact h1
  exfalso
  set T0 : Pair (3 + 1) := nodePair 3 0 (by omega) with hT0
  set T2 : Pair (3 + 1) := nodePair 3 2 (by omega) with hT2
  have hzu : zEltU (GaloisField 3 2) 3 1 T2 = u * zEltU (GaloisField 3 2) 3 1 T0 := by
    apply suMat_injective
    rw [suMat_mul, h1, neg_one_mul, suMat_zEltU, suMat_zEltU]
    exact zMat_nodePair_two_eq_neg
  have hψ : d.ψ (zEltU (GaloisField 3 2) 3 1 T0) = d.ψ (zEltU (GaloisField 3 2) 3 1 T2) := by
    rw [hzu, map_mul, MonoidHom.mem_ker.mp hu, one_mul]
  obtain ⟨L, hL, -, hLR⟩ := exists_member_of_rootU3 (m := 3) (by omega) hΩ hex hK hz hP1 hO3 d
    (LcU_mem_longRootSetU h2 hn T0)
  obtain ⟨L', hL', -, hLR'⟩ := exists_member_of_rootU3 (m := 3) (by omega) hΩ hex hK hz hP1 hO3 d
    (LcU_mem_longRootSetU h2 hn T2)
  obtain ⟨w, hw⟩ := hΩ.classical L hL.1
  obtain ⟨w', hw'⟩ := hΩ.classical L' hL'.1
  have hy : w ∈ locLayer Ω z := le_centralizingLayer hL hw.mem
  have hy' : w' ∈ locLayer Ω z := le_centralizingLayer hL' hw'.mem
  have hinv : d.ψ (zEltU (GaloisField 3 2) 3 1 T0) = locElt Ω z w hy :=
    psiU_root_inv3 (by omega) d (isLongRootSU2_LcU h2 hn T0) hLR (le_centralizingLayer hL)
      hw.mem hw.orderOf_eq_two
  have hinv' : d.ψ (zEltU (GaloisField 3 2) 3 1 T2) = locElt Ω z w' hy' :=
    psiU_root_inv3 (by omega) d (isLongRootSU2_LcU h2 hn T2) hLR' (le_centralizingLayer hL')
      hw'.mem hw'.orderOf_eq_two
  have hwe : locElt Ω z w hy = locElt Ω z w' hy' := hinv.symm.trans (hψ.trans hinv')
  have hww : w = w' := congrArg Subtype.val
    (eq_of_involutions_of_mk (Y := ↥(locLayer Ω z)) hP1 (a := ⟨w, hy⟩) (b := ⟨w', hy'⟩)
      (Subtype.ext (mul_self_of_isClassicalMember3 hw))
      (Subtype.ext (mul_self_of_isClassicalMember3 hw')) hwe)
  obtain ⟨g, hg⟩ := hsingle L hL.1
  have hwg : w = g * z * g⁻¹ := involution_unique3 hw (hg ▸ hz.conj g)
  have hNΩ : conjSub g⁻¹ L' ∈ Ω := hΩ.conjInvariant g⁻¹ L' hL'.1
  have hNcl : IsClassicalMember3 (conjSub g⁻¹ L') z := by
    have e : g⁻¹ * w' * g⁻¹⁻¹ = z := by rw [inv_inv, ← hww, hwg]; group
    exact e ▸ hw'.conj g⁻¹
  have hNz : conjSub g⁻¹ L' ∈ centralizingMembers Ω {z} :=
    ⟨hNΩ, isSubnormal_le hNcl.subnormal⟩
  have hNK : conjSub g⁻¹ L' = K :=
    eq_of_locImg_le_Q₀U3 (by omega) hΩ hex hK hz hP1 hO3 d hNz
      (locImg_self_le_Q₀U3 (by omega) hNΩ hNcl d)
  have hL'L : L' = L := by
    rw [hg, ← hNK, conjSub_conjSub_inv]
  have hc : Commutes L L' := by
    refine commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes d.ψ
      (commutes_LcU_of_disjoint h2 (nodePair_disjoint (by omega) (by omega) (by omega)))
  rw [hL'L] at hc
  exact not_commutes_self3 hw hc

end Ker

end CFSG.ClassicalInvolution.Q3.Q3W
