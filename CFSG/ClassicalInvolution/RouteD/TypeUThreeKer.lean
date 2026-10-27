module

public import CFSG.ClassicalInvolution.RouteD.SmallAKer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Pairs
public import CFSG.ClassicalInvolution.RouteD.TypeURoot

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem ShapeUDict.kerInvolutionFree_three (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeUDict p f 3 Ω z) :
    Transfer.KerInvolutionFree d.ψ := by
  have hK2 : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := typeU_card_field hq
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have h2' : (2 : GaloisField p f) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hn : 2 ≤ 3 + 1 := by omega
  intro u hu hu2
  rcases Transfer.eq_one_or_suMat_eq_neg_one hK2 hq (by omega : 3 ≤ 3 + 1) (d.ker_le hu) hu2
    with h1 | h1
  · exact h1
  exfalso
  set T0 : Pair (3 + 1) := nodePair 3 0 (by omega) with hT0
  set T2 : Pair (3 + 1) := nodePair 3 2 (by omega) with hT2
  have hzu : zEltU (GaloisField p (2 * f)) p f T2 = u * zEltU (GaloisField p (2 * f)) p f T0 := by
    apply suMat_injective
    rw [suMat_mul, h1, neg_one_mul, suMat_zEltU, suMat_zEltU]
    exact zMat_nodePair_two_eq_neg
  have hψ : d.ψ (zEltU (GaloisField p (2 * f)) p f T0) =
      d.ψ (zEltU (GaloisField p (2 * f)) p f T2) := by
    rw [hzu, map_mul, MonoidHom.mem_ker.mp hu, one_mul]
  obtain ⟨L, hL, -, hLR⟩ := typeU_exists_member_of_root hp2 hq (m := 3) (by omega) hΩ hK hz hP1 d
    (LcU_mem_longRootSetU h2 hn T0)
  obtain ⟨L', hL', -, hLR'⟩ := typeU_exists_member_of_root hp2 hq (m := 3) (by omega) hΩ hK hz hP1 d
    (LcU_mem_longRootSetU h2 hn T2)
  obtain ⟨w, hw⟩ := hΩ.classical L hL.1
  obtain ⟨w', hw'⟩ := hΩ.classical L' hL'.1
  have hy : w ∈ locLayer Ω z := le_centralizingLayer hL hw.mem
  have hy' : w' ∈ locLayer Ω z := le_centralizingLayer hL' hw'.mem
  have hinv : d.ψ (zEltU (GaloisField p (2 * f)) p f T0) = locElt Ω z w hy :=
    psiU_root_inv hp2 hq (by omega) d (isLongRootSU2_LcU h2 hn T0) hLR (le_centralizingLayer hL)
      hw.mem hw.orderOf_eq_two
  have hinv' : d.ψ (zEltU (GaloisField p (2 * f)) p f T2) = locElt Ω z w' hy' :=
    psiU_root_inv hp2 hq (by omega) d (isLongRootSU2_LcU h2 hn T2) hLR' (le_centralizingLayer hL')
      hw'.mem hw'.orderOf_eq_two
  have hwe : locElt Ω z w hy = locElt Ω z w' hy' := hinv.symm.trans (hψ.trans hinv')
  have hww : w = w' := congrArg Subtype.val
    (eq_of_involutions_of_mk (Y := ↥(locLayer Ω z)) hP1 (a := ⟨w, hy⟩) (b := ⟨w', hy'⟩)
      (Subtype.ext (mul_self_of_isClassicalMember hw))
      (Subtype.ext (mul_self_of_isClassicalMember hw')) hwe)
  obtain ⟨g, hg⟩ := hsingle L hL.1
  have hwg : w = g * z * g⁻¹ :=
    unique_involution_of_isClassicalMember h2' (hex L hL.1) hw (hg ▸ hz.conj g)
  have hNΩ : conjSub g⁻¹ L' ∈ Ω := hΩ.conjInvariant g⁻¹ L' hL'.1
  have hNcl : IsClassicalMember p f (conjSub g⁻¹ L') z := by
    have e : g⁻¹ * w' * g⁻¹⁻¹ = z := by rw [inv_inv, ← hww, hwg]; group
    exact e ▸ hw'.conj g⁻¹
  have hNz : conjSub g⁻¹ L' ∈ centralizingMembers Ω {z} :=
    ⟨hNΩ, le_centralizer_of_isClassicalMember hNcl⟩
  have hNK : conjSub g⁻¹ L' = K :=
    typeU_eq_of_locImg_le_Q₀ hp2 hq (by omega) hΩ hex hK hz hP1 d hNz
      (typeU_locImg_self_le_Q₀ hp2 hq (by omega) hNΩ hNcl d)
  have hL'L : L' = L := by
    rw [hg, ← hNK, conjSub_conjSub_inv]
  have hc : Commutes L L' := by
    refine (commutes_iff_locImg hΩ hP1 hL hL').mpr ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes d.ψ
      (commutes_LcU_of_disjoint h2 (nodePair_disjoint (by omega) (by omega) (by omega)))
  rw [hL'L] at hc
  exact not_commutes_self_of_isClassicalMember hw hc

end CFSG.ClassicalInvolution.RouteD
