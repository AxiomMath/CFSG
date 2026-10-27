module

public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.Generic.StepMember

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic CFSG.Open
  CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

theorem eq_of_involutions_of_mk {Y : Type} [Group Y] [Finite Y]
    (hO : classicalInvolutionOddCore Y ≤ Subgroup.center Y) {a b : Y} (ha : a * a = 1)
    (hb : b * b = 1)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore Y) a =
      QuotientGroup.mk' (classicalInvolutionOddCore Y) b) : a = b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  set c : Y := a⁻¹ * b with hc
  have hcO : c ∈ classicalInvolutionOddCore Y := QuotientGroup.eq.mp h
  have hcen : a * c = c * a := Subgroup.mem_center_iff.mp (hO hcO) a
  have hab : a * b = b * a := by
    have h1 : b = a⁻¹ * b * a := by
      calc b = a * (a⁻¹ * b) := by group
        _ = (a⁻¹ * b) * a := hcen
    calc a * b = a * (a⁻¹ * b * a) := by rw [← h1]
      _ = b * a := by group
  have hcc : c * c = 1 := by
    rw [hc, ha']
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  have hord2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcc)
  have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
  have hdvd : orderOf (⟨c, hcO⟩ : classicalInvolutionOddCore Y) ∣
      Nat.card (classicalInvolutionOddCore Y) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  have hc1 : c = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  exact inv_mul_eq_one.mp hc1

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem zMat_nodePair_two_eq_neg {F : Type} [Field F] :
    zMat F (3 + 1) (nodePair 3 2 (by omega)).1 = -zMat F (3 + 1) (nodePair 3 0 (by omega)).1 := by
  rw [zMat, zMat]
  ext a b
  by_cases hab : a = b
  · subst hab
    fin_cases a <;> simp [nodePair, natPair]
  · simp [Matrix.diagonal_apply_ne _ hab]

theorem ShapeADict.kerInvolutionFree_three (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeADict p f 3 Ω z) :
    Transfer.KerInvolutionFree d.ψ := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]; exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have hn : 2 ≤ 3 + 1 := by omega
  intro u hu hu2
  rcases Transfer.eq_one_or_coe_eq_neg_one (by omega : 1 ≤ 3 + 1) (d.ker_le hu) hu2 with h1 | h1
  · exact h1
  exfalso
  set T0 : Pair (3 + 1) := nodePair 3 0 (by omega) with hT0
  set T2 : Pair (3 + 1) := nodePair 3 2 (by omega) with hT2
  have hzu : zElt (GaloisField p f) T2 = u * zElt (GaloisField p f) T0 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, h1, neg_one_mul]
    exact zMat_nodePair_two_eq_neg
  have hψ : d.ψ (zElt (GaloisField p f) T0) = d.ψ (zElt (GaloisField p f) T2) := by
    rw [hzu, map_mul, MonoidHom.mem_ker.mp hu, one_mul]
  have hR0 : Lc (GaloisField p f) T0 ∈ longRootSet (K := GaloisField p f) hn :=
    ⟨_, isLongRootSL2_Lc h2 hn T0⟩
  have hR2 : Lc (GaloisField p f) T2 ∈ longRootSet (K := GaloisField p f) hn :=
    ⟨_, isLongRootSL2_Lc h2 hn T2⟩
  obtain ⟨L, hL, -, hLR⟩ := exists_member_of_root (m := 3) (by omega) hodd hΩ hK hz hP1 d hR0
  obtain ⟨L', hL', -, hLR'⟩ := exists_member_of_root (m := 3) (by omega) hodd hΩ hK hz hP1 d hR2
  obtain ⟨w, hw⟩ := hΩ.classical L hL.1
  obtain ⟨w', hw'⟩ := hΩ.classical L' hL'.1
  have hy : w ∈ locLayer Ω z := le_centralizingLayer hL hw.mem
  have hy' : w' ∈ locLayer Ω z := le_centralizingLayer hL' hw'.mem
  have hinv : d.ψ (zElt (GaloisField p f) T0) = locElt Ω z w hy :=
    psi_root_inv (by omega) hodd d (isLongRootSL2_Lc h2 hn T0) (by simpa using hLR)
      (le_centralizingLayer hL) hw.mem hw.orderOf_eq_two
  have hinv' : d.ψ (zElt (GaloisField p f) T2) = locElt Ω z w' hy' :=
    psi_root_inv (by omega) hodd d (isLongRootSL2_Lc h2 hn T2) (by simpa using hLR')
      (le_centralizingLayer hL') hw'.mem hw'.orderOf_eq_two
  have hwe : locElt Ω z w hy = locElt Ω z w' hy' := hinv.symm.trans (hψ.trans hinv')
  have hww : w = w' := congrArg Subtype.val
    (eq_of_involutions_of_mk (Y := ↥(locLayer Ω z)) hP1 (a := ⟨w, hy⟩) (b := ⟨w', hy'⟩)
      (Subtype.ext (mul_self_of_isClassicalMember hw))
      (Subtype.ext (mul_self_of_isClassicalMember hw')) hwe)
  obtain ⟨g, hg⟩ := hsingle L hL.1
  have hwg : w = g * z * g⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex L hL.1) hw (hg ▸ hz.conj g)
  have hNΩ : conjSub g⁻¹ L' ∈ Ω := hΩ.conjInvariant g⁻¹ L' hL'.1
  have hNcl : IsClassicalMember p f (conjSub g⁻¹ L') z := by
    have e : g⁻¹ * w' * g⁻¹⁻¹ = z := by rw [inv_inv, ← hww, hwg]; group
    exact e ▸ hw'.conj g⁻¹
  have hNz : conjSub g⁻¹ L' ∈ centralizingMembers Ω {z} :=
    ⟨hNΩ, le_centralizer_of_isClassicalMember hNcl⟩
  have hNK : conjSub g⁻¹ L' = K :=
    eq_of_locImg_le_Q₀ (by omega) hodd hΩ hex hK hz hP1 d hNz
      (locImg_self_le_Q₀ (by omega) hodd hNΩ hNcl d)
  have hL'L : L' = L := by
    rw [hg, ← hNK, conjSub_conjSub_inv]
  have hc : Commutes L L' := by
    refine (commutes_iff_locImg hΩ hP1 hL hL').mpr ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes d.ψ
      (commutes_Lc_of_disjoint h2 (nodePair_disjoint (by omega) (by omega) (by omega)))
  rw [hL'L] at hc
  exact not_commutes_self_of_isClassicalMember hw hc

end CFSG.ClassicalInvolution.RouteD
