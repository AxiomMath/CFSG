module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dSp

public section

namespace CFSG.ClassicalInvolution.NDB.WC.Sp

open CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp CFSG.ClassicalInvolution.NDB.Model
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (QE r0 isQuasisimple_sl2)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf perfectResidual)
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.SCRSp4 (commute_longBlock_01 sq_neg_one_of_center_same
  sq_neg_one_of_center_other sp4_mul_self_eq_one_of_center neg_one_inv_SL2)
open CFSG.ClassicalInvolution.Generic (conjSub)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem exists_conj_u0_of_twin [Finite F] (h2 : (2 : F) ≠ 0)
    {R R' : Subgroup (StatedSp 2 F)} (hR : ∃ i, IsLongRootSp2 R i)
    (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R') {x x' : StatedSp 2 F} (hxR : x ∈ R)
    (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F)) {a a' : StatedSp 2 F} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F)) :
    ∃ c : StatedSp 2 F, a * a' = c * u0 F * c⁻¹ ∧ x * x'⁻¹ = zneg F := by
  have hx2 : x * x = 1 := sp4_mul_self_eq_one_of_center hR hxR hxc
  have hx'2 : x' * x' = 1 := sp4_mul_self_eq_one_of_center hR' hx'R' hx'c
  have hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    have := (Subgroup.center (StatedSp 2 F)).inv_mem hsame
    simpa using this
  obtain ⟨g, k, hRg, hR'g⟩ := CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4.twin_std_sp h2
    hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  have hxg : x = g * longInv F 2 k * g⁻¹ := by
    have hi : IsLongRootSp2 R (g * longInv F 2 k * g⁻¹) := by
      rw [hRg]
      exact (isLongRootSp2_standard k).conj g
    exact hi.eq_of_orderOf_eq_two h2 hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hx'g : x' = g * longInv F 2 (Fin.rev k) * g⁻¹ := by
    have hi : IsLongRootSp2 R' (g * longInv F 2 (Fin.rev k) * g⁻¹) := by
      rw [hR'g]
      exact (isLongRootSp2_standard (Fin.rev k)).conj g
    exact hi.eq_of_orderOf_eq_two h2 hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
  rw [hRg] at ha
  rw [hR'g] at ha'
  obtain ⟨a₀, ⟨A, hA⟩, hae⟩ := ha
  obtain ⟨a₀', ⟨A', hA'⟩, hae'⟩ := ha'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae hae'
  have hsq'' : a' * a' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    have := (Subgroup.center (StatedSp 2 F)).mul_mem hsq' hc
    simpa [mul_assoc] using this
  have hA₁ : longBlock F 2 k A * longBlock F 2 k A * (longInv F 2 k)⁻¹ ∈
      Subgroup.center (StatedSp 2 F) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (longBlock F 2 k A * longBlock F 2 k A * (longInv F 2 k)⁻¹) * g⁻¹ =
        a * a * x⁻¹ := by
      rw [← hae, hA, hxg]
      group
    rw [e]
    exact hsq
  have hA₂ : longBlock F 2 (Fin.rev k) A' * longBlock F 2 (Fin.rev k) A' * (longInv F 2 k)⁻¹ ∈
      Subgroup.center (StatedSp 2 F) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (longBlock F 2 (Fin.rev k) A' * longBlock F 2 (Fin.rev k) A' *
        (longInv F 2 k)⁻¹) * g⁻¹ = a' * a' * x⁻¹ := by
      rw [← hae', hA', hxg]
      group
    rw [e]
    exact hsq''
  have hAA : A * A = -1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, sq_neg_one_of_center_same k hA₁,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one])
  have hAA' : A' * A' = -1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, sq_neg_one_of_center_other k hA₂,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one])
  have hcomm : Commute (longBlock F 2 k A) (longBlock F 2 (Fin.rev k) A') := by
    fin_cases k
    · exact commute_longBlock_01 A A'
    · exact (commute_longBlock_01 A' A).symm
  set w := longBlock F 2 k A * longBlock F 2 (Fin.rev k) A' with hw
  have e2 : a * a' = g * w * g⁻¹ := by
    rw [← hae, ← hae', ← hA, ← hA', hw]
    group
  have hwR : w ∈ R0 F ⊔ R0' F := by
    fin_cases k
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨A, rfl⟩) (Subgroup.mem_sup_right ⟨A', rfl⟩)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨A, rfl⟩) (Subgroup.mem_sup_left ⟨A', rfl⟩)
  have hww : w * w = zneg F := by
    rw [hw, mul_mul_eq_of_commute hcomm, ← map_mul, ← map_mul, hAA, hAA', ←
      longInv_mul_longInv_rev k]
    rfl
  have hwc : w * w ∈ Subgroup.center (StatedSp 2 F) := hww ▸ zneg_mem_center
  have hz1 := zneg_ne_one h2
  have hzx : zneg F * x0 F * (zneg F * x0 F) = 1 := by
    have hc0 := Subgroup.mem_center_iff.mp (zneg_mem_center (F := F)) (x0 F)
    rw [mul_mul_eq_of_commute (show Commute (zneg F) (x0 F) from hc0.symm), zneg_mul_self,
      x0_mul_self, one_mul]
  rcases classify_w h2 hwR hwc with h | h | h | h | ⟨hh, -, hwh⟩
  · rw [h, one_mul] at hww
    exact absurd hww.symm hz1
  · rw [h, x0_mul_self] at hww
    exact absurd hww.symm hz1
  · rw [h, hzx] at hww
    exact absurd hww.symm hz1
  · rw [h, zneg_mul_self] at hww
    exact absurd hww.symm hz1
  have hinv : (longInv F 2 (Fin.rev k))⁻¹ = longInv F 2 (Fin.rev k) := by
    rw [longInv, ← map_inv, neg_one_inv_SL2]
  refine ⟨g * hh, by rw [e2, hwh]; group, ?_⟩
  rw [hxg, hx'g]
  have : g * longInv F 2 k * g⁻¹ * (g * longInv F 2 (Fin.rev k) * g⁻¹)⁻¹ =
      g * (longInv F 2 k * (longInv F 2 (Fin.rev k))⁻¹) * g⁻¹ := by group
  rw [this, hinv, longInv_mul_longInv_rev k, zneg_conj]

theorem eq_of_centralizes_twin [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {R R' : Subgroup (StatedSp 2 F)} (hR : ∃ i, IsLongRootSp2 R i)
    (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R') {x x' : StatedSp 2 F} (hxR : x ∈ R)
    (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F)) {a a' : StatedSp 2 F} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F)) {y : StatedSp 2 F}
    (hy2 : y * y = 1) (hyu : y * (a * a') = a * a' * y)
    (hyc : ∀ w ∈ perfectResidualOf (Subgroup.centralizer ({a * a'} : Set (StatedSp 2 F))),
      y * w = w * y) : y = 1 ∨ y = x * x'⁻¹ := by
  obtain ⟨c, hc, hxx⟩ := exists_conj_u0_of_twin h2 hR hR' hne hxR hxc hx1 hx'R' hx'c hx'1 hsame
    ha ha' hsq hsq'
  obtain ⟨lam, hlam⟩ := exists_lam h2
  set y₀ := c⁻¹ * y * c with hy₀
  have hy₀2 : y₀ * y₀ = 1 := by
    calc y₀ * y₀ = c⁻¹ * (y * y) * c := by rw [hy₀]; group
      _ = 1 := by rw [hy2]; group
  have hy₀u : y₀ * u0 F = u0 F * y₀ := by
    have e : u0 F = c⁻¹ * (a * a') * c := by rw [hc]; group
    rw [e, hy₀]
    calc c⁻¹ * y * c * (c⁻¹ * (a * a') * c) = c⁻¹ * (y * (a * a')) * c := by group
      _ = c⁻¹ * (a * a' * y) * c := by rw [hyu]
      _ = c⁻¹ * (a * a') * c * (c⁻¹ * y * c) := by group
  have hy₀c : ∀ B : SL(2, F), y₀ * iota h2 hlam B = iota h2 hlam B * y₀ := by
    intro B
    have hmem : c * iota h2 hlam B * c⁻¹ ∈
        perfectResidualOf (Subgroup.centralizer ({a * a'} : Set (StatedSp 2 F))) := by
      rw [hc, ← CFSG.ClassicalInvolution.Balance.conjSub_centralizer_singleton,
        Balance.Bootstrap.perfectResidualOf_conjSub, perfectResidualOf_centralizer_u0 h2 h4 hlam]
      exact ⟨iota h2 hlam B, ⟨B, rfl⟩, rfl⟩
    have h1 := hyc _ hmem
    rw [hy₀]
    calc c⁻¹ * y * c * iota h2 hlam B = c⁻¹ * (y * (c * iota h2 hlam B * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * iota h2 hlam B * c⁻¹) * y) * c := by rw [h1]
      _ = iota h2 hlam B * (c⁻¹ * y * c) := by group
  rcases eq_one_or_zneg_of_centralizes h2 hlam hy₀2 hy₀u hy₀c with h | h
  · left
    calc y = c * y₀ * c⁻¹ := by rw [hy₀]; group
      _ = 1 := by rw [h]; group
  · right
    calc y = c * y₀ * c⁻¹ := by rw [hy₀]; group
      _ = x * x'⁻¹ := by rw [h, zneg_conj, hxx]

theorem eq_of_centralizes_model {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (t : StatedLieTag)
    (n e : ℕ) (ht : t = .PSp) (hn : n = 2) (hadm : StatedLieAdmissible t n p e)
    (h4 : 4 ≤ p ^ e) {R R' : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hne : R ≠ R') {x x' : (Generic.modelUniv t n p e Fact.out).K} (hxR : x ∈ R)
    (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    {a a' : (Generic.modelUniv t n p e Fact.out).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    {y : (Generic.modelUniv t n p e Fact.out).K} (hy2 : y * y = 1)
    (hyu : y * (a * a') = a * a' * y)
    (hyc : ∀ w ∈ perfectResidualOf (Subgroup.centralizer
      ({a * a'} : Set (Generic.modelUniv t n p e Fact.out).K)), y * w = w * y) :
    y = 1 ∨ y = x * x'⁻¹ := by
  subst ht hn
  have he : e ≠ 0 := by
    rintro rfl
    simp at h4
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hcard : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    exact h4
  exact eq_of_centralizes_twin h2 hcard ((ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).mp hR)
    ((ModelFacts.fund_iff_isLongRootSp2 hadm h2 R').mp hR') hne hxR hxc hx1 hx'R' hx'c hx'1 hsame
    ha ha' hsq hsq' hy2 hyu hyc

end CFSG.ClassicalInvolution.NDB.WC.Sp
