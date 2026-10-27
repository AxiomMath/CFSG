module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpLayer
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSp4

public section

namespace CFSG.ClassicalInvolution.NDB.Model

open CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (QE r0 isQuasisimple_sl2)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf perfectResidual)
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.SCRSp4 (commute_longBlock_01 sq_neg_one_of_center_same
  sq_neg_one_of_center_other sp4_mul_self_eq_one_of_center neg_one_inv_SL2)
open CFSG.ClassicalInvolution.Generic (conjSub)
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F] {lam : QE F}

theorem commutator_centralizer_u0_le (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) :
    ⁅Subgroup.centralizer ({u0 F} : Set (StatedSp 2 F)),
      Subgroup.centralizer ({u0 F} : Set (StatedSp 2 F))⁆ ≤ (iota h2 hlam).range := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hg' : g * u0 F = u0 F * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hh' : h * u0 F = u0 F * h := Subgroup.mem_centralizer_singleton_iff.mp hh
  have hgi : g⁻¹ * u0 F = u0 F * g⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ hg)
  have hhi : h⁻¹ * u0 F = u0 F * h⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ hh)
  rw [mem_range_iota_iff h2 hlam]
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mp ?_, ?_⟩
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)
  · obtain ⟨Ng, hNg, -⟩ := exists_unitary_of_comm g hg'
    obtain ⟨Nh, hNh, -⟩ := exists_unitary_of_comm h hh'
    obtain ⟨Ng', hNg', -⟩ := exists_unitary_of_comm g⁻¹ hgi
    obtain ⟨Nh', hNh', -⟩ := exists_unitary_of_comm h⁻¹ hhi
    have hg1 : Ng * Ng' = 1 := by
      apply PhiS_injective
      rw [map_mul, ← hNg, ← hNg', ← map_mul, mul_inv_cancel, map_one, map_one]
    have hh1 : Nh * Nh' = 1 := by
      apply PhiS_injective
      rw [map_mul, ← hNh, ← hNh', ← map_mul, mul_inv_cancel, map_one, map_one]
    refine ⟨Ng * Nh * Ng' * Nh', ?_, ?_⟩
    · rw [commutatorElement_def, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hNg, hNh,
        hNg', hNh']
    · have d1 : Ng.det * Ng'.det = 1 := by rw [← Matrix.det_mul, hg1, Matrix.det_one]
      have d2 : Nh.det * Nh'.det = 1 := by rw [← Matrix.det_mul, hh1, Matrix.det_one]
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
      linear_combination Nh.det * Nh'.det * d1 + d2

theorem perfectResidualOf_le_commutator {M : Type*} [Group M] (H : Subgroup M) :
    perfectResidualOf H ≤ ⁅H, H⁆ := by
  have h1 : perfectResidual ↥H ≤ derivedSeries ↥H 1 := iInf_le _ 1
  have h2 : (derivedSeries ↥H 1).map H.subtype = ⁅H, H⁆ := by
    rw [derivedSeries_one, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  calc perfectResidualOf H = (perfectResidual ↥H).map H.subtype := rfl
    _ ≤ (derivedSeries ↥H 1).map H.subtype := Subgroup.map_mono h1
    _ = ⁅H, H⁆ := h2

theorem perfectResidualOf_centralizer_u0 [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (hlam : star lam * lam = -1) :
    perfectResidualOf (Subgroup.centralizer ({u0 F} : Set (StatedSp 2 F))) =
      (iota h2 hlam).range := by
  have hq : CFSG.IsQuasisimple SL(2, F) := isQuasisimple_sl2 h4
  have : Group.IsPerfect SL(2, F) := hq.1
  have hperf : Group.IsPerfect (iota h2 hlam).range := Group.IsPerfect.range (iota h2 hlam)
  refine le_antisymm ((perfectResidualOf_le_commutator _).trans
    (commutator_centralizer_u0_le h2 hlam)) ?_
  refine Balance.Bootstrap.le_perfectResidualOf_of_perfect ?_ hperf
  rintro _ ⟨B, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (iota_comm_u0 h2 hlam B)


theorem zneg_ne_one (h2 : (2 : F) ≠ 0) : zneg F ≠ 1 := by
  intro h
  have h1 := congrArg (mat 2 F) h
  rw [mat_zneg, map_one] at h1
  have h00 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
  have h3 : (-1 : F) = 1 := by simpa using h00
  exact h2 (by linear_combination -h3)

theorem zneg_mem_range_iota (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) :
    zneg F ∈ (iota h2 hlam).range := by
  rw [mem_range_iota_iff h2 hlam]
  refine ⟨(Subgroup.mem_center_iff.mp zneg_mem_center (u0 F)).symm, -1, ?_, ?_⟩
  · rw [mat_zneg, map_neg, map_one]
  · rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    norm_num

theorem longInv_mul_longInv_rev (k : Fin 2) :
    longInv F 2 k * longInv F 2 (Fin.rev k) = zneg F := by
  rw [zneg_eq_blk, blk]
  fin_cases k
  · rfl
  · exact (commute_longBlock_01 (-1) (-1)).eq.symm

theorem mul_mul_eq_of_commute {M : Type*} [Monoid M] {a b : M} (h : Commute a b) :
    a * b * (a * b) = a * a * (b * b) := by
  rw [mul_assoc, ← mul_assoc b, ← h.eq]
  simp only [mul_assoc]

theorem exists_iota_of_twin [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {R R' : Subgroup (StatedSp 2 F)} (hR : ∃ i, IsLongRootSp2 R i)
    (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R') {x x' : StatedSp 2 F} (hxR : x ∈ R)
    (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F)) {a a' : StatedSp 2 F} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F)) :
    ∃ ι : SL(2, F) →* StatedSp 2 F, Function.Injective ι ∧
      perfectResidualOf (Subgroup.centralizer ({a * a'} : Set (StatedSp 2 F))) = ι.range ∧
      x * x'⁻¹ ∈ ι.range := by
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
  obtain ⟨lam, hlam⟩ := exists_lam h2
  refine ⟨(MulAut.conj (g * hh)).toMonoidHom.comp (iota h2 hlam),
    (MulAut.conj (g * hh)).injective.comp (iota_injective h2 hlam), ?_, ?_⟩
  · have e3 : a * a' = (g * hh) * u0 F * (g * hh)⁻¹ := by
      rw [e2, hwh]
      group
    rw [e3, ← CFSG.ClassicalInvolution.Balance.conjSub_centralizer_singleton,
      Balance.Bootstrap.perfectResidualOf_conjSub, perfectResidualOf_centralizer_u0 h2 h4 hlam,
      MonoidHom.range_comp]
    rfl
  · have hinv : (longInv F 2 (Fin.rev k))⁻¹ = longInv F 2 (Fin.rev k) := by
      rw [longInv, ← map_inv, neg_one_inv_SL2]
    have e4 : x * x'⁻¹ = zneg F := by
      rw [hxg, hx'g]
      have : g * longInv F 2 k * g⁻¹ * (g * longInv F 2 (Fin.rev k) * g⁻¹)⁻¹ =
          g * (longInv F 2 k * (longInv F 2 (Fin.rev k))⁻¹) * g⁻¹ := by group
      rw [this, hinv, longInv_mul_longInv_rev k, zneg_conj]
    obtain ⟨B, hB⟩ := zneg_mem_range_iota h2 hlam
    refine ⟨B, ?_⟩
    rw [e4]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hB]
    exact zneg_conj (g * hh)

theorem exists_iota_model {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (t : StatedLieTag) (n e : ℕ)
    (ht : t = .PSp) (hn : n = 2) (hadm : StatedLieAdmissible t n p e) (h4 : 4 ≤ p ^ e)
    {R R' : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hne : R ≠ R') {x x' : (Generic.modelUniv t n p e Fact.out).K} (hxR : x ∈ R)
    (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    {a a' : (Generic.modelUniv t n p e Fact.out).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K) :
    ∃ ι : SL(2, GaloisField p e) →* (Generic.modelUniv t n p e Fact.out).K,
      Function.Injective ι ∧
      perfectResidualOf (Subgroup.centralizer
        ({a * a'} : Set (Generic.modelUniv t n p e Fact.out).K)) = ι.range ∧
      x * x'⁻¹ ∈ ι.range := by
  subst ht hn
  have he : e ≠ 0 := by
    rintro rfl
    simp at h4
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hcard : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    exact h4
  exact exists_iota_of_twin h2 hcard ((ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).mp hR)
    ((ModelFacts.fund_iff_isLongRootSp2 hadm h2 R').mp hR') hne hxR hxc hx1 hx'R' hx'c hx'1 hsame
    ha ha' hsq hsq'

end CFSG.ClassicalInvolution.NDB.Model
