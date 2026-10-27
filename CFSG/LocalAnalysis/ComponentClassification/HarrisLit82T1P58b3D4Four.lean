module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3D4Blk
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDFour

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open P58b3 (OddGen rhoL rhoR)
open scoped MatrixGroups

namespace P58b3D4

variable {K : Type} [Field K] [Finite K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem false_of_blockFactor (hK3 : Nat.card K = 3) {J I : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hI : I = J ∨ I = Jᶜ) (hIc : Iᶜ.Nonempty)
    (Φ : oIsoBlock K hw I ≃* DeterminantIsometries K) {ρ₀ : SL(2, K) →* DeterminantIsometries K}
    (hρ₀ : ρ₀ = rhoL ∨ ρ₀ = rhoR)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, oQ (diagGL hw) x = 0)
    {R₁ : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hR₁x : R₁ ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hR₁s : (R₁.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal)
    (hR₁odd : OddGen ↥R₁) (hnc : ∀ s ∈ R₁, (∀ h ∈ R₁, s * h = h * s) → s * s = 1 → s = 1)
    {B : matrixDerived (oQ (diagGL hw))} (hBR : projH _ B ∈ R₁) (hB3 : projH _ B ^ 3 = 1)
    {A : SL(2, K)} {Y : GL (Fin d) K} (hBY : (B : GL (Fin d) K) = blockFactor hw Φ ρ₀ A * Y)
    (hY : ∀ A' : SL(2, K), blockFactor hw Φ ρ₀ A' * Y = Y * blockFactor hw Φ ρ₀ A')
    (hA3 : A ^ 3 = 1 ∨ A ^ 3 = -1) (hA1 : A ≠ 1) (hA2 : A ≠ -1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hρ₀i : Function.Injective ρ₀ := by
    rcases hρ₀ with rfl | rfl
    · exact P58b3.rhoL_injective
    · exact P58b3.rhoR_injective
  set ρ := blockFactorP hw hK3 Φ ρ₀ hT with hρdef
  have hρi : Function.Injective ρ := blockFactorP_injective hw hK3 hIc Φ hρ₀i hT
  set x := projH (matrixDerived (oQ (diagGL hw))) ⟨signGL K J, hJ⟩ with hx
  have hnorm : ∀ y ∈ centralizer ({x} : Set _), Odd (orderOf y) → ∀ A' : SL(2, K),
      ∃ A'' : SL(2, K), y * ρ A' * y⁻¹ = ρ A'' := by
    intro y hy hyo A'
    obtain ⟨B', rfl, hB'o⟩ := P58b3.exists_odd_orderOf_lift_of_finite
      (QuotientGroup.mk'_surjective _) hyo
    have hcom := commute_sign_of_odd hw hJ hy hB'o
    obtain ⟨A'', hA''⟩ := conj_blockFactor_of_odd hw hK hI Φ hρ₀
      (matrixDerived_le_isometryGroup hw h2 B'.2) hcom (by rwa [Subgroup.orderOf_coe]) A'
    refine ⟨A'', ?_⟩
    rw [hρdef, blockFactorP_apply, blockFactorP_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hA''
  have hρx : ∀ A' : SL(2, K), ρ A' ∈ centralizer ({x} : Set _) := by
    intro A'
    rw [hρdef, blockFactorP_apply, mem_centralizer_singleton_iff, hx, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commute_sign_of_mem hw J I hI (blockFactor_mem hw Φ ρ₀ A'))
  set C : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw)))) :=
    closure {y | y ∈ centralizer ({x} : Set _) ∧ Odd (orderOf y)} with hC
  have hCx : C ≤ centralizer ({x} : Set _) := (closure_le _).mpr fun y hy => hy.1
  have hRC : ρ.range ≤ C := by
    rintro _ ⟨A', rfl⟩
    have hA' : A' ∈ closure {u : SL(2, K) | orderOf u = 3} := by
      rw [CFSG.LieType.HighestRoot.closure_orderOf_three_eq_top_of_mulEquiv hK3
        (MulEquiv.refl _)]
      exact mem_top A'
    have hle : (closure {u : SL(2, K) | orderOf u = 3}).map ρ ≤ C := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨u, hu, rfl⟩
      have hu3 : orderOf u = 3 := hu
      exact subset_closure ⟨hρx u, Odd.of_dvd_nat (by decide) (hu3 ▸ orderOf_map_dvd ρ u)⟩
    exact hle ⟨A', hA', rfl⟩
  have hCN : C ≤ normalizer (ρ.range : Set _) := by
    rw [hC, closure_le]
    intro y hy
    rw [SetLike.mem_coe, mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨A', rfl⟩
      obtain ⟨A'', hA''⟩ := hnorm y hy.1 hy.2 A'
      exact ⟨A'', hA''.symm⟩
    · rintro ⟨A'', hA''⟩
      obtain ⟨A₃, hA₃⟩ := hnorm y⁻¹ (inv_mem hy.1) (by rw [orderOf_inv]; exact hy.2) A''
      refine ⟨A₃, ?_⟩
      rw [← hA₃, hA'', inv_inv]
      group
  have hRn : (ρ.range.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hRC).mpr hCN
  have hR₁C : R₁ ≤ C := hR₁odd.le_closure.trans (closure_mono fun y hy => ⟨hR₁x hy.1, hy.2⟩)
  have hR₁sC : (R₁.subgroupOf C).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hCx hR₁s
  have hYΩ : Y ∈ matrixDerived (oQ (diagGL hw)) := by
    have e : Y = (blockFactor hw Φ ρ₀ A)⁻¹ * B := by rw [hBY]; group
    rw [e]
    exact mul_mem (inv_mem (blockFactor_mem_matrixDerived hw hK3 Φ ρ₀ hT A)) B.2
  set y := projH (matrixDerived (oQ (diagGL hw))) ⟨Y, hYΩ⟩ with hy
  have hxa : projH _ B = ρ A * y := by
    rw [hρdef, blockFactorP_apply, hy, ← map_mul]
    congr 1
    exact Subtype.ext hBY
  have hyc : ∀ u ∈ ρ.range, u * y = y * u := by
    rintro _ ⟨A', rfl⟩
    rw [hρdef, blockFactorP_apply, hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hY A')
  have ha3 : ρ A ^ 3 = 1 ∨ ρ A ^ 3 = ρ (-1) := by
    rcases hA3 with h | h
    · left
      rw [← map_pow, h, map_one]
    · right
      rw [← map_pow, h]
  have ha1 : ρ A ≠ 1 := fun h => hA1 (hρi (h.trans (map_one ρ).symm))
  have ha2 : ρ A ≠ ρ (-1) := fun h => hA2 (hρi h)
  obtain ⟨k, ⟨hkR, g, rfl⟩, hk4, hk2⟩ := exists_mem_inf_of_noncentral hK3 ρ hρi hRC hRn hR₁C
    hR₁sC hBR hB3 ⟨A, rfl⟩ hyc hxa ha3 ha1 ha2
  have hg4 : g ^ 4 = 1 := hρi (by rw [map_pow, hk4, map_one])
  have hg2 : g ^ 2 ≠ 1 := fun h => hk2 (by rw [← map_pow, h, map_one])
  have hgsq := P58b3.sq_eq_neg_one_of_pow_four h2 hg4 hg2
  have hcen : ∀ c ∈ C, c * ρ (-1) = ρ (-1) * c := by
    intro c hc
    obtain ⟨u, hu⟩ : c * ρ (-1) * c⁻¹ ∈ ρ.range :=
      (mem_normalizer_iff.mp (hCN hc) _).mp ⟨-1, rfl⟩
    have hord : orderOf (ρ u) = 2 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj c) (ρ (-1))
      rw [MulAut.conj_apply] at h
      rw [hu, h, orderOf_injective ρ hρi,
        (CFSG.LocalAnalysis.ComponentInitial.sl2_orderOf_eq_two_iff hK _).mpr rfl]
    have hu1 : u = -1 := by
      rw [orderOf_injective ρ hρi] at hord
      exact (CFSG.LocalAnalysis.ComponentInitial.sl2_orderOf_eq_two_iff hK u).mp hord
    rw [hu1] at hu
    calc c * ρ (-1) = c * ρ (-1) * c⁻¹ * c := by group
      _ = ρ (-1) * c := by rw [← hu]
  have hs := hnc _ (pow_mem hkR 2)
    (fun h hh => by rw [← map_pow, hgsq]; exact (hcen h (hR₁C hh)).symm)
    (by rw [← pow_add]; exact hk4)
  exact hk2 hs

theorem false_of_sign_four_plus (hK3 : Nat.card K = 3) {J : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hJ4 : J.card = 4) (hJc4 : Jᶜ.card = 4)
    (hqJ : ¬ IsQuasisimple (blockP K hw J)) (hqJc : ¬ IsQuasisimple (blockP K hw Jᶜ))
    {R₁ : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hR₁x : R₁ ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hR₁s : (R₁.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))).IsSubnormal)
    (hR₁odd : OddGen ↥R₁) {r} (hr : r ∈ R₁) (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1)
    (hnc : ∀ s ∈ R₁, (∀ h ∈ R₁, s * h = h * s) → s * s = 1 → s = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd : d = 8 := by
    have h := Finset.card_add_card_compl J
    rw [Fintype.card_fin, hJ4, hJc4] at h
    omega
  have hT := exists_totallySingular_three hd
    (P58b3L.isPlusType_of_not_isQuasisimple_four hK hw hJ4 hJc4 hqJ hqJc)
  have hro : Odd (orderOf r) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hr3)
  obtain ⟨B, rfl, hBo⟩ := P58b3.exists_odd_orderOf_lift_of_finite
    (QuotientGroup.mk'_surjective _) hro
  have hcom := commute_sign_of_odd hw hJ (hR₁x hr) hBo
  have hB3 : (B : GL (Fin d) K) ^ 3 = 1 := by
    have h1 : projH _ (B ^ 3) = projH _ 1 := by rw [map_pow, map_one]; exact hr3
    rw [projH_eq_projH_iff] at h1
    obtain ⟨c, hc⟩ := mem_subgroupOf.mp h1
    have hz2 : (B ^ 3) ^ 2 = 1 := by
      have e : ((B ^ 3)⁻¹ : matrixDerived (oQ (diagGL hw))) ^ 2 = 1 := by
        apply Subtype.ext
        have e' : (((B ^ 3)⁻¹ * 1 : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) ^ 2 =
            GeneralLinearGroup.scalar (Fin d) (c ^ 2) := by rw [← hc, map_pow]
        rw [P58b3.units_sq_eq_one hK3 c, map_one, mul_one] at e'
        rw [Subgroup.coe_pow, e', Subgroup.coe_one]
      rw [inv_pow, inv_eq_one] at e
      exact e
    have hzm : (B ^ 3) ^ orderOf B = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hz : B ^ 3 = 1 := by
      obtain ⟨j, hj⟩ := hBo
      rw [hj, pow_succ, pow_mul, hz2, one_pow, one_mul] at hzm
      exact hzm
    rw [← Subgroup.coe_pow, hz, Subgroup.coe_one]
  have hBne : (B : GL (Fin d) K) ≠ 1 := fun h => hr1 (by
    have e : B = 1 := Subtype.ext h
    rw [e, map_one])
  obtain ⟨B₁, hB₁, B₂, hB₂, hBe, hBc, hB₁3, hB₂3⟩ := exists_block_of_pow_eq_one hw hK
    (Or.inl rfl) (matrixDerived_le_isometryGroup hw h2 B.2) hcom hB3
  obtain ⟨I, hI, BI, hBI, B', hB', hBe', hBI3, hBI1⟩ : ∃ I : Finset (Fin d), (I = J ∨ I = Jᶜ) ∧
      ∃ BI ∈ oIsoBlock K hw I, ∃ B' ∈ oIsoBlock K hw Iᶜ, (B : GL (Fin d) K) = BI * B' ∧
        BI ^ 3 = 1 ∧ BI ≠ 1 := by
    by_cases h1 : B₁ = 1
    · refine ⟨Jᶜ, Or.inr rfl, B₂, hB₂, B₁, by rwa [compl_compl], by rw [hBe, hBc], hB₂3,
        fun h => hBne ?_⟩
      rw [hBe, h1, h, one_mul]
    · exact ⟨J, Or.inl rfl, B₁, hB₁, B₂, hB₂, hBe, hB₁3, h1⟩
  have hI4 : I.card = 4 := by
    rcases hI with rfl | rfl
    · exact hJ4
    · exact hJc4
  have hIc : Iᶜ.Nonempty := by
    rcases hI with rfl | rfl
    · exact Finset.card_pos.mp (by omega)
    · rw [compl_compl]
      exact Finset.card_pos.mp (by omega)
  have hqI : ¬ IsQuasisimple (blockP K hw I) := by
    rcases hI with rfl | rfl
    · exact hqJ
    · exact hqJc
  obtain ⟨Φ⟩ := nonempty_oIsoBlock_equiv_det hw hK hI4 hIc hqI
  set bI : oIsoBlock K hw I := ⟨BI, hBI⟩ with hbI
  have hΦ3 : Φ bI ^ 3 = 1 := by
    have e : bI ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hBI3)
    rw [← map_pow, e, map_one]
  have hΦodd : Odd (orderOf (Φ bI)) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hΦ3)
  obtain ⟨z, hz⟩ := P58b3.mem_leftRightImage_of_odd hΦodd
  obtain ⟨A, A', hAA, hA3, hA'3⟩ := P58b3.exists_sl_of_rho_pow_three hK3 z (by rw [hz]; exact hΦ3)
  have hBIe : BI = blockFactor hw Φ rhoL A * blockFactor hw Φ rhoR A' := by
    have e : bI = Φ.symm (rhoL A) * Φ.symm (rhoR A') := by
      rw [← map_mul, ← hAA, hz, MulEquiv.symm_apply_apply]
    exact congrArg (fun u : oIsoBlock K hw I => (u : GL (Fin d) K)) e
  have hLR : ∀ A₁ A₂ : SL(2, K), blockFactor hw Φ rhoL A₁ * blockFactor hw Φ rhoR A₂ =
      blockFactor hw Φ rhoR A₂ * blockFactor hw Φ rhoL A₁ := by
    intro A₁ A₂
    have e : Φ.symm (rhoL A₁) * Φ.symm (rhoR A₂) = Φ.symm (rhoR A₂) * Φ.symm (rhoL A₁) := by
      rw [← map_mul, ← map_mul, P58b3.rhoL_mul_rhoR]
    exact congrArg (fun u : oIsoBlock K hw I => (u : GL (Fin d) K)) e
  have hB'c : ∀ (ρ₀ : SL(2, K) →* DeterminantIsometries K) (A₁ : SL(2, K)),
      blockFactor hw Φ ρ₀ A₁ * B' = B' * blockFactor hw Φ ρ₀ A₁ :=
    fun ρ₀ A₁ => commute_of_mem_oIsoBlock hw (blockFactor_mem hw Φ ρ₀ A₁) hB'
  by_cases hAc : A = 1 ∨ A = -1
  · by_cases hA'c : A' = 1 ∨ A' = -1
    ·
      apply hBI1
      have hA2 : A ^ 2 = 1 := by rcases hAc with rfl | rfl <;> simp [pow_two]
      have hA'2 : A' ^ 2 = 1 := by rcases hA'c with rfl | rfl <;> simp [pow_two]
      have hsq : BI ^ 2 = 1 := by
        rw [hBIe, Commute.mul_pow (hLR A A') 2, ← map_pow, ← map_pow, hA2, hA'2, map_one,
          map_one, mul_one]
      calc BI = BI ^ 3 * (BI ^ 2)⁻¹ := by group
        _ = 1 := by rw [hBI3, hsq, inv_one, mul_one]
    · rw [not_or] at hA'c
      refine false_of_blockFactor hw hK3 hJ hI hIc Φ (Or.inr rfl) hT hR₁x hR₁s hR₁odd hnc hr hr3
        (A := A') (Y := blockFactor hw Φ rhoL A * B') ?_ (fun A₂ => ?_) hA'3 hA'c.1 hA'c.2
      · rw [hBe', hBIe, hLR, mul_assoc]
      · rw [← mul_assoc, ← hLR, mul_assoc, hB'c rhoR A₂, ← mul_assoc]
  · rw [not_or] at hAc
    refine false_of_blockFactor hw hK3 hJ hI hIc Φ (Or.inl rfl) hT hR₁x hR₁s hR₁odd hnc hr hr3
      (A := A) (Y := blockFactor hw Φ rhoR A' * B') ?_ (fun A₂ => ?_) hA3 hAc.1 hAc.2
    · rw [hBe', hBIe, mul_assoc]
    · rw [← mul_assoc, hLR, mul_assoc, hB'c rhoL A₂, ← mul_assoc]

end P58b3D4

end CFSG.ComponentClassification.HarrisLit.T1
