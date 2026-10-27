module

public import CFSG.ClassicalInvolution.Q3.Q3EXConj
public import CFSG.ClassicalInvolution.Q3.Q3EXFixed

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Quotients

theorem finite_spin_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    Finite (spinGroup (quadOdd n 𝔽₃)) :=
  ModelFacts.finite_modelUniv (t := .POmegaOdd) (by norm_num) Nat.prime_three trivial hadm

theorem finite_spin_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    Finite (spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
  ModelFacts.finite_modelUniv (t := .POmegaMinus) (by norm_num) Nat.prime_three trivial hadm

theorem central3_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1)
    [Finite (spinGroup (quadOdd n 𝔽₃))] :
    Central3 (spinAction (quadOdd n 𝔽₃)) (fundamentalSubgroups .POmegaOdd (oddDatum n 𝔽₃))
      (fundSet (quadOdd n 𝔽₃)) := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hM : modelUniv .POmegaOdd n 3 1 Fact.out =
      ⟨spinGroup (quadOdd n (GaloisField 3 1)), oddDatum n (GaloisField 3 1)⟩ := rfl
  have hsingle : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaOdd n 3 1 Fact.out trivial hadm (by decide)
      (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D,
      ModelFacts.Gen3 R := fun R hR =>
    ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaOdd) h3 trivial hadm (by decide)
      (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaOdd n 3 1 Fact.out).D.rank, k.val + 1 < n →
      IsLongestRoot (modelUniv .POmegaOdd n 3 1 Fact.out).D (Pi.single k 1) :=
    fun k hk => ModelFacts.isLongestRoot_single .POmegaOdd n 3 1 Fact.out trivial hadm k hk
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaOdd)
      trivial hadm (by decide) (by decide) hR
  have hne : (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D).Nonempty :=
    nonempty_fund_odd (p := 3) (f := 1) hn3
  generalize modelUniv .POmegaOdd n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hne
  subst hM
  have hn0 : 0 < n := by omega
  have ctx := spinCtx3_odd hn3 ⟨0, hn0⟩ rfl hsingle (hlong ⟨0, hn0⟩ (by show 0 + 1 < n; omega))
    hG3 hsl2
  exact central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne

theorem central3_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1)
    [Finite (spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))] :
    Central3 (spinAction (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
      (fundamentalSubgroups .POmegaMinus (minusDatum n (minusCoeffs_irr 3 1)))
      (fundSet (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hM : modelUniv .POmegaMinus n 3 1 Fact.out =
      ⟨spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum n (minusCoeffs_irr 3 1)⟩ := rfl
  have hsingle : FundamentalSingleClass .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaMinus n 3 1 Fact.out trivial hadm (by decide)
      (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D,
      ModelFacts.Gen3 R := fun R hR =>
    ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaMinus) h3 trivial hadm (by decide)
      (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaMinus n 3 1 Fact.out).D.rank, k.val + 2 < n →
      IsLongestRoot (modelUniv .POmegaMinus n 3 1 Fact.out).D (Pi.single k 1) :=
    fun k hk => ModelFacts.isLongestRoot_single .POmegaMinus n 3 1 Fact.out trivial hadm k hk
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaMinus)
      trivial hadm (by decide) (by decide) hR
  have hne : (fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Fact.out).D).Nonempty :=
    nonempty_fund_minus (p := 3) (f := 1) hn4
  generalize modelUniv .POmegaMinus n 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hne
  subst hM
  have hn0 : 0 < n - 1 := by omega
  have ctx := spinCtx3_minus (minusCoeffs_irr 3 1) hn4 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 2 < n; omega)) hG3 hsl2
  exact central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne

end Quotients

section Fixed

theorem oddTwinFixed3_spin (hadm : StatedLieAdmissible .POmegaOdd 3 3 1)
    [Finite (spinGroup (quadOdd 3 𝔽₃))] {X : Type} [Group X]
    (ψ : spinGroup (quadOdd 3 𝔽₃) →* X)
    (hψker : ψ.ker ≤ Subgroup.center (spinGroup (quadOdd 3 𝔽₃)))
    (σ : X ≃* X) (hσ2 : ∀ x, σ (σ x) = x) (hσr : ∀ k, σ (ψ k) ∈ ψ.range)
    {R R' : Subgroup (spinGroup (quadOdd 3 𝔽₃))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 𝔽₃))
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 𝔽₃))
    (htw : IsFundTwin (fundamentalSubgroups .POmegaOdd (oddDatum 3 𝔽₃)) R R')
    (hfixR : ∀ r ∈ R, σ (ψ r) = ψ r) : ∀ r ∈ R', σ (ψ r) = ψ r := by
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hn3 : 3 ≤ 3 := le_refl 3
  have hC := central3_odd hadm
  have hQ := nondegenerate_polarBilin_quadOdd 3 𝔽₃ h2
  have hdim : Module.finrank 𝔽₃ (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hY := yData3_odd hn3 hadm
  have hcop : ∀ w ∈ Subgroup.center (spinGroup (quadOdd 3 𝔽₃)), ¬ 3 ∣ orderOf w := hY.cop
  have hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1 := by
    intro x hx h3
    by_contra hne
    have h1 : orderOf x ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    have h33 : orderOf x = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3)).resolve_left h1
    exact hcop x (hψker hx) (by rw [h33])
  obtain ⟨α, g, hαψ, hα⟩ :=
    ModelFacts.OrthAut.exists_isConj_lift_odd (p := 3) (f := 1) (by norm_num) hn3 le_rfl
      (by rw [natCard_galoisField_three]; norm_num) ψ hψker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadOdd 3 𝔽₃)) := isPerfect_spinGroup_quadOdd h2 hn3
  have hα2 : ∀ y, α (α y) = y := by
    have key := ModelFacts.OrthAut.eq_of_inv_mul_mem_center
      ((α : spinGroup (quadOdd 3 𝔽₃) →* _).comp (α : spinGroup (quadOdd 3 𝔽₃) →* _))
      (MonoidHom.id _) (fun x => by
        apply hψker
        rw [MonoidHom.mem_ker]
        change ψ (x⁻¹ * α (α x)) = 1
        rw [map_mul, map_inv, hαψ, hαψ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  obtain ⟨i, fr, hRfr, -⟩ := hC.map_mem R hR
  have htwin := IsFundTwin.to_map3 hC hR hR' htw
  rw [hRfr] at htwin
  have hsame : ∀ (R₀ R₁ : Subgroup (_ ≃ₗ[𝔽₃] _)) (i₀ i₁ : _ ≃ₗ[𝔽₃] _),
      IsFundamental (quadOdd 3 𝔽₃) R₀ i₀ → IsFundamental (quadOdd 3 𝔽₃) R₁ i₁ →
      Commutes R₀ R₁ → i₁ = i₀ :=
    fun R₀ R₁ i₀ i₁ h₀ h₁ hc => commuting_same_involution hodd (by rw [hdim]; omega) h₀ h₁ hc
  have hR'fr : R'.map (spinAction (quadOdd 3 𝔽₃)) = fr.swap.La.range :=
    eq_swap_of_isFundTwin hodd hsame fr (hC.map_mem R' hR') htwin
  have hfix : ∀ r ∈ R, α r = r :=
    fixes_of_gen3_of_ker ψ hψker hk3 (hC.gen R hR) α fun r hr => by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαψ, hfixR r hr, inv_mul_cancel]
  have hfixR' := fixes_twin_of_isConj3 hQ (by rw [hdim]; omega) hα hα2
    (ker_spinAction_le_center _) hC.k3 fr (hC.gen R' hR') hRfr hR'fr hfix
    (fun g' hg hskew _ => no_skew_adjoint_odd h2 hQ (by rw [hdim]; decide) g' hg hskew)
  intro r' hr'
  rw [← hαψ, hfixR' r' hr']

theorem minusTwinFixed3_spin (hadm : StatedLieAdmissible .POmegaMinus 4 3 1)
    [Finite (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))]
    {X : Type} [Group X]
    (ψ : spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) →* X)
    (hψker : ψ.ker ≤ Subgroup.center
      (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))
    (σ : X ≃* X) (hσ2 : ∀ x, σ (σ x) = x) (hσr : ∀ k, σ (ψ k) ∈ ψ.range)
    {R R' : Subgroup (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))}
    (hR : R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)))
    (htw : IsFundTwin
      (fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1))) R R')
    (hfixR : ∀ r ∈ R, σ (ψ r) = ψ r) : ∀ r ∈ R', σ (ψ r) = ψ r := by
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hn4 : 4 ≤ 4 := le_refl 4
  have h4 : 2 ≤ Nat.card 𝔽₃ := by rw [natCard_galoisField_three]; norm_num
  have hirr := minusCoeffs_irr 3 1
  have hC := central3_minus hadm
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 𝔽₃ hirr
  have hdim : Module.finrank 𝔽₃ (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hY := yData3_minus hn4 hadm
  have hcop : ∀ w ∈ Subgroup.center
      (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)), ¬ 3 ∣ orderOf w :=
    hY.cop
  have hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1 := by
    intro x hx h3
    by_contra hne
    have h1 : orderOf x ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    have h33 : orderOf x = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3)).resolve_left h1
    exact hcop x (hψker hx) (by rw [h33])
  obtain ⟨α, g, hαψ, hα⟩ :=
    ModelFacts.OrthAut.exists_isConj_lift_minus (p := 3) (f := 1) (by norm_num) hn4 le_rfl
      (by rw [natCard_galoisField_three]; norm_num) hirr ψ hψker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
    isPerfect_spinGroup_quadMinus hn4 hirr
  have hα2 : ∀ y, α (α y) = y := by
    have key := ModelFacts.OrthAut.eq_of_inv_mul_mem_center
      ((α : spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) →* _).comp
        (α : spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) →* _))
      (MonoidHom.id _) (fun x => by
        apply hψker
        rw [MonoidHom.mem_ker]
        change ψ (x⁻¹ * α (α x)) = 1
        rw [map_mul, map_inv, hαψ, hαψ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  obtain ⟨i, fr, hRfr, -⟩ := hC.map_mem R hR
  have htwin := IsFundTwin.to_map3 hC hR hR' htw
  rw [hRfr] at htwin
  have hsame : ∀ (R₀ R₁ : Subgroup (_ ≃ₗ[𝔽₃] _)) (i₀ i₁ : _ ≃ₗ[𝔽₃] _),
      IsFundamental (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) R₀ i₀ →
      IsFundamental (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) R₁ i₁ →
      Commutes R₀ R₁ → i₁ = i₀ :=
    fun R₀ R₁ i₀ i₁ h₀ h₁ hc => quadMinus_four_same_involution3 hodd hirr h4 h₀ h₁ hc
  have hR'fr : R'.map (spinAction (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) =
      fr.swap.La.range := eq_swap_of_isFundTwin hodd hsame fr (hC.map_mem R' hR') htwin
  have hfix : ∀ r ∈ R, α r = r :=
    fixes_of_gen3_of_ker ψ hψker hk3 (hC.gen R hR) α fun r hr => by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαψ, hfixR r hr, inv_mul_cancel]
  have hfixR' := fixes_twin_of_isConj3 hQ (by rw [hdim]; omega) hα hα2
    (ker_spinAction_le_center _) hC.k3 fr (hC.gen R' hR') hRfr hR'fr hfix
    (fun g' hg hskew ⟨c, hc, hsq⟩ =>
      false_of_skewRoot_quadMinus_four3 h2 hodd hirr h4 ⟨hg, hskew, hsq, hc⟩)
  intro r' hr'
  rw [← hαψ, hfixR' r' hr']

end Fixed

end CFSG.ClassicalInvolution.Q3.Q3W.EX

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups


theorem shapePiece3_of_fixedFacts (h3 : OddThreeFreeInput) {tY : StatedLieTag} {nY : ℕ}
    (hY : YData3 tY nY) (hne : (modelFund 3 1 tY nY).Nonempty)
    (hgen : ∀ {X : Type} [Group X] (ψ : (modelUniv tY nY 3 1 Nat.prime_three).K →* X),
      ψ.range ≤ ⨆ R ∈ modelFund 3 1 tY nY, R.map ψ)
    (hT : FundTwinsExist (modelFund 3 1 tY nY)) (hDC : FundHubUnique (modelFund 3 1 tY nY))
    (hL : FundTwinFixed (modelFund 3 1 tY nY)) : ShapePiece3 1 (CompData.model tY nY) := by
  intro G _ _ _ hnab K z hR hshape
  exfalso
  have hΩ := hR.inClass
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictT hY.sc hΩ hK hR.cls hshape
  let c : ETCtx3 tY nY (conjClass3 K) K z :=
    { hΩ := hΩ, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1, hO3 := h3 G K z hR, d := d,
      hY := hY }
  exact EX.false_of_twin_fixed3 c (fun L hLΩ => single_class3 K L hLΩ) hshape hne (hgen c.d.ψ)
    hT hDC hL

theorem shapePiece3_odd_small (h3 : OddThreeFreeInput) :
    ShapePiece3 1 (CompData.model .POmegaOdd 3) := by
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hY := yData3_odd (le_refl 3) hadm
  have : Finite (spinGroup (quadOdd 3 (GaloisField 3 1))) := EX.finite_spin_odd hadm
  have hC := EX.central3_odd hadm
  have hodd := odd_natCard_galoisField_three
  have hQ := nondegenerate_polarBilin_quadOdd 3 (GaloisField 3 1) two_ne_zero_three
  have hdim : Module.finrank (GaloisField 3 1) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField 3 1) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hT : FundTwinsExist (fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField 3 1))) :=
    EX.FundTwinsExist.of_central3 hC (fun L hL => exists_isFundTwin_fundSet hodd hL)
  have hDC : FundHubUnique (fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField 3 1))) :=
    EX.FundHubUnique.of_central3 hC (fundSet_hubUnique hodd hQ (Or.inr (by omega)))
  refine shapePiece3_of_fixedFacts h3 hY (nonempty_fund_odd (p := 3) (f := 1) le_rfl) ?_ hT hDC ?_
  · intro X _ ψ
    exact Gaps.range_le_iSup_fund_odd (p := 3) (f := 1) le_rfl hadm hY.std ψ
  · intro X _ ψ hψker σ hσ2 hσr R hR R' hR' htw hfixR
    exact EX.oddTwinFixed3_spin hadm ψ hψker σ hσ2 hσr hR hR' htw hfixR

theorem shapePiece3_minus_small (h3 : OddThreeFreeInput) :
    ShapePiece3 1 (CompData.model .POmegaMinus 4) := by
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hY := yData3_minus (le_refl 4) hadm
  have : Finite (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2)) := EX.finite_spin_minus hadm
  have hC := EX.central3_minus hadm
  have hodd := odd_natCard_galoisField_three
  have h4 : 2 ≤ Nat.card (GaloisField 3 1) := by rw [natCard_galoisField_three]; norm_num
  have hT : FundTwinsExist
      (fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1))) :=
    EX.FundTwinsExist.of_central3 hC (fun L hL => exists_isFundTwin_fundSet hodd hL)
  have hDC : FundHubUnique
      (fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1))) :=
    EX.FundHubUnique.of_central3 hC (fundSet_hubUnique_of_same hodd
      fun R₀ R₁ i₀ i₁ h₀ h₁ hc =>
        EX.quadMinus_four_same_involution3 hodd (minusCoeffs_irr 3 1) h4 h₀ h₁ hc)
  refine shapePiece3_of_fixedFacts h3 hY (nonempty_fund_minus (p := 3) (f := 1) le_rfl) ?_ hT hDC
    ?_
  · intro X _ ψ
    exact range_le_iSup_fund_minus (p := 3) (f := 1) le_rfl hadm hY.std ψ
  · intro X _ ψ hψker σ hσ2 hσr R hR R' hR' htw hfixR
    exact EX.minusTwinFixed3_spin hadm ψ hψker σ hσ2 hσr hR hR' htw hfixR

end CFSG.ClassicalInvolution.Q3.Q3W
