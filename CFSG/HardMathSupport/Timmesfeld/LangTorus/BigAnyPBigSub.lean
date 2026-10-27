module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeCentralCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped commutatorElement

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section Core

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem not_coprime_of_commutator_pair_sub (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {Θ : Set (Fin τ.rank → ℤ)} (hΘ : Θ ⊆ rationalRoots S.ρ (rootCharHom a) i)
    (hMΓ : rootSpan τ L Θ ⊓ S.D.model ≤ S.Γ)
    {y ν : ModGL τ L} {k : ℕ} (hy : y ∈ rootSpan τ L Θ) (hyF : S.D.step y = y)
    (hyp : y ^ p = 1) (hy1 : y ≠ 1) (hν : ν ∈ rootSpan τ L Θ) (hνF : S.D.step ν = ν)
    (hconj : ν * y * ν⁻¹ = y ^ k) (hk : ¬ (p : ℤ) ∣ (k : ℤ) - 1) :
    ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hp := S.hp
  have hle : rootSpan τ L Θ ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) :=
    biSup_mono hΘ
  have hmodel : ∀ g ∈ rootSpan τ L Θ, S.D.step g = g → g ∈ S.Γ := by
    intro g hg hgF
    refine hMΓ (Subgroup.mem_inf.2 ⟨hg, ⟨?_, hgF⟩⟩)
    have : rootSpan τ L Θ ≤ adjointGroup τ L :=
      iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ
    exact this hg
  have hyS : y ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.mem_inf.2 ⟨hle hy, hmodel y hy hyF⟩
  have hνS : ν ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.mem_inf.2 ⟨hle hν, hmodel ν hν hνF⟩
  have hk' : (k : ZMod p) - 1 ≠ 0 := by
    intro h
    apply hk
    have : ((((k : ℤ) - 1 : ℤ)) : ZMod p) = 0 := by
      push_cast
      exact h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 this
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ZMod p) * ((k : ZMod p) - 1) = 1 := by
    refine ⟨(((k : ZMod p) - 1)⁻¹).val, ?_⟩
    rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ hk']
  have hym : y ^ m ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := Subgroup.pow_mem _ hyS m
  have hcomm : ⁅ν, y ^ m⁆ = y := by
    have h1 : ν * y ^ m * ν⁻¹ = y ^ (k * m) := by
      rw [← conj_pow, hconj, ← pow_mul]
    have hint : ((m : ℤ) * ((k : ℤ) - 1) - 1 : ℤ) ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ) := by
      rw [Ideal.mem_span_singleton, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hm, sub_self]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 hint
    rw [commutatorElement_def, h1]
    have h2 : y ^ (k * m) * (y ^ m)⁻¹ * y⁻¹ = y ^ (((k : ℤ) * m - m - 1 : ℤ)) := by
      rw [show ((k : ℤ) * m - m - 1) = ((k * m : ℕ) : ℤ) + (-(m : ℤ)) + (-1) by push_cast; ring,
        zpow_add, zpow_add, zpow_natCast, zpow_neg, zpow_neg, zpow_natCast, zpow_one]
    have h3 : ((k : ℤ) * m - m - 1 : ℤ) = p * t := by linarith
    have h4 : y ^ (k * m) * (y ^ m)⁻¹ * y⁻¹ = 1 := by
      rw [h2, h3, zpow_mul, zpow_natCast, hyp, one_zpow]
    exact mul_inv_eq_one.1 h4
  have hyR : y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator hνS hym
  have hord : orderOf y = p := by
    refine orderOf_eq_prime hyp hy1
  have hdvd : p ∣ Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    have h := Subgroup.orderOf_dvd_natCard (rationalComponent S.ρ S.Γ (rootCharHom a) i) hyR
    rw [hord] at h
    exact h
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt dvd_rfl hdvd

end Core

end CFSG.HardMathSupport.Timmesfeld.LangTorus
