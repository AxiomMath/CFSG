module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.Burgoyne.X10
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem noPSL2Odd_toralCentralizer_G2_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) (b : Fin Tag.G2.rank → Kˣ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) {M : Subgroup (toralCentralizer .G2 K b)}
    (hM : IsComponent M) : NoPSL2Odd M := by
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hKodd) (by decide)
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hKr : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, -, hcases, hstruct, hq3⟩ :=
    odd_G2_toral_involution_fixed_p_components K hKodd b hb
  by_cases hK3 : Nat.card K = 3
  · have := (hq3 hK3 hb1).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨α₀, β₀, hc⟩ : ∃ α₀ β₀ : Fin Tag.G2.rank → ℤ,
      (b = ![-1, 1] ∧ α₀ = ![0, 1] ∧ β₀ = ![2, 3]) ∨
        (b = ![1, -1] ∧ α₀ = ![1, 0] ∧ β₀ = ![1, 2]) ∨
          (b = ![-1, -1] ∧ α₀ = ![1, 1] ∧ β₀ = ![1, 3]) := by
    rcases hcases with h | h | h | h
    · exact absurd h hb1
    · exact ⟨_, _, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨_, _, Or.inr (Or.inl ⟨h, rfl, rfl⟩)⟩
    · exact ⟨_, _, Or.inr (Or.inr ⟨h, rfl, rfl⟩)⟩
  obtain ⟨-, -, hS, hcomm, -, ⟨eα⟩, ⟨eβ⟩, hSX, hSn, hsolv, -⟩ := hstruct α₀ β₀ hc
  set X := toralCentralizer .G2 K b
  set Qα := rootSubgroup .G2 K α₀ ⊔ rootSubgroup .G2 K (-α₀)
  set Qβ := rootSubgroup .G2 K β₀ ⊔ rootSubgroup .G2 K (-β₀)
  have hQαX : Qα ≤ X := (hS ▸ (le_sup_left : Qα ≤ Qα ⊔ Qβ)).trans hSX
  have hQβX : Qβ ≤ X := (hS ▸ (le_sup_right : Qβ ≤ Qα ⊔ Qβ)).trans hSX
  have hD : (rootSpan .G2 K (rootCharKernel b)).subgroupOf X =
      Qα.subgroupOf X ⊔ Qβ.subgroupOf X := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hQαX hQβX
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  let eα' : Qα.subgroupOf X ≃* SL2 K := (Subgroup.subgroupOfEquivOfLe hQαX).trans eα.symm
  let eβ' : Qβ.subgroupOf X ≃* SL2 K := (Subgroup.subgroupOfEquivOfLe hQβX).trans eβ.symm
  have hqα : IsQuasisimple (Qα.subgroupOf X) := LocalCores.isQuasisimple_of_mulEquiv eα'.symm hSL
  have hqβ : IsQuasisimple (Qβ.subgroupOf X) := LocalCores.isQuasisimple_of_mulEquiv eβ'.symm hSL
  have hαβ : ∀ x ∈ Qα.subgroupOf X, ∀ y ∈ Qβ.subgroupOf X, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp h1 _ hy).symm)
  have hnα : ((Qα.subgroupOf X).subgroupOf
      ((rootSpan .G2 K (rootCharKernel b)).subgroupOf X)).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  have hnβ : ((Qβ.subgroupOf X).subgroupOf
      ((rootSpan .G2 K (rootCharKernel b)).subgroupOf X)).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hαβ y hy x hx).symm)
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  rcases eq_or_eq_of_isComponent_le_sup hD hqα hqβ hnα hnβ hM hMS with h | h
  · exact noPSL2Odd_of_mulEquiv_SL2 hKr ((MulEquiv.subgroupCongr h).trans eα')
  · exact noPSL2Odd_of_mulEquiv_SL2 hKr ((MulEquiv.subgroupCongr h).trans eβ')

theorem excInnerNoPSL2_G2
    : ExcInnerNoPSL2 .G2 := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo L hL
  have hKodd : Odd (Nat.card K) := by rw [hKp]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hKp
      exact absurd hKp (Finite.one_lt_card).ne'
    · exact h0
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag (Or.inl rfl) hKodd hαg hα
  exact NoPSL2Odd.of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
    (noPSL2Odd_toralCentralizer_G2_component hp hp2 hKp hf b hb (hb1 hα1)
      (LocalCores.isComponent_map_mulEquiv Θ hL))

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
