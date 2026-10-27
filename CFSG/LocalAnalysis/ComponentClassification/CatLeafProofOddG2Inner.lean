module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.LocalAnalysis.SteinbergBMOddResidualToral
public import CFSG.LieType.Chevalley.OddG2ToralInvolutionComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem le_of_isComponent_of_solvable_quotient {G : Type*} [Group G] {J M : Subgroup G}
    [J.Normal] (hsolv : Group.IsSolvable (G ⧸ J)) (hM : IsComponent M) : M ≤ J := by
  intro y hy
  have hf := MonoidHom.range_eq_bot_iff.1
    (LieType.Chevalley.OddToralOrdinary.range_eq_bot_of_commutator_eq_top
      (Group.isPerfect_def.mp hM.1.1) ((QuotientGroup.mk' J).comp M.subtype))
  have hy' : (QuotientGroup.mk' J) y = 1 := DFunLike.congr_fun hf ⟨y, hy⟩
  exact (QuotientGroup.eq_one_iff y).1 hy'

theorem toralCentralizer_G2_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) (b : Fin Tag.G2.rank → Kˣ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) {M : Subgroup (toralCentralizer .G2 K b)}
    (hM : IsComponent M) : OddLieCentralQuotient p M := by
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hKodd) (by decide)
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
  · let e := (MulEquiv.subgroupCongr h).trans eα'
    exact oddLieCentralQuotient_of_equiv_psl_two hp hf hK hK2 hK3
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))
  · let e := (MulEquiv.subgroupCongr h).trans eβ'
    exact oddLieCentralQuotient_of_equiv_psl_two hp hf hK hK2 hK3
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))


theorem exists_toralCentralizer_equiv_of_innerDiag
    {τ : Tag} {K : Type} [Field K] [Finite K] (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hKodd : Odd (Nat.card K)) {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K}
    {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) :
    ∃ b : Fin τ.rank → Kˣ, (∀ i, b i = 1 ∨ b i = -1) ∧ (α ≠ 1 → b ≠ 1) ∧
      Nonempty (fixedSubgroup α ≃* toralCentralizer τ K b) := by
  obtain ⟨b, hb, ⟨Θ⟩⟩ :=
    LocalAnalysis.SteinbergBM.exists_mulEquiv_toralCentralizer_of_innerDiagonal hτ hKodd hαg hα
  refine ⟨b, hb, fun hα1 hb1 => hα1 ?_, ⟨Θ⟩⟩
  have : Finite (ModGL τ K) := finite_modGL
  have htop : toralCentralizer τ K b = adjointGroup τ K := by
    refine le_antisymm inf_le_left fun y hy => Subgroup.mem_inf.2 ⟨hy, ?_⟩
    rw [hb1, rootDiagUnit_one]
    exact Subgroup.mem_centralizer_singleton_iff.2 ((mul_one y).trans (one_mul y).symm)
  have hcard : Nat.card (fixedSubgroup α) = Nat.card (adjointGroup τ K) :=
    (Nat.card_congr Θ.toEquiv).trans (by rw [htop])
  have hfix : fixedSubgroup α = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  refine MulEquiv.ext fun h => ?_
  have hh : h ∈ fixedSubgroup α := hfix ▸ Subgroup.mem_top h
  exact hh

theorem oddExcInnerDiagInput_G2
    : OddExcInnerDiagInput .G2 := by
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
  exact oddLieCentralQuotient_of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
    (toralCentralizer_G2_component hp hp2 hKp hf b hb (hb1 hα1)
      (LocalCores.isComponent_map_mulEquiv Θ hL))

end CFSG.ComponentClassification.CatLeafProof
