module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups


theorem card_eq_of_isPComponent_toralCentralizer_G2 {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (b : Fin Tag.G2.rank → Fˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hb1 : b ≠ 1) {M : Subgroup (toralCentralizer .G2 F b)} (hM : IsPComponent 2 M) :
    Nat.card M = Nat.card SL(2, F) := by
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  obtain ⟨hqs, -, hcases, hstruct, hq3⟩ := odd_G2_toral_involution_fixed_p_components F hF b hb
  by_cases hF3 : Nat.card F = 3
  · exact ((hq3 hF3 hb1).2 2 M hM).elim
  have hF2 : Nat.card F ≠ 2 := fun h => absurd (h ▸ hF) (by decide)
  obtain ⟨α₀, β₀, hc⟩ : ∃ α₀ β₀ : Fin Tag.G2.rank → ℤ,
      (b = ![-1, 1] ∧ α₀ = ![0, 1] ∧ β₀ = ![2, 3]) ∨
        (b = ![1, -1] ∧ α₀ = ![1, 0] ∧ β₀ = ![1, 2]) ∨
          (b = ![-1, -1] ∧ α₀ = ![1, 1] ∧ β₀ = ![1, 3]) := by
    rcases hcases with h | h | h | h
    · exact absurd h hb1
    · exact ⟨_, _, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨_, _, Or.inr (Or.inl ⟨h, rfl, rfl⟩)⟩
    · exact ⟨_, _, Or.inr (Or.inr ⟨h, rfl, rfl⟩)⟩
  obtain ⟨-, -, hS, hcomm, -, ⟨eα⟩, ⟨eβ⟩, hSX, -, hsolv, -⟩ := hstruct α₀ β₀ hc
  set Qα := rootSubgroup .G2 F α₀ ⊔ rootSubgroup .G2 F (-α₀)
  set Qβ := rootSubgroup .G2 F β₀ ⊔ rootSubgroup .G2 F (-β₀)
  have hQαX : Qα ≤ (toralCentralizer .G2 F b) := (hS ▸ (le_sup_left : Qα ≤ Qα ⊔ Qβ)).trans hSX
  have hQβX : Qβ ≤ (toralCentralizer .G2 F b) := (hS ▸ (le_sup_right : Qβ ≤ Qα ⊔ Qβ)).trans hSX
  have hD : (rootSpan .G2 F (rootCharKernel b)).subgroupOf (toralCentralizer .G2 F b) =
      Qα.subgroupOf (toralCentralizer .G2 F b) ⊔ Qβ.subgroupOf (toralCentralizer .G2 F b) := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hQαX hQβX
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl (Or.inr hF2)
    (Or.inr hF3)
  let eα' : Qα.subgroupOf (toralCentralizer .G2 F b) ≃* SL2 F :=
    (Subgroup.subgroupOfEquivOfLe hQαX).trans eα.symm
  let eβ' : Qβ.subgroupOf (toralCentralizer .G2 F b) ≃* SL2 F :=
    (Subgroup.subgroupOfEquivOfLe hQβX).trans eβ.symm
  have hqα : IsQuasisimple (Qα.subgroupOf (toralCentralizer .G2 F b)) :=
    LocalCores.isQuasisimple_of_mulEquiv eα'.symm hSL
  have hqβ : IsQuasisimple (Qβ.subgroupOf (toralCentralizer .G2 F b)) :=
    LocalCores.isQuasisimple_of_mulEquiv eβ'.symm hSL
  have hαβ : ∀ x ∈ Qα.subgroupOf (toralCentralizer .G2 F b),
      ∀ y ∈ Qβ.subgroupOf (toralCentralizer .G2 F b), x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp h1 _ hy).symm)
  have hnα : ((Qα.subgroupOf (toralCentralizer .G2 F b)).subgroupOf
      ((rootSpan .G2 F (rootCharKernel b)).subgroupOf (toralCentralizer .G2 F b))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  have hnβ : ((Qβ.subgroupOf (toralCentralizer .G2 F b)).subgroupOf
      ((rootSpan .G2 F (rootCharKernel b)).subgroupOf (toralCentralizer .G2 F b))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hαβ y hy x hx).symm)
  have hsub : M.IsSubnormal := by
    obtain ⟨_, _, h, _⟩ := hM
    exact h
  have hMc : IsComponent M := ⟨hqs 2 Nat.prime_two M hM, hsub⟩
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hMc
  rcases eq_or_eq_of_isComponent_le_sup hD hqα hqβ hnα hnβ hMc hMS with h | h
  · rw [h]
    exact Nat.card_congr eα'.toEquiv
  · rw [h]
    exact Nat.card_congr eβ'.toEquiv

theorem g2_propC_false {K : Type} [Group K] [Finite K] {n' p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel K .G2 n' p' f') {x : K} {R₁ R₂ : Subgroup K} {p n : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p n) : False := by
  have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2
    (hm.2 : UntwistedChevalleyModel K .G2 (p' ^ f'))
  have hp' : p'.Prime := hm.1.1
  have hFodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp'.eq_two_or_odd'.resolve_left hp2').pow
  have hC' := hC.map e
  set y := e x with hy
  have hy2 : y ^ 2 = 1 := by
    rw [← hC'.orderOf_eq]
    exact pow_orderOf_eq_one y
  set β : MulAut (adjointGroup .G2 F) := MulAut.conj y with hβ
  have hβ2 : β ^ 2 = 1 := by rw [hβ, ← map_pow, hy2, map_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    have hyc : y ∈ center (adjointGroup .G2 F) := by
      rw [mem_center_iff]
      intro g
      have h3 : y * g * y⁻¹ = g := by
        have := congrArg (fun φ : MulAut (adjointGroup .G2 F) => φ g) h1
        simpa [hβ, MulAut.conj_apply] using this
      calc g * y = y * g * y⁻¹ * y := by rw [h3]
        _ = y * g := by group
    rw [center_adjointGroup_eq_bot, mem_bot] at hyc
    have := hC'.orderOf_eq
    rw [hyc, orderOf_one] at this
    exact absurd this (by norm_num)
  have hβg : ∀ h : adjointGroup .G2 F, (β h : ModGL .G2 F) =
      (y : ModGL .G2 F) * rootDiagUnit .G2 1 * (h : ModGL .G2 F) * (rootDiagUnit .G2 1)⁻¹ *
        (y : ModGL .G2 F)⁻¹ := by
    intro h
    rw [rootDiagUnit_one, mul_one, inv_one, mul_one, hβ, MulAut.conj_apply]
    rfl
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag (Or.inl rfl) hFodd
    hβg hβ2
  have hfix : fixedSubgroup β = centralizer ({y} : Set (adjointGroup .G2 F)) := by
    ext g
    rw [mem_centralizer_singleton_iff]
    change β g = g ↔ _
    rw [hβ, MulAut.conj_apply]
    constructor
    · intro h
      calc g * y = y * g * y⁻¹ * y := by rw [h]
        _ = y * g := by group
    · intro h
      rw [← h, mul_inv_cancel_right]
  set Θ' := (MulEquiv.subgroupCongr hfix.symm).trans Θ with hΘ'
  have hcard : ∀ {R : Subgroup (adjointGroup .G2 F)}, R ≤ centralizer ({y} : Set _) →
      IsPComponent 2 (R.subgroupOf (centralizer ({y} : Set _))) →
        Nat.card R = Nat.card SL(2, F) := by
    intro R hR hRc
    have hRc' := (LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2
      Nat.prime_two Θ').1 _ |>.1 hRc
    rw [← card_eq_of_isPComponent_toralCentralizer_G2 hFodd b hb (hb1 hβ1) hRc',
      Nat.card_congr ((R.subgroupOf _).equivMapOfInjective _ Θ'.injective).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv]
  exact hC'.card_ne ((hcard hC'.le₁ hC'.comp₁).trans (hcard hC'.le₂ hC'.comp₂).symm)

end CFSG.ComponentClassification.Burgoyne.C
