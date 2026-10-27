module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieDatum
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD (hiF4 isRoot_hiF4 rankOneHiF4 commutes_rankOneHiF4
  commutes_iSup_left)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem exists_quaternion_of_rootPair_le
    {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {X H : Subgroup (ModGL τ K)} (hHX : H ≤ X)
    (hle : rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ≤ H) :
    ∃ Q : Subgroup (H.subgroupOf X), Nonempty (Q ≃* QuaternionGroup 2) := by
  obtain ⟨-, ⟨e⟩, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK2 hβ
  let φ : SL(2, K) →* H.subgroupOf X :=
    ((Subgroup.subgroupOfEquivOfLe hHX).symm.toMonoidHom.comp (Subgroup.inclusion hle)).comp
      e.toMonoidHom
  exact exists_quaternion_of_injective_SL hK2 φ
    (((Subgroup.subgroupOfEquivOfLe hHX).symm.injective.comp
      (Subgroup.inclusion_injective hle)).comp e.injective)

theorem rootPair_le_subsystemGroup
    {τ : Tag} {K : Type} [Field K] {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J) :
    rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-(Pi.single i 1)) ≤
      subsystemGroup τ K J := by
  have h0 : ∀ j ∉ J, (Pi.single i 1 : Fin τ.rank → ℤ) j = 0 := fun j hj =>
    Pi.single_eq_of_ne (fun h : j = i => hj (h ▸ hi)) _
  refine sup_le (rootSubgroup_le_subsystemGroup ⟨isRoot_single τ i, h0⟩)
    (rootSubgroup_le_subsystemGroup ⟨IsRoot.neg (isRoot_single τ i), fun j hj => ?_⟩)
  rw [Pi.neg_apply, h0 j hj, neg_zero]

theorem toralCentralizer_quat_of_orbitCheck
    {τ : Tag} {K : Type} [Field K] (hK2 : ringChar K ≠ 2) {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (hcert : OrbitCheck τ reps entries)
    (hreps : ∀ ρ < reps.length, listMask (τ := τ) (reps.getD ρ []) ≠ (fun _ => false) →
      QuatComponentForm (toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ [])))))
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    QuatComponentForm (toralCentralizer τ K b) := by
  obtain ⟨ρ, hρ, w, hw, hmap⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 hcert hb
  by_cases h0 : listMask (τ := τ) (reps.getD ρ []) = fun _ => false
  · refine absurd (eq_one_of_rootChar_smul_eq_one (w := w) fun v => ?_) hb1
    rw [hw v]
    congr 1
    funext i
    change (if listMask (τ := τ) (reps.getD ρ []) i then (-1 : Kˣ) else 1) = 1
    rw [h0]
    rfl
  · let e : toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ []))) ≃*
        toralCentralizer τ K b :=
      ((toralCentralizer τ K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact quatComponentForm_of_mulEquiv e.symm (hreps ρ hρ h0)

theorem oddExcInnerDiagQuatForm_of_toral
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hrow : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 →
      Nat.card K = p ^ f → ∀ b : Fin τ.rank → Kˣ, (∀ i, b i = 1 ∨ b i = -1) → b ≠ 1 →
        QuatComponentForm (toralCentralizer τ K b)) :
    OddExcInnerDiagQuatForm τ := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo
  have hKodd : Odd (Nat.card K) := by
    rw [hKp]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag hτ hKodd hαg hα
  exact quatComponentForm_of_mulEquiv Θ (hrow K p f hp hp2 hKp b hb (hb1 hα1))

theorem g2_toral_quat
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) (hK2 : ringChar K ≠ 2)
    (b : Fin Tag.G2.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    QuatComponentForm (toralCentralizer .G2 K b) := by
  intro M hM
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK2' : Nat.card K ≠ 2 := fun h => absurd (h ▸ hK) (by decide)
  obtain ⟨-, -, hcases, hstruct, hq3⟩ := odd_G2_toral_involution_fixed_p_components K hK b hb
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
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2')
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
  · exact exists_quaternion_of_mulEquiv_SL hK2 ((MulEquiv.subgroupCongr h).trans eα')
  · exact exists_quaternion_of_mulEquiv_SL hK2 ((MulEquiv.subgroupCongr h).trans eβ')

end CFSG.ComponentClassification.CatLeafProof
