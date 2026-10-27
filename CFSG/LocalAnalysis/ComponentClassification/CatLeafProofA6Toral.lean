module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Core
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem isEmpty_a6_of_lieModel
    {B H : Type} [Group B] [Group H] (e : B ≃* H) {τ' : StatedLieTag} {n' p f : ℕ}
    (hadm : StatedLieAdmissible τ' n' p f) (hp2 : p ≠ 2)
    (hlie : Blueprint.LieModel (H ⧸ center H) τ' n' p f) (hne : ¬ (τ' = .PSL ∧ n' = 2)) :
    IsEmpty (B ⧸ center B ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun eA => hne ?_⟩
  have hlieB : Blueprint.LieModel (B ⧸ center B) τ' n' p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hlie
  obtain ⟨h1, h2, -⟩ := lieModel_of_a6 ⟨eA⟩ hadm hp2 hlieB
  exact ⟨h1, h2⟩

theorem a6CentreForm_of_eq_or_SL {K : Type} [Field K] [Finite K] {G : Type} [Group G]
    {B : Subgroup G} (hB : IsEmpty (B ⧸ center B ≃* alternatingGroup (Fin 6)))
    (h : ∀ M : Subgroup G, IsComponent M → M = B ∨ Nonempty (M ≃* SL(2, K))) :
    A6CentreForm G := by
  rintro M hM ⟨eA⟩
  rcases h M hM with rfl | he
  · exact (hB.false eA).elim
  · obtain ⟨e⟩ := he
    exact isPGroup_center_of_mulEquiv_SL e

@[expose] def OddExcInnerDiagA6Form (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → orderOf α = 2 →
      A6CentreForm (fixedSubgroup α)

theorem toralCentralizer_a6_of_orbitCheck
    {τ : Tag} {K : Type} [Field K] (hK2 : ringChar K ≠ 2) {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (hcert : OrbitCheck τ reps entries)
    (hreps : ∀ ρ < reps.length, listMask (τ := τ) (reps.getD ρ []) ≠ (fun _ => false) →
      A6CentreForm (toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ [])))))
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    A6CentreForm (toralCentralizer τ K b) := by
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
    exact a6CentreForm_of_mulEquiv e.symm (hreps ρ hρ h0)

theorem oddExcInnerDiagA6Form_of_toral
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hrow : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 →
      Nat.card K = p ^ f → ∀ b : Fin τ.rank → Kˣ, (∀ i, b i = 1 ∨ b i = -1) → b ≠ 1 →
        A6CentreForm (toralCentralizer τ K b)) :
    OddExcInnerDiagA6Form τ := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo
  have hKodd : Odd (Nat.card K) := by
    rw [hKp]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag hτ hKodd hαg hα
  exact a6CentreForm_of_mulEquiv Θ (hrow K p f hp hp2 hKp b hb (hb1 hα1))

theorem toralCentralizer_G2_a6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (b : Fin Tag.G2.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hb1 : b ≠ 1) : A6CentreForm (toralCentralizer .G2 K b) := by
  intro M hM _
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
  · exact isPGroup_center_of_mulEquiv_SL ((MulEquiv.subgroupCongr h).trans eα')
  · exact isPGroup_center_of_mulEquiv_SL ((MulEquiv.subgroupCongr h).trans eβ')

theorem oddExcInnerDiagA6Form_G2
    : OddExcInnerDiagA6Form .G2 :=
  oddExcInnerDiagA6Form_of_toral (Or.inl rfl)
    fun _ _ _ _ _ hp hp2 hKp b hb hb1 => toralCentralizer_G2_a6 hp hp2 hKp b hb hb1

end CFSG.ComponentClassification.CatLeafProof
