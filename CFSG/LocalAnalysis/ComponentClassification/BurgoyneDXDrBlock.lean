module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcComp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOCent

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Dr

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C (blockP exists_block_mul_of_commute
  commute_of_mem_oIsoBlock commutatorElement_mul_mul commute_sign_of_mem
  matrixDerived_le_isometryGroup)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL commutatorElement_mul_mem_center)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem le_oBlock_sup (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (J : Finset (Fin d)) {M : Subgroup (GL (Fin d) K)} (hperf : ⁅M, M⁆ = M)
    (hiso : ∀ X ∈ M, X ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hfix : ∀ X ∈ M, X * signGL K J = signGL K J * X) :
    M ≤ oBlock K hw J ⊔ oBlock K hw Jᶜ := by
  rw [← hperf, commutator_le]
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, hae⟩ := exists_block_mul_of_commute hK hw J (hiso a ha) (hfix a ha)
  obtain ⟨b₁, hb₁, b₂, hb₂, hbe⟩ := exists_block_mul_of_commute hK hw J (hiso b hb) (hfix b hb)
  rw [hae, hbe, commutatorElement_mul_mul (fun m hm n hn => commute_of_mem_oIsoBlock hw hm hn)
    ha₁ hb₁ ha₂ hb₂]
  exact mul_mem (mem_sup_left (commutator_mem_commutator ha₁ hb₁))
    (mem_sup_right (commutator_mem_commutator ha₂ hb₂))

theorem blockP_le_autFixed (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (J I : Finset (Fin d)) (hI : I = J ∨ I = Jᶜ) :
    blockP K hw I ≤ autFixed (oκ _ (sgnPair h2 hw J)) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_autFixed_iff, kappa_proj]
  congr 1
  apply Subtype.ext
  rw [sgnPair, coe_conj_linPair]
  have hc := commute_sign_of_mem hw J I hI (oBlock_le_oIsoBlock hw _ (mem_subgroupOf.1 hg))
  rw [← hc, mul_inv_cancel_right]

theorem blockP_commute {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d))
    {a b : StatedProj (matrixDerived (oQ (diagGL hw)))} (ha : a ∈ blockP K hw J)
    (hb : b ∈ blockP K hw Jᶜ) : a * b = b * a := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (commute_of_mem_oIsoBlock hw (oBlock_le_oIsoBlock hw _ (mem_subgroupOf.1 hx))
    (oBlock_le_oIsoBlock hw _ (mem_subgroupOf.1 hy)))

theorem le_normalizer_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ normalizer (A : Set G) := by
  intro b hb
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : b * h * b⁻¹ = h := by rw [← hAB h hh b hb, mul_inv_cancel_right]
    rw [e]
    exact hh
  · intro hh
    have hc := hAB _ hh b hb
    have e : b * h = b * (b * h * b⁻¹) := by
      rw [← hc]
      group
    rw [mul_left_cancel e]
    exact hh

theorem normal_blockP {w : Fin d → K} (hw : ∀ i, w i ≠ 0) (J I : Finset (Fin d))
    (hI : I = J ∨ I = Jᶜ) :
    ((blockP K hw I).subgroupOf (blockP K hw J ⊔ blockP K hw Jᶜ)).Normal := by
  rcases hI with rfl | rfl
  · rw [normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le le_normalizer (le_normalizer_of_commute fun a ha b hb => blockP_commute hw I ha hb)
  · rw [normal_subgroupOf_iff_le_normalizer le_sup_right]
    exact sup_le (le_normalizer_of_commute fun a ha b hb => (blockP_commute hw J hb ha).symm)
      le_normalizer

theorem le_oBlock_of_map_le {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {I : Finset (Fin d)}
    {M : Subgroup (GL (Fin d) K)} (hle : M ≤ matrixDerived (oQ (diagGL hw)))
    (hperf : ⁅M, M⁆ = M)
    (hP : (M.subgroupOf (matrixDerived (oQ (diagGL hw)))).map (projH _) ≤ blockP K hw I) :
    M ≤ oBlock K hw I := by
  set H := matrixDerived (oQ (diagGL hw)) with hH
  have hlift : ∀ m (hm : m ∈ M), ∃ ω ∈ (oBlock K hw I).subgroupOf H, ∃ z ∈ center H,
      (⟨m, hle hm⟩ : H) = ω * z := by
    intro m hm
    obtain ⟨ω, hω, hωm⟩ := hP ⟨⟨m, hle hm⟩, mem_subgroupOf.2 hm, rfl⟩
    exact ⟨ω, hω, ω⁻¹ * ⟨m, hle hm⟩,
      scalars_subgroupOf_le_center ((projH_eq_projH_iff).1 hωm), by group⟩
  rw [← hperf, commutator_le]
  intro a ha b hb
  obtain ⟨ω₁, hω₁, z₁, hz₁, e₁⟩ := hlift a ha
  obtain ⟨ω₂, hω₂, z₂, hz₂, e₂⟩ := hlift b hb
  have e : ⁅(⟨a, hle ha⟩ : H), ⟨b, hle hb⟩⁆ = ⁅ω₁, ω₂⁆ := by
    rw [e₁, e₂, commutatorElement_mul_mem_center ω₁ ω₂ hz₁ hz₂]
  have e' := congrArg Subtype.val e
  change ⁅a, b⁆ = ⁅(ω₁ : GL (Fin d) K), (ω₂ : GL (Fin d) K)⁆ at e'
  rw [e', commutatorElement_def]
  have h₁ := mem_subgroupOf.1 hω₁
  have h₂ := mem_subgroupOf.1 hω₂
  exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem exists_block_of_comp [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {M : Subgroup (GL (Fin d) K)}
    (hle : M ≤ matrixDerived (oQ (diagGL hw))) (hperf : ⁅M, M⁆ = M) (J : Finset (Fin d))
    (hfix : ∀ X ∈ M, X * signGL K J = signGL K J * X)
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ (diagGL hw)))).map
      (projH _)).subgroupOf (autFixed (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J))))) :
    ∃ I : Finset (Fin d), (I = J ∨ I = Jᶜ) ∧ M ≤ oBlock K hw I := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set H := matrixDerived (oQ (diagGL hw)) with hH
  set Qb := (M.subgroupOf H).map (projH H) with hQb
  set P' := blockP K hw J ⊔ blockP K hw Jᶜ with hP'
  have hiso : ∀ X ∈ M, X ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) :=
    fun X hX => matrixDerived_le_isometryGroup hw h2 (hle hX)
  have hMJ := le_oBlock_sup hK hw J hperf hiso hfix
  have hQP : Qb ≤ P' := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : (g : GL (Fin d) K) ∈ oBlock K hw J ⊔ oBlock K hw Jᶜ := hMJ (mem_subgroupOf.1 hg)
    have hgs : g ∈ (oBlock K hw J).subgroupOf H ⊔ (oBlock K hw Jᶜ).subgroupOf H := by
      rw [← subgroupOf_sup (C.oBlock_le_matrixDerived hw h2 J)
        (C.oBlock_le_matrixDerived hw h2 Jᶜ)]
      exact hg'
    have := mem_map_of_mem (projH H) hgs
    rwa [Subgroup.map_sup] at this
  have hPs : P' ≤ autFixed (oκ _ (sgnPair h2 hw J)) :=
    sup_le (blockP_le_autFixed h2 hw J J (Or.inl rfl))
      (blockP_le_autFixed h2 hw J Jᶜ (Or.inr rfl))
  have hQc' := C.isPComponent_subgroupOf_of_le hQP hPs hQc
  rcases C.le_or_le_of_le_sup hQP hQc' le_sup_left le_sup_right
      (normal_blockP hw J J (Or.inl rfl)).isSubnormal
      (normal_blockP hw J Jᶜ (Or.inr rfl)).isSubnormal hQP with h | h
  · exact ⟨J, Or.inl rfl, le_oBlock_of_map_le hw hle hperf h⟩
  · exact ⟨Jᶜ, Or.inr rfl, le_oBlock_of_map_le hw hle hperf h⟩

end CFSG.ComponentClassification.Burgoyne.DX.Dr
