module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOLayer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpPerf
public import CFSG.RankThree.OrthogonalInvolutions.Witt

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

section Conj

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {Q₀ : (ι → K) → K}
  {G : GL ι K} (hG : ∀ v, Q₀ ((G : Matrix ι ι K) *ᵥ v) = Q₀ v)
include hG

theorem map_conj_statedOmega :
    (StatedOmega Q₀).map (MulAut.conj G).toMonoidHom = StatedOmega Q₀ := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_statedOmega hG hg
  · intro g hg
    refine ⟨G⁻¹ * g * G, ?_, ?_⟩
    · have h := conj_mem_statedOmega (isometry_inv hG) hg
      rwa [inv_inv] at h
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

@[expose] noncomputable def isoConj : StatedOmega Q₀ ≃* StatedOmega Q₀ :=
  ((MulAut.conj G).subgroupMap (StatedOmega Q₀)).trans
    (MulEquiv.subgroupCongr (map_conj_statedOmega hG))

theorem coe_isoConj (g : StatedOmega Q₀) :
    ((isoConj hG g : StatedOmega Q₀) : GL ι K) = G * g * G⁻¹ :=
  rfl

theorem isoConj_eq_of_mem {g : StatedOmega Q₀}
    (hg : g ∈ (StatedScalars ι K).subgroupOf (StatedOmega Q₀)) : isoConj hG g = g := by
  rw [mem_subgroupOf, StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  apply Subtype.ext
  rw [coe_isoConj, Subgroup.mem_center_iff.mp hg G, mul_inv_cancel_right]

theorem map_isoConj_scalars :
    ((StatedScalars ι K).subgroupOf (StatedOmega Q₀)).map (isoConj hG).toMonoidHom =
      (StatedScalars ι K).subgroupOf (StatedOmega Q₀) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, isoConj_eq_of_mem hG hg]
    exact hg
  · intro g hg
    exact ⟨g, hg, isoConj_eq_of_mem hG hg⟩

@[expose] noncomputable def projConj : MulAut (StatedProj (StatedOmega Q₀)) :=
  QuotientGroup.congr _ _ (isoConj hG) (map_isoConj_scalars hG)

theorem projConj_mk (g : StatedOmega Q₀) :
    projConj hG (QuotientGroup.mk g) = QuotientGroup.mk (isoConj hG g) :=
  QuotientGroup.congr_mk _ _ _ _ g

end Conj

section Singular

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm K (ι → K)}

omit [CharP K 2] [Fintype ι] [DecidableEq ι] in
theorem linearIndependent_pair_of_polar {a₁ a₂ x y : ι → K} (h₁ : Q.polarBilin a₁ y = 1)
    (h₂ : Q.polarBilin a₂ y = 0) (h₃ : Q.polarBilin a₂ x = 1) :
    LinearIndependent K ![a₁, a₂] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
  have hy := congrArg (fun v => Q.polarBilin v y) hst
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₁, h₂,
    mul_one, mul_zero, add_zero, map_zero, LinearMap.zero_apply] at hy
  subst hy
  have hx := congrArg (fun v => Q.polarBilin v x) hst
  simp only [zero_smul, zero_add, map_smul, LinearMap.smul_apply, smul_eq_mul, h₃, mul_one,
    map_zero, LinearMap.zero_apply] at hx
  exact ⟨rfl, hx⟩

theorem exists_cTwoX_of_singular (hQ : Q.polarBilin.Nondegenerate) {M : GL ι K}
    (hMQ : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) (hM2 : orderOf M = 2) (hr : commRank M = 2)
    (hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0) :
    ∃ a₁ a₂ : ι → K, (M : Matrix ι ι K) - 1 = cTwoX Q a₂ a₁ ∧ Q a₁ = 0 ∧ Q a₂ = 0 ∧
      Q.polarBilin a₁ a₂ = 0 ∧ LinearIndependent K ![a₂, a₁] := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hN := sub_one_mul_self_eq_zero hM2
  have hadj := polarBilin_sub_one_adj (polarBilin_mulVec_of_isometry Q hMQ) hM2
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hadj hsing
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hr' : N.rank = 2 := by rw [hNdef]; exact hr
  have halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0 := fun v => by
    have h1 := hMQ v
    rw [hMN, add_mulVec, one_mulVec, quad_add, hsing, add_zero] at h1
    exact add_eq_left.mp h1
  have hNN : ∀ a b, Q.polarBilin (N *ᵥ a) (N *ᵥ b) = 0 := fun a b => by
    rw [hadj, mulVec_mulVec, hN, zero_mulVec, map_zero]
  have hN0 : N ≠ 0 := fun h => by
    rw [h, Matrix.rank_zero] at hr'
    exact absurd hr' (by norm_num)
  obtain ⟨y, hy⟩ : ∃ y, N *ᵥ y ≠ 0 := by
    by_contra! h
    exact hN0 (Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec])
  obtain ⟨x, hxy⟩ : ∃ x, Q.polarBilin x (N *ᵥ y) = 1 := by
    obtain ⟨x, hx⟩ : ∃ x, Q.polarBilin x (N *ᵥ y) ≠ 0 := by
      by_contra! h
      exact hy (hQ.2 _ h)
    exact ⟨(Q.polarBilin x (N *ᵥ y))⁻¹ • x, by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx]⟩
  have hyx : Q.polarBilin y (N *ᵥ x) = 1 := by rw [← hadj, hBs, hxy]
  have hNE : N = cTwoX Q (N *ᵥ y) (N *ᵥ x) := by
    obtain ⟨-, -, -, -, -, hrk⟩ := sub_cTwoX_of_alt hN hadj halt hxy rfl
    rw [hr'] at hrk
    exact sub_eq_zero.mp (eq_zero_of_rank_eq_zero hrk)
  refine ⟨N *ᵥ x, N *ᵥ y, hNdef ▸ hNE, hsing x, hsing y, hNN x y,
    linearIndependent_pair_of_polar (Q := Q) (x := y) (y := x) ?_ ?_ ?_⟩
  · rw [hadj, hyx]
  · rw [hadj, halt]
  · rw [hadj, hxy]

theorem exists_isometryGL_pair (hQ : Q.polarBilin.Nondegenerate) {a₁ a₂ b₁ b₂ : ι → K}
    (ha : LinearIndependent K ![a₁, a₂]) (hb : LinearIndependent K ![b₁, b₂])
    (hQa₁ : Q a₁ = 0) (hQa₂ : Q a₂ = 0) (hQb₁ : Q b₁ = 0) (hQb₂ : Q b₂ = 0)
    (ha₁₂ : Q.polarBilin a₁ a₂ = 0) (hb₁₂ : Q.polarBilin b₁ b₂ = 0) :
    ∃ G : GL ι K, (∀ v, Q ((G : Matrix ι ι K) *ᵥ v) = Q v) ∧ (G : Matrix ι ι K) *ᵥ a₁ = b₁ ∧
      (G : Matrix ι ι K) *ᵥ a₂ = b₂ := by
  have hself : ∀ v, polar Q v v = 0 := fun v => by
    rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have ha' : polar Q a₁ a₂ = 0 := by rw [← polarBilin_apply_apply]; exact ha₁₂
  have hb' : polar Q b₁ b₂ = 0 := by rw [← polarBilin_apply_apply]; exact hb₁₂
  obtain ⟨g, hg, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQ ![a₁, a₂] ![b₁, b₂] ha hb (fun i => by fin_cases i <;> simp [hQa₁, hQa₂, hQb₁, hQb₂])
    (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [hself, ha', hb', polar_comm Q a₂ a₁, polar_comm Q b₂ b₁])
  set G := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm g
  have hGv : ∀ v, (G : Matrix ι ι K) *ᵥ v = g v := fun v => by
    rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, MulEquiv.apply_symm_apply]
  refine ⟨G, fun v => ?_, ?_, ?_⟩
  · rw [hGv]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg v
  · rw [hGv]
    exact hgu 0
  · rw [hGv]
    exact hgu 1

end Singular

end CFSG.ComponentClassification.RankTwoClassical
