module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutAll
public import CFSG.ClassicalInvolution.Q3.Q3T7W21P02
public import CFSG.ClassicalInvolution.Q3.Q3SPN3Stmt
public import CFSG.ClassicalInvolution.Asc77.AscT7PF
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace E4G3

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem sq_trichotomy_of_twin_pair (hG : Q3SPN3.SpinGen3) {n : ℕ} (hn : CITBelowT (.sl2 3 1) n)
    (hih : IH8T 3 1 n) (hlt : Nat.card X < n) (hΦ : HypOmegaModU (.sl2 3 1) Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) (hdisc : ¬ DConnected Φ) {A B : Subgroup X}
    (hAΦ : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) {x₀ : X} (hxA : IsUniqueInvolution A x₀)
    (hxB : IsUniqueInvolution B x₀) (α : MulAut X) (hα4 : α * α * (α * α) = 1)
    (hαA : ∀ a ∈ A, α a * a⁻¹ ∈ oddCoreOf A) (hαB : ∀ b ∈ B, α b * b⁻¹ ∈ oddCoreOf B) :
    α * α = 1 ∨ α * α = MulAut.conj x₀ ∨
      Subgroup.closure ({q | (α * α) q = q} ∪ {q | x₀ * q = q * x₀}) = ⊤ := by
  obtain ⟨t, k, htag, ⟨M⟩⟩ := e4_tag3D hn hih hlt hΦ hO hgen hA hdisc hAΦ hB
  have hcen : x₀ * x₀ ∈ Subgroup.center X := by
    rw [hxA.sq]
    exact Subgroup.one_mem _
  have hG2 : t ≠ .G2 := by
    rcases htag with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;>
      decide
  have hD4 : t ≠ .trialityD4 := by
    rcases htag with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;>
      decide
  have hnpsl : ¬ (t = .PSL ∧ k = 2) := by
    rintro ⟨h1, h2⟩
    rcases htag with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact absurd (h1.symm.trans h3) (by decide)
    · omega
    · exact absurd (h1.symm.trans h3) (by decide)
    · exact absurd (h1.symm.trans h3) (by decide)
    · exact absurd (h1.symm.trans h3) (by decide)
    · exact absurd (h1.symm.trans h3) (by decide)
  have hSperf : Group.IsPerfect (modelUniv t k 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (ModelFacts.modelClauseZero t k 3 1 Fact.out (ih8_isFundTag_mf M.isFundTag)
        M.admissible).1.1
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hAΦ hB hxA hxB hcen
  have hex := exactMembers_of_ih8Model M hΦ hG2 hD4
  have hαA' : ∀ a ∈ A, α a = a := fun a ha => by
    have h1 := hαA a ha
    rw [oddCoreOf_eq_bot_of_exact hex hAΦ, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hαB' : ∀ b ∈ B, α b = b := fun b hb => by
    have h1 := hαB b hb
    rw [oddCoreOf_eq_bot_of_exact hex hB.1, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hαR : ∀ r ∈ R, α (M.ψ r) = M.ψ r := fun r hr =>
    hαA' _ (hAR ▸ Subgroup.mem_map_of_mem _ hr)
  have hαR' : ∀ r ∈ R', α (M.ψ r) = M.ψ r := fun r hr =>
    hαB' _ (hBR ▸ Subgroup.mem_map_of_mem _ hr)
  have hsame : M.ψ y = M.ψ y' := hy.trans hy'.symm
  have hTP : TwinPairOn t (modelUniv t k 3 1 Fact.out) M.ψ R R' y y' :=
    ⟨M.ker_le_center, M.cls_sub hR, M.cls_sub hR', hP.ne, hP.comm, hP.hy, hP.hy2, hP.hy1, hP.hy',
      hP.hy'2, hP.hy'1, hsame⟩
  have hspin : T7P.SpinTag t k → α * α = 1 ∨ α * α = MulAut.conj x₀ ∨
      Subgroup.closure ({q | (α * α) q = q} ∪ {q | x₀ * q = q * x₀}) = ⊤ := fun hs => by
    have := sq_trichotomy_of_spinGenOn (hG t k hs M.admissible) M.ψ M.surj hTP α hα4 hαR hαR'
    rwa [hy] at this
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h4 | h5 | h6
  ·
    have key := Q3TIY.sqDichotomyC_psp2 X M.ψ M.surj M.ker_le_center R R' (M.cls_sub hR)
      (M.cls_sub hR') hP.ne y y' hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1 hsame α hα4 hαR hαR'
    rw [hy] at key
    exact key.imp_right Or.inl
  ·
    have key := Q3TIY.sqDichotomyC_psl4 M.admissible X M.ψ M.surj M.ker_le_center R R'
      (M.cls_sub hR) (M.cls_sub hR') hP.ne y y' hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1 hsame
      α hα4 hαR hαR'
    rw [hy] at key
    exact key.imp_right Or.inl
  ·
    have key := Q3TIY.sqDichotomyC_psu4 M.admissible X M.ψ M.surj M.ker_le_center R R'
      (M.cls_sub hR) (M.cls_sub hR') hP.ne y y' hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1 hsame
      α hα4 hαR hαR'
    rw [hy] at key
    exact key.imp_right Or.inl
  · exact hspin (Or.inl h4)
  · exact hspin (Or.inr (Or.inl h5))
  · exact hspin (Or.inr (Or.inr h6))

end E4G3

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
