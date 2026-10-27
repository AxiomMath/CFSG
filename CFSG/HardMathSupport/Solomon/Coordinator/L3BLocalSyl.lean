module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalData

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns CFSG.RankThree.PartTwo.Sec4
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped Pointwise

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {X : Type} [Group X] [Finite X]
  {φ : X →* GL (Fin 3) K}

theorem l3b_sylow_heis (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (P : Sylow 3 (X ⧸ Subgroup.center X)) :
    ∃ g ∈ glPi π 3 (p ^ f) K, ∃ x₁ x₂ : X, φ x₁ = g * diagTau hτ * g⁻¹ ∧
      φ x₂ = g * cycThree * g⁻¹ ∧
      Subgroup.zpowers (QuotientGroup.mk x₁ : X ⧸ Subgroup.center X) ⊔
        Subgroup.zpowers (QuotientGroup.mk x₂ : X ⧸ Subgroup.center X) ≤ (P : Subgroup _) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set Zc := Subgroup.center X with hZc
  obtain ⟨y₁, y₂, hy₁, hy₂⟩ := l3b_exists_heis hK hq hφ hτ (g := 1) (one_mem _)
  obtain ⟨hE1, -, -, -⟩ := l3b_heis_data hK hq hφ hτ hτ1 (one_mem _) hy₁ hy₂
    (E := Subgroup.zpowers (QuotientGroup.mk y₁ : X ⧸ Zc) ⊔
      Subgroup.zpowers (QuotientGroup.mk y₂ : X ⧸ Zc)) rfl
  have hp3 : IsPGroup 3 ↥(Subgroup.zpowers (QuotientGroup.mk y₁ : X ⧸ Zc) ⊔
      Subgroup.zpowers (QuotientGroup.mk y₂ : X ⧸ Zc)) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    intro e
    exact ⟨1, Subtype.ext (by simpa using hE1.2 e e.2)⟩
  obtain ⟨P₁, hP₁⟩ := hp3.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (X ⧸ Zc) P₁ P
  obtain ⟨κ, rfl⟩ := QuotientGroup.mk_surjective k
  have hκ : φ κ ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ (hφ.mem_sl κ)
  refine ⟨φ κ, hκ, κ * y₁ * κ⁻¹, κ * y₂ * κ⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, hy₁]; group
  · rw [map_mul, map_mul, map_inv, hy₂]; group
  · have hPP : (P : Subgroup (X ⧸ Zc)) = MulAut.conj (QuotientGroup.mk κ : X ⧸ Zc) • (P₁ : Subgroup (X ⧸ Zc)) := by
      rw [← hk, Sylow.coe_subgroup_smul]
    have hmem : ∀ e ∈ (P₁ : Subgroup (X ⧸ Zc)), (QuotientGroup.mk κ : X ⧸ Zc) * e *
        (QuotientGroup.mk κ)⁻¹ ∈ (P : Subgroup (X ⧸ Zc)) := by
      intro e he
      rw [hPP, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨e, he, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    have h1 : (QuotientGroup.mk y₁ : X ⧸ Zc) ∈ (P₁ : Subgroup _) :=
      hP₁ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have h2 : (QuotientGroup.mk y₂ : X ⧸ Zc) ∈ (P₁ : Subgroup _) :=
      hP₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
    · have := hmem _ h1
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this
    · have := hmem _ h2
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this

end CFSG.HardMathSupport.Solomon.Coordinator
