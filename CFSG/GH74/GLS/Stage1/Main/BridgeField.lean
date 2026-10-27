module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedL4

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec7

@[expose] def L4NFField : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G) (ε : Bool), Cen2 G z S →
    Term7Out G z S q w → w ≠ 1 → q % 4 = (if ε then 3 else 1) →
      ∀ L₁ L₂ : Subgroup (CentralizerBar z), Stage1Pair G z S q L₁ L₂ →
        ∀ x₀ : G, TwoClassData G z S L₁ L₂ q x₀ → L4TwoClassField z S L₁ L₂ q x₀

@[expose] def L4TwoFieldStmt (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) : Prop :=
  ∀ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (x₀ : G), k = Kind.l4 ε →
    Stage1L4 G z S ε q L₁ L₂ → TwoClassData G z S L₁ L₂ q x₀ → q % 4 = (if ε then 3 else 1) →
      L4TwoClassField z S L₁ L₂ q x₀

section Lemmas

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem isCentralInvolution_of_isConj_Y {G : Type} [Group G] {z x : G} (hz : IsCentralInvolution z)
    (h : IsConj z x) : IsCentralInvolution x := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group

theorem stage1Pair_q_eq {q q' : ℕ} {L₁ L₂ L₁' L₂' : Subgroup (CentralizerBar z)}
    (h : Stage1Pair G z S q L₁ L₂) (h' : Stage1Pair G z S q' L₁' L₂') : q = q' := by
  have hmem : L₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
    rw [h.comps]
    exact Set.mem_insert _ _
  rw [h'.comps] at hmem
  rcases hmem with h1 | h1
  · have h2 : HasSL2Model ↥L₁ (fun r => r = q') := by
      rw [h1]
      exact h'.sl₁
    exact eq_of_hasSL2Model h.sl₁ h2
  · have h2 : HasSL2Model ↥L₁ (fun r => r = q') := by
      rw [show L₁ = L₂' from h1]
      exact h'.sl₂
    exact eq_of_hasSL2Model h.sl₁ h2

theorem L4TwoFieldStmt.of_ne {k : Kind} (h : ∀ ε : Bool, k ≠ Kind.l4 ε) : L4TwoFieldStmt G z k S :=
  fun ε _ _ _ _ hk => absurd hk (h ε)

theorem L4TwoFieldStmt.of_one_class (hz : IsCentralInvolution z)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (k : Kind) : L4TwoFieldStmt G z k S := by
  intro ε q L₁ L₂ x₀ _ _ hx _
  exact absurd (isCentralInvolution_of_isConj_Y hz (hone z x₀ hz.1 hx.x_inv)) hx.x_nonCentral

theorem L4TwoFieldStmt.of_term7 (hfld : L4NFField) (hcen : Cen2 G z S) {q₀ : ℕ} {w₀ : G}
    (hT : Term7Out G z S q₀ w₀) (hw : w₀ ≠ 1) {L₁₀ L₂₀ : Subgroup (CentralizerBar z)}
    (hp : Stage1Pair G z S q₀ L₁₀ L₂₀) (k : Kind) : L4TwoFieldStmt G z k S := by
  intro ε q L₁ L₂ x₀ _ h4 hx hq4
  have hq : q = q₀ := stage1Pair_q_eq h4.pair hp
  subst hq
  exact hfld G z S q w₀ ε hcen hT hw hq4 L₁ L₂ h4.pair x₀ hx

end Lemmas

end CFSG.GH74.GLS.Stage1.Main
