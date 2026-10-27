module

import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalPerfectLifts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

theorem isSylowOf_inf_sup {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Q H N A : Subgroup X} (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hAQ : A ≤ Q) :
    CFSG.ABGLocalTools.IsSylowOf p (Q ⊓ (A ⊔ N)) (A ⊔ N) := by
  have hHnormN : H ≤ normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
  have hAnormN : A ≤ normalizer (N : Set X) := hAQ.trans (hQ.le.trans hHnormN)
  have hAnormQ : A ≤ normalizer (Q : Set X) := hAQ.trans Q.le_normalizer
  have hAnormQN : A ≤ normalizer ((Q ⊓ N : Subgroup X) : Set X) :=
    (le_inf hAnormQ hAnormN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQN : CFSG.ABGLocalTools.IsSylowOf p (Q ⊓ N) N :=
    hQ.inf_of_le_normalizer hNH hHnormN
  have hQNindex : ¬ p ∣ (Q ⊓ N).relIndex N := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hQN
    exact hQN.2.2
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨inf_le_right, hQ.isPGroup.to_le inf_le_left, ?_⟩
  let T : Subgroup X := (Q ⊓ N) ⊔ A
  have hTle : T ≤ Q ⊓ (A ⊔ N) :=
    sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_right)) (le_inf hAQ le_sup_left)
  have hTle' : T ≤ A ⊔ N := sup_le (inf_le_right.trans le_sup_right) le_sup_left
  have hAT : Nat.card ↥T * Nat.card ↥(A ⊓ N) = Nat.card ↥(Q ⊓ N) * Nat.card ↥A := by
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf
      (A := Q ⊓ N) (B := A) hAnormQN
    have hinf : (Q ⊓ N) ⊓ A = A ⊓ N := by
      rw [inf_comm (Q ⊓ N) A, ← inf_assoc, inf_eq_left.mpr hAQ]
    rwa [hinf] at h
  have hAN : Nat.card ↥(A ⊔ N) * Nat.card ↥(A ⊓ N) = Nat.card ↥A * Nat.card ↥N := by
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf
      (A := N) (B := A) hAnormN
    rw [sup_comm N A, inf_comm N A, mul_comm (Nat.card ↥N)] at h
    exact h
  have hTA : T.relIndex (A ⊔ N) * Nat.card ↥T = Nat.card ↥(A ⊔ N) := by
    have h := Subgroup.relIndex_mul_card T (A ⊔ N)
    rwa [inf_eq_left.mpr hTle'] at h
  have hQNN : (Q ⊓ N).relIndex N * Nat.card ↥(Q ⊓ N) = Nat.card ↥N := by
    have h := Subgroup.relIndex_mul_card (Q ⊓ N) N
    rwa [inf_eq_left.mpr inf_le_right] at h
  have hTindex : T.relIndex (A ⊔ N) = (Q ⊓ N).relIndex N := by
    have hposA : 0 < Nat.card ↥A := Nat.card_pos
    have hposQN : 0 < Nat.card ↥(Q ⊓ N) := Nat.card_pos
    have key : T.relIndex (A ⊔ N) * Nat.card ↥(Q ⊓ N) = Nat.card ↥N := by
      have e : T.relIndex (A ⊔ N) * Nat.card ↥(Q ⊓ N) * Nat.card ↥A
          = Nat.card ↥N * Nat.card ↥A := by
        calc T.relIndex (A ⊔ N) * Nat.card ↥(Q ⊓ N) * Nat.card ↥A
            = T.relIndex (A ⊔ N) * (Nat.card ↥T * Nat.card ↥(A ⊓ N)) := by
              rw [hAT]; ring
          _ = (T.relIndex (A ⊔ N) * Nat.card ↥T) * Nat.card ↥(A ⊓ N) := by ring
          _ = Nat.card ↥(A ⊔ N) * Nat.card ↥(A ⊓ N) := by rw [hTA]
          _ = Nat.card ↥A * Nat.card ↥N := hAN
          _ = Nat.card ↥N * Nat.card ↥A := by ring
      exact Nat.eq_of_mul_eq_mul_right hposA e
    exact Nat.eq_of_mul_eq_mul_right hposQN (by rw [key, hQNN])
  have hdiv : (Q ⊓ (A ⊔ N)).relIndex (A ⊔ N) ∣ (Q ⊓ N).relIndex N := by
    rw [← hTindex]
    exact Subgroup.relIndex_dvd_of_le_left (A ⊔ N) hTle
  intro hdvd
  exact hQNindex (hdvd.trans hdiv)

theorem commutator_mem_centralizer_of_isCyclic {X : Type*} [Group X] {R : Subgroup X}
    (hR : IsCyclic R) {g₁ g₂ : X} (h₁ : g₁ ∈ normalizer (R : Set X))
    (h₂ : g₂ ∈ normalizer (R : Set X)) :
    g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ centralizer (R : Set X) := by
  haveI := hR
  have hpow : ∀ g ∈ normalizer (R : Set X), ∃ m : ℤ, ∀ r ∈ R, g * r * g⁻¹ = r ^ m := by
    intro g hg
    let σ : R →* R :=
      { toFun := fun r => ⟨g * r * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg r).mp r.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    obtain ⟨m, hm⟩ := σ.map_cyclic
    refine ⟨m, fun r hr => ?_⟩
    have h := congrArg Subtype.val (hm ⟨r, hr⟩)
    simpa [σ] using h
  obtain ⟨m₁, hm₁⟩ := hpow g₁ h₁
  obtain ⟨m₂, hm₂⟩ := hpow g₂ h₂
  have hg21 : g₂ * g₁ ∈ normalizer (R : Set X) := Subgroup.mul_mem _ h₂ h₁
  have hrel : ∀ r ∈ R, (g₁ * g₂) * r * (g₁ * g₂)⁻¹ =
      (g₂ * g₁) * r * (g₂ * g₁)⁻¹ := by
    intro r hr
    calc (g₁ * g₂) * r * (g₁ * g₂)⁻¹ = g₁ * (g₂ * r * g₂⁻¹) * g₁⁻¹ := by group
      _ = g₁ * (r ^ m₂) * g₁⁻¹ := by rw [hm₂ r hr]
      _ = (r ^ m₂) ^ m₁ := hm₁ _ (R.zpow_mem hr m₂)
      _ = (r ^ m₁) ^ m₂ := by rw [← zpow_mul, ← zpow_mul, mul_comm]
      _ = (g₂ * g₁) * r * (g₂ * g₁)⁻¹ := by
            rw [← hm₂ _ (R.zpow_mem hr m₁), ← hm₁ r hr]
            group
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hs : (g₂ * g₁)⁻¹ * r * (g₂ * g₁) ∈ R := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg21) r).mp hr
    simpa using h
  have h3 : (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)⁻¹ = r := by
    calc (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)⁻¹
        = (g₁ * g₂) * ((g₂ * g₁)⁻¹ * r * (g₂ * g₁)) * (g₁ * g₂)⁻¹ := by group
      _ = (g₂ * g₁) * ((g₂ * g₁)⁻¹ * r * (g₂ * g₁)) * (g₂ * g₁)⁻¹ := hrel _ hs
      _ = r := by group
  calc r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)
      = ((g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)⁻¹) *
          (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) := by rw [h3]
    _ = (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r := by group

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
