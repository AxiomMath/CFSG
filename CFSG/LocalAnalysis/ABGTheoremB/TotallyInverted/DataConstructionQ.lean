module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionSetting

public section

namespace CFSG.ABGTheoremB.TotallyInverted.DataConstruction

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] {σ : Setting G}

structure QPair (σ : Setting G) (r : ℕ) (J Q Qs : Subgroup G) : Prop where
  le : Q ≤ J
  le_s : Qs ≤ J
  isPGroup : IsPGroup r Q
  isPGroup_s : IsPGroup r Qs
  normal : σ.C ≤ Subgroup.normalizer (Q : Set G)
  normal_s : σ.C ≤ Subgroup.normalizer (Qs : Set G)
  card_eq : Nat.card Q = Nat.card Qs
  trivial : ¬ (σ.DeltaEpsMinus ∧ r ∣ σ.q) → Q = ⊥ ∧ Qs = ⊥
  cover : ∀ X : Subgroup G, X ≤ J → IsPGroup r X → σ.C ≤ Subgroup.normalizer (X : Set G) →
    X ≤ Q ∨ X ≤ Qs
  cases : σ.DeltaEpsMinus ∧ r ∣ σ.q →
    Q ≠ Qs ∧ Nat.card Q = σ.q ∧ Nat.card Qs = σ.q ∧ J = Q ⊔ Qs ∧
      (∃ z ∈ σ.D, conjSub z Q = Qs) ∧
      (∀ X : Subgroup G, X ≤ Q → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Q) ∧
      (∀ X : Subgroup G, X ≤ Qs → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Qs)

theorem le_normalizer_bot (X : Subgroup G) :
    X ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g _ =>
  conjSub_eq_self_iff.mp (conjSub_bot g)

theorem mem_signalizers_J [Finite G] {r : ℕ} (hr : r.Prime) (hti : σ.TotallyInverted r)
    {J X : Subgroup G} (hJ : σ.IsLayerComplement J) (hXJ : X ≤ J) (hX : IsPGroup r X)
    (hCX : σ.C ≤ Subgroup.normalizer (X : Set G)) : X ∈ signalizers J σ.C r :=
  ⟨hXJ, hX, hCX, inf_C_eq_bot hr hti hX (hXJ.trans (J_le_L hJ))⟩

theorem exists_QPair [Finite G] (hσ : σ.IsValid) (hT : σ.TIFacts) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hti : σ.TotallyInverted r) {J : Subgroup G} (hJ : σ.IsLayerComplement J) :
    ∃ Q Qs : Subgroup G, QPair σ r J Q Qs := by
  by_cases hc : σ.DeltaEpsMinus ∧ r ∣ σ.q
  · have hrp : r = σ.p := (Nat.prime_dvd_prime_iff_eq hr hσ.p_prime).mp
      (hr.dvd_of_dvd_pow (show r ∣ σ.p ^ σ.f from hc.2))
    obtain ⟨Q, Qs, hQ, hQs, hcQ, hcQs, hne, hJeq, hz, hcov, hirr, hirrs⟩ :=
      hT.layer_signalizer_pair J hJ hc.1
    rw [← hrp] at hQ hQs hcov
    exact ⟨Q, Qs,
      { le := hQ.1
        le_s := hQs.1
        isPGroup := hQ.2.1
        isPGroup_s := hQs.2.1
        normal := hQ.2.2.1
        normal_s := hQs.2.2.1
        card_eq := hcQ.trans hcQs.symm
        trivial := fun h => absurd hc h
        cover := fun X hXJ hX hCX => hcov X (mem_signalizers_J hr hti hJ hXJ hX hCX)
        cases := fun _ => ⟨hne, hcQ, hcQs, hJeq, hz, hirr, hirrs⟩ }⟩
  · refine ⟨⊥, ⊥,
      { le := bot_le
        le_s := bot_le
        isPGroup := IsPGroup.of_bot
        isPGroup_s := IsPGroup.of_bot
        normal := le_normalizer_bot _
        normal_s := le_normalizer_bot _
        card_eq := rfl
        trivial := fun _ => ⟨rfl, rfl⟩
        cover := fun X hXJ hX hCX => Or.inl ?_
        cases := fun h => absurd h hc }⟩
    by_contra hne
    rw [le_bot_iff] at hne
    obtain ⟨hδ, hrp⟩ :=
      hT.layer_signalizer J hJ r hr hr2 X (mem_signalizers_J hr hti hJ hXJ hX hCX) hne
    refine hc ⟨hδ, ?_⟩
    rw [hrp]
    exact dvd_pow_self σ.p (by have := hσ.one_le_f; omega)

end CFSG.ABGTheoremB.TotallyInverted.DataConstruction
