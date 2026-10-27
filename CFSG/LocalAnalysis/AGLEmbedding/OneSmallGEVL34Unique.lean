module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauAlg
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem L34Squeeze.exchange {H N M : Subgroup G}
    (hα : ∀ h ∈ H, ∃ a ∈ H ⊓ N, ∃ b ∈ H ⊓ M, h = a * b)
    (hβ : ∀ n ∈ N, ∃ a ∈ H ⊓ N, ∃ b ∈ N ⊓ M, n = a * b) :
    ∀ w ∈ (H ⊓ M) ⊔ (N ⊓ M),
      (∀ y ∈ H ⊓ N, ∃ w' ∈ (H ⊓ M) ⊔ (N ⊓ M), ∃ y' ∈ H ⊓ N, y * w = w' * y') ∧
      (∀ y ∈ H ⊓ N, ∃ y' ∈ H ⊓ N, ∃ w' ∈ (H ⊓ M) ⊔ (N ⊓ M), w * y = y' * w') := by
  set W := (H ⊓ M) ⊔ (N ⊓ M) with hWdef
  have hα' : ∀ h ∈ H, ∃ b ∈ H ⊓ M, ∃ a ∈ H ⊓ N, h = b * a := by
    intro h hh
    obtain ⟨a, ha, b, hb, he⟩ := hα h⁻¹ (H.inv_mem hh)
    exact ⟨b⁻¹, (H ⊓ M).inv_mem hb, a⁻¹, (H ⊓ N).inv_mem ha, by
      rw [← inv_inv h, he]; group⟩
  have hβ' : ∀ n ∈ N, ∃ b ∈ N ⊓ M, ∃ a ∈ H ⊓ N, n = b * a := by
    intro n hn
    obtain ⟨a, ha, b, hb, he⟩ := hβ n⁻¹ (N.inv_mem hn)
    exact ⟨b⁻¹, (N ⊓ M).inv_mem hb, a⁻¹, (H ⊓ N).inv_mem ha, by
      rw [← inv_inv n, he]; group⟩
  have hHMW : H ⊓ M ≤ W := le_sup_left
  have hNMW : N ⊓ M ≤ W := le_sup_right
  intro w hw
  rw [hWdef, Subgroup.sup_eq_closure] at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · obtain ⟨b, hb, a, ha, he⟩ := hα' (y * x) (H.mul_mem hy.1 hx.1)
        exact ⟨b, hHMW hb, a, ha, he⟩
      · obtain ⟨a, ha, b, hb, he⟩ := hα (x * y) (H.mul_mem hx.1 hy.1)
        exact ⟨a, ha, b, hHMW hb, he⟩
    · refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · obtain ⟨b, hb, a, ha, he⟩ := hβ' (y * x) (N.mul_mem hy.2 hx.1)
        exact ⟨b, hNMW hb, a, ha, he⟩
      · obtain ⟨a, ha, b, hb, he⟩ := hβ (x * y) (N.mul_mem hx.1 hy.2)
        exact ⟨a, ha, b, hNMW hb, he⟩
  | one => exact ⟨fun y hy => ⟨1, W.one_mem, y, hy, by group⟩,
      fun y hy => ⟨y, hy, 1, W.one_mem, by group⟩⟩
  | mul x₁ x₂ _ _ h₁ h₂ =>
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨w₁, hw₁, y₁, hy₁, e₁⟩ := h₁.1 y hy
      obtain ⟨w₂, hw₂, y₂, hy₂, e₂⟩ := h₂.1 y₁ hy₁
      exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, y₂, hy₂, by
        rw [← mul_assoc, e₁, mul_assoc, e₂, mul_assoc]⟩
    · obtain ⟨y₂, hy₂, w₂, hw₂, e₂⟩ := h₂.2 y hy
      obtain ⟨y₁, hy₁, w₁, hw₁, e₁⟩ := h₁.2 y₂ hy₂
      exact ⟨y₁, hy₁, w₁ * w₂, W.mul_mem hw₁ hw₂, by
        rw [mul_assoc, e₂, ← mul_assoc, e₁, mul_assoc]⟩
  | inv x _ h =>
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨y', hy', w', hw', e⟩ := h.2 y⁻¹ ((H ⊓ N).inv_mem hy)
      refine ⟨w'⁻¹, W.inv_mem hw', y'⁻¹, (H ⊓ N).inv_mem hy', ?_⟩
      have := congrArg (·⁻¹) e
      simp only [mul_inv_rev, inv_inv] at this
      exact this
    · obtain ⟨w', hw', y', hy', e⟩ := h.1 y⁻¹ ((H ⊓ N).inv_mem hy)
      refine ⟨y'⁻¹, (H ⊓ N).inv_mem hy', w'⁻¹, W.inv_mem hw', ?_⟩
      have := congrArg (·⁻¹) e
      simp only [mul_inv_rev, inv_inv] at this
      exact this

theorem L34Squeeze.eq_of_factorizations {H N M S Q : Subgroup G}
    (hH : GLBIsMaxTwoLocal H) (hN : GLBIsMaxTwoLocal N)
    (hSH : H ≤ Subgroup.normalizer (S : Set G)) (hSM : S ≤ M)
    (hQM : M ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 Q) (hQS : Q ⊓ S ≠ ⊥)
    (hα : ∀ h ∈ H, ∃ a ∈ H ⊓ N, ∃ b ∈ H ⊓ M, h = a * b)
    (hβ : ∀ n ∈ N, ∃ a ∈ H ⊓ N, ∃ b ∈ N ⊓ M, n = a * b) : N = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := (H ⊓ M) ⊔ (N ⊓ M) with hWdef
  have hex := L34Squeeze.exchange hα hβ
  have hWM : W ≤ M := sup_le inf_le_right inf_le_right
  set Γ : Set G := {x | ∃ w ∈ W, ∃ s ∈ S, x = w * s * w⁻¹} with hΓdef
  set V := Subgroup.closure Γ with hVdef
  have hVM : V ≤ M := by
    rw [hVdef, Subgroup.closure_le]
    rintro _ ⟨w, hw, s, hs, rfl⟩
    exact M.mul_mem (M.mul_mem (hWM hw) (hSM hs)) (M.inv_mem (hWM hw))
  have hSV : S ≤ V := fun s hs => Subgroup.subset_closure ⟨1, W.one_mem, s, hs, by group⟩
  have hmapΓ : ∀ g : G, (∃ b ∈ W, ∃ a ∈ H ⊓ N, g = b * a) → ∀ x ∈ Γ, g * x * g⁻¹ ∈ Γ := by
    rintro g ⟨b, hb, a, ha, rfl⟩ _ ⟨w, hw, s, hs, rfl⟩
    obtain ⟨w', hw', a', ha', e⟩ := (hex w hw).1 a ha
    have hs' : a' * s * a'⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hSH ha'.1) s).mp hs
    refine ⟨b * w', W.mul_mem hb hw', a' * s * a'⁻¹, hs', ?_⟩
    calc b * a * (w * s * w⁻¹) * (b * a)⁻¹ = b * (a * w) * s * (a * w)⁻¹ * b⁻¹ := by group
      _ = b * (w' * a') * s * (w' * a')⁻¹ * b⁻¹ := by rw [e]
      _ = b * w' * (a' * s * a'⁻¹) * (b * w')⁻¹ := by group
  have hnorm : ∀ g : G, (∃ b ∈ W, ∃ a ∈ H ⊓ N, g = b * a) →
      g ∈ Subgroup.normalizer (V : Set G) := by
    intro g hg
    have hsub : V.map (MulAut.conj g).toMonoidHom ≤ V := by
      rw [hVdef, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.subset_closure (by simpa [MulAut.conj_apply] using hmapΓ g hg x hx)
    have hcard : Nat.card V ≤ Nat.card (V.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr (Subgroup.eq_of_le_of_card_ge hsub hcard)
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := by
    intro h hh
    obtain ⟨a, ha, b, hb, he⟩ := hα h⁻¹ (H.inv_mem hh)
    refine hnorm h ⟨b⁻¹, W.inv_mem ((le_sup_left : H ⊓ M ≤ W) hb), a⁻¹, (H ⊓ N).inv_mem ha, ?_⟩
    rw [← inv_inv h, he]; group
  have hNV : N ≤ Subgroup.normalizer (V : Set G) := by
    intro n hn
    obtain ⟨a, ha, b, hb, he⟩ := hβ n⁻¹ (N.inv_mem hn)
    refine hnorm n ⟨b⁻¹, W.inv_mem ((le_sup_right : N ⊓ M ≤ W) hb), a⁻¹, (H ⊓ N).inv_mem ha, ?_⟩
    rw [← inv_inv n, he]; group
  have hQVn : V ≤ Subgroup.normalizer ((Q ⊓ V : Subgroup G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hQM (hVM hv)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hv) y
    simp only [Subgroup.mem_inf]
    exact and_congr h1 h2
  have hQV : Q ⊓ V ≤ pCoreOf 2 V :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hQVn (hQ.to_le inf_le_left)
  have hO1 : pCoreOf 2 V ≠ ⊥ := by
    intro hbot
    apply hQS
    rw [eq_bot_iff, ← hbot]
    exact (inf_le_inf_left Q hSV).trans hQV
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 V : Set G)) :=
    ⟨pCoreOf 2 V, hO1, RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 V, rfl⟩
  have hVO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 V
  have hL := hH.2 _ hloc (hHV.trans hVO)
  exact (hN.2 H hH.1 (hL ▸ hNV.trans hVO)).symm

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

end CFSG.AGLEmbedding
