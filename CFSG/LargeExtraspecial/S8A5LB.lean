module

public import CFSG.LargeExtraspecial.S8A5LA

public section

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.CGT.Timmesfeld75

universe u

variable {Γ : Type u} [Group Γ]

namespace PairDataE

variable {M A N : Subgroup Γ} {t x : Γ} (P : PairDataE M A N t x)
include P

theorem comm_mem_F₁ {f : Γ} (hf : f ∈ A ⊓ normalizer (conjSubgroup x A : Set Γ)) {b : Γ}
    (hb : b ∈ conjSubgroup x A) :
    f * b * f⁻¹ * b⁻¹ ∈ conjSubgroup x A ⊓ normalizer (A : Set Γ) := by
  have hcB₁ : f * b * f⁻¹ * b⁻¹ ∈ conjSubgroup x A :=
    mul_mem ((mem_normalizer_iff.mp hf.2 b).mp hb) (inv_mem hb)
  refine ⟨hcB₁, (P.mem_normalizer_iff_comm hcB₁).mpr ?_⟩
  exact comm_of_hP1E (T := Epair A x) P.htt
    (fun y hy hc hne hE => P.hP1 y hy hc hne (Or.inl hE))
    (fun e he het => P.mul_t_mem_Epair he het)
    P.hA₁M P.hsq₁ P.t_mem_F.2 hf.1 (P.hsq f hf.1) hf.2 hb

theorem comm_mem_F {f : Γ} (hf : f ∈ conjSubgroup x A ⊓ normalizer (A : Set Γ)) {a : Γ}
    (ha : a ∈ A) :
    f * a * f⁻¹ * a⁻¹ ∈ A ⊓ normalizer (conjSubgroup x A : Set Γ) := by
  have hcA : f * a * f⁻¹ * a⁻¹ ∈ A := mul_mem ((mem_normalizer_iff.mp hf.2 a).mp ha) (inv_mem ha)
  refine ⟨hcA, (P.hF _ hcA).mpr ?_⟩
  have hσσ : x * t * x⁻¹ * (x * t * x⁻¹) = 1 := by
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [P.htt]; group
  exact comm_of_hP1E (T := Epair A x) hσσ P.hP1σ (fun e he het => P.mul_σ_mem_Epair he het)
    P.hAM P.hsq P.σ_mem_F₁.2 hf.1 (P.hsq₁ f hf.1) hf.2 ha

theorem comm_F_F₁ {f f₁ : Γ} (hf : f ∈ A ⊓ normalizer (conjSubgroup x A : Set Γ))
    (hf₁ : f₁ ∈ conjSubgroup x A ⊓ normalizer (A : Set Γ)) : f * f₁ = f₁ * f := by
  have h1 : f * f₁ * f⁻¹ * f₁⁻¹ ∈ conjSubgroup x A :=
    mul_mem ((mem_normalizer_iff.mp hf.2 f₁).mp hf₁.1) (inv_mem hf₁.1)
  have h2 : f * f₁ * f⁻¹ * f₁⁻¹ ∈ A := by
    rw [show f * f₁ * f⁻¹ * f₁⁻¹ = f * (f₁ * f⁻¹ * f₁⁻¹) by group]
    exact mul_mem hf.1 ((mem_normalizer_iff.mp hf₁.2 f⁻¹).mp (inv_mem hf.1))
  have h3 : f * f₁ * f⁻¹ * f₁⁻¹ ∈ A ⊓ conjSubgroup x A := ⟨h2, h1⟩
  rw [P.inf_eq_bot, mem_bot] at h3
  calc f * f₁ = f * f₁ * f⁻¹ * f₁⁻¹ * (f₁ * f) := by group
    _ = f₁ * f := by rw [h3, one_mul]

theorem F₁_le_normalizer_F : conjSubgroup x A ⊓ normalizer (A : Set Γ) ≤
    normalizer ((A ⊓ normalizer (conjSubgroup x A : Set Γ) : Subgroup Γ) : Set Γ) :=
  S9.TIX.le_normalizer_of_comm' fun _ hf₁ _ hf => (P.comm_F_F₁ hf hf₁).symm

theorem exists_mul_of_mem_E {e : Γ} (he : e ∈ Epair A x) :
    ∃ f ∈ A ⊓ normalizer (conjSubgroup x A : Set Γ),
      ∃ f₁ ∈ conjSubgroup x A ⊓ normalizer (A : Set Γ), e = f * f₁ :=
  S9.TIX.exists_mul_of_mem_sup' P.F₁_le_normalizer_F he

theorem comm_E {e e' : Γ} (he : e ∈ Epair A x) (he' : e' ∈ Epair A x) : e * e' = e' * e := by
  obtain ⟨f, hf, f₁, hf₁, rfl⟩ := P.exists_mul_of_mem_E he
  obtain ⟨g', hg, g₁, hg₁, rfl⟩ := P.exists_mul_of_mem_E he'
  have h1 := S9.TIX.comm_of_sq P.hsq hf.1 hg.1
  have h2 := S9.TIX.comm_of_sq P.hsq₁ hf₁.1 hg₁.1
  have h3 := P.comm_F_F₁ hf hg₁
  have h4 := P.comm_F_F₁ hg hf₁
  calc f * f₁ * (g' * g₁) = (f * g') * (f₁ * g₁) := by
        rw [show f * f₁ * (g' * g₁) = f * (f₁ * g') * g₁ by group, ← h4]; group
    _ = (g' * f) * (g₁ * f₁) := by rw [h1, h2]
    _ = g' * g₁ * (f * f₁) := by
        rw [show g' * f * (g₁ * f₁) = g' * (f * g₁) * f₁ by group, h3]; group

theorem sup_le_normalizer_E :
    A ⊔ conjSubgroup x A ≤ normalizer ((Epair A x : Subgroup Γ) : Set Γ) := by
  have key : ∀ a : Γ, a * a = 1 → (∀ e ∈ Epair A x, a * e * a⁻¹ ∈ Epair A x) →
      a ∈ normalizer ((Epair A x : Subgroup Γ) : Set Γ) := by
    intro a haa h
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    rw [mem_normalizer_iff]
    intro e
    refine ⟨h e, fun he => ?_⟩
    have := h _ he
    rwa [hainv, show a * (a * e * a) * a = (a * a) * e * (a * a) by group, haa, one_mul,
      mul_one] at this
  refine sup_le (fun a ha => key a (P.hsq a ha) fun e he => ?_)
    (fun b hb => key b (P.hsq₁ b hb) fun e he => ?_)
  · obtain ⟨f, hf, f₁, hf₁, rfl⟩ := P.exists_mul_of_mem_E he
    have h1 : a * f * a⁻¹ = f := by rw [S9.TIX.comm_of_sq P.hsq ha hf.1]; group
    have h2 : a * f₁ * a⁻¹ = (f₁ * a * f₁⁻¹ * a⁻¹)⁻¹ * f₁ := by group
    rw [show a * (f * f₁) * a⁻¹ = (a * f * a⁻¹) * (a * f₁ * a⁻¹) by group, h1, h2]
    exact mul_mem (mem_sup_left hf) (mul_mem (mem_sup_left (inv_mem (P.comm_mem_F hf₁ ha)))
      (mem_sup_right hf₁))
  · obtain ⟨f, hf, f₁, hf₁, rfl⟩ := P.exists_mul_of_mem_E he
    have h1 : b * f₁ * b⁻¹ = f₁ := by rw [S9.TIX.comm_of_sq P.hsq₁ hb hf₁.1]; group
    have h2 : b * f * b⁻¹ = (f * b * f⁻¹ * b⁻¹)⁻¹ * f := by group
    rw [show b * (f * f₁) * b⁻¹ = (b * f * b⁻¹) * (b * f₁ * b⁻¹) by group, h1, h2]
    exact mul_mem (mul_mem (mem_sup_right (inv_mem (P.comm_mem_F₁ hf hb))) (mem_sup_left hf))
      (mem_sup_right hf₁)

theorem sup_le_M : A ⊔ conjSubgroup x A ≤ M := sup_le P.hAM P.hA₁M

theorem comm_zpowers_N {z : Γ} (hz : z ∈ zpowers t) {n : Γ} (hn : n ∈ N) : n * z = z * n := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  exact (Commute.zpow_right (P.htN n hn) k).eq

end PairDataE

end CFSG.LargeExtraspecial.S8
