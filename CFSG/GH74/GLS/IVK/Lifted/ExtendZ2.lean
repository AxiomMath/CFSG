module

public import CFSG.GH74.GLS.IVK.Lifted.GroupAux

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup

section Z2

variable {H : Type} [Group H] {N : Subgroup H} {x : H}

theorem mem_sup_zpowers_cases (hx2 : x * x = 1) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) {g : H}
    (hg : g ∈ N ⊔ zpowers x) : g ∈ N ∨ ∃ n ∈ N, g = n * x := by
  have hxnorm : x ∈ normalizer (N : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hxN n, fun h => ?_⟩
    have h2 := hxN _ h
    have e : x * (x * n * x⁻¹) * x⁻¹ = n := by
      calc x * (x * n * x⁻¹) * x⁻¹ = (x * x) * n * (x * x)⁻¹ := by group
        _ = n := by rw [hx2]; group
    rwa [e] at h2
  obtain ⟨o, ho, i, rfl⟩ := exists_mul_zpow_of_mem_sup hxnorm hg
  rcases zpow_eq_one_or_self hx2 i with h | h
  · left
    rw [h, mul_one]
    exact ho
  · right
    exact ⟨o, ho, by rw [h]⟩

theorem exists_mulEquiv_sup_zpowers {H H' : Type} [Group H] [Group H'] {N : Subgroup H} {x : H}
    {N' : Subgroup H'} {x' : H'} (hx2 : x * x = 1) (hx'2 : x' * x' = 1)
    (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hx'N : ∀ n ∈ N', x' * n * x'⁻¹ ∈ N')
    (hxn : x ∉ N) (hx'n : x' ∉ N') (θ : ↥N ≃* ↥N')
    (hθ : ∀ n : ↥N, ∀ h : x * (n : H) * x⁻¹ ∈ N,
      ((θ ⟨x * (n : H) * x⁻¹, h⟩ : ↥N') : H') = x' * ((θ n : ↥N') : H') * x'⁻¹) :
    ∃ θh : ↥(N ⊔ zpowers x) ≃* ↥(N' ⊔ zpowers x'),
      (∀ n : ↥N, ((θh ⟨(n : H), mem_sup_left n.2⟩ : ↥(N' ⊔ zpowers x')) : H') = ((θ n : ↥N') : H')) ∧
      ((θh ⟨x, mem_sup_right (mem_zpowers x)⟩ : ↥(N' ⊔ zpowers x')) : H') = x' := by
  classical
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hx'i : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
  let θ₀ : H → H' := fun g => if h : g ∈ N then ((θ ⟨g, h⟩ : ↥N') : H') else 1
  have hθ₀ : ∀ (n : H) (hn : n ∈ N), θ₀ n = ((θ ⟨n, hn⟩ : ↥N') : H') := fun n hn => by
    simp [θ₀, hn]
  have hθ₀1 : θ₀ 1 = 1 := by
    rw [hθ₀ 1 (one_mem N)]
    have : (⟨1, one_mem N⟩ : ↥N) = 1 := rfl
    rw [this, map_one]
    rfl
  have hθ₀m : ∀ a ∈ N, ∀ b ∈ N, θ₀ (a * b) = θ₀ a * θ₀ b := by
    intro a ha b hb
    rw [hθ₀ _ (mul_mem ha hb), hθ₀ a ha, hθ₀ b hb]
    have : (⟨a * b, mul_mem ha hb⟩ : ↥N) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul]
    rfl
  have hθ₀mem : ∀ a ∈ N, θ₀ a ∈ N' := fun a ha => by
    rw [hθ₀ a ha]
    exact (θ ⟨a, ha⟩).2
  have hθ₀c : ∀ n ∈ N, x' * θ₀ n * x'⁻¹ = θ₀ (x * n * x⁻¹) := by
    intro n hn
    rw [hθ₀ n hn, hθ₀ _ (hxN n hn)]
    exact (hθ ⟨n, hn⟩ (hxN n hn)).symm
  have hθ₀inj : ∀ a ∈ N, ∀ b ∈ N, θ₀ a = θ₀ b → a = b := by
    intro a ha b hb h
    rw [hθ₀ a ha, hθ₀ b hb] at h
    have := θ.injective (Subtype.ext h)
    exact congrArg Subtype.val this
  let F : H → H' := fun g => if g ∈ N then θ₀ g else θ₀ (g * x⁻¹) * x'
  have hxN' : ∀ n ∈ N, n * x ∉ N := fun n hn h => hxn (by
    have := mul_mem (inv_mem hn) h
    simpa using this)
  have hx'N'' : ∀ n ∈ N', n * x' ∉ N' := fun n hn h => hx'n (by
    have := mul_mem (inv_mem hn) h
    simpa using this)
  have hF1 : ∀ n ∈ N, F n = θ₀ n := fun n hn => by simp [F, hn]
  have hF2 : ∀ n ∈ N, F (n * x) = θ₀ n * x' := by
    intro n hn
    have := hxN' n hn
    simp [F, this]
  have hFmem : ∀ g ∈ N ⊔ zpowers x, F g ∈ N' ⊔ zpowers x' := by
    intro g hg
    rcases mem_sup_zpowers_cases hx2 hxN hg with h | ⟨n, hn, rfl⟩
    · rw [hF1 g h]
      exact mem_sup_left (hθ₀mem g h)
    · rw [hF2 n hn]
      exact mul_mem (mem_sup_left (hθ₀mem n hn)) (mem_sup_right (mem_zpowers x'))
  have hFmul : ∀ g₁ ∈ N ⊔ zpowers x, ∀ g₂ ∈ N ⊔ zpowers x, F (g₁ * g₂) = F g₁ * F g₂ := by
    intro g₁ hg₁ g₂ hg₂
    rcases mem_sup_zpowers_cases hx2 hxN hg₁ with h₁ | ⟨n₁, hn₁, rfl⟩ <;>
    rcases mem_sup_zpowers_cases hx2 hxN hg₂ with h₂ | ⟨n₂, hn₂, rfl⟩
    · rw [hF1 _ (mul_mem h₁ h₂), hF1 _ h₁, hF1 _ h₂, hθ₀m _ h₁ _ h₂]
    · have e : g₁ * (n₂ * x) = (g₁ * n₂) * x := by group
      rw [e, hF2 _ (mul_mem h₁ hn₂), hF1 _ h₁, hF2 _ hn₂, hθ₀m _ h₁ _ hn₂, mul_assoc]
    · have e : n₁ * x * g₂ = (n₁ * (x * g₂ * x⁻¹)) * x := by group
      rw [e, hF2 _ (mul_mem hn₁ (hxN g₂ h₂)), hF2 _ hn₁, hF1 _ h₂,
        hθ₀m _ hn₁ _ (hxN g₂ h₂), ← hθ₀c g₂ h₂]
      group
    · have e : n₁ * x * (n₂ * x) = n₁ * (x * n₂ * x⁻¹) := by
        calc n₁ * x * (n₂ * x) = n₁ * (x * n₂ * x⁻¹) * (x * x) := by group
          _ = n₁ * (x * n₂ * x⁻¹) := by rw [hx2, mul_one]
      rw [e, hF1 _ (mul_mem hn₁ (hxN n₂ hn₂)), hF2 _ hn₁, hF2 _ hn₂,
        hθ₀m _ hn₁ _ (hxN n₂ hn₂), ← hθ₀c n₂ hn₂, hx'i]
      calc θ₀ n₁ * (x' * θ₀ n₂ * x') = θ₀ n₁ * (x' * θ₀ n₂ * x') := rfl
        _ = _ := by group
  let Φ : ↥(N ⊔ zpowers x) →* ↥(N' ⊔ zpowers x') :=
    { toFun := fun g => ⟨F g, hFmem g g.2⟩
      map_one' := by
        apply Subtype.ext
        show F 1 = 1
        rw [hF1 1 (one_mem N), hθ₀1]
      map_mul' := fun g₁ g₂ => Subtype.ext (hFmul g₁ g₁.2 g₂ g₂.2) }
  have hΦ : ∀ g : ↥(N ⊔ zpowers x), ((Φ g : ↥(N' ⊔ zpowers x')) : H') = F g := fun g => rfl
  have hinj : Function.Injective Φ := by
    intro g₁ g₂ h
    have h' : F g₁ = F g₂ := congrArg Subtype.val h
    apply Subtype.ext
    rcases mem_sup_zpowers_cases hx2 hxN g₁.2 with h₁ | ⟨n₁, hn₁, hg₁⟩ <;>
    rcases mem_sup_zpowers_cases hx2 hxN g₂.2 with h₂ | ⟨n₂, hn₂, hg₂⟩
    · rw [hF1 _ h₁, hF1 _ h₂] at h'
      exact hθ₀inj _ h₁ _ h₂ h'
    · rw [hg₂, hF1 _ h₁, hF2 _ hn₂] at h'
      exfalso
      apply hx'n
      have e : x' = (θ₀ n₂)⁻¹ * θ₀ g₁ := by rw [h']; group
      rw [e]
      exact mul_mem (inv_mem (hθ₀mem _ hn₂)) (hθ₀mem _ h₁)
    · rw [hg₁, hF2 _ hn₁, hF1 _ h₂] at h'
      exfalso
      apply hx'n
      have e : x' = (θ₀ n₁)⁻¹ * θ₀ g₂ := by rw [← h']; group
      rw [e]
      exact mul_mem (inv_mem (hθ₀mem _ hn₁)) (hθ₀mem _ h₂)
    · rw [hg₁, hg₂, hF2 _ hn₁, hF2 _ hn₂] at h'
      have h3 : θ₀ n₁ = θ₀ n₂ := mul_right_cancel h'
      rw [hg₁, hg₂, hθ₀inj _ hn₁ _ hn₂ h3]
  have hsurj : Function.Surjective Φ := by
    intro g'
    rcases mem_sup_zpowers_cases hx'2 hx'N g'.2 with h' | ⟨n', hn', hg'⟩
    · obtain ⟨n, hn⟩ := θ.surjective ⟨g', h'⟩
      refine ⟨⟨(n : H), mem_sup_left n.2⟩, Subtype.ext ?_⟩
      rw [hΦ, hF1 _ n.2, hθ₀ _ n.2]
      exact congrArg (fun a : ↥N' => (a : H')) hn
    · obtain ⟨n, hn⟩ := θ.surjective ⟨n', hn'⟩
      refine ⟨⟨(n : H) * x, mul_mem (mem_sup_left n.2) (mem_sup_right (mem_zpowers x))⟩,
        Subtype.ext ?_⟩
      rw [hΦ, hF2 _ n.2, hθ₀ _ n.2, hg']
      exact congrArg (fun a : ↥N' => (a : H') * x') hn
  refine ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun n => ?_, ?_⟩
  · show F n = _
    rw [hF1 _ n.2, hθ₀ _ n.2]
  · show F x = x'
    have := hF2 1 (one_mem N)
    rw [one_mul] at this
    rw [this, hθ₀1, one_mul]

end Z2

end CFSG.GH74.GLS.IVK.Lifted
