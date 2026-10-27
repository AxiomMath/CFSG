module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldDef

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X} {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem fixedN_pow_form (R : RGD2 6 H r₁ r₂ U root) {m η₀ : X} (hm : m ∈ R.N) (hη₀ : η₀ ∈ H)
    (j : ℕ) : ∃ η ∈ H, (m * η₀) ^ j = m ^ j * η := by
  induction j with
  | zero => exact ⟨1, H.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨η, hη, he⟩ := ih
    refine ⟨(m⁻¹ * η * m) * η₀, H.mul_mem ((R.N_normalizes_H hm η hη).2) hη₀, ?_⟩
    rw [pow_succ, he, pow_succ]
    group

theorem fixedN_g0_form (R : RGD2 6 H r₁ r₂ U root) {r₁' r₂' : X} (h1H : r₁⁻¹ * r₁' ∈ H)
    (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) : ∃ η ∈ H, r₁' * r₂' = (r₁ * r₂) ^ 2 * η := by
  obtain ⟨c₁, hc₁, rfl⟩ : ∃ c ∈ H, r₁' = r₁ * c := ⟨r₁⁻¹ * r₁', h1H, by group⟩
  obtain ⟨c₂, hc₂, rfl⟩ : ∃ c ∈ H, r₂' = r₂ * r₁ * r₂⁻¹ * c :=
    ⟨(r₂ * r₁ * r₂⁻¹)⁻¹ * r₂', h2H, by group⟩
  have h3 : (r₂ * r₁ * r₂⁻¹)⁻¹ * c₁ * (r₂ * r₁ * r₂⁻¹) ∈ H :=
    (R.N_normalizes_H R.r_alpha_mem_N c₁ hc₁).2
  refine ⟨(r₂⁻¹ * r₂⁻¹) * ((r₂ * r₁ * r₂⁻¹)⁻¹ * c₁ * (r₂ * r₁ * r₂⁻¹)) * c₂,
    H.mul_mem (H.mul_mem R.sq₂_inv h3) hc₂, ?_⟩
  rw [pow_two]
  group

theorem fixedN_aux (R : RGD2 6 H r₁ r₂ U root)
    (hz : ∀ h ∈ H, φ ((r₁ * r₂) ^ 3 * h) ≠ (r₁ * r₂) ^ 3 * h)
    {r₁' r₂' : X} (h1 : φ r₁' = r₁') (h1H : r₁⁻¹ * r₁' ∈ H)
    (h2 : φ r₂' = r₂') (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) {s s' : X}
    (hs' : s' ∈ Subgroup.closure (((H ⊓ foldFix φ : Subgroup X) : Set X) ∪ {r₁', r₂'}))
    (hsφ : φ s' = s') (hss' : s⁻¹ * s' ∈ H) {k : ℕ} {h : X} (hh : h ∈ H)
    (hfix : φ (s * (r₁ * r₂) ^ k * h) = s * (r₁ * r₂) ^ k * h) :
    s * (r₁ * r₂) ^ k * h ∈
      Subgroup.closure (((H ⊓ foldFix φ : Subgroup X) : Set X) ∪ {r₁', r₂'}) := by
  set G₁ := Subgroup.closure (((H ⊓ foldFix φ : Subgroup X) : Set X) ∪ {r₁', r₂'}) with hG₁
  have hρN : r₁ * r₂ ∈ R.N := R.N.mul_mem R.r₁_mem_N R.r₂_mem_N
  have hg0G : r₁' * r₂' ∈ G₁ :=
    G₁.mul_mem (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
      (Subgroup.subset_closure (Or.inr (Or.inr rfl)))
  have hg0φ : φ (r₁' * r₂') = r₁' * r₂' := by rw [map_mul, h1, h2]
  obtain ⟨η₀, hη₀, hg0⟩ := fixedN_g0_form R h1H h2H
  have hgform : ∀ j : ℕ, ∃ η' ∈ H, s' * (r₁' * r₂') ^ j = s * (r₁ * r₂) ^ (2 * j) * η' := by
    intro j
    obtain ⟨η, hη, he⟩ := fixedN_pow_form R (R.N.pow_mem hρN 2) hη₀ j
    have hmj : ((r₁ * r₂) ^ 2) ^ j ∈ R.N := R.N.pow_mem (R.N.pow_mem hρN 2) j
    refine ⟨(((r₁ * r₂) ^ 2) ^ j)⁻¹ * (s⁻¹ * s') * ((r₁ * r₂) ^ 2) ^ j * η, ?_, ?_⟩
    · exact H.mul_mem ((R.N_normalizes_H hmj _ hss').2) hη
    · rw [hg0, he, pow_mul]
      group
  have hgφ : ∀ j : ℕ, φ (s' * (r₁' * r₂') ^ j) = s' * (r₁' * r₂') ^ j := fun j => by
    rw [map_mul, map_pow, hsφ, hg0φ]
  have hgG : ∀ j : ℕ, s' * (r₁' * r₂') ^ j ∈ G₁ := fun j => G₁.mul_mem hs' (G₁.pow_mem hg0G j)
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · obtain ⟨η', hη', he⟩ := hgform j
    have hm : (s' * (r₁' * r₂') ^ j)⁻¹ * (s * (r₁ * r₂) ^ (2 * j) * h) ∈ H ⊓ foldFix φ := by
      refine ⟨?_, ?_⟩
      · rw [he]
        have : (s * (r₁ * r₂) ^ (2 * j) * η')⁻¹ * (s * (r₁ * r₂) ^ (2 * j) * h) = η'⁻¹ * h := by
          group
        rw [this]
        exact H.mul_mem (H.inv_mem hη') hh
      · show φ _ = _
        rw [map_mul, map_inv, hgφ, hfix]
    have := G₁.mul_mem (hgG j) (Subgroup.subset_closure (Or.inl hm))
    rwa [mul_inv_cancel_left] at this
  · exfalso
    obtain ⟨η', hη', he⟩ := hgform (j + 2)
    have hρ3 : (r₁ * r₂) ^ 3 ∈ R.N := R.N.pow_mem hρN 3
    have hh₁ : ((r₁ * r₂) ^ 6)⁻¹ * h ∈ H := H.mul_mem (H.inv_mem R.pow) hh
    have hn' : s * (r₁ * r₂) ^ (2 * j + 1) * h =
        s * (r₁ * r₂) ^ (2 * (j + 2)) * ((r₁ * r₂) ^ 3 * (((r₁ * r₂) ^ 6)⁻¹ * h)) := by
      group
    have hconj : ((r₁ * r₂) ^ 3)⁻¹ * η'⁻¹ * (r₁ * r₂) ^ 3 ∈ H :=
      (R.N_normalizes_H hρ3 _ (H.inv_mem hη')).2
    have hh₂ : (((r₁ * r₂) ^ 3)⁻¹ * η'⁻¹ * (r₁ * r₂) ^ 3) * (((r₁ * r₂) ^ 6)⁻¹ * h) ∈ H :=
      H.mul_mem hconj hh₁
    have hq : (s' * (r₁' * r₂') ^ (j + 2))⁻¹ * (s * (r₁ * r₂) ^ (2 * j + 1) * h) =
        (r₁ * r₂) ^ 3 * ((((r₁ * r₂) ^ 3)⁻¹ * η'⁻¹ * (r₁ * r₂) ^ 3) *
          (((r₁ * r₂) ^ 6)⁻¹ * h)) := by
      rw [he, hn']
      group
    apply hz _ hh₂
    rw [← hq, map_mul, map_inv, hgφ, hfix]

namespace FoldData

theorem fixed_N_mem (hf : FoldData R φ)
    (hz : ∀ h ∈ H, φ ((r₁ * r₂) ^ 3 * h) ≠ (r₁ * r₂) ^ 3 * h)
    {r₁' r₂' : X} (h1 : φ r₁' = r₁') (h1H : r₁⁻¹ * r₁' ∈ H)
    (h2 : φ r₂' = r₂') (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) {n : X} (hn : n ∈ R.N)
    (hfix : φ n = n) :
    n ∈ Subgroup.closure (((H ⊓ foldFix φ : Subgroup X) : Set X) ∪ {r₁', r₂'}) := by
  have _ := hf
  obtain ⟨k, h, hh, hk | hk⟩ := R.exists_normal_form hn
  · subst hk
    have := fixedN_aux R hz h1 h1H h2 h2H (s := 1) (s' := 1) (Subgroup.one_mem _) (map_one φ)
      (by simp) hh (by simpa using hfix)
    simpa using this
  · subst hk
    exact fixedN_aux R hz h1 h1H h2 h2H (s := r₁) (s' := r₁')
      (Subgroup.subset_closure (Or.inr (Or.inl rfl))) h1 h1H hh hfix

end FoldData

end CFSG.GH74.GLS.SP
