module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8AP

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

omit [Finite X] in
theorem conj_pow_eq_of_conj_eq {g h : X} {T : Subgroup X}
    (hT : ∀ τ ∈ T, g * τ * g⁻¹ = h * τ * h⁻¹) (hgT : ∀ τ ∈ T, g * τ * g⁻¹ ∈ T) :
    ∀ n : ℕ, ∀ τ ∈ T, g ^ n * τ * (g ^ n)⁻¹ = h ^ n * τ * (h ^ n)⁻¹ ∧
      g ^ n * τ * (g ^ n)⁻¹ ∈ T := by
  intro n
  induction n with
  | zero => intro τ hτ; simpa using hτ
  | succ n ih =>
    intro τ hτ
    obtain ⟨h1, h2⟩ := ih τ hτ
    refine ⟨?_, ?_⟩
    · calc g ^ (n + 1) * τ * (g ^ (n + 1))⁻¹ = g * (g ^ n * τ * (g ^ n)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = h * (g ^ n * τ * (g ^ n)⁻¹) * h⁻¹ := hT _ h2
        _ = h * (h ^ n * τ * (h ^ n)⁻¹) * h⁻¹ := by rw [h1]
        _ = h ^ (n + 1) * τ * (h ^ (n + 1))⁻¹ := by rw [pow_succ']; group
    · rw [show g ^ (n + 1) * τ * (g ^ (n + 1))⁻¹ = g * (g ^ n * τ * (g ^ n)⁻¹) * g⁻¹ by
        rw [pow_succ']; group]
      exact hgT _ h2

omit [Finite X] in
theorem pow_odd_of_sq {h : X} (hh : h * h = 1) {m : ℕ} (hm : Odd m) : h ^ m = h := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, pow_two, hh, one_pow, one_mul]

namespace AData

variable (A : AData S F T₁)

theorem w₂₂_sq : A.D₂.w₂ * A.D₂.w₂ = 1 := by rw [← pow_two]; exact A.V₂.w₂_sq_of_elem A.hq₂

theorem exists_p : ∃ c ∈ MA.ZList, ∃ p : X, p ∈ normalizer (A.D₁.S₁ : Set X) ∧
    A.ActsW c p ∧ (∀ τ ∈ T₁, p * τ * p⁻¹ = A.D₂.w₂ * τ * A.D₂.w₂⁻¹) ∧
      ∃ a : ℕ, p ^ 2 ^ a = 1 := by
  obtain ⟨c, hc, p₀, hN, hW, hτ⟩ := A.exists_p₀
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos p₀).ne'
  have hgT : ∀ τ ∈ T₁, p₀ * τ * p₀⁻¹ ∈ T₁ := fun τ hτ' => A.conj_mem_T₁_of_actsW hc hW hτ'
  have hact : ∀ τ ∈ T₁, p₀ ^ m * τ * (p₀ ^ m)⁻¹ = A.D₂.w₂ * τ * A.D₂.w₂⁻¹ := by
    intro τ hτ'
    rw [(conj_pow_eq_of_conj_eq hτ hgT m τ hτ').1, pow_odd_of_sq A.w₂₂_sq hm]
  refine ⟨c, hc, p₀ ^ m, pow_mem hN m, ?_, hact, a, ?_⟩
  · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := A.ι_mem_T₁_gens
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hW
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hact _ g6, ← hτ _ g6, h1]
    · rw [hact _ g1, ← hτ _ g1, h2]
    · rw [hact _ g5, ← hτ _ g5, h3]
    · rw [hact _ g4, ← hτ _ g4, h4]
    · rw [hact _ g7, ← hτ _ g7, h5]
    · rw [hact _ g2, ← hτ _ g2, h6]
    · rw [hact _ g3, ← hτ _ g3, h7]
  · rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]

structure PData (A : AData S F T₁) where
  c : MA
  hc : c ∈ MA.ZList
  p : X
  hN : p ∈ normalizer (A.D₁.S₁ : Set X)
  hW : A.ActsW c p
  hact : ∀ τ ∈ T₁, p * τ * p⁻¹ = A.D₂.w₂ * τ * A.D₂.w₂⁻¹
  a : ℕ
  hpow : p ^ 2 ^ a = 1

theorem nonempty_PData : Nonempty A.PData := by
  obtain ⟨c, hc, p, hN, hW, hact, a, hpow⟩ := A.exists_p
  exact ⟨⟨c, hc, p, hN, hW, hact, a, hpow⟩⟩

namespace PData

variable {A} (B : A.PData)

@[expose] noncomputable def R₂ : Subgroup X := A.D₁.S₁ ⊔ zpowers B.p

theorem S₁_le_R₂ : A.D₁.S₁ ≤ B.R₂ := le_sup_left

theorem p_mem_R₂ : B.p ∈ B.R₂ := mem_sup_right (mem_zpowers _)

theorem isPGroup_R₂ : IsPGroup 2 B.R₂ :=
  IsPGroup.to_sup_of_normal_left' A.D₁.isPGroup_S₁ (isPGroup_zpowers_of_pow B.hpow)
    (zpowers_le.mpr B.hN)

theorem p_conj_t : B.p * S.t * B.p⁻¹ = A.ι (MA.t * MA.u) := by
  have := B.hW.1
  rwa [A.ι_t] at this

theorem p_not_mem_S₁ : B.p ∉ A.D₁.S₁ := by
  intro h
  obtain ⟨s, hs⟩ := A.mem_range_of_mem_S₁ h
  apply MA.not_conj_t_tu s
  apply A.ι_injective
  rw [map_mul, map_mul, map_inv, hs, A.ι_t, B.p_conj_t]

theorem p_sq_conj {τ : X} (hτ : τ ∈ T₁) : (B.p * B.p) * τ * (B.p * B.p)⁻¹ = τ := by
  have h1 := B.hact τ hτ
  have h2 := B.hact _ (A.conj_mem_T₁_of_actsW B.hc B.hW hτ)
  rw [h1] at h2
  calc (B.p * B.p) * τ * (B.p * B.p)⁻¹ = B.p * (B.p * τ * B.p⁻¹) * B.p⁻¹ := by group
    _ = B.p * (A.D₂.w₂ * τ * A.D₂.w₂⁻¹) * B.p⁻¹ := by rw [h1]
    _ = A.D₂.w₂ * (A.D₂.w₂ * τ * A.D₂.w₂⁻¹) * A.D₂.w₂⁻¹ := h2
    _ = (A.D₂.w₂ * A.D₂.w₂) * τ * (A.D₂.w₂ * A.D₂.w₂)⁻¹ := by group
    _ = τ := by rw [A.w₂₂_sq]; group

theorem p_sq_mem_S₁ : B.p * B.p ∈ A.D₁.S₁ := by
  have hC : B.p * B.p ∈ centralizer (T₁ : Set X) := by
    rw [mem_centralizer_iff]
    intro τ hτ
    have := B.p_sq_conj hτ
    calc τ * (B.p * B.p) = ((B.p * B.p) * τ * (B.p * B.p)⁻¹) * (B.p * B.p) := by rw [this]
      _ = (B.p * B.p) * τ := by group
  have hE := A.centralizer_T₁_le hC
  have hle : A.D₁.S₁ ⊔ zpowers (B.p * B.p) ≤ B.R₂ :=
    sup_le B.S₁_le_R₂ (zpowers_le.mpr (mul_mem B.p_mem_R₂ B.p_mem_R₂))
  have hmax := A.D₁.S₁_maximal _ (B.isPGroup_R₂.to_le hle) le_sup_left
    (sup_le A.D₁.S₁_le (zpowers_le.mpr hE))
  rw [← hmax]
  exact mem_sup_right (mem_zpowers _)

theorem exists_σ : ∃ σ ∈ MA.ZList, B.p * B.p = A.ι σ := by
  obtain ⟨σ, hσ⟩ := A.mem_range_of_mem_S₁ B.p_sq_mem_S₁
  refine ⟨σ, ?_, hσ.symm⟩
  have hc : ∀ g ∈ [MA.u, MA.w₁, MA.v, MA.z, MA.y, MA.t, MA.k], g * σ = σ * g := by
    intro g hg
    have hgT : MA.inT1 g = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    have h1 := B.p_sq_conj (A.ι_mem_of_T1 hgT)
    rw [← hσ] at h1
    apply A.ι_injective
    rw [map_mul, map_mul]
    calc A.ι g * A.ι σ = (A.ι σ * A.ι g * (A.ι σ)⁻¹) * A.ι σ := by rw [h1]
      _ = A.ι σ * A.ι g := by group
  rcases MA.cent_T1 σ hc with rfl | rfl | rfl | rfl <;> simp [MA.ZList]

theorem mem_R₂ {g : X} (hg : g ∈ B.R₂) : g ∈ A.D₁.S₁ ∨ g * B.p⁻¹ ∈ A.D₁.S₁ :=
  mem_or_of_mem_sup_zpowers B.hN (by rw [pow_two]; exact B.p_sq_mem_S₁) hg

theorem p_conj_W {c : MA} (hc : MA.inW c = true) : B.p * A.ι c * B.p⁻¹ = A.ι c := by
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := B.hW
  have := map_mem_of_inSpan (A.ι) (MA.W_span c hc) (H := centralizer ({B.p} : Set X))
    fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rw [mem_centralizer_singleton_iff]
      rcases hg with rfl | rfl | rfl | rfl
      · calc A.ι MA.w₁ * B.p = (B.p * A.ι MA.w₁ * B.p⁻¹) * B.p := by rw [h6]
          _ = B.p * A.ι MA.w₁ := by group
      · calc A.ι MA.v * B.p = (B.p * A.ι MA.v * B.p⁻¹) * B.p := by rw [h7]
          _ = B.p * A.ι MA.v := by group
      · calc A.ι MA.z * B.p = (B.p * A.ι MA.z * B.p⁻¹) * B.p := by rw [h4]
          _ = B.p * A.ι MA.z := by group
      · calc A.ι MA.k * B.p = (B.p * A.ι MA.k * B.p⁻¹) * B.p := by rw [h5]
          _ = B.p * A.ι MA.k := by group
  rw [mem_centralizer_singleton_iff] at this
  rw [← this, mul_inv_cancel_right]

theorem p_conj_M1 {m : MA} (hm : MA.inM1 m = true) :
    ∃ c : MA, MA.inW c = true ∧ B.p * A.ι m * B.p⁻¹ = A.ι (m * c) := by
  obtain ⟨-, h2, h3, -, -, -, -⟩ := B.hW
  have hcW : MA.inW (MA.w₁ * B.c) = true :=
    MA.ZList_mul_W B.c B.hc MA.w₁ (by decide +kernel)
  obtain ⟨d, hd, hm'⟩ := MA.M1_decomp m hm
  have hpd := B.p_conj_W hd
  have hcomm : ∀ a, a * d * (MA.w₁ * B.c) = a * (MA.w₁ * B.c) * d := by
    intro a; rw [mul_assoc, MA.W_comm d hd _ hcW, ← mul_assoc]
  rcases hm' with rfl | rfl | rfl | rfl
  · exact ⟨1, by decide +kernel, by rw [hpd, mul_one]⟩
  · refine ⟨1, by decide +kernel, ?_⟩
    rw [map_mul, show B.p * (A.ι MA.u * A.ι d) * B.p⁻¹ = (B.p * A.ι MA.u * B.p⁻¹) *
      (B.p * A.ι d * B.p⁻¹) by group, h2, hpd, ← map_mul, mul_one]
  · refine ⟨MA.w₁ * B.c, hcW, ?_⟩
    rw [map_mul, show B.p * (A.ι MA.y * A.ι d) * B.p⁻¹ = (B.p * A.ι MA.y * B.p⁻¹) *
      (B.p * A.ι d * B.p⁻¹) by group, h3, hpd, ← map_mul]
    congr 1
    rw [mul_assoc MA.y d, MA.W_comm d hd _ hcW]
    simp only [mul_assoc]
  · refine ⟨MA.w₁ * B.c, hcW, ?_⟩
    rw [map_mul, map_mul, show B.p * (A.ι MA.u * A.ι MA.y * A.ι d) * B.p⁻¹ =
      (B.p * A.ι MA.u * B.p⁻¹) * (B.p * A.ι MA.y * B.p⁻¹) * (B.p * A.ι d * B.p⁻¹) by group,
      h2, h3, hpd, ← map_mul, ← map_mul]
    congr 1
    rw [mul_assoc (MA.u * MA.y) d, MA.W_comm d hd _ hcW]
    simp only [mul_assoc]

theorem exists_ρ : ∃ ρ : MA, MA.inW ρ = true ∧ B.p * A.ι MA.w₂ * B.p⁻¹ = A.ι (MA.w₂ * ρ) := by
  have hmem : B.p * A.ι MA.w₂ * B.p⁻¹ ∈ A.D₁.S₁ :=
    conj_mem_of_mem_normalizer B.hN (A.ι_mem_S₁ _)
  obtain ⟨s, hs⟩ := A.mem_range_of_mem_S₁ hmem
  have hC := inv_mul_mem_centralizer (H := T₁) (fun τ hτ => A.conj_w₂_of_actsW B.hc B.hW hτ)
  rw [← hs] at hC
  set ζ := (MA.condWit B.c)⁻¹ * s with hζ
  have hζc : ∀ g ∈ [MA.u, MA.w₁, MA.v, MA.z, MA.y, MA.t, MA.k], g * ζ = ζ * g := by
    intro g hg
    have hgT : MA.inT1 g = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    have h1 := mem_centralizer_iff.mp hC _ (A.ι_mem_of_T1 hgT)
    apply A.ι_injective
    simp only [hζ, map_mul, map_inv]
    exact h1
  have hζZ : ζ ∈ MA.ZList := by
    rcases MA.cent_T1 ζ hζc with h | h | h | h <;> rw [h] <;> simp [MA.ZList]
  refine ⟨MA.w₂ * (MA.condWit B.c * ζ), MA.condW_wit_W B.c B.hc ζ hζZ, ?_⟩
  rw [← hs, hζ, ← mul_assoc, MA.w₂_sq, one_mul, mul_inv_cancel_left]

end PData

end AData

end Sec8

end CFSG.ComponentClassification.HSFLit
