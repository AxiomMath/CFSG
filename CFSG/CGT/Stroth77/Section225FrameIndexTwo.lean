module

public import CFSG.CGT.Stroth77.DeviationGenericFamilyTwo

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace DeviationGeneric

open Stroth225Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem devMat_col_of_fixed (hk : ∀ i, 2 ≤ τ.k i) {y : G} (hy : y ∈ 𝓡[S, D])
    (ht : actT (devMat dD hk y hy) = devMat dD hk y hy)
    (huv : actUv (devMat dD hk y hy) = devMat dD hk y hy) : ∀ i, devMat dD hk y hy i 0 = 0 := by
  obtain ⟨h1, -, -, h4, h5⟩ := block_of_fixed _ ht huv
  intro i
  fin_cases i
  · exact h1
  · exact h4
  · exact h5

theorem vec_eq_of_c_eq (v : Fin 3 → ZMod 2) (h : ![1, 0, 0] = ![1, 0, 0] + ![1, 0, 0] + v) :
    v = ![1, 0, 0] := by
  have key : ∀ a b c : ZMod 2, (![1, 0, 0] : Fin 3 → ZMod 2) = ![1, 0, 0] + ![1, 0, 0] +
      ![a, b, c] → (![a, b, c] : Fin 3 → ZMod 2) = ![1, 0, 0] := by
    decide
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h ⊢
  exact key _ _ _ h

section Fixed

variable (hfam : τ.m + 2 = τ.n) (hm : 2 ≤ τ.m) (hk : ∀ i, 2 ≤ τ.k i) (hDS : D ≤ S)
  (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) (huvS : dD.uv ∈ S) (htS : dD.t ∈ S)

include hfam hk hcent huvS htS

include hDS in
theorem sqBar_of_fixed {y : G} (hy : y ∈ 𝓡[S, D])
    (ht : actT (devMat dD hk y hy) = devMat dD hk y hy)
    (huv : actUv (devMat dD hk y hy) = devMat dD hk y hy) :
    sqBar dD hk hcent y hy 1 = 0 ∧ sqBar dD hk hcent y hy 2 = 0 := by
  have hyuv := conj_mem_R huvS dD.uv_mem hy
  have hyt := conj_mem_R htS dD.t_mem hy
  have h1 : barUv *ᵥ sqBar dD hk hcent y hy = sqBar dD hk hcent y hy := by
    rw [← sqBar_conj_uv hfam hk hcent hy hyuv]
    exact (sqBar_eq_of_devMat_eq hk hcent hDS hy hyuv
      ((devMat_conj_uv hfam hk hy hyuv).trans huv).symm).symm
  have h2 : barT *ᵥ sqBar dD hk hcent y hy = sqBar dD hk hcent y hy := by
    rw [← sqBar_conj_t hfam hk hcent hy hyt]
    exact (sqBar_eq_of_devMat_eq hk hcent hDS hy hyt
      ((devMat_conj_t hfam hk hy hyt).trans ht).symm).symm
  exact fixed_vec_of_uv_t _ h2 h1

theorem exists_fixed_of_not_mem {x : G} (hx : x ∈ 𝓡[S, D]) (hxD : x ∉ D) :
    ∃ y : G, ∃ hy : y ∈ 𝓡[S, D], y ∉ D ∧ actT (devMat dD hk y hy) = devMat dD hk y hy ∧
      actUv (devMat dD hk y hy) = devMat dD hk y hy := by
  obtain ⟨x₁, hx₁, hx₁D, ht₁⟩ : ∃ x₁ : G, ∃ hx₁ : x₁ ∈ 𝓡[S, D], x₁ ∉ D ∧
      actT (devMat dD hk x₁ hx₁) = devMat dD hk x₁ hx₁ := by
    have hxt := conj_mem_R htS dD.t_mem hx
    have hmul := mul_mem hx hxt
    have hdev : devMat dD hk _ hmul = devMat dD hk x hx + actT (devMat dD hk x hx) := by
      rw [devMat_mul hk hx hxt, devMat_conj_t hfam hk hx hxt]
    by_cases hz : devMat dD hk _ hmul = 0
    · rw [hdev] at hz
      exact ⟨x, hx, hxD, eq_of_add_eq_zero_two hz⟩
    · refine ⟨_, hmul, fun h => hz ((devMat_eq_zero_iff hk hcent hmul).mpr h), ?_⟩
      rw [hdev, actT_add, actT_actT, add_comm]
  have hxuv := conj_mem_R huvS dD.uv_mem hx₁
  have hmul := mul_mem hx₁ hxuv
  have hdev : devMat dD hk _ hmul = devMat dD hk x₁ hx₁ + actUv (devMat dD hk x₁ hx₁) := by
    rw [devMat_mul hk hx₁ hxuv, devMat_conj_uv hfam hk hx₁ hxuv]
  by_cases hz : devMat dD hk _ hmul = 0
  · rw [hdev] at hz
    exact ⟨x₁, hx₁, hx₁D, ht₁, eq_of_add_eq_zero_two hz⟩
  · refine ⟨_, hmul, fun h => hz ((devMat_eq_zero_iff hk hcent hmul).mpr h), ?_, ?_⟩
    · rw [hdev, actT_add, actT_actUv, ht₁]
    · rw [hdev, actUv_add, actUv_actUv, add_comm]

variable {A : Subgroup G} (hAD : A ≤ D) (hΩA : omegaIn 1 D ≤ A) (hA4 : ∀ a ∈ A, a ^ 4 = 1)
  (hinv : ∀ z ∈ S, z * z = 1 → z ∈ Subgroup.centralizer (A : Set G) →
    z⁻¹ * (dD.uv⁻¹ * z * dD.uv) ∈ A → z⁻¹ * (dD.t⁻¹ * z * dD.t) ∈ A → z ∈ A)

include hm hDS hAD hΩA hA4 hinv

theorem mem_D_of_fixed_of_sqBar_eq_zero {y : G} (hy : y ∈ 𝓡[S, D])
    (ht : actT (devMat dD hk y hy) = devMat dD hk y hy)
    (huv : actUv (devMat dD hk y hy) = devMat dD hk y hy)
    (hq : sqBar dD hk hcent y hy = 0) : y ∈ D := by
  have hcol := devMat_col_of_fixed hk hy ht huv
  have hk3 : 3 ≤ τ.k 1 := by rw [familyTwo_k hfam]; simp; omega
  have hk3' : 3 ≤ τ.k 2 := by rw [familyTwo_k hfam]; simp; omega
  have hyuv := conj_mem_R huvS dD.uv_mem hy
  have hyt := conj_mem_R htS dD.t_mem hy
  refine mem_D_of_sq_mem_mhoOne dD hk hDS hAD hΩA hA4 dD.uv_mem dD.t_mem hinv hy
    (fun w hw hw4 => ?_) ?_ ?_ ((barD_eq_zero_iff hk _).mp hq)
  · have hw4' : (⟨w, hw⟩ : D) ^ 4 = 1 := Subtype.ext (by simpa using hw4)
    obtain ⟨h1, h2⟩ := barD_of_pow_four hk hk3 hk3' hw4'
    exact conj_eq_of_devMat_col hk hy hcol h1 h2
  · exact inv_mul_mem_of_devMat_eq hk hcent hy hyuv
      ((devMat_conj_uv hfam hk hy hyuv).trans huv).symm
  · exact inv_mul_mem_of_devMat_eq hk hcent hy hyt ((devMat_conj_t hfam hk hy hyt).trans ht).symm

theorem sqBar_eq_c_of_fixed {y : G} (hy : y ∈ 𝓡[S, D]) (hyD : y ∉ D)
    (ht : actT (devMat dD hk y hy) = devMat dD hk y hy)
    (huv : actUv (devMat dD hk y hy) = devMat dD hk y hy) :
    sqBar dD hk hcent y hy = ![1, 0, 0] := by
  obtain ⟨h1, h2⟩ := sqBar_of_fixed hfam hk hDS hcent huvS htS hy ht huv
  have h0 : sqBar dD hk hcent y hy 0 ≠ 0 := by
    intro h0
    apply hyD
    refine mem_D_of_fixed_of_sqBar_eq_zero hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hy ht
      huv ?_
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  funext i
  fin_cases i
  · show sqBar dD hk hcent y hy 0 = 1
    revert h0
    generalize sqBar dD hk hcent y hy 0 = a
    intro h0
    fin_cases a
    · exact absurd rfl h0
    · rfl
  · exact h1
  · exact h2

end Fixed

section Layers

variable (hfam : τ.m + 2 = τ.n) (hm : 2 ≤ τ.m) (hk : ∀ i, 2 ≤ τ.k i) (hDS : D ≤ S)
  (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) (huvS : dD.uv ∈ S) (htS : dD.t ∈ S)
  (huS : dD.u ∈ S) (hS : Local.Setting S D)
  {A : Subgroup G} (hAD : A ≤ D) (hΩA : omegaIn 1 D ≤ A) (hA4 : ∀ a ∈ A, a ^ 4 = 1)
  (hinv : ∀ z ∈ S, z * z = 1 → z ∈ Subgroup.centralizer (A : Set G) →
    z⁻¹ * (dD.uv⁻¹ * z * dD.uv) ∈ A → z⁻¹ * (dD.t⁻¹ * z * dD.t) ∈ A → z ∈ A)

include hfam hm hk hDS hcent huvS htS hS hAD hΩA hA4 hinv

theorem false_of_devMat_w0 {w : G} (hw : w ∈ 𝓡[S, D])
    (hW : devMat dD hk w hw = w0a ∨ devMat dD hk w hw = w0b ∨ devMat dD hk w hw = w0c) :
    False := by
  have hw₂ := proj_mem_R dD hk hS hw
  set w₂ := hS.proj dD.ρ w
  have hdev₂ := devMat_proj_rho hfam hk hS hw hw₂
  obtain ⟨hW₂, hne, hW₃⟩ := rho_w0 _ hW
  rw [← hdev₂] at hW₂ hne hW₃
  have hw₃ := mul_mem hw hw₂
  have hdev₃ := devMat_mul (dD := dD) hk hw hw₂
  rw [← hdev₃] at hW₃
  have hsq : ∀ (y : G) (hy : y ∈ 𝓡[S, D]), (devMat dD hk y hy = w0a ∨
      devMat dD hk y hy = w0b ∨ devMat dD hk y hy = w0c) → sqBar dD hk hcent y hy = ![1, 0, 0] ∧
      (∀ i, devMat dD hk y hy i 0 = 0) := by
    intro y hy hW'
    obtain ⟨hne0, -, h00, h01, h02, h10, h20⟩ := w0_block _ hW'
    obtain ⟨ht, huv⟩ := fixed_of_block _ ⟨h00, h01, h02, h10, h20⟩
    have hyD : y ∉ D := fun h => hne0 ((devMat_eq_zero_iff hk hcent hy).mpr h)
    exact ⟨sqBar_eq_c_of_fixed hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hy hyD ht huv,
      devMat_col_of_fixed hk hy ht huv⟩
  obtain ⟨hq₁, hc₁⟩ := hsq w hw hW
  obtain ⟨hq₂, hc₂⟩ := hsq w₂ hw₂ hW₂
  obtain ⟨hq₃, -⟩ := hsq _ hw₃ hW₃
  have hzD := commutator_mem_D dD hk hcent hw hw₂
  set z : D := ⟨w * w₂ * w⁻¹ * w₂⁻¹, hzD⟩
  have hzbar : barD dD hk z = ![1, 0, 0] := by
    have h := sqBar_mul (dD := dD) hk hcent hw hw₂
    rw [hq₁, hq₂, hq₃] at h
    exact vec_eq_of_c_eq _ h
  have hw2D := mul_self_mem_of_mem_R dD hk hcent hw
  have hcw : w₂ * (w * w) * w₂⁻¹ = w * w := by
    have h1 : barD dD hk ⟨w * w, hw2D⟩ 1 = 0 := by
      have := congrFun hq₁ 1; simpa [sqBar] using this
    have h2 : barD dD hk ⟨w * w, hw2D⟩ 2 = 0 := by
      have := congrFun hq₁ 2; simpa [sqBar] using this
    exact conj_eq_of_devMat_col hk hw₂ hc₂ h1 h2
  have hcomm : (w * w) * w₂ = w₂ * (w * w) := by
    calc (w * w) * w₂ = (w₂ * (w * w) * w₂⁻¹) * w₂ := by rw [hcw]
      _ = w₂ * (w * w) := by group
  have hconj : (w * w) * w₂ * (w * w)⁻¹ = w₂ := by rw [hcomm]; group
  have hinvz : w * (z : G) * w⁻¹ = (z : G)⁻¹ := by
    simp only [z]
    calc w * (w * w₂ * w⁻¹ * w₂⁻¹) * w⁻¹ = (w * w) * w₂ * (w * w)⁻¹ * (w * w₂⁻¹ * w⁻¹) := by
          group
      _ = w₂ * (w * w₂⁻¹ * w⁻¹) := by rw [hconj]
      _ = (w * w₂ * w⁻¹ * w₂⁻¹)⁻¹ := by group
  have hcz : w * (z : G) * w⁻¹ = z :=
    conj_eq_of_devMat_col hk hw hc₁ (by rw [hzbar]; rfl) (by rw [hzbar]; rfl)
  have hz2 : z ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    simp only [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    calc (z : G) * z = (z : G) * (z : G)⁻¹⁻¹ := by rw [inv_inv]
      _ = (z : G) * (w * (z : G) * w⁻¹)⁻¹ := by rw [hinvz]
      _ = 1 := by rw [hcz, mul_inv_cancel]
  have h0 := barD_eq_zero_of_pow (dD := dD) hk hz2 (i := 0) (hk 0)
  rw [hzbar] at h0
  exact absurd h0 (by decide)

include huS in
theorem exists_devMat_eq_devD {x : G} (hx : x ∈ 𝓡[S, D]) (hxD : x ∉ D) :
    ∃ s : G, ∃ hs : s ∈ 𝓡[S, D], devMat dD hk s hs = devD := by
  obtain ⟨y, hy, hyD, ht, huv⟩ := exists_fixed_of_not_mem hfam hk hcent huvS htS hx hxD
  have hb := block_of_fixed _ ht huv
  have hne : devMat dD hk y hy ≠ 0 := fun h => hyD ((devMat_eq_zero_iff hk hcent hy).mp h)
  rcases block_cases _ hb hne with h | h | h
  · exact ⟨y, hy, h⟩
  · have hyu := conj_mem_R huS dD.u_mem hy
    refine ⟨_, mul_mem hy hyu, ?_⟩
    rw [devMat_mul hk hy hyu, devMat_conj_u hfam hk hy hyu]
    exact h
  · exfalso
    have hyρ := proj_mem_R dD hk hS hy
    apply false_of_devMat_w0 hfam hm hk hDS hcent huvS htS hS hAD hΩA hA4 hinv (mul_mem hy hyρ)
    rw [devMat_mul hk hy hyρ, devMat_proj_rho hfam hk hS hy hyρ]
    exact h

omit hS in
theorem exists_sq_eq_c_of_devMat_eq_devD {s : G} (hs : s ∈ 𝓡[S, D])
    (hd : devMat dD hk s hs = devD) :
    ∃ s' : G, ∃ hs' : s' ∈ 𝓡[S, D], s⁻¹ * s' ∈ D ∧ s' * s' = (dD.c : G) ∧
      devMat dD hk s' hs' = devD := by
  obtain ⟨hne0, h00, h01, h02, h10, h20⟩ := devD_block
  obtain ⟨ht, huv⟩ := fixed_of_block devD ⟨h00, h01, h02, h10, h20⟩
  rw [← hd] at ht huv
  have hsD : s ∉ D := fun h => hne0 (hd ▸ (devMat_eq_zero_iff hk hcent hs).mpr h)
  have hq := sqBar_eq_c_of_fixed hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hsD ht huv
  have hcol := devMat_col_of_fixed hk hs ht huv
  have hk3 : 3 ≤ τ.k 1 := by rw [familyTwo_k hfam]; simp; omega
  have hk3' : 3 ≤ τ.k 2 := by rw [familyTwo_k hfam]; simp; omega
  have hs2D := mul_self_mem_of_mem_R dD hk hcent hs
  have hmem : (s * s)⁻¹ * (dD.c : G) ∈ mhoOne D := by
    have h1 : barD dD hk (⟨s * s, hs2D⟩⁻¹ * dD.c) = 0 := by
      rw [barD_mul, barD_inv, barD_c]
      have : barD dD hk ⟨s * s, hs2D⟩ = sqBar dD hk hcent s hs := rfl
      rw [this, hq]
      funext i
      exact CharTwo.add_self_eq_zero _
    have := (barD_eq_zero_iff hk _).mp h1
    simpa using this
  obtain ⟨d, hdD, hdeq⟩ := exists_conj_mul_eq dD hk hs (fun w hw hw4 => by
    have hw4' : (⟨w, hw⟩ : D) ^ 4 = 1 := Subtype.ext (by simpa using hw4)
    obtain ⟨h1, h2⟩ := barD_of_pow_four hk hk3 hk3' hw4'
    exact conj_eq_of_devMat_col hk hs hcol h1 h2) hmem
  refine ⟨s * d, mul_mem hs (D_le_R dD hDS hdD), ?_, ?_, ?_⟩
  · simpa using hdD
  · calc (s * d) * (s * d) = (s * s) * (s⁻¹ * d * s * d) := by group
      _ = (dD.c : G) := by rw [hdeq]; group
  · rw [devMat_mul hk hs (D_le_R dD hDS hdD), hd,
      (devMat_eq_zero_iff hk hcent (D_le_R dD hDS hdD)).mpr hdD, add_zero]

end Layers

end DeviationGeneric

end CFSG.CGT.Stroth77
