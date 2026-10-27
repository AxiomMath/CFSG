module

public import CFSG.CGT.Stroth77.Section225FrameIndexTwo

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace DeviationGeneric

open Stroth225Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

section RTwo

variable (hfam : τ.m + 2 = τ.n) (hm : 2 ≤ τ.m) (hk : ∀ i, 2 ≤ τ.k i) (hDS : D ≤ S)
  (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) (huvS : dD.uv ∈ S) (htS : dD.t ∈ S)
  {A : Subgroup G} (hAD : A ≤ D) (hΩA : omegaIn 1 D ≤ A) (hA4 : ∀ a ∈ A, a ^ 4 = 1)
  (hinv : ∀ z ∈ S, z * z = 1 → z ∈ Subgroup.centralizer (A : Set G) →
    z⁻¹ * (dD.uv⁻¹ * z * dD.uv) ∈ A → z⁻¹ * (dD.t⁻¹ * z * dD.t) ∈ A → z ∈ A)

include hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv

theorem barD_commutator_eq_zero {s : G} (hs : s ∈ 𝓡[S, D]) (hd : devMat dD hk s hs = devD)
    {y : G} (hy : y ∈ 𝓡[S, D]) (hcol : ∀ i, devMat dD hk y hy i 0 = 0) :
    barD dD hk ⟨y * s * y⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hy hs⟩ = 0 := by
  obtain ⟨hne0, h00, h01, h02, h10, h20⟩ := devD_block
  obtain ⟨ht, huv⟩ := fixed_of_block devD ⟨h00, h01, h02, h10, h20⟩
  rw [← hd] at ht huv
  have hsD : s ∉ D := fun h => hne0 (hd ▸ (devMat_eq_zero_iff hk hcent hs).mpr h)
  have hq := sqBar_eq_c_of_fixed hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hsD ht huv
  have hscol := devMat_col_of_fixed hk hs ht huv
  have hk3 : 3 ≤ τ.k 1 := by rw [familyTwo_k hfam]; simp; omega
  have hk3' : 3 ≤ τ.k 2 := by rw [familyTwo_k hfam]; simp; omega
  set w : D := ⟨y * s * y⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hy hs⟩
  have hs2D := mul_self_mem_of_mem_R dD hk hcent hs
  have hys2 : y * (s * s) * y⁻¹ = s * s := by
    have h1 : barD dD hk ⟨s * s, hs2D⟩ 1 = 0 := by
      have := congrFun hq 1; simpa [sqBar] using this
    have h2 : barD dD hk ⟨s * s, hs2D⟩ 2 = 0 := by
      have := congrFun hq 2; simpa [sqBar] using this
    exact conj_eq_of_devMat_col hk hy hcol h1 h2
  have hinvw : s * (w : G) * s⁻¹ = (w : G)⁻¹ := by
    have h1 : (w : G) * (s * (w : G) * s⁻¹) = 1 := by
      simp only [w]
      calc y * s * y⁻¹ * s⁻¹ * (s * (y * s * y⁻¹ * s⁻¹) * s⁻¹) =
            (y * (s * s) * y⁻¹) * (s * s)⁻¹ := by group
        _ = 1 := by rw [hys2, mul_inv_cancel]
    exact eq_inv_of_mul_eq_one_right h1
  have hwΩ := commutator_mem_omegaIn_one dD hs w.2
  rw [hinvw] at hwΩ
  have hw4 : w ^ 4 = 1 := by
    have h3 := ((mem_omegaIn_iff_of_comm (fun a ha b hb => comm_of_mem dD ha hb)).mp hwΩ).2
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    have h4 : ((w : G)⁻¹ * (w : G)⁻¹) ^ 2 = ((w : G) ^ 4)⁻¹ := by group
    rw [pow_one, h4] at h3
    exact inv_eq_one.mp h3
  obtain ⟨hw1, hw2⟩ := barD_of_pow_four hk hk3 hk3' hw4
  have hsw := conj_eq_of_devMat_col hk hs hscol hw1 hw2
  have hw2' : w ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    simp only [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    calc (w : G) * w = (w : G) * (w : G)⁻¹⁻¹ := by rw [inv_inv]
      _ = (w : G) * (s * (w : G) * s⁻¹)⁻¹ := by rw [hinvw]
      _ = 1 := by rw [hsw, mul_inv_cancel]
  have hw0 := barD_eq_zero_of_pow (dD := dD) hk hw2' (i := 0) (hk 0)
  funext i
  fin_cases i
  · exact hw0
  · exact hw1
  · exact hw2

theorem devMat_fixed_eq_zero_or_devD {s : G} (hs : s ∈ 𝓡[S, D]) (hd : devMat dD hk s hs = devD)
    {y : G} (hy : y ∈ 𝓡[S, D]) (ht : actT (devMat dD hk y hy) = devMat dD hk y hy)
    (huv : actUv (devMat dD hk y hy) = devMat dD hk y hy) :
    devMat dD hk y hy = 0 ∨ devMat dD hk y hy = devD := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne0, hned⟩ := hcon
  obtain ⟨hd0, h00, h01, h02, h10, h20⟩ := devD_block
  obtain ⟨htd, huvd⟩ := fixed_of_block devD ⟨h00, h01, h02, h10, h20⟩
  have hyD : y ∉ D := fun h => hne0 ((devMat_eq_zero_iff hk hcent hy).mpr h)
  have hq := sqBar_eq_c_of_fixed hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hy hyD ht huv
  have hys := mul_mem hy hs
  have hdev : devMat dD hk _ hys = devMat dD hk y hy + devD := by
    rw [devMat_mul hk hy hs, hd]
  have hysD : y * s ∉ D := by
    intro h
    have h0 := (devMat_eq_zero_iff (dD := dD) hk hcent hys).mpr h
    rw [hdev] at h0
    exact hned (eq_of_add_eq_zero_two h0).symm
  have hts : actT (devMat dD hk _ hys) = devMat dD hk _ hys := by
    rw [hdev, actT_add, ht, htd]
  have huvs : actUv (devMat dD hk _ hys) = devMat dD hk _ hys := by
    rw [hdev, actUv_add, huv, huvd]
  have hqs := sqBar_eq_c_of_fixed hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hys hysD hts huvs
  have hcol := devMat_col_of_fixed hk hy ht huv
  have hβ := barD_commutator_eq_zero hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hd hy hcol
  have hsq := sqBar_mul (dD := dD) hk hcent hy hs
  have hsD : s ∉ D := fun h => hd0 (hd ▸ (devMat_eq_zero_iff hk hcent hs).mpr h)
  have hts' : actT (devMat dD hk s hs) = devMat dD hk s hs := by rw [hd, htd]
  have huvs' : actUv (devMat dD hk s hs) = devMat dD hk s hs := by rw [hd, huvd]
  have hqs' := sqBar_eq_c_of_fixed hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hsD hts' huvs'
  rw [hqs, hq, hqs', hβ] at hsq
  have := congrFun hsq 0
  revert this
  decide

theorem devMat_eq_zero_or_devD {s : G} (hs : s ∈ 𝓡[S, D]) (hd : devMat dD hk s hs = devD)
    {y : G} (hy : y ∈ 𝓡[S, D]) (hcol : ∀ i, devMat dD hk y hy i 0 = 0) :
    devMat dD hk y hy = 0 ∨ devMat dD hk y hy = devD := by
  by_cases hfix : actT (devMat dD hk y hy) = devMat dD hk y hy ∧
      actUv (devMat dD hk y hy) = devMat dD hk y hy
  · exact devMat_fixed_eq_zero_or_devD hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hd hy
      hfix.1 hfix.2
  · exfalso
    have hyt := conj_mem_R htS dD.t_mem hy
    have hyuv := conj_mem_R huvS dD.uv_mem hy
    have hyt' := conj_mem_R huvS dD.uv_mem hyt
    have e1 := devMat_conj_t (dD := dD) hfam hk hy hyt
    have e2 := devMat_conj_uv (dD := dD) hfam hk hy hyuv
    have e3 : devMat dD hk _ hyt' = actUv (actT (devMat dD hk y hy)) := by
      rw [devMat_conj_uv hfam hk hyt hyt', e1]
    rcases hc_cases _ ⟨hcol 0, hcol 1, hcol 2⟩ hfix with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · have hm' := mul_mem hy hyt
      have hdev : devMat dD hk _ hm' = devMat dD hk y hy + actT (devMat dD hk y hy) := by
        rw [devMat_mul hk hy hyt, e1]
      rw [← hdev] at h1 h2 h3 h4
      rcases devMat_fixed_eq_zero_or_devD hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hd
        hm' h1 h2 with h | h
      · exact h3 h
      · exact h4 h
    · have hm' := mul_mem hy hyuv
      have hdev : devMat dD hk _ hm' = devMat dD hk y hy + actUv (devMat dD hk y hy) := by
        rw [devMat_mul hk hy hyuv, e2]
      rw [← hdev] at h1 h2 h3 h4
      rcases devMat_fixed_eq_zero_or_devD hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hd
        hm' h1 h2 with h | h
      · exact h3 h
      · exact h4 h
    · have hm' := mul_mem hy hyt'
      have hdev : devMat dD hk _ hm' = devMat dD hk y hy + actUv (actT (devMat dD hk y hy)) := by
        rw [devMat_mul hk hy hyt', e3]
      rw [← hdev] at h1 h2 h3 h4
      rcases devMat_fixed_eq_zero_or_devD hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hd
        hm' h1 h2 with h | h
      · exact h3 h
      · exact h4 h

end RTwo

section Assembly

variable (hfam : τ.m + 2 = τ.n) (hm : 2 ≤ τ.m) (hk : ∀ i, 2 ≤ τ.k i) (hDS : D ≤ S)
  (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) (huvS : dD.uv ∈ S) (htS : dD.t ∈ S)
  (huS : dD.u ∈ S) (hS : Local.Setting S D)
  {A : Subgroup G} (hAD : A ≤ D) (hΩA : omegaIn 1 D ≤ A) (hA4 : ∀ a ∈ A, a ^ 4 = 1)
  (hinv : ∀ z ∈ S, z * z = 1 → z ∈ Subgroup.centralizer (A : Set G) →
    z⁻¹ * (dD.uv⁻¹ * z * dD.uv) ∈ A → z⁻¹ * (dD.t⁻¹ * z * dD.t) ∈ A → z ∈ A)

omit [Finite G] in
theorem le_centralizer_omegaIn (dD : StrothWeakTypeData D τ) [Finite G] (j : ℕ) :
    D ≤ Subgroup.centralizer ((omegaIn j D : Subgroup G) : Set G) := fun _ hd =>
  Subgroup.mem_centralizer_iff.mpr fun _ hw => comm_of_mem dD (omegaIn_le j D hw) hd

include hfam hm hk hDS hcent huvS htS huS hS hAD hΩA hA4 hinv

theorem exists_eq_sup_zpowers_of_ne
    (hne : 𝓡[S, D] ⊓ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ≠ D) :
    ∃ s : G, ∃ hs : s ∈ 𝓡[S, D], devMat dD hk s hs = devD ∧ s * s = (dD.c : G) ∧
      s ∈ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ∧
      𝓡[S, D] ⊓ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) =
        D ⊔ Subgroup.zpowers s := by
  have hDR2 : D ≤ 𝓡[S, D] ⊓ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) :=
    le_inf (D_le_R dD hDS) (le_centralizer_omegaIn dD _)
  obtain ⟨x, hxR2, hxD⟩ : ∃ x ∈ 𝓡[S, D] ⊓
      Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G), x ∉ D := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hne (le_antisymm (fun x hx => h x hx) hDR2)
  obtain ⟨s₀, hs₀, hd₀⟩ := exists_devMat_eq_devD hfam hm hk hDS hcent huvS htS huS hS hAD hΩA
    hA4 hinv (Subgroup.mem_inf.mp hxR2).1 hxD
  obtain ⟨s, hs, -, hs2, hd⟩ := exists_sq_eq_c_of_devMat_eq_devD hfam hm hk hDS hcent huvS htS
    hAD hΩA hA4 hinv hs₀ hd₀
  obtain ⟨-, h00, -, -, h10, h20⟩ := devD_block
  have hsC : s ∈ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) := by
    refine (mem_centralizer_omegaIn_iff (dD := dD) hfam hk hs).mpr fun i => ?_
    rw [hd]
    fin_cases i
    · exact h00
    · exact h10
    · exact h20
  refine ⟨s, hs, hd, hs2, hsC, le_antisymm ?_ (sup_le hDR2 ?_)⟩
  · intro y hy
    obtain ⟨hyR, hyC⟩ := Subgroup.mem_inf.mp hy
    have hcol := (mem_centralizer_omegaIn_iff (dD := dD) hfam hk hyR).mp hyC
    rcases devMat_eq_zero_or_devD hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hd hyR hcol
      with h | h
    · exact Subgroup.mem_sup_left ((devMat_eq_zero_iff hk hcent hyR).mp h)
    · have hsy := inv_mul_mem_of_devMat_eq hk hcent hs hyR (hd.trans h.symm)
      have hy' : y = s * (s⁻¹ * y) := by group
      rw [hy']
      exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)) (Subgroup.mem_sup_left hsy)
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨hs, hsC⟩

end Assembly

end DeviationGeneric

end CFSG.CGT.Stroth77
