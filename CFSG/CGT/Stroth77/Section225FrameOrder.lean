module

public import CFSG.CGT.Stroth77.Section225FrameSquare

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace DeviationGeneric

open Stroth225Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

section Order

variable (hfam : τ.m + 2 = τ.n) (hm : 2 ≤ τ.m) (hk : ∀ i, 2 ≤ τ.k i) (hDS : D ≤ S)
  (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) (huvS : dD.uv ∈ S) (htS : dD.t ∈ S)
  (huS : dD.u ∈ S) (hS : Local.Setting S D)
  {A : Subgroup G} (hAD : A ≤ D) (hΩA : omegaIn 1 D ≤ A) (hA4 : ∀ a ∈ A, a ^ 4 = 1)
  (hinv : ∀ z ∈ S, z * z = 1 → z ∈ Subgroup.centralizer (A : Set G) →
    z⁻¹ * (dD.uv⁻¹ * z * dD.uv) ∈ A → z⁻¹ * (dD.t⁻¹ * z * dD.t) ∈ A → z ∈ A)

include hfam hm hk hDS hcent huvS htS huS hS hAD hΩA hA4 hinv

theorem exists_devD_of_not_mem {x : G} (hx : x ∈ 𝓡[S, D]) (hxD : x ∉ D) :
    ∃ s : G, ∃ hs : s ∈ 𝓡[S, D], devMat dD hk s hs = devD ∧ s * s = (dD.c : G) := by
  obtain ⟨s₀, hs₀, hd₀⟩ := exists_devMat_eq_devD hfam hm hk hDS hcent huvS htS huS hS hAD hΩA
    hA4 hinv hx hxD
  obtain ⟨s, hs, -, hs2, hd⟩ := exists_sq_eq_c_of_devMat_eq_devD hfam hm hk hDS hcent huvS htS
    hAD hΩA hA4 hinv hs₀ hd₀
  exact ⟨s, hs, hd, hs2⟩

theorem f00_eq_zero {x : G} (hx : x ∈ 𝓡[S, D]) : devMat dD hk x hx 0 0 = 0 := by
  by_contra hne
  have hf : devMat dD hk x hx 0 0 = 1 := by
    revert hne
    generalize devMat dD hk x hx 0 0 = a
    intro hne
    fin_cases a
    · exact absurd rfl hne
    · rfl
  have hxD : x ∉ D := fun h => by
    rw [(devMat_eq_zero_iff hk hcent hx).mpr h] at hf
    exact absurd hf (by decide)
  obtain ⟨s, hs, hd, hs2⟩ := exists_devD_of_not_mem hfam hm hk hDS hcent huvS htS huS hS hAD hΩA
    hA4 hinv hx hxD
  rcases Nat.lt_or_ge τ.m 3 with hlt | hge
  · have hm2 : τ.m = 2 := by omega
    have hR2 : ∀ (y : G) (hy : y ∈ 𝓡[S, D]), devMat dD hk y hy 0 0 = 0 →
        sqBar dD hk hcent y hy 1 = 0 → sqBar dD hk hcent y hy 2 = 0 →
        devMat dD hk y hy = 0 ∨ devMat dD hk y hy = devD := by
      intro y hy hf0 hq1 hq2
      have hcol := devMat_mulVec_c_eq hfam hk hcent hs hd hs2 hy (Or.inr hf0)
      rw [(devD_mulVec_eq_zero_iff _).mpr ⟨hq1, hq2⟩] at hcol
      refine devMat_eq_zero_or_devD hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hd hy
        fun i => ?_
      have := congrFun hcol i
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have hqx : sqBar dD hk hcent x hx 1 = 0 ∧ sqBar dD hk hcent x hx 2 = 0 := by
      have h := devMat_mulVec_c_add_barD hfam hk hcent hs hd hs2 hx
      have hw0 := barD_commutator_zero_eq hfam hk hcent hs hd hs2 hm2 hx
      obtain ⟨h1, h2⟩ := barD_commutator_one_two (dD := dD) hfam hk hcent hx hs
      have hcw : (![1, 0, 0] : Fin 3 → ZMod 2) +
          barD dD hk ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩ = 0 := by
        funext i
        fin_cases i
        · show 1 + barD dD hk ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩ 0 = 0
          rw [hw0, hf]
          decide
        · show 0 + barD dD hk ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩ 1 = 0
          rw [h1]
          rfl
        · show 0 + barD dD hk ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩ 2 = 0
          rw [h2]
          rfl
      rw [hcw, Matrix.mulVec_zero] at h
      exact (devD_mulVec_eq_zero_iff _).mp h.symm
    have hxuv := conj_mem_R huvS dD.uv_mem hx
    have hxt := conj_mem_R htS dD.t_mem hx
    have hx₁ := mul_mem hx hxuv
    have hx₂ := mul_mem hx hxt
    have hdev₁ : devMat dD hk _ hx₁ = devMat dD hk x hx + actUv (devMat dD hk x hx) := by
      rw [devMat_mul hk hx hxuv, devMat_conj_uv hfam hk hx hxuv]
    have hdev₂ : devMat dD hk _ hx₂ = devMat dD hk x hx + actT (devMat dD hk x hx) := by
      rw [devMat_mul hk hx hxt, devMat_conj_t hfam hk hx hxt]
    obtain ⟨⟨hu1, hu2⟩, ⟨ht1, ht2⟩⟩ := bar_mulVec_one_two hqx.1 hqx.2
    obtain ⟨hb1, hb2⟩ := barD_commutator_one_two (dD := dD) hfam hk hcent hx hxuv
    obtain ⟨hc1, hc2⟩ := barD_commutator_one_two (dD := dD) hfam hk hcent hx hxt
    have hq₁ := sqBar_mul (dD := dD) hk hcent hx hxuv
    rw [sqBar_conj_uv hfam hk hcent hx hxuv] at hq₁
    have hq₂ := sqBar_mul (dD := dD) hk hcent hx hxt
    rw [sqBar_conj_t hfam hk hcent hx hxt] at hq₂
    have h₁ := hR2 _ hx₁ (by rw [hdev₁]; exact (f00_one_add _).1)
      (by rw [hq₁]; simp only [Pi.add_apply, hqx.1, hu1, hb1, add_zero])
      (by rw [hq₁]; simp only [Pi.add_apply, hqx.2, hu2, hb2, add_zero])
    have h₂ := hR2 _ hx₂ (by rw [hdev₂]; exact (f00_one_add _).2)
      (by rw [hq₂]; simp only [Pi.add_apply, hqx.1, ht1, hc1, add_zero])
      (by rw [hq₂]; simp only [Pi.add_apply, hqx.2, ht2, hc2, add_zero])
    rw [hdev₁] at h₁
    rw [hdev₂] at h₂
    exact false_of_f00_of_add_mem _ hf h₁ h₂
  · have h := congrFun (devMat_mulVec_c_eq hfam hk hcent hs hd hs2 hx (Or.inl hge)) 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, devD, hf] at h

theorem devMat_mulVec_c_eq_of_mem {s : G} (hs : s ∈ 𝓡[S, D]) (hd : devMat dD hk s hs = devD)
    (hs2 : s * s = (dD.c : G)) {x : G} (hx : x ∈ 𝓡[S, D]) :
    devMat dD hk x hx *ᵥ ![1, 0, 0] = devD *ᵥ sqBar dD hk hcent x hx :=
  devMat_mulVec_c_eq hfam hk hcent hs hd hs2 hx
    (Or.inr (f00_eq_zero hfam hm hk hDS hcent huvS htS huS hS hAD hΩA hA4 hinv hx))

theorem le_centralizer_omegaIn_of_pow_eq_one {B : Subgroup G} (hBR : B ≤ 𝓡[S, D])
    (hB : ∀ b ∈ B, b ^ (2 ^ τ.n) = 1) :
    B ≤ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) := by
  intro x hxB
  have hx := hBR hxB
  by_cases hxD : x ∈ D
  · exact le_centralizer_omegaIn dD _ hxD
  obtain ⟨s, hs, hd, hs2⟩ := exists_devD_of_not_mem hfam hm hk hDS hcent huvS htS huS hS hAD hΩA
    hA4 hinv hx hxD
  have hcol := devMat_mulVec_c_eq_of_mem hfam hm hk hDS hcent huvS htS huS hS hAD hΩA hA4 hinv
    hs hd hs2 hx
  have hx2 := mul_self_mem_of_mem_R dD hk hcent hx
  have hpow : (⟨x * x, hx2⟩ : D) ^ (2 ^ (τ.m + 1)) = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← pow_two, ← pow_mul, ← pow_succ', show τ.m + 1 + 1 = τ.n by omega]
    exact hB x hxB
  have hkk := familyTwo_k hfam
  have hq1 : sqBar dD hk hcent x hx 1 = 0 :=
    barD_eq_zero_of_pow (dD := dD) hk hpow (by rw [hkk]; simp)
  have hq2 : sqBar dD hk hcent x hx 2 = 0 :=
    barD_eq_zero_of_pow (dD := dD) hk hpow (by rw [hkk]; simp)
  rw [(devD_mulVec_eq_zero_iff _).mpr ⟨hq1, hq2⟩] at hcol
  refine (mem_centralizer_omegaIn_iff (dD := dD) hfam hk hx).mpr fun i => ?_
  have := congrFun hcol i
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this

theorem mem_omegaIn_one_of_mul_self_eq_one {z : G} (hz : z ∈ 𝓡[S, D]) (hz2 : z * z = 1) :
    z ∈ omegaIn 1 D := by
  by_cases hzD : z ∈ D
  · exact mem_omegaIn_one_of_mul_self hzD hz2
  exfalso
  have hzn : z ^ (2 ^ τ.n) = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, 2 ^ τ.n = 2 * j := ⟨2 ^ (τ.n - 1), by rw [← pow_succ']; congr 1; omega⟩
    rw [hj, pow_mul, pow_two, hz2, one_pow]
  have hzC : z ∈ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) := by
    refine le_centralizer_omegaIn_of_pow_eq_one hfam hm hk hDS hcent huvS htS huS hS hAD hΩA hA4
      hinv (B := Subgroup.zpowers z) (Subgroup.zpowers_le.mpr hz) (fun b hb => ?_)
      (Subgroup.mem_zpowers z)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hzn,
      _root_.one_zpow]
  have hne : 𝓡[S, D] ⊓ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ≠ D :=
    fun heq => hzD (heq ▸ Subgroup.mem_inf.mpr ⟨hz, hzC⟩)
  obtain ⟨s, hs, hd, hs2, -, -⟩ := exists_eq_sup_zpowers_of_ne hfam hm hk hDS hcent huvS htS huS
    hS hAD hΩA hA4 hinv hne
  have hcol := (mem_centralizer_omegaIn_iff (dD := dD) hfam hk hz).mp hzC
  rcases devMat_eq_zero_or_devD hfam hm hk hDS hcent huvS htS hAD hΩA hA4 hinv hs hd hz hcol with
    h0 | h0
  · exact hzD ((devMat_eq_zero_iff hk hcent hz).mp h0)
  · have hq := sqBar_eq_of_devMat_eq hk hcent hDS hz hs (h0.trans hd.symm)
    have h1 : sqBar dD hk hcent z hz = 0 := by
      rw [sqBar, show (⟨z * z, mul_self_mem_of_mem_R dD hk hcent hz⟩ : D) = 1 from
        Subtype.ext hz2, barD_one]
    have h2 : sqBar dD hk hcent s hs = ![1, 0, 0] := by
      rw [sqBar, show (⟨s * s, mul_self_mem_of_mem_R dD hk hcent hs⟩ : D) = dD.c from
        Subtype.ext hs2, barD_c]
    rw [h1, h2] at hq
    exact absurd (congrFun hq 0) (by decide)

end Order

end DeviationGeneric

end CFSG.CGT.Stroth77
