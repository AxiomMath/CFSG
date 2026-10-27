module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section CubeRoots

variable {ω : K}

theorem cubeRoot_one_add_add_sq (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) : 1 + ω + ω ^ 2 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
  rcases mul_eq_zero.1 h with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hω1
  · exact h1

theorem ker_sub_one_eq_eigenspace (t : Module.End K V) :
    LinearMap.ker (t - 1) = t.eigenspace 1 := by
  ext v
  rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, one_smul, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

theorem eq_zero_of_add_eigen (h3 : (3 : K) ≠ 0) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (t : Module.End K V) {a b c : V} (ha : t a = a) (hb : t b = ω • b) (hc : t c = ω ^ 2 • c)
    (h : a + b + c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hs := cubeRoot_one_add_add_sq hω1 hω3
  have h1 : a + ω • b + ω ^ 2 • c = 0 := by
    have := congrArg t h
    rwa [map_add, map_add, ha, hb, hc, map_zero] at this
  have h2 : a + ω ^ 2 • b + ω • c = 0 := by
    have := congrArg t h1
    rw [map_add, map_add, map_smul, map_smul, ha, hb, hc, map_zero, smul_smul, smul_smul] at this
    have e1 : ω * ω = ω ^ 2 := by ring
    have e2 : ω ^ 2 * ω ^ 2 = ω := by linear_combination ω * hω3
    rwa [e1, e2] at this
  have ha0 : a = 0 := by
    have h3a : (3 : K) • a = 0 := by
      linear_combination (norm := module) h + h1 + h2 - hs • b - hs • c
    exact (smul_eq_zero.1 h3a).resolve_left h3
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hne : ω - ω ^ 2 ≠ 0 := by
    have e : ω - ω ^ 2 = ω * (1 - ω) := by ring
    rw [e]
    exact mul_ne_zero hω0 (sub_ne_zero.2 (Ne.symm hω1))
  have hb0 : b = 0 := by
    have hb' : (ω - ω ^ 2) • b = 0 := by
      linear_combination (norm := module) h1 - ω ^ 2 • h + (ω ^ 2 - 1) • ha0
    exact (smul_eq_zero.1 hb').resolve_left hne
  refine ⟨ha0, hb0, ?_⟩
  rw [ha0, hb0, zero_add, zero_add] at h
  exact h

theorem exists_eigen_decomp (h3 : (3 : K) ≠ 0) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {t : Module.End K V} (ht : t ^ 3 = 1) {U : Submodule K V} (hU : ∀ u ∈ U, t u ∈ U)
    {u : V} (hu : u ∈ U) :
    ∃ u₀ u₁ u₂ : V, u₀ ∈ U ∧ u₁ ∈ U ∧ u₂ ∈ U ∧ t u₀ = u₀ ∧ t u₁ = ω • u₁ ∧ t u₂ = ω ^ 2 • u₂ ∧
      u₀ + u₁ + u₂ = u := by
  have hs := cubeRoot_one_add_add_sq hω1 hω3
  have htu : t (t (t u)) = u := by
    have := congrArg (fun f : Module.End K V => f u) ht
    simpa only [pow_three, Module.End.mul_apply, Module.End.one_apply] using this
  set c : K := (3 : K)⁻¹ with hc
  have h3c : (3 : K) * c = 1 := mul_inv_cancel₀ h3
  have htuU : t u ∈ U := hU u hu
  have httuU : t (t u) ∈ U := hU _ htuU
  refine ⟨c • (u + t u + t (t u)), c • (u + ω ^ 2 • t u + ω • t (t u)),
    c • (u + ω • t u + ω ^ 2 • t (t u)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact U.smul_mem c (U.add_mem (U.add_mem hu htuU) httuU)
  · exact U.smul_mem c (U.add_mem (U.add_mem hu (U.smul_mem _ htuU)) (U.smul_mem _ httuU))
  · exact U.smul_mem c (U.add_mem (U.add_mem hu (U.smul_mem _ htuU)) (U.smul_mem _ httuU))
  · rw [map_smul, map_add, map_add, htu]
    module
  · rw [map_smul, map_add, map_add, map_smul, map_smul, htu]
    linear_combination (norm := module) hω3.symm • (c • t u)
  · rw [map_smul, map_add, map_add, map_smul, map_smul, htu]
    linear_combination (norm := module) hω3.symm • (c • t u) + hω3.symm • ((c * ω) • t (t u))
  · linear_combination (norm := module) hs • (c • t u) + hs • (c • t (t u)) + h3c • u

end CubeRoots

section Dimensions

variable [FiniteDimensional K V] {ω : K}

theorem finrank_add_add_le (h3 : (3 : K) ≠ 0) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (t : Module.End K V) {A B C X : Submodule K V} (hAX : A ≤ X) (hBX : B ≤ X) (hCX : C ≤ X)
    (hA : ∀ a ∈ A, t a = a) (hB : ∀ b ∈ B, t b = ω • b) (hC : ∀ c ∈ C, t c = ω ^ 2 • c) :
    finrank K A + finrank K B + finrank K C ≤ finrank K X := by
  let f : (A × (B × C)) →ₗ[K] V := A.subtype.coprod (B.subtype.coprod C.subtype)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b, c⟩ h
    have h' : (a : V) + (b : V) + (c : V) = 0 := by
      have e : f (a, b, c) = (a : V) + ((b : V) + (c : V)) := by
        simp only [f, LinearMap.coprod_apply, Submodule.subtype_apply]
      rw [e] at h
      rw [add_assoc]
      exact h
    obtain ⟨ha0, hb0, hc0⟩ :=
      eq_zero_of_add_eigen h3 hω1 hω3 t (hA a a.2) (hB b b.2) (hC c c.2) h'
    exact Prod.ext (Subtype.ext ha0) (Prod.ext (Subtype.ext hb0) (Subtype.ext hc0))
  have hle : LinearMap.range f ≤ X := by
    rintro _ ⟨⟨a, b, c⟩, rfl⟩
    exact X.add_mem (hAX a.2) (X.add_mem (hBX b.2) (hCX c.2))
  have h1 := LinearMap.finrank_range_of_inj hf
  rw [Module.finrank_prod, Module.finrank_prod] at h1
  have h2 := Submodule.finrank_mono hle
  omega

theorem finrank_le_add_add (h3 : (3 : K) ≠ 0) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {t : Module.End K V} (ht : t ^ 3 = 1) {U : Submodule K V} (hU : ∀ u ∈ U, t u ∈ U) :
    finrank K U ≤ finrank K ↥(U ⊓ t.eigenspace 1) + finrank K ↥(U ⊓ t.eigenspace ω) +
      finrank K ↥(U ⊓ t.eigenspace (ω ^ 2)) := by
  let f : (↥(U ⊓ t.eigenspace 1) × (↥(U ⊓ t.eigenspace ω) × ↥(U ⊓ t.eigenspace (ω ^ 2)))) →ₗ[K] V :=
    (U ⊓ t.eigenspace 1).subtype.coprod
      ((U ⊓ t.eigenspace ω).subtype.coprod (U ⊓ t.eigenspace (ω ^ 2)).subtype)
  have hle : U ≤ LinearMap.range f := by
    intro u hu
    obtain ⟨u₀, u₁, u₂, h0U, h1U, h2U, h0, h1, h2, hsum⟩ := exists_eigen_decomp h3 hω1 hω3 ht hU hu
    refine LinearMap.mem_range.2
      ⟨(⟨u₀, Submodule.mem_inf.2 ⟨h0U, Module.End.mem_eigenspace_iff.2 (by rw [one_smul]; exact h0)⟩⟩,
        ⟨u₁, Submodule.mem_inf.2 ⟨h1U, Module.End.mem_eigenspace_iff.2 h1⟩⟩,
        ⟨u₂, Submodule.mem_inf.2 ⟨h2U, Module.End.mem_eigenspace_iff.2 h2⟩⟩), ?_⟩
    change u₀ + (u₁ + u₂) = u
    rw [← add_assoc]
    exact hsum
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_le f
  rw [Module.finrank_prod, Module.finrank_prod] at h2
  omega

theorem finrank_eq_add_add (h3 : (3 : K) ≠ 0) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {t : Module.End K V} (ht : t ^ 3 = 1) {U : Submodule K V} (hU : ∀ u ∈ U, t u ∈ U) :
    finrank K U = finrank K ↥(U ⊓ t.eigenspace 1) + finrank K ↥(U ⊓ t.eigenspace ω) +
      finrank K ↥(U ⊓ t.eigenspace (ω ^ 2)) := by
  refine le_antisymm (finrank_le_add_add h3 hω1 hω3 ht hU) ?_
  refine finrank_add_add_le h3 hω1 hω3 t inf_le_left inf_le_left inf_le_left ?_ ?_ ?_
  · intro a ha
    rw [(Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 ha).2), one_smul]
  · intro b hb
    exact Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hb).2
  · intro c hc
    exact Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hc).2

theorem three_mul_add_le_coset (h3 : (3 : K) ≠ 0) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {h t : Module.End K V} (hh : h ^ 3 = 1) (hht : h * t = t * h) {W : Submodule K V}
    (hWh : ∀ w ∈ W, h w ∈ W) (hWt : ∀ w ∈ W, t w ∈ W) :
    3 * finrank K ↥(W ⊓ t.eigenspace 1 ⊓ h.eigenspace 1) + finrank K ↥(W ⊓ t.eigenspace ω) +
        finrank K ↥(W ⊓ t.eigenspace (ω ^ 2)) ≤
      finrank K ↥(W ⊓ h.eigenspace 1) + finrank K ↥(W ⊓ (h * t).eigenspace 1) +
        finrank K ↥(W ⊓ (h * t * t).eigenspace 1) := by
  have hcomm : ∀ v, h (t v) = t (h v) := fun v => by
    have := congrArg (fun f : Module.End K V => f v) hht
    simpa only [Module.End.mul_apply] using this
  have hinv : ∀ μ : K, ∀ w ∈ W ⊓ t.eigenspace μ, h w ∈ W ⊓ t.eigenspace μ := by
    intro μ w hw
    obtain ⟨hwW, hwt⟩ := Submodule.mem_inf.1 hw
    refine Submodule.mem_inf.2 ⟨hWh w hwW, Module.End.mem_eigenspace_iff.2 ?_⟩
    rw [← hcomm, Module.End.mem_eigenspace_iff.1 hwt, map_smul]
  have hD1 := finrank_eq_add_add h3 hω1 hω3 hh (hinv ω)
  have hD2 := finrank_eq_add_add h3 hω1 hω3 hh (hinv (ω ^ 2))
  have mem : ∀ {μ ν : K} {v : V}, v ∈ W ⊓ t.eigenspace μ ⊓ h.eigenspace ν →
      v ∈ W ∧ t v = μ • v ∧ h v = ν • v := fun hv => by
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨hv3, hv4⟩ := Submodule.mem_inf.1 hv1
    exact ⟨hv3, Module.End.mem_eigenspace_iff.1 hv4, Module.End.mem_eigenspace_iff.1 hv2⟩
  have tpiece : ∀ {μ ν : K}, ∀ v ∈ W ⊓ t.eigenspace μ ⊓ h.eigenspace ν, t v = μ • v :=
    fun v hv => (mem hv).2.1
  have hk0 : finrank K ↥(W ⊓ t.eigenspace 1 ⊓ h.eigenspace 1) +
      finrank K ↥(W ⊓ t.eigenspace ω ⊓ h.eigenspace 1) +
        finrank K ↥(W ⊓ t.eigenspace (ω ^ 2) ⊓ h.eigenspace 1) ≤
      finrank K ↥(W ⊓ h.eigenspace 1) := by
    refine finrank_add_add_le h3 hω1 hω3 t ?_ ?_ ?_
      (fun a ha => by rw [tpiece a ha, one_smul]) (fun b hb => tpiece b hb) (fun c hc => tpiece c hc)
    all_goals
      intro v hv
      obtain ⟨hvW, -, hvh⟩ := mem hv
      exact Submodule.mem_inf.2 ⟨hvW, Module.End.mem_eigenspace_iff.2 hvh⟩
  have hk1 : finrank K ↥(W ⊓ t.eigenspace 1 ⊓ h.eigenspace 1) +
      finrank K ↥(W ⊓ t.eigenspace ω ⊓ h.eigenspace (ω ^ 2)) +
        finrank K ↥(W ⊓ t.eigenspace (ω ^ 2) ⊓ h.eigenspace ω) ≤
      finrank K ↥(W ⊓ (h * t).eigenspace 1) := by
    refine finrank_add_add_le h3 hω1 hω3 t ?_ ?_ ?_
      (fun a ha => by rw [tpiece a ha, one_smul]) (fun b hb => tpiece b hb) (fun c hc => tpiece c hc)
    · intro v hv
      obtain ⟨hvW, hvt, hvh⟩ := mem hv
      refine Submodule.mem_inf.2 ⟨hvW, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [Module.End.mul_apply, hvt, one_smul, hvh, one_smul]
    · intro v hv
      obtain ⟨hvW, hvt, hvh⟩ := mem hv
      refine Submodule.mem_inf.2 ⟨hvW, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [Module.End.mul_apply, hvt, map_smul, hvh, smul_smul, one_smul]
      linear_combination (norm := module) hω3 • v
    · intro v hv
      obtain ⟨hvW, hvt, hvh⟩ := mem hv
      refine Submodule.mem_inf.2 ⟨hvW, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [Module.End.mul_apply, hvt, map_smul, hvh, smul_smul, one_smul]
      linear_combination (norm := module) hω3 • v
  have hk2 : finrank K ↥(W ⊓ t.eigenspace 1 ⊓ h.eigenspace 1) +
      finrank K ↥(W ⊓ t.eigenspace ω ⊓ h.eigenspace ω) +
        finrank K ↥(W ⊓ t.eigenspace (ω ^ 2) ⊓ h.eigenspace (ω ^ 2)) ≤
      finrank K ↥(W ⊓ (h * t * t).eigenspace 1) := by
    refine finrank_add_add_le h3 hω1 hω3 t ?_ ?_ ?_
      (fun a ha => by rw [tpiece a ha, one_smul]) (fun b hb => tpiece b hb) (fun c hc => tpiece c hc)
    · intro v hv
      obtain ⟨hvW, hvt, hvh⟩ := mem hv
      refine Submodule.mem_inf.2 ⟨hvW, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [Module.End.mul_apply, Module.End.mul_apply, hvt, one_smul, hvt, one_smul, hvh, one_smul]
    · intro v hv
      obtain ⟨hvW, hvt, hvh⟩ := mem hv
      refine Submodule.mem_inf.2 ⟨hvW, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [Module.End.mul_apply, Module.End.mul_apply, hvt, map_smul, hvt, smul_smul, map_smul, hvh,
        smul_smul, one_smul]
      linear_combination (norm := module) hω3 • v
    · intro v hv
      obtain ⟨hvW, hvt, hvh⟩ := mem hv
      refine Submodule.mem_inf.2 ⟨hvW, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [Module.End.mul_apply, Module.End.mul_apply, hvt, map_smul, hvt, smul_smul, map_smul, hvh,
        smul_smul, one_smul]
      linear_combination (norm := module) (ω ^ 3 + 1) • hω3 • v
  have e1 : finrank K ↥(W ⊓ t.eigenspace ω) = finrank K ↥(W ⊓ t.eigenspace ω ⊓ h.eigenspace 1) +
      finrank K ↥(W ⊓ t.eigenspace ω ⊓ h.eigenspace ω) +
        finrank K ↥(W ⊓ t.eigenspace ω ⊓ h.eigenspace (ω ^ 2)) := hD1
  have e2 : finrank K ↥(W ⊓ t.eigenspace (ω ^ 2)) =
      finrank K ↥(W ⊓ t.eigenspace (ω ^ 2) ⊓ h.eigenspace 1) +
        finrank K ↥(W ⊓ t.eigenspace (ω ^ 2) ⊓ h.eigenspace ω) +
          finrank K ↥(W ⊓ t.eigenspace (ω ^ 2) ⊓ h.eigenspace (ω ^ 2)) := hD2
  omega

end Dimensions

section Average

variable [FiniteDimensional K V] {ω : K}

theorem card_mul_finrank_le_three_mul_sum (h3 : (3 : K) ≠ 0) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {G : Type*} [Group G] [Fintype G] (hcomm : ∀ a b : G, a * b = b * a)
    (hexp : ∀ g : G, g ^ 3 = 1) (ρ : G →* Module.End K V) (W : Submodule K V)
    (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W) :
    Fintype.card G * finrank K W ≤ 3 * ∑ g : G, finrank K ↥(W ⊓ (ρ g).eigenspace 1) := by
  suffices H : ∀ n : ℕ, ∀ W : Submodule K V, finrank K W = n → (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) →
      Fintype.card G * finrank K W ≤ 3 * ∑ g : G, finrank K ↥(W ⊓ (ρ g).eigenspace 1) from
    H _ W rfl hW
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hWn hW
  have hρ3 : ∀ g : G, ρ g ^ 3 = 1 := fun g => by rw [← map_pow, hexp g, map_one]
  have hρc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := fun a b => by rw [← map_mul, hcomm a b, map_mul]
  by_cases htriv : ∀ g : G, ∀ w ∈ W, ρ g w = w
  · have hfix : ∀ g : G, finrank K ↥(W ⊓ (ρ g).eigenspace 1) = finrank K W := fun g => by
      rw [inf_eq_left.2 fun w hw => Module.End.mem_eigenspace_iff.2 (by rw [one_smul]; exact htriv g w hw)]
    simp only [hfix, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  · push Not at htriv
    obtain ⟨y, w, hw, hyw⟩ := htriv
    set t := ρ y with ht
    set W₀ := W ⊓ t.eigenspace 1 with hW₀
    have hW₀lt : W₀ < W := by
      refine lt_of_le_of_ne inf_le_left fun heq => hyw ?_
      have hw0 : w ∈ W₀ := heq ▸ hw
      have h1 := Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hw0).2
      rw [one_smul] at h1
      exact h1
    have hlt : finrank K W₀ < finrank K W := Submodule.finrank_lt_finrank_of_lt hW₀lt
    have hW₀inv : ∀ g : G, ∀ v ∈ W₀, ρ g v ∈ W₀ := by
      intro g v hv
      obtain ⟨hvW, hvt⟩ := Submodule.mem_inf.1 hv
      refine Submodule.mem_inf.2 ⟨hW g v hvW, Module.End.mem_eigenspace_iff.2 ?_⟩
      have e : t (ρ g v) = ρ g (t v) := by
        have := congrArg (fun f : Module.End K V => f v) (hρc y g)
        simpa only [Module.End.mul_apply, ht] using this
      rw [e, Module.End.mem_eigenspace_iff.1 hvt, map_smul]
    have IH := ih (finrank K W₀) (hWn ▸ hlt) W₀ rfl hW₀inv
    have hWt : ∀ v ∈ W, t v ∈ W := hW y
    have hcos : ∀ g : G, 3 * finrank K ↥(W₀ ⊓ (ρ g).eigenspace 1) + finrank K ↥(W ⊓ t.eigenspace ω) +
        finrank K ↥(W ⊓ t.eigenspace (ω ^ 2)) ≤
        finrank K ↥(W ⊓ (ρ g).eigenspace 1) + finrank K ↥(W ⊓ (ρ (g * y)).eigenspace 1) +
          finrank K ↥(W ⊓ (ρ (g * y * y)).eigenspace 1) := by
      intro g
      have := three_mul_add_le_coset h3 hω1 hω3 (hρ3 g) (hρc g y) (hW g) hWt
      rw [map_mul, map_mul, map_mul]
      exact this
    have hsum := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hcos g
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
    have hr1 : ∑ g : G, finrank K ↥(W ⊓ (ρ (g * y)).eigenspace 1) =
        ∑ g : G, finrank K ↥(W ⊓ (ρ g).eigenspace 1) :=
      Fintype.sum_equiv (Equiv.mulRight y) _ _ fun _ => rfl
    have hr2 : ∑ g : G, finrank K ↥(W ⊓ (ρ (g * y * y)).eigenspace 1) =
        ∑ g : G, finrank K ↥(W ⊓ (ρ g).eigenspace 1) :=
      Fintype.sum_equiv (Equiv.mulRight (y * y)) _ _ fun g =>
        congrArg (fun z : G => finrank K ↥(W ⊓ (ρ z).eigenspace 1)) (mul_assoc g y y)
    rw [hr1, hr2, ← Finset.mul_sum] at hsum
    have hdec : finrank K W = finrank K W₀ + finrank K ↥(W ⊓ t.eigenspace ω) +
        finrank K ↥(W ⊓ t.eigenspace (ω ^ 2)) := finrank_eq_add_add h3 hω1 hω3 (hρ3 y) hWt
    rw [hdec, Nat.mul_add, Nat.mul_add]
    omega

theorem card_mul_finrank_le_three_mul_sum_ker (h3 : (3 : K) ≠ 0) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {G : Type*} [Group G] [Fintype G] (hcomm : ∀ a b : G, a * b = b * a)
    (hexp : ∀ g : G, g ^ 3 = 1) (ρ : G →* Module.End K V) :
    Fintype.card G * finrank K V ≤ 3 * ∑ g : G, finrank K ↥(LinearMap.ker (ρ g - 1)) := by
  have h := card_mul_finrank_le_three_mul_sum h3 hω1 hω3 hcomm hexp ρ ⊤ fun _ _ _ => Submodule.mem_top
  have e : ∀ g : G, finrank K ↥((⊤ : Submodule K V) ⊓ (ρ g).eigenspace 1) =
      finrank K ↥(LinearMap.ker (ρ g - 1)) := fun g => by
    rw [top_inf_eq, ker_sub_one_eq_eigenspace]
  simp only [e, finrank_top] at h
  exact h

end Average

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u

end
