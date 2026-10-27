module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UbGen

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_z (hσ : IsUnitaryInvolution σ) (hn : n = 4 ∨ n = 5)
    {e₁ f₁ e₂ f₂ : Fin n → K} (hF : FrameRel σ e₁ f₁ e₂ f₂) :
    ∃ z : Fin n → K, ZRel σ e₁ f₁ e₂ f₂ z ∧ (z ≠ 0 → herm σ z z ≠ 0) ∧
      (∀ v : Fin n → K, ∃ ε₁ φ₁ ε₂ φ₂ c₅ : K,
        v = vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ + c₅ • z) ∧
      (∀ w : Fin n → K, herm σ e₁ w = 0 → herm σ f₁ w = 0 → herm σ e₂ w = 0 →
        herm σ f₂ w = 0 → ∃ c : K, w = c • z) := by
  classical
  let L : (Fin n → K) →ₗ[K] K × K × K × K :=
    (hermL σ e₁).prod ((hermL σ f₁).prod ((hermL σ e₂).prod (hermL σ f₂)))
  have hL : ∀ w, L w = (herm σ e₁ w, herm σ f₁ w, herm σ e₂ w, herm σ f₂ w) := fun w => rfl
  have hsurj : Function.Surjective L := by
    rintro ⟨a, b, c, d⟩
    refine ⟨vec4 e₁ f₁ e₂ f₂ b a d c, ?_⟩
    rw [hL, herm_e1_vec4 hF, herm_f1_vec4 hF, herm_e2_vec4 hF, herm_f2_vec4 hF]
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrk
  simp only [Module.finrank_prod, Module.finrank_self] at hrk
  have hker : Module.finrank K (LinearMap.ker L) ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hker
  have hmem : ∀ w : Fin n → K, w ∈ LinearMap.ker L ↔ herm σ e₁ w = 0 ∧ herm σ f₁ w = 0 ∧
      herm σ e₂ w = 0 ∧ herm σ f₂ w = 0 := by
    intro w
    rw [LinearMap.mem_ker, hL]
    simp only [Prod.mk_eq_zero]
  have hchar : ∀ w : Fin n → K, herm σ e₁ w = 0 → herm σ f₁ w = 0 → herm σ e₂ w = 0 →
      herm σ f₂ w = 0 → ∃ c : K, w = c • (v : Fin n → K) := by
    intro w h1 h2 h3 h4
    obtain ⟨c, hc⟩ := hv ⟨w, (hmem w).2 ⟨h1, h2, h3, h4⟩⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  obtain ⟨h1, h2, h3, h4⟩ := (hmem v).1 v.2
  have hinv := hσ.invol
  have hZ : ZRel σ e₁ f₁ e₂ f₂ v :=
    ⟨h1, h2, h3, h4, herm_eq_zero_comm σ hinv h1, herm_eq_zero_comm σ hinv h2,
      herm_eq_zero_comm σ hinv h3, herm_eq_zero_comm σ hinv h4⟩
  have hspan : ∀ y : Fin n → K, ∃ ε₁ φ₁ ε₂ φ₂ c₅ : K,
      y = vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ + c₅ • (v : Fin n → K) := by
    intro y
    obtain ⟨c, hc⟩ := hchar (y - vec4 e₁ f₁ e₂ f₂ (herm σ f₁ y) (herm σ e₁ y) (herm σ f₂ y)
        (herm σ e₂ y))
      (by rw [herm_sub_right, herm_e1_vec4 hF, sub_self])
      (by rw [herm_sub_right, herm_f1_vec4 hF, sub_self])
      (by rw [herm_sub_right, herm_e2_vec4 hF, sub_self])
      (by rw [herm_sub_right, herm_f2_vec4 hF, sub_self])
    exact ⟨_, _, _, _, c, by rw [← hc]; abel⟩
  refine ⟨v, hZ, ?_, hspan, hchar⟩
  intro hz hzz
  apply hz
  apply eq_zero_of_herm σ
  intro y
  obtain ⟨ε₁, φ₁, ε₂, φ₂, c₅, hy⟩ := hspan y
  rw [hy, herm_add_right, herm_smul_right, hzz, mul_zero, add_zero]
  simp only [vec4, herm_add_right, herm_smul_right, hZ.ze1, hZ.zf1, hZ.ze2, hZ.zf2, mul_zero,
    add_zero]

theorem fixes_z (hσ : IsUnitaryInvolution σ) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hσq : ∀ u : K, u ^ r = 1 → σ u = u) {e₁ f₁ e₂ f₂ z : Fin n → K}
    (hZ : ZRel σ e₁ f₁ e₂ f₂ z) (hz0 : z ≠ 0 → herm σ z z ≠ 0)
    (hR : ∀ w : Fin n → K, herm σ e₁ w = 0 → herm σ f₁ w = 0 → herm σ e₂ w = 0 →
      herm σ f₂ w = 0 → ∃ c : K, w = c • z)
    {x : SUid σ n} (hx : x ^ r = 1) {α β : K} (hα : α ^ r = 1) (hβ : β ^ r = 1)
    (h₁ : x • e₁ = α • e₁) (h₂ : x • f₁ = α⁻¹ • f₁) (h₃ : x • e₂ = β • e₂)
    (h₄ : x • f₂ = β⁻¹ • f₂) : x • z = z := by
  have _ := hσ
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hr.ne_zero] at hα
    exact zero_ne_one hα
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hr.ne_zero] at hβ
    exact zero_ne_one hβ
  have key : ∀ (e : Fin n → K) (a : K), a ≠ 0 → x • e = a • e → herm σ e z = 0 →
      herm σ e (x • z) = 0 := by
    intro e a ha hxe hez
    have h := herm_smul_smul σ x e z
    rw [hxe, herm_smul_left, hez] at h
    exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero σ).2 ha)
  obtain ⟨ρ, hρ⟩ := hR (x • z) (key e₁ α hα0 h₁ hZ.e1z) (key f₁ α⁻¹ (inv_ne_zero hα0) h₂ hZ.f1z)
    (key e₂ β hβ0 h₃ hZ.e2z) (key f₂ β⁻¹ (inv_ne_zero hβ0) h₄ hZ.f2z)
  by_cases hz : z = 0
  · rw [hz, smul_zero]
  have hzz := hz0 hz
  have hnorm : σ ρ * ρ = 1 := by
    have h := herm_smul_smul σ x z z
    rw [hρ, herm_smul_left, herm_smul_right, ← mul_assoc] at h
    exact mul_right_cancel₀ hzz (by rw [h, one_mul])
  have hpow : ∀ m : ℕ, x ^ m • z = ρ ^ m • z := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_smul, hρ, smul_comm, ih, smul_smul, ← pow_succ']
  have hρr : ρ ^ r = 1 := by
    have h := hpow r
    rw [hx, one_smul] at h
    have h' : ρ ^ r • z = (1 : K) • z := by rw [one_smul]; exact h.symm
    exact smul_left_injective K hz h'
  have hρσ : σ ρ = ρ := hσq ρ hρr
  have hρ2 : ρ ^ 2 = 1 := by
    rw [pow_two]
    rw [hρσ] at hnorm
    exact hnorm
  have hρ1 : ρ = 1 := by
    obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
    have h : ρ ^ r = ρ := by rw [hk, pow_succ, pow_mul, hρ2, one_pow, one_mul]
    rw [← h, hρr]
  rw [hρ, hρ1, one_smul]

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub
