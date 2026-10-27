module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem isElemAbelian_zpowers_of_mul_self {Y : Type*} [Group Y] {x : Y} (hx : x * x = 1) :
    IsElemAbelian 2 (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hsq : x ^ 2 = 1 := by rw [sq]; exact hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsq, one_zpow]

theorem three_noncommuting {Y : Type*} [Group Y] {A A' : Subgroup Y}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a)
    {e₁ e₂ e₃ : Y} (h₁ : e₁ ∈ A ∨ e₁ ∈ A') (h₂ : e₂ ∈ A ∨ e₂ ∈ A') (h₃ : e₃ ∈ A ∨ e₃ ∈ A')
    (c₁₂ : e₁ * e₂ ≠ e₂ * e₁) (c₁₃ : e₁ * e₃ ≠ e₃ * e₁) (c₂₃ : e₂ * e₃ ≠ e₃ * e₂) : False := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃
  · exact c₁₂ (hA _ h₁ _ h₂)
  · exact c₁₂ (hA _ h₁ _ h₂)
  · exact c₁₃ (hA _ h₁ _ h₃)
  · exact c₂₃ (hA' _ h₂ _ h₃)
  · exact c₂₃ (hA _ h₂ _ h₃)
  · exact c₁₃ (hA' _ h₁ _ h₃)
  · exact c₁₂ (hA' _ h₁ _ h₂)
  · exact c₁₂ (hA' _ h₁ _ h₂)

theorem ExamAbs.exists_RprimeE {Kg : Type} [Group Kg] [Finite Kg] {A A' P R : Subgroup Kg} {m : ℕ}
    (h : ExamAbs Kg A A' P R m) {X : Type} [Group X] [Finite X]
    (θ : Kg →* X) (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center Kg)
    (U : Subgroup X) (hU : IsSylowTwoOf U ⊤) :
    ∃ R₀ A₀ A₀' : Subgroup X, R₀ ≤ U ∧
      (∀ n ∈ Subgroup.normalizer (U : Set X), ∀ r ∈ R₀, n * r * n⁻¹ ∈ R₀) ∧ R₀ ≠ ⊥ ∧
      IsElemAbelian 2 A₀ ∧ IsElemAbelian 2 A₀' ∧
      (∀ e ∈ R₀, e * e = 1 → e ∈ A₀ ∨ e ∈ A₀') ∧
      (∀ r ∈ R₀, r * r = 1 → ∀ g : X, g * r * g⁻¹ ∈ U → g * r * g⁻¹ ∈ R₀) := by
  have hP2 : IsPGroup 2 P := h.sylowP.2.1
  have hPX : IsSylowTwoOf (P.map θ) ⊤ := CFSG.Quasithin.A312.isSylowTwoOf_top_map θ hθ h.sylowP
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hPX hU
  let Θ : Kg →* X := (MulAut.conj g).toMonoidHom.comp θ
  have hΘsurj : Function.Surjective Θ := (MulAut.conj g).surjective.comp hθ
  have hΘP : P.map Θ = U := by
    rw [← hg, Subgroup.map_map]
  have hΘker : ∀ x, Θ x = 1 → θ x = 1 := by
    intro x hx
    have : g * θ x * g⁻¹ = 1 := hx
    simpa using this
  have hkerR : ∀ x ∈ R, Θ x = 1 → x = 1 := fun x hx hΘx =>
    h.center_inf_R x (hker (MonoidHom.mem_ker.mpr (hΘker x hΘx))) hx
  have hRP : ∀ x ∈ R, x ∈ P := fun x hx => h.R_le_P hx
  have hRelem : ∀ x ∈ R, x ∈ A ∨ x ∈ A' → x ^ 2 = 1 := by
    rintro x - (hx | hx)
    · exact h.A_elem.2 x hx
    · exact h.A'_elem.2 x hx
  have hstrong : ∀ x ∈ R, x ^ 2 = 1 → ∀ n : X, n * Θ x * n⁻¹ ∈ U →
      n * Θ x * n⁻¹ ∈ R.map Θ := by
    intro x hxR hx2 n hU'
    obtain ⟨κ, hκ⟩ := hΘsurj n⁻¹
    have hconj : n * Θ x * n⁻¹ = Θ (κ⁻¹ * x * κ) := by
      rw [map_mul, map_mul, map_inv, hκ]; simp
    rw [← hΘP] at hU'
    obtain ⟨p, hp, hpe⟩ := hU'
    rw [hconj] at hpe
    have hz : p⁻¹ * (κ⁻¹ * x * κ) ∈ Subgroup.center Kg := by
      apply hker
      rw [MonoidHom.mem_ker]
      have : Θ (p⁻¹ * (κ⁻¹ * x * κ)) = 1 := by rw [map_mul, map_inv, hpe, inv_mul_cancel]
      exact hΘker _ this
    set z := p⁻¹ * (κ⁻¹ * x * κ) with hzdef
    have hxe : κ⁻¹ * x * κ = p * z := by rw [hzdef]; group
    have hsq : (κ⁻¹ * x * κ) ^ 2 = 1 := by
      rw [sq, show κ⁻¹ * x * κ * (κ⁻¹ * x * κ) = κ⁻¹ * (x * x) * κ by group, ← sq, hx2]
      group
    have hzc : ∀ w : Kg, w * z = z * w := fun w => Subgroup.mem_center_iff.mp hz w
    have hpz : (p * z) ^ 2 = p ^ 2 * z ^ 2 := Commute.mul_pow (show Commute p z from hzc p) 2
    have hpz2 : p ^ 2 * z ^ 2 = 1 := by rw [← hpz, ← hxe]; exact hsq
    have hz2P : z ^ 2 = (p ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hpz2
    obtain ⟨k, hk⟩ := hP2 ⟨(p ^ 2)⁻¹, P.inv_mem (P.pow_mem hp 2)⟩
    have hzk : z ^ (2 ^ (k + 1)) = 1 := by
      have hk' : ((p ^ 2)⁻¹) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      rw [pow_succ', pow_mul, hz2P, hk']
    have hzP : z ∈ P := mem_of_central_two_element h.sylowP hz hzk
    have hpP : κ⁻¹ * x * κ ∈ P := by rw [hxe]; exact P.mul_mem hp hzP
    have hxR' : κ⁻¹ * x * κ ∈ R := h.strong x hxR hx2 κ hpP
    rw [hconj]
    exact Subgroup.mem_map_of_mem _ hxR'
  have hnorm : ∀ n ∈ Subgroup.normalizer (U : Set X), ∀ ρ ∈ R, n * Θ ρ * n⁻¹ ∈ R.map Θ := by
    intro n hn ρ hρ
    have hρ' : ρ ∈ A ⊔ A' := h.R_eq ▸ hρ
    rw [Subgroup.sup_eq_closure] at hρ'
    clear hρ
    induction hρ' using Subgroup.closure_induction with
    | mem x hx =>
      have hxR : x ∈ R := by
        rcases hx with hx | hx
        · exact h.A_le_R hx
        · exact h.A'_le_R hx
      have hx2 : x ^ 2 = 1 := hRelem x hxR (by simpa using hx)
      have hU' : n * Θ x * n⁻¹ ∈ U := by
        have hx' : Θ x ∈ U := by rw [← hΘP]; exact Subgroup.mem_map_of_mem _ (hRP x hxR)
        exact (Subgroup.mem_normalizer_iff.mp hn (Θ x)).mp hx'
      exact hstrong x hxR hx2 n hU'
    | one => simp
    | mul x y hx hy ihx ihy =>
      have : n * Θ (x * y) * n⁻¹ = (n * Θ x * n⁻¹) * (n * Θ y * n⁻¹) := by
        rw [map_mul]; group
      rw [this]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
      have : n * Θ x⁻¹ * n⁻¹ = (n * Θ x * n⁻¹)⁻¹ := by
        rw [map_inv]; group
      rw [this]
      exact Subgroup.inv_mem _ ihx
  refine ⟨R.map Θ, A.map Θ, A'.map Θ, ?_, ?_, ?_, isElemAbelian_map' h.A_elem Θ,
    isElemAbelian_map' h.A'_elem Θ, ?_, ?_⟩
  · rw [← hΘP]
    exact Subgroup.map_mono h.R_le_P
  · rintro n hn _ ⟨ρ, hρ, rfl⟩
    exact hnorm n hn ρ hρ
  · intro hbot
    have hRbot : R = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : Θ x ∈ R.map Θ := Subgroup.mem_map_of_mem _ hx
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (hkerR x hx this)
    have hcard := h.card_R
    rw [hRbot, Subgroup.card_bot] at hcard
    have hm := h.two_le
    have : 2 ^ 1 ≤ 2 ^ (4 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rintro _ ⟨x, hxR, rfl⟩ hxx
    have hx2 : x * x = 1 := hkerR (x * x) (R.mul_mem hxR hxR) (by rw [map_mul]; exact hxx)
    have hE : IsElemAbelian 2 (Subgroup.zpowers x) := isElemAbelian_zpowers_of_mul_self hx2
    rcases h.elem_le _ ((Subgroup.zpowers_le).mpr hxR) hE with hle | hle
    · exact Or.inl ⟨x, hle (Subgroup.mem_zpowers x), rfl⟩
    · exact Or.inr ⟨x, hle (Subgroup.mem_zpowers x), rfl⟩
  · rintro _ ⟨ρ, hρ, rfl⟩ hr2 g hg
    have hρ2 : ρ ^ 2 = 1 :=
      hkerR (ρ ^ 2) (R.pow_mem hρ 2) (by rw [map_pow, sq]; exact hr2)
    exact hstrong ρ hρ hρ2 g hg

end CFSG.QuasithinUnique.Lin2
