module

public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

theorem t2P53_v {G : Type} [Group G] [Finite G] {K₁ : Subgroup G} {F₁ : Type} [Field F₁] [Finite F₁]
    (hodd : Odd (Nat.card F₁)) (h3 : 3 < Nat.card F₁)
    (e₁ : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁) {z u g : G}
    (hz2 : z * z = 1) (hzu : z * u = u * z) (hg : g⁻¹ * z * g = u)
    (hnorm : ∀ c : G, c * z = z * c → ∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁)
    (hK₁ : ∀ x ∈ K₁, x * x = 1 → x = 1 ∨ x = z)
    (hnc : ∃ x ∈ K₁, (g * z * g⁻¹) * x * (g * z * g⁻¹)⁻¹ ≠ x) :
    ∃ v : G, v * v = u ∧ v * z * v⁻¹ = z * u := by
  set y : G := g * z * g⁻¹ with hy
  have hyz : y * z = z * y := by
    have hz : z = g * u * g⁻¹ := by rw [← hg]; group
    calc y * z = g * z * g⁻¹ * (g * u * g⁻¹) := by rw [← hz]
      _ = g * (z * u) * g⁻¹ := by group
      _ = g * (u * z) * g⁻¹ := by rw [hzu]
      _ = (g * u * g⁻¹) * (g * z * g⁻¹) := by group
      _ = z * y := by rw [← hz]
  have hy2 : y * y = 1 := by
    calc y * y = g * (z * z) * g⁻¹ := by rw [hy]; group
      _ = 1 := by rw [hz2]; group
  have hyn : y ∈ normalizer (K₁ : Set G) := Subgroup.mem_normalizer_fintype (hnorm y hyz)
  let α : MulAut ↥K₁ := Subgroup.normalizerMonoidHom K₁ ⟨y, hyn⟩
  have hα : ∀ x : ↥K₁, ((α x : ↥K₁) : G) = y * x * y⁻¹ := fun x => rfl
  have hαα : α * α = 1 := by
    ext x
    show ((α (α x) : ↥K₁) : G) = (x : G)
    rw [hα, hα]
    calc y * (y * x * y⁻¹) * y⁻¹ = (y * y) * x * (y * y)⁻¹ := by group
      _ = x := by rw [hy2]; group
  have hα1 : α ≠ 1 := by
    intro h
    obtain ⟨x, hx, hne⟩ := hnc
    apply hne
    have := congrArg (fun r : MulAut ↥K₁ => ((r ⟨x, hx⟩ : ↥K₁) : G)) h
    simpa [hα] using this
  have hord : orderOf α = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hαα
    · exact hα1
  obtain ⟨x, hx4, hαx⟩ := CFSG.GH74.GLS.IVK.ivk_1_13 F₁ hodd h3 ↥K₁
    (e₁.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F₁)) α hord
  set v₀ : G := (x : G) with hv₀
  have hyv : y * v₀ * y⁻¹ = v₀⁻¹ := by
    have := congrArg (fun r : ↥K₁ => (r : G)) hαx
    simpa [hα] using this
  have hv₀z : v₀ * v₀ = z := by
    have h1 : (v₀ * v₀) ∈ K₁ := K₁.mul_mem x.2 x.2
    have h2 : (v₀ * v₀) * (v₀ * v₀) = 1 := by
      have : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
      have h3' : (x : G) ^ 4 = 1 := by
        have := congrArg (fun r : ↥K₁ => (r : G)) this
        simpa using this
      calc v₀ * v₀ * (v₀ * v₀) = v₀ ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := h3'
    rcases hK₁ _ h1 h2 with h | h
    · exfalso
      have hx2 : x ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two, hv₀] using h
      have := orderOf_dvd_of_pow_eq_one hx2
      rw [hx4] at this
      omega
    · exact h
  refine ⟨g⁻¹ * v₀ * g, ?_, ?_⟩
  · calc g⁻¹ * v₀ * g * (g⁻¹ * v₀ * g) = g⁻¹ * (v₀ * v₀) * g := by group
      _ = u := by rw [hv₀z, hg]
  · have hzc : z * (g⁻¹ * v₀ * g) * z⁻¹ = (g⁻¹ * v₀ * g)⁻¹ := by
      have hzy : z = g⁻¹ * y * g := by rw [hy]; group
      calc z * (g⁻¹ * v₀ * g) * z⁻¹ = g⁻¹ * (y * v₀ * y⁻¹) * g := by
            rw [hzy]; group
        _ = g⁻¹ * v₀⁻¹ * g := by rw [hyv]
        _ = (g⁻¹ * v₀ * g)⁻¹ := by group
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rw [hzi] at hzc
    have hvv : g⁻¹ * v₀ * g * (g⁻¹ * v₀ * g) = u := by
      calc g⁻¹ * v₀ * g * (g⁻¹ * v₀ * g) = g⁻¹ * (v₀ * v₀) * g := by group
        _ = u := by rw [hv₀z, hg]
    set v := g⁻¹ * v₀ * g with hv
    have hvinv : v⁻¹ = z * v * z := hzc.symm
    calc v * z * v⁻¹ = v * z * (z * v * z) := by rw [← hvinv]
      _ = v * (z * z) * v * z := by group
      _ = v * v * z := by rw [hz2, mul_one]
      _ = u * z := by rw [hvv]
      _ = z * u := hzu.symm

end CFSG.GH74.GLS.Stage4.Rest
