module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BBigAb
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructNonab

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BBig

open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem card_le_of_isPGroup_small [Finite K] (hK : Nat.card K = 4) {E : Type*}
    [AddCommGroup E] [Module K E] [Module.Finite K E] (hE : Module.finrank K E ≤ 2)
    (H : Subgroup (E ≃ₗ[K] E)) (hH : IsPGroup 3 H) : Nat.card H ≤ 3 ^ Module.finrank K E := by
  haveI : Finite (E ≃ₗ[K] E) := finite_linearEquiv
  rcases (by omega : Module.finrank K E = 0 ∨ Module.finrank K E = 1 ∨ Module.finrank K E = 2)
    with h | h | h
  · have := card_le_of_isPGroup hK h H hH
    rw [h]
    simpa using this
  · have := card_le_of_isPGroup hK h H hH
    rw [h]
    simpa using this
  · obtain ⟨j, hj⟩ := hH.exists_card_eq
    have hdvd : 3 ^ j ∣ Nat.card (E ≃ₗ[K] E) := hj ▸ Subgroup.card_subgroup_dvd_card H
    rw [card_linearEquiv_eq hK h] at hdvd
    simp only [Fin.prod_univ_two] at hdvd
    have hj2 : j ≤ 2 := by
      by_contra hj3
      have h27 : 3 ^ 3 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
      have := h27.trans hdvd
      norm_num at this
    rw [hj, h]
    exact Nat.pow_le_pow_right (by norm_num) hj2

private theorem card_le_of_nonab_small [Finite K] (hK : Nat.card K = 4) [FiniteDimensional K V]
    (hV : Module.finrank K V ≤ 8) {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q)
    {g h : V ≃ₗ[K] V} (hg : g ∈ Q) (hh : h ∈ Q) (hg3 : g ^ 3 = 1) (hgh : g * h ≠ h * g) :
    Nat.card Q ≤ 3 ^ 4 := by
  classical
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  haveI : Finite (eig g 1 ≃ₗ[K] eig g 1) := finite_linearEquiv
  have hZ := scalarLike_scalars (V := V) hK
  obtain ⟨ω, hω3, hω1, hω⟩ := exists_omega hK (hQ.1 g hg h hh) hgh
  obtain ⟨C, hCQ, hCg, hCcard⟩ := exists_centralizer_of_good hZ hQ hg
  have hCU : ∀ x ∈ C, ∀ u ∈ eig g 1, x u ∈ eig g 1 := by
    intro x hx u hu
    rw [mem_eig_iff] at hu ⊢
    have h1 : g (x u) = x (g u) := by
      have := congrArg (fun e : V ≃ₗ[K] V => e u) (hCg x hx)
      simpa using this
    rw [h1, hu, one_smul, one_smul]
  let ρ : C →* (eig g 1 ≃ₗ[K] eig g 1) :=
    CFSG.LargeExtraspecial.S4.restrictHom C.subtype (eig g 1) (fun x u hu => hCU x x.2 u hu)
  let κ : C →* scalars K V := (commHomLeft hZ hQ hh).comp (Subgroup.inclusion hCQ)
  let Θ : C →* ρ.range × scalars K V := ρ.rangeRestrict.prod κ
  have hΘ : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have h1 : ρ c = 1 := by
      have := congrArg (fun p => (p.1 : eig g 1 ≃ₗ[K] eig g 1)) hc
      simpa [Θ] using this
    have h2 : κ c = 1 := by
      have := congrArg Prod.snd hc
      simpa [Θ] using this
    have hfix : ∀ u ∈ eig g 1, (c : V ≃ₗ[K] V) u = u :=
      (CFSG.LargeExtraspecial.S4.restrictHom_eq_one_iff C.subtype (eig g 1) _ c).1 h1
    have hch : (c : V ≃ₗ[K] V) * h = h * (c : V ≃ₗ[K] V) := by
      have h3 : ⁅(c : V ≃ₗ[K] V), h⁆ = 1 := by
        have := congrArg Subtype.val h2
        simpa [κ, commHomLeft] using this
      exact commutatorElement_eq_one_iff_mul_comm.1 h3
    exact Subtype.ext (eq_one_of_fix_eig hg3 hω hω3 hω1 hch hfix)
  have hcard1 : Nat.card C ≤ Nat.card ρ.range * 3 := by
    have := Nat.card_le_card_of_injective Θ hΘ
    rw [Nat.card_prod] at this
    exact this.trans (Nat.mul_le_mul_left _ hZ.card_le)
  have hPG : IsPGroup 3 ρ.range := by
    apply isPGroup_three_of_pow_nine
    rintro _ ⟨c, rfl⟩
    rw [← map_pow]
    have : c ^ 9 = 1 := Subtype.ext (hQ.pow_nine hZ (hCQ c.2))
    rw [this, map_one]
  have hn2 : Module.finrank K (eig g 1) ≤ 2 := by
    have := three_mul_finrank_eig_le hω hω3 hω1
    omega
  have hcard2 := card_le_of_isPGroup_small hK hn2 ρ.range hPG
  calc Nat.card Q ≤ 3 * Nat.card C := hCcard
    _ ≤ 3 * (Nat.card ρ.range * 3) := Nat.mul_le_mul_left _ hcard1
    _ ≤ 3 * (3 ^ Module.finrank K (eig g 1) * 3) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcard2)
    _ ≤ 3 * (3 ^ 2 * 3) := Nat.mul_le_mul_left _
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hn2))
    _ = 3 ^ 4 := by norm_num

theorem abelian_exp_three_of_card_le_nine [Finite K] (hK : Nat.card K = 4) [FiniteDimensional K V]
    {N : ℕ} (hN : Module.finrank K V = N) (hN5 : 5 ≤ N) (hN9 : N ≤ 9)
    {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q)
    (hcard : 3 ^ (max 5 (N - 2)) ≤ Nat.card Q) :
    (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ ∀ x ∈ Q, x ^ 3 = 1 := by
  classical
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hZ := scalarLike_scalars (V := V) hK
  by_cases hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x
  · refine ⟨hab, ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨x, hx, hx3⟩ := hne
    have h1 := card_le_of_abelian_cube hK hQ hab hx hx3
    rw [hN] at h1
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hcard.trans h1)
    omega
  · exfalso
    obtain ⟨g, hg, h, hh, hg3, hgh⟩ := exists_pow_three_eq_one_noncomm hZ hQ hab
    by_cases hN8 : N ≤ 8
    · have h1 := card_le_of_nonab_small hK (by omega) hQ hg hh hg3 hgh
      have h3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hcard.trans h1)
      omega
    · obtain ⟨n, hn3, hcardn⟩ := card_le_of_nonab hK hQ hg hh hg3 hgh
      have h2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hcard.trans hcardn)
      rw [hN] at hn3
      omega

end CFSG.LocalAnalysis.GLTheoremA.S265.BBig

end
