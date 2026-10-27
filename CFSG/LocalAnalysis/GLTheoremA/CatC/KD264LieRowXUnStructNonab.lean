module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructEig
public import CFSG.LargeExtraspecial.S4Restrict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem card_le_of_nonab [Finite K] (hK : Nat.card K = 4) [FiniteDimensional K V]
    {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q)
    {g h : V ≃ₗ[K] V} (hg : g ∈ Q) (hh : h ∈ Q) (hg3 : g ^ 3 = 1) (hgh : g * h ≠ h * g) :
    ∃ n : ℕ, 3 * n ≤ Module.finrank K V ∧ Nat.card Q ≤ 3 ^ (2 + (n + n / 2)) := by
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
  have hcard2 := card_le_of_isPGroup hK (rfl : Module.finrank K (eig g 1) = _) ρ.range hPG
  refine ⟨Module.finrank K (eig g 1), three_mul_finrank_eig_le hω hω3 hω1, ?_⟩
  calc Nat.card Q ≤ 3 * Nat.card C := hCcard
    _ ≤ 3 * (Nat.card ρ.range * 3) := Nat.mul_le_mul_left _ hcard1
    _ ≤ 3 * (3 ^ (Module.finrank K (eig g 1) + Module.finrank K (eig g 1) / 2) * 3) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcard2)
    _ = 3 ^ (2 + (Module.finrank K (eig g 1) + Module.finrank K (eig g 1) / 2)) := by
        rw [pow_add]; ring

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

end
