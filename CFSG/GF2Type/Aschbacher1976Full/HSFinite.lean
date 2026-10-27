module

public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteCanon

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open Equiv CFSG.GF2Type.Aschbacher1976Full.HS.Six

theorem six_classify {Q : Type*} [Group Q] [Finite Q] (ι : Q →* Equiv.Perm (Fin 6))
    (hι : Function.Injective ι)
    (hO2 : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥)
    (a : Q) (ha : orderOf a = 2)
    (hP1 : ∀ x y : Q, orderOf ((x * a * x⁻¹) * (y * a * y⁻¹)) ≠ 4)
    (hK4 : ∃ x y : Q, (x * a * x⁻¹) * (y * a * y⁻¹) = (y * a * y⁻¹) * (x * a * x⁻¹) ∧
        x * a * x⁻¹ ≠ y * a * y⁻¹ ∧ ∃ w : Q, (x * a * x⁻¹) * (y * a * y⁻¹) = w * a * w⁻¹) :
    Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨ Nonempty (Q ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨x, y, hcomm, hne, w, hw⟩ := hK4
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, sq] at this
  have hsq : ∀ z : Q, ι (z * a * z⁻¹) * ι (z * a * z⁻¹) = 1 := by
    intro z
    have : z * a * z⁻¹ * (z * a * z⁻¹) = 1 := by
      calc z * a * z⁻¹ * (z * a * z⁻¹) = z * (a * a) * z⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    rw [← map_mul, this, map_one]
  have hsupp : ∀ z : Q, (ι (z * a * z⁻¹)).support.card = (ι a).support.card := by
    intro z
    have : ι (z * a * z⁻¹) = ι z * ι a * (ι z)⁻¹ := by simp [map_mul, map_inv]
    rw [this, Equiv.Perm.card_support_conj]
  have hc : ι (x * a * x⁻¹) * ι (y * a * y⁻¹) = ι (y * a * y⁻¹) * ι (x * a * x⁻¹) := by
    rw [← map_mul, ← map_mul, hcomm]
  have hde : ι (x * a * x⁻¹) * ι (y * a * y⁻¹) = ι (w * a * w⁻¹) := by rw [← map_mul, hw]
  obtain ⟨-, σ, hσ⟩ := wlog_pair (hsq x) (hsq y) (fun h => hne (hι h)) hc
    (by rw [hsupp, hsupp]) (by rw [hde, hsupp, hsupp])
  let ι' : Q →* Perm (Fin 6) := (MulAut.conj σ).toMonoidHom.comp ι
  have hι' : Function.Injective ι' := (MulAut.conj σ).injective.comp hι
  have hι'x : ∀ z : Q, ι' (z * a * z⁻¹) = σ * ι (z * a * z⁻¹) * σ⁻¹ := fun z => rfl
  have hxy : ι' (w * a * w⁻¹) = σ * (ι (x * a * x⁻¹) * ι (y * a * y⁻¹)) * σ⁻¹ := by
    rw [hι'x, hde]
  have hxy' : ι' (w * a * w⁻¹) =
      (σ * ι (x * a * x⁻¹) * σ⁻¹) * (σ * ι (y * a * y⁻¹) * σ⁻¹) := by
    rw [hxy]
    group
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine canonical cfgA cfgA_ok ι' hι' hO2 a ha hP1 fun v hv => ?_
    simp only [cfgA, VA, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨x, by rw [hι'x, h1]; rfl⟩
    · exact ⟨y, by rw [hι'x, h2]; rfl⟩
    · refine ⟨w, ?_⟩
      rw [hxy', h1, h2]
      decide +kernel
  · refine canonical cfgB cfgB_ok ι' hι' hO2 a ha hP1 fun v hv => ?_
    simp only [cfgB, VB, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨x, by rw [hι'x, h1]; rfl⟩
    · exact ⟨y, by rw [hι'x, h2]; rfl⟩
    · refine ⟨w, ?_⟩
      rw [hxy', h1, h2]
      decide +kernel

end CFSG.GF2Type.Aschbacher1976Full.HS
