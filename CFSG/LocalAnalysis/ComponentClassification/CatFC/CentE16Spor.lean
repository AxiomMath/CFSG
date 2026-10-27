module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint

open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem e16_spor_two_pow (s : TauCeti.SporadicName) (h1 : s ≠ .M11) (h2 : s ≠ .J1) :
    2 ^ 5 ∣ sporOrder s := by
  cases s <;> first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | (simp only [sporOrder, GSThmB.QPUSpor.sporFactors]; decide)

theorem e16_mem_range_conj_of_congr {K H : Type} [Group K] [Group H] (θ : K ≃* H)
    {τ : MulAut K} (h : ∃ g : H, MulAut.congr θ τ = MulAut.conj g) :
    τ ∈ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨g, hg⟩ := h
  refine ⟨θ.symm g, ?_⟩
  ext x
  have h1 := congrArg (fun φ : MulAut H => φ (θ x)) hg
  simp only [MulAut.congr_apply, MulAut.conj_apply] at h1
  change θ.symm g * x * (θ.symm g)⁻¹ = τ x
  apply θ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← h1]
  simp

theorem e16_false_sporadic
    (hcard : ∀ s : TauCeti.SporadicName, Nat.card (NativeSporadic.Carrier s) = sporOrder s)
    (hm11 : Nat.card {x : NativeSporadic.Carrier .M11 // orderOf x = 2} = 165)
    (hj1 : ∀ φ : MulAut (NativeSporadic.Carrier .J1), ∃ g : NativeSporadic.Carrier .J1,
      φ = MulAut.conj g)
    {K : Type} [Group K] [Finite K] (D : CatE16Data K) (hsp : NativeSporadic.SporadicRep K) :
    False := by
  obtain ⟨s, ⟨θ⟩⟩ := hsp
  have hK : Nat.card K = sporOrder s := (Nat.card_congr θ.toEquiv).trans (hcard s)
  by_cases h1 : s = .M11
  · subst h1
    have h7920 : Nat.card K = 7920 := by
      rw [hK]
      simp only [sporOrder, GSThmB.QPUSpor.sporFactors]
      decide
    have hnum : Nat.card {x : K // orderOf x = 2} = 165 := by
      rw [← hm11]
      exact Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv (fun x => by
        simp [MulEquiv.orderOf_eq]))
    have hle : (conjugatesOf D.κ).ncard ≤ 165 := by
      rw [← hnum, ← Nat.card_coe_set_eq]
      refine Nat.card_le_card_of_injective
        (fun x : conjugatesOf D.κ => (⟨x.1, ?_⟩ : {x : K // orderOf x = 2})) ?_
      · obtain ⟨c, hc⟩ := isConj_iff.1 x.2
        rw [← hc, ← D.hκ2]
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective D.κ
        simpa [MulAut.conj_apply] using this
      · intro x y hxy
        have := congrArg (fun z : {x : K // orderOf x = 2} => z.1) hxy
        exact Subtype.ext this
    have hidx := Subgroup.index_centralizer_eq_ncard D.κ
    have hmul := Subgroup.index_mul_card (Subgroup.centralizer ({D.κ} : Set K))
    have hQ := D.hQ
    rw [hidx, h7920] at hmul
    have : (conjugatesOf D.κ).ncard * Nat.card (Subgroup.centralizer ({D.κ} : Set K)) ≤ 165 * 16 :=
      Nat.mul_le_mul hle hQ
    omega
  by_cases h2 : s = .J1
  · subst h2
    exact D.hout (e16_mem_range_conj_of_congr θ (hj1 _))
  exact D.not_two_pow_five_dvd (hK ▸ e16_spor_two_pow s h1 h2)

end CFSG.ComponentClassification.CatFC
