module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenDefs

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergCB

theorem stabO_swap45 : StabO (swap (4 : Fin 6) 5) := by decide

theorem swap45_apply_of_lt {i : Fin 6} (hi : (i : ℕ) < 4) : swap (4 : Fin 6) 5 i = i := by
  refine swap_apply_of_ne_of_ne (fun h => ?_) (fun h => ?_)
  · rw [h] at hi
    exact absurd hi (by decide)
  · rw [h] at hi
    exact absurd hi (by decide)

theorem restrictO_commute_swap45 {π : Perm (Fin 6)} (hπ : StabO π) :
    restrictO π * swap 4 5 = swap 4 5 * restrictO π := by
  rcases apply45_of_stabO hπ with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · rw [restrictO_eq_one_of hπ h4 h5, one_mul, mul_one]
  · rw [restrictO_eq_swap45_of hπ h4 h5]

theorem restrictO_conj_swap45 {π : Perm (Fin 6)} (hπ : StabO π) :
    restrictO (swap 4 5 * π * (swap 4 5)⁻¹) = restrictO π := by
  have hs := stabO_mul (stabO_mul stabO_swap45 hπ) (stabO_inv stabO_swap45)
  have e4 : (swap 4 5 * π * (swap 4 5)⁻¹ : Perm (Fin 6)) 4 = swap 4 5 (π 5) := by
    rw [swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left]
  have e5 : (swap 4 5 * π * (swap 4 5)⁻¹ : Perm (Fin 6)) 5 = swap 4 5 (π 4) := by
    rw [swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_right]
  rcases apply45_of_stabO hπ with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · rw [restrictO_eq_one_of hπ h4 h5]
    refine restrictO_eq_one_of hs ?_ ?_
    · rw [e4, h5, swap_apply_right]
    · rw [e5, h4, swap_apply_left]
  · rw [restrictO_eq_swap45_of hπ h4 h5]
    refine restrictO_eq_swap45_of hs ?_ ?_
    · rw [e4, h5, swap_apply_left]
    · rw [e5, h4, swap_apply_right]

theorem altCoords_relabel45 {G : Type} [Group G] {A B : Subgroup G}
    {ψA : A ≃* alternatingGroup (Fin 6)} {ψB : B ≃* alternatingGroup (Fin 6)}
    (h : AltCoords 6 A B ψA ψB) : AltCoords 6 A B ψA (ψB.trans (conjPerm 6 (swap 4 5))) := by
  unfold AltCoords at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  set s : Perm (Fin 6) := swap 4 5 with hsdef
  set ψB' := ψB.trans (conjPerm 6 s) with hψB'def
  have hψB' : ∀ b, (ψB' b : Perm (Fin 6)) = s * ψB b * s⁻¹ := fun b => by
    rw [hψB'def, MulEquiv.trans_apply, conjPerm_apply]
  have hc1 : ∀ z ∈ rootAlt 6, conjPerm 6 s z = z := fun z hz => by
    obtain ⟨h4', h5'⟩ := apply_four_five_of_mem_rootAlt hz
    apply Subtype.ext
    rw [conjPerm_apply, hsdef, ← commute_swap45_of_fix h4' h5', mul_inv_cancel_right]
  have hc2 : ∀ z ∈ rootAlt 6, (conjPerm 6 s).symm z = z := fun z hz => by
    rw [MulEquiv.symm_apply_eq]
    exact (hc1 z hz).symm
  have hmap : ∀ P : Subgroup (alternatingGroup (Fin 6)), P ≤ rootAlt 6 →
      P.map ψB'.symm.toMonoidHom = P.map ψB.symm.toMonoidHom := by
    intro P hP
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by rw [hψB'def, MulEquiv.symm_trans_apply, hc2 z (hP hz)]⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by rw [hψB'def, MulEquiv.symm_trans_apply, hc2 z (hP hz)]⟩
  have hstab : ∀ y : B, (∀ i : Fin 6, (i : ℕ) < 4 → ((ψB' y : Perm (Fin 6)) i : ℕ) < 4) →
      ∀ i : Fin 6, (i : ℕ) < 4 → ((ψB y : Perm (Fin 6)) i : ℕ) < 4 := by
    intro y hy i hi
    have e : (ψB y : Perm (Fin 6)) = s⁻¹ * ψB' y * s := by rw [hψB']; group
    rw [e, Perm.mul_apply, Perm.mul_apply, hsdef, swap45_apply_of_lt hi, swap_inv,
      swap45_apply_of_lt (hy i hi)]
    exact hy i hi
  refine ⟨h1, ?_, h3, ?_, ?_, ?_, ?_, ?_, h9⟩
  · rw [hmap _ (rootV_le_rootAlt 6)]
    exact h2
  · rw [hmap _ le_rfl]
    exact h4
  ·
    intro x hx b
    obtain ⟨hb, e⟩ := h5 x hx b
    refine ⟨hb, ?_⟩
    have hcomm := restrictO_commute_swap45 (stabO_of_lt (by decide) hx)
    rw [hψB', hψB', e]
    set ρ := restrictO (ψA x : Perm (Fin 6))
    calc s * (ρ * ψB b * ρ⁻¹) * s⁻¹ = (s * ρ) * ψB b * (s * ρ)⁻¹ := by group
      _ = (ρ * s) * ψB b * (ρ * s)⁻¹ := by rw [hcomm]
      _ = ρ * (s * ψB b * s⁻¹) * ρ⁻¹ := by group
  ·
    intro y hy
    exact h6 y (hstab y hy)
  ·
    obtain ⟨β', hβ'F, hβ'⟩ := h7
    refine ⟨β', hβ'F, fun y hy a => ?_⟩
    obtain ⟨ha, e⟩ := hβ' y (hstab y hy) a
    refine ⟨ha, ?_⟩
    rw [e, hψB', hsdef, restrictO_conj_swap45 (stabO_of_lt (by decide) (hstab y hy))]
  ·
    intro k hk
    obtain ⟨hkB, π, hπ, hπb⟩ := h8 k hk
    refine ⟨hkB, π, hπ, fun b => ?_⟩
    obtain ⟨hb, e⟩ := hπb b
    refine ⟨hb, ?_⟩
    have hcomm : π * s = s * π := commute_swap45_of_fix (hπ 4 (by decide)) (hπ 5 (by decide))
    rw [hψB', hψB', e]
    calc s * (π * ψB b * π⁻¹) * s⁻¹ = (s * π) * ψB b * (s * π)⁻¹ := by group
      _ = (π * s) * ψB b * (π * s)⁻¹ := by rw [hcomm]
      _ = π * (s * ψB b * s⁻¹) * π⁻¹ := by group

end CFSG.ComponentClassification.RankTwoAlt
