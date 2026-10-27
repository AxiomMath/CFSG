module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

open scoped Pointwise
open Equiv

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

namespace SylowAltSix

theorem set_mul_eq_of_card {Γ : Type*} [Group Γ] [Finite Γ] (X Y H : Subgroup Γ)
    (hX : X ≤ H) (hY : Y ≤ H) (hXY : X ⊓ Y = ⊥)
    (hcard : Nat.card X * Nat.card Y = Nat.card H) :
    (X : Set Γ) * (Y : Set Γ) = (H : Set Γ) := by
  have hsub : (X : Set Γ) * (Y : Set Γ) ⊆ (H : Set Γ) := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact H.mul_mem (hX hx) (hY hy)
  let f : X × Y → Γ := fun p => (p.1 : Γ) * (p.2 : Γ)
  have hinj : Function.Injective f := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h' : (x : Γ) * (y : Γ) = (x' : Γ) * (y' : Γ) := h
    have hz : ((x' : Γ)⁻¹ * (x : Γ)) ∈ X ⊓ Y := by
      refine ⟨X.mul_mem (X.inv_mem x'.2) x.2, ?_⟩
      have : (x' : Γ)⁻¹ * (x : Γ) = (y' : Γ) * (y : Γ)⁻¹ := by
        calc (x' : Γ)⁻¹ * (x : Γ)
            = (x' : Γ)⁻¹ * ((x : Γ) * (y : Γ)) * (y : Γ)⁻¹ := by group
          _ = (x' : Γ)⁻¹ * ((x' : Γ) * (y' : Γ)) * (y : Γ)⁻¹ := by rw [h']
          _ = (y' : Γ) * (y : Γ)⁻¹ := by group
      rw [this]
      exact Y.mul_mem y'.2 (Y.inv_mem y.2)
    rw [hXY, Subgroup.mem_bot, inv_mul_eq_one] at hz
    have hx : x = x' := Subtype.ext hz.symm
    subst hx
    have hy' : (y : Γ) = (y' : Γ) := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext hy')
  have himg : f '' Set.univ = (X : Set Γ) * (Y : Set Γ) := by
    ext z
    constructor
    · rintro ⟨p, -, rfl⟩
      exact ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Set.mem_univ _, rfl⟩
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [← himg, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_prod, hcard]
  exact (Nat.card_coe_set_eq (H : Set Γ)).symm.le

abbrev Low : Type := {x : Fin 6 // x.val < 4}

@[expose] def swap45 : Perm (Fin 6) := swap 4 5

@[expose] def signSwap : ℤˣ →* Perm (Fin 6) where
  toFun u := if u = 1 then 1 else swap45
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [swap45]

theorem signSwap_apply (u : ℤˣ) : signSwap u = if u = 1 then 1 else swap45 := rfl

theorem sign_signSwap (u : ℤˣ) : Perm.sign (signSwap u) = u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [signSwap_apply]
  · simp [signSwap_apply, swap45, Equiv.Perm.sign_swap (by decide : (4 : Fin 6) ≠ 5)]

theorem swap45_fix_of_low (x : Fin 6) (hx : x.val < 4) : swap45 x = x := by
  have h4 : x ≠ 4 := by
    intro h
    subst h
    exact absurd hx (by decide)
  have h5 : x ≠ 5 := by
    intro h
    subst h
    exact absurd hx (by decide)
  exact swap_apply_of_ne_of_ne h4 h5

theorem signSwap_fix_of_low (u : ℤˣ) (x : Fin 6) (hx : x.val < 4) : signSwap u x = x := by
  rw [signSwap_apply]
  split_ifs
  · rfl
  · exact swap45_fix_of_low x hx

theorem fin6_not_low (z : Fin 6) (hz : ¬ z.val < 4) : z = 4 ∨ z = 5 := by
  revert hz
  revert z
  decide

theorem commute_ofSubtype_swap45 (σ : Perm Low) :
    Commute (Perm.ofSubtype σ) swap45 := by
  show Perm.ofSubtype σ * swap45 = swap45 * Perm.ofSubtype σ
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x.val < 4
  · rw [swap45_fix_of_low x hx, Perm.ofSubtype_apply_of_mem σ hx,
      swap45_fix_of_low _ (σ ⟨x, hx⟩).2]
  · have hs : ¬ (swap45 x).val < 4 := by
      rcases fin6_not_low x hx with rfl | rfl <;> decide
    rw [Perm.ofSubtype_apply_of_not_mem σ hs, Perm.ofSubtype_apply_of_not_mem σ hx]

theorem commute_ofSubtype_signSwap (u : ℤˣ) (σ : Perm Low) :
    Commute (Perm.ofSubtype σ) (signSwap u) := by
  rw [signSwap_apply]
  split_ifs
  · exact Commute.one_right _
  · exact commute_ofSubtype_swap45 σ

@[expose] def twist : Perm Low →* Perm (Fin 6) :=
  MonoidHom.mk' (fun σ => Perm.ofSubtype σ * signSwap (Perm.sign σ)) (by
    intro σ τ
    have hc : Commute (signSwap (Perm.sign σ)) (Perm.ofSubtype τ) :=
      (commute_ofSubtype_signSwap (Perm.sign σ) τ).symm
    simp only [map_mul, mul_assoc]
    rw [← mul_assoc (Perm.ofSubtype τ), ← hc.eq, mul_assoc])

theorem twist_apply (σ : Perm Low) :
    twist σ = Perm.ofSubtype σ * signSwap (Perm.sign σ) := rfl

theorem twist_injective : Function.Injective twist := by
  intro σ τ h
  have h' : Perm.ofSubtype σ * signSwap (Perm.sign σ)
      = Perm.ofSubtype τ * signSwap (Perm.sign τ) := h
  ext y
  have hy := congrArg (fun π : Perm (Fin 6) => π y.1) h'
  simp only [Perm.mul_apply] at hy
  rw [signSwap_fix_of_low _ _ y.2, signSwap_fix_of_low _ _ y.2,
    Perm.ofSubtype_apply_of_mem σ y.2, Perm.ofSubtype_apply_of_mem τ y.2] at hy
  exact congrArg Fin.val hy

theorem twist_mem (σ : Perm Low) : twist σ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup, twist_apply, map_mul, Perm.sign_ofSubtype, sign_signSwap]
  exact Int.units_mul_self _

@[expose] def twistA : Perm Low →* alternatingGroup (Fin 6) :=
  twist.codRestrict (alternatingGroup (Fin 6)) twist_mem

theorem twistA_injective : Function.Injective twistA :=
  fun _ _ h => twist_injective (congrArg Subtype.val h)

@[expose] def H0 : Subgroup (alternatingGroup (Fin 6)) := twistA.range

theorem card_low : Nat.card Low = 4 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem card_H0 : Nat.card H0 = 24 := by
  have h1 : Nat.card H0 = Nat.card (Perm Low) :=
    (Nat.card_congr (MonoidHom.ofInjective twistA_injective).toEquiv).symm
  rw [h1, Nat.card_perm, card_low]
  rfl

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem exists_sylow_in_H0 :
    ∃ Q : Subgroup (alternatingGroup (Fin 6)), Q ≤ H0 ∧ Nat.card Q = 8 := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H0) 2 (n := 3)
    (by rw [card_H0]; norm_num)
  refine ⟨K.map H0.subtype, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK]
    norm_num

theorem exists_conj_sylow_le (S : Subgroup (alternatingGroup (Fin 6))) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.index) :
    ∃ H : Subgroup (alternatingGroup (Fin 6)), S ≤ H ∧ Nat.card H = 24 ∧ Nat.card S = 8 := by
  obtain ⟨Q, hQH0, hQcard⟩ := exists_sylow_in_H0
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num)
  have hQidx : ¬ 2 ∣ Q.index := by
    have h := Subgroup.card_mul_index Q
    rw [hQcard, card_alt6] at h
    have h45 : Q.index = 45 := by omega
    rw [h45]
    norm_num
  let Qs : Sylow 2 (alternatingGroup (Fin 6)) := hQp.toSylow hQidx
  let Ss : Sylow 2 (alternatingGroup (Fin 6)) := hS2.toSylow hSidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) Qs Ss
  have hSeq : S = Q.map (MulAut.conj g).toMonoidHom := by
    have hgQ : ((g • Qs : Sylow 2 (alternatingGroup (Fin 6))) : Subgroup (alternatingGroup (Fin 6)))
        = S := by
      rw [hg]
      rfl
    rw [Sylow.coe_subgroup_smul] at hgQ
    rw [← hgQ]
    ext x
    simp [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map, Qs]
  refine ⟨H0.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rw [hSeq]
    exact Subgroup.map_mono hQH0
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_H0]
  · rw [hSeq, Subgroup.card_map_of_injective (MulAut.conj g).injective, hQcard]

theorem exists_order_three_permuting_sylow_two_alternating_six
    (S : Subgroup (alternatingGroup (Fin 6))) (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.index) :
    ∃ P : Subgroup (alternatingGroup (Fin 6)), Nat.card P = 3 ∧
      (S : Set (alternatingGroup (Fin 6))) * P = (P : Set (alternatingGroup (Fin 6))) * S := by
  obtain ⟨H, hSH, hH, hScard⟩ := exists_conj_sylow_le S hS2 hSidx
  obtain ⟨P, hPH, hPcard⟩ : ∃ P : Subgroup (alternatingGroup (Fin 6)),
      P ≤ H ∧ Nat.card P = 3 := by
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 1)
      (by rw [hH]; norm_num)
    refine ⟨K.map H.subtype, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK]
      norm_num
  have hSP : S ⊓ P = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card (S ⊓ P : Subgroup (alternatingGroup (Fin 6))) ∣ Nat.card S :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (S ⊓ P : Subgroup (alternatingGroup (Fin 6))) ∣ Nat.card P :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hScard] at h1
    rw [hPcard] at h2
    have h3 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 8 3 = 1 by norm_num] at h3
    exact Nat.dvd_one.mp h3
  have e1 : (S : Set (alternatingGroup (Fin 6))) * (P : Set (alternatingGroup (Fin 6)))
      = (H : Set (alternatingGroup (Fin 6))) :=
    set_mul_eq_of_card S P H hSH hPH hSP (by rw [hScard, hPcard, hH])
  have e2 : (P : Set (alternatingGroup (Fin 6))) * (S : Set (alternatingGroup (Fin 6)))
      = (H : Set (alternatingGroup (Fin 6))) :=
    set_mul_eq_of_card P S H hPH hSH (by rw [inf_comm]; exact hSP)
      (by rw [hScard, hPcard, hH])
  exact ⟨P, hPcard, by rw [e1, e2]⟩

end SylowAltSix

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
