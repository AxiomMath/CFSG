module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowAltSix

public section

open scoped Pointwise
open Equiv

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowAltSix

namespace SylowSymSix

@[expose] def phi : Perm Low × ℤˣ →* Perm (Fin 6) :=
  MonoidHom.mk' (fun p => Perm.ofSubtype p.1 * signSwap p.2) (by
    intro p q
    have hc : Commute (signSwap p.2) (Perm.ofSubtype q.1) :=
      (commute_ofSubtype_signSwap p.2 q.1).symm
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_assoc]
    rw [← mul_assoc (Perm.ofSubtype q.1), ← hc.eq, mul_assoc])

theorem phi_apply (p : Perm Low × ℤˣ) : phi p = Perm.ofSubtype p.1 * signSwap p.2 := rfl

theorem phi_injective : Function.Injective phi := by
  rintro ⟨σ, u⟩ ⟨τ, v⟩ h
  have h' : Perm.ofSubtype σ * signSwap u = Perm.ofSubtype τ * signSwap v := h
  have hσ : σ = τ := by
    ext y
    have hy := congrArg (fun π : Perm (Fin 6) => π y.1) h'
    simp only [Perm.mul_apply] at hy
    rw [signSwap_fix_of_low _ _ y.2, signSwap_fix_of_low _ _ y.2,
      Perm.ofSubtype_apply_of_mem σ y.2, Perm.ofSubtype_apply_of_mem τ y.2] at hy
    exact congrArg Fin.val hy
  subst hσ
  have h4 : signSwap u = signSwap v := mul_left_cancel h'
  have := congrArg Perm.sign h4
  rw [sign_signSwap, sign_signSwap] at this
  exact Prod.ext rfl this

@[expose] def H0 : Subgroup (Perm (Fin 6)) := phi.range

theorem card_H0 : Nat.card H0 = 48 := by
  have h1 : Nat.card H0 = Nat.card (Perm Low × ℤˣ) :=
    (Nat.card_congr (MonoidHom.ofInjective phi_injective).toEquiv).symm
  rw [h1, Nat.card_prod, Nat.card_perm, card_low]
  have : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [this]
  rfl

theorem card_perm6 : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm]
  simp [Nat.card_eq_fintype_card]
  rfl

theorem exists_sylow_in_H0 :
    ∃ Q : Subgroup (Perm (Fin 6)), Q ≤ H0 ∧ Nat.card Q = 16 := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H0) 2 (n := 4)
    (by rw [card_H0]; norm_num)
  refine ⟨K.map H0.subtype, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK]
    norm_num

theorem exists_conj_sylow_le (S : Subgroup (Perm (Fin 6))) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.index) :
    ∃ H : Subgroup (Perm (Fin 6)), S ≤ H ∧ Nat.card H = 48 ∧ Nat.card S = 16 := by
  obtain ⟨Q, hQH0, hQcard⟩ := exists_sylow_in_H0
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 4) (by rw [hQcard]; norm_num)
  have hQidx : ¬ 2 ∣ Q.index := by
    have h := Subgroup.card_mul_index Q
    rw [hQcard, card_perm6] at h
    have h45 : Q.index = 45 := by omega
    rw [h45]
    norm_num
  let Qs : Sylow 2 (Perm (Fin 6)) := hQp.toSylow hQidx
  let Ss : Sylow 2 (Perm (Fin 6)) := hS2.toSylow hSidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) Qs Ss
  have hSeq : S = Q.map (MulAut.conj g).toMonoidHom := by
    have hgQ : ((g • Qs : Sylow 2 (Perm (Fin 6))) : Subgroup (Perm (Fin 6))) = S := by
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

end SylowSymSix

open SylowSymSix in
theorem exists_order_three_permuting_sylow_two_perm_six
    (S : Subgroup (Equiv.Perm (Fin 6))) (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.index) :
    ∃ P : Subgroup (Equiv.Perm (Fin 6)), P ≤ alternatingGroup (Fin 6) ∧ Nat.card P = 3 ∧
      (S : Set (Equiv.Perm (Fin 6))) * P = (P : Set (Equiv.Perm (Fin 6))) * S := by
  obtain ⟨H, hSH, hH, hScard⟩ := exists_conj_sylow_le S hS2 hSidx
  obtain ⟨P, hPH, hPcard⟩ : ∃ P : Subgroup (Perm (Fin 6)), P ≤ H ∧ Nat.card P = 3 := by
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 1)
      (by rw [hH]; norm_num)
    refine ⟨K.map H.subtype, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK]
      norm_num
  have hSP : S ⊓ P = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card (S ⊓ P : Subgroup (Perm (Fin 6))) ∣ Nat.card S :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (S ⊓ P : Subgroup (Perm (Fin 6))) ∣ Nat.card P :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hScard] at h1
    rw [hPcard] at h2
    have h3 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 16 3 = 1 by norm_num] at h3
    exact Nat.dvd_one.mp h3
  have e1 : (S : Set (Perm (Fin 6))) * (P : Set (Perm (Fin 6))) = (H : Set (Perm (Fin 6))) :=
    set_mul_eq_of_card S P H hSH hPH hSP (by rw [hScard, hPcard, hH])
  have e2 : (P : Set (Perm (Fin 6))) * (S : Set (Perm (Fin 6))) = (H : Set (Perm (Fin 6))) :=
    set_mul_eq_of_card P S H hPH hSH (by rw [inf_comm]; exact hSP)
      (by rw [hScard, hPcard, hH])
  refine ⟨P, ?_, hPcard, by rw [e1, e2]⟩
  intro x hx
  rw [Perm.mem_alternatingGroup]
  have hx3 : x ^ 3 = 1 := by
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : P)
    rw [hPcard] at h
    have h' := orderOf_dvd_iff_pow_eq_one.mp h
    exact congrArg Subtype.val h'
  rcases Int.units_eq_one_or (Perm.sign x) with h | h
  · exact h
  · have := congrArg Perm.sign hx3
    rw [map_pow, h, map_one] at this
    exact absurd this (by decide)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
