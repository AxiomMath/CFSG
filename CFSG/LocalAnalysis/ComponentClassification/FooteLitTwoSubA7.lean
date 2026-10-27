module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5A7
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5Transport

public section

namespace CFSG.ComponentClassification.FooteLit.TwoSub

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.Foote5
open CFSG.ClassicalInvolution.Hat2A7 (A7)
open CFSG.ComponentClassification.FooteLit.Aut5A7

theorem twoSub_a7 {Y : Type} [Group Y] [Finite Y] (e : Y ≃* A7)
    (R : Sylow 2 Y) (P : Subgroup (MulAut Y)) (hP : IsPGroup 2 P)
    (hRP : (R : Subgroup Y).map (MulAut.conj : Y →* MulAut Y) ≤ P) :
    (Nat.card P ≤ 2 * Nat.card R ∧ (AschbacherTheorem3.IsDihedralTwoGroup P ∨
      AschbacherTheorem3.IsSemidihedralTwoGroup P)) ∨
    ∃ β ∈ P, β * β = 1 ∧ β ∉ innAut5 Y ∧ ∃ R' : Sylow 2 Y, ∀ r ∈ (R' : Subgroup Y), β r = r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ : MulAut Y ≃* Perm (Fin 7) := (MulAut.congr e).trans autPerm with hΦ
  have hΦconj : ∀ y : Y, Φ (MulAut.conj y) = ((e y : A7) : Perm (Fin 7)) := fun y => by
    rw [hΦ, MulEquiv.trans_apply, Aut5.congr_conj, autPerm_conj]
  set R₇ : Sylow 2 A7 := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective R with hR₇def
  have hR₇ : (R₇ : Subgroup A7) = (R : Subgroup Y).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  set RS : Subgroup (Perm (Fin 7)) := (R₇ : Subgroup A7).map (alternatingGroup (Fin 7)).subtype
    with hRSdef
  set PS : Subgroup (Perm (Fin 7)) := P.map Φ.toMonoidHom with hPSdef
  have hmemR₇ : ∀ r : Y, r ∈ (R : Subgroup Y) ↔ e r ∈ (R₇ : Subgroup A7) := fun r => by
    rw [hR₇, mem_map_equiv, MulEquiv.symm_apply_apply]
  have hRS : RS ≤ PS := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ (R : Subgroup Y), e r = x := by
      refine ⟨e.symm x, (hmemR₇ _).mpr ?_, e.apply_symm_apply x⟩
      rwa [MulEquiv.apply_symm_apply]
    exact ⟨MulAut.conj r, hRP ⟨r, hr, rfl⟩, hΦconj r⟩
  have hcardR₇ : Nat.card (R₇ : Subgroup A7) = 8 := card_sylow R₇
  have hcardRS : Nat.card RS = 8 := by
    rw [hRSdef, card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective, hcardR₇]
  have hcardR : Nat.card (R : Subgroup Y) = 8 := by
    rw [← hcardR₇, hR₇, card_map_of_injective (f := e.toMonoidHom) e.injective]
  have hcardP : Nat.card P = Nat.card PS :=
    (card_map_of_injective (f := Φ.toMonoidHom) Φ.injective).symm
  have hPS2 : IsPGroup 2 PS := hP.map _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPS2
  have h8 : 8 ∣ Nat.card PS := hcardRS ▸ card_dvd_of_le hRS
  have hdvd : Nat.card PS ∣ 5040 := by
    have := card_subgroup_dvd_card PS
    rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin,
      show Nat.factorial 7 = 5040 by decide] at this
  have hk4 : k ≤ 4 := by
    by_contra h
    have h32 : 2 ^ 5 ∣ 5040 := (Nat.pow_dvd_pow 2 (by omega)).trans (hk ▸ hdvd)
    norm_num at h32
  have hk3 : 3 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by positivity) (hk ▸ h8)
    omega
  rcases (show k = 3 ∨ k = 4 by omega) with rfl | rfl
  ·
    left
    have hPSeq : PS = RS := (eq_of_le_of_card_ge hRS (by rw [hk, hcardRS]; norm_num)).symm
    refine ⟨by rw [hcardP, hk, hcardR]; norm_num, Or.inl ⟨3, by norm_num, ?_⟩⟩
    obtain ⟨ρ⟩ := AutL2Facts.sylow_two_dihedral_a7 (MulEquiv.refl A7) R₇
    have e1 : P ≃* PS := Φ.subgroupMap P
    have e2 : PS ≃* RS := MulEquiv.subgroupCongr hPSeq
    have e3 : RS ≃* (R₇ : Subgroup A7) :=
      (Subgroup.equivMapOfInjective (R₇ : Subgroup A7) (alternatingGroup (Fin 7)).subtype
        (alternatingGroup (Fin 7)).subtype_injective).symm
    exact ⟨((e1.trans e2).trans e3).trans ρ⟩
  ·
    right
    have hinter : PS ⊓ alternatingGroup (Fin 7) = RS := by
      have h2 : IsPGroup 2 ((PS ⊓ alternatingGroup (Fin 7)).comap
          (alternatingGroup (Fin 7)).subtype) :=
        (hPS2.to_le inf_le_left).comap_of_injective _ (alternatingGroup (Fin 7)).subtype_injective
      have hle : (R₇ : Subgroup A7) ≤
          (PS ⊓ alternatingGroup (Fin 7)).comap (alternatingGroup (Fin 7)).subtype :=
        fun x hx => ⟨hRS ⟨x, hx, rfl⟩, x.2⟩
      have heq := R₇.3 h2 hle
      apply le_antisymm
      · intro x hx
        have hxA : x ∈ alternatingGroup (Fin 7) := hx.2
        refine ⟨⟨x, hxA⟩, ?_, rfl⟩
        rw [← heq]
        exact hx
      · exact le_inf hRS (map_subtype_le _)
    obtain ⟨g, hgP, hg⟩ : ∃ g ∈ PS, Perm.sign g = -1 := by
      by_contra h
      push Not at h
      have hle : PS ≤ alternatingGroup (Fin 7) := fun x hx => by
        rcases Int.units_eq_one_or (Perm.sign x) with h1 | h1
        · exact Perm.mem_alternatingGroup.mpr h1
        · exact absurd h1 (h x hx)
      have hc : Nat.card PS ≤ Nat.card RS := by
        rw [← hinter, inf_eq_left.mpr hle]
      rw [hk, hcardRS] at hc
      norm_num at hc
    obtain ⟨t, ht, htt, htR⟩ := exists_odd_central R₇
    have hnorm : ∀ x ∈ RS, g * x * g⁻¹ ∈ RS := fun x hx => by
      rw [← hinter]
      refine ⟨PS.mul_mem (PS.mul_mem hgP (hRS hx)) (PS.inv_mem hgP), ?_⟩
      have hx' : x ∈ alternatingGroup (Fin 7) := (hinter ▸ inf_le_right : RS ≤ _) hx
      exact (alternatingGroup.normal (α := Fin 7)).conj_mem x hx' g
    have hβg : ∀ r ∈ (R₇ : Subgroup A7), autPerm.symm g r ∈ (R₇ : Subgroup A7) := fun r hr => by
      obtain ⟨y, hy, hyx⟩ := hnorm _ ⟨r, hr, rfl⟩
      have : autPerm.symm g r = y := Subtype.ext (by rw [autPerm_symm_apply]; exact hyx.symm)
      rw [this]
      exact hy
    obtain ⟨r₀, hr₀, h | h⟩ := autPerm_eq_of_normalizes R₇ ht htt htR hβg
    · rw [MulEquiv.apply_symm_apply] at h
      have := Perm.mem_alternatingGroup.mp r₀.2
      rw [← h, hg] at this
      exact absurd this (by decide)
    rw [MulEquiv.apply_symm_apply] at h
    have htP : t ∈ PS := by
      have h1 : (r₀ : Perm (Fin 7)) ∈ PS := hRS ⟨r₀, hr₀, rfl⟩
      rw [show t = (r₀ : Perm (Fin 7))⁻¹ * g by rw [h]; group]
      exact PS.mul_mem (PS.inv_mem h1) hgP
    obtain ⟨β, hβP, hβt⟩ := htP
    refine ⟨β, hβP, ?_, ?_, R, fun r hr => ?_⟩
    · apply Φ.injective
      rw [map_mul, map_one]
      exact hβt ▸ htt
    · intro hβI
      have h1 : MulAut.congr e β ∈ innAut5 A7 := (Aut5.congr_mem_innAut5_iff e β).mpr hβI
      rw [mem_innAut5_iff] at h1
      have h2 : autPerm (MulAut.congr e β) = t := hβt
      rw [h2, ht] at h1
      exact absurd h1 (by decide)
    · have hr₇ : e r ∈ (R₇ : Subgroup A7) := (hmemR₇ r).mp hr
      apply e.injective
      have h1 : (MulAut.congr e β) (e r) = e r := by
        apply Subtype.ext
        rw [coe_apply]
        have h2 : autPerm (MulAut.congr e β) = t := hβt
        rw [h2, ← htR _ hr₇, mul_inv_cancel_right]
      rw [Aut5.congr_apply_apply, MulEquiv.symm_apply_apply] at h1
      exact h1

end CFSG.ComponentClassification.FooteLit.TwoSub
