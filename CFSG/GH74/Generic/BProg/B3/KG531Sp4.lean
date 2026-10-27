module

public import CFSG.GH74.Generic.BProg.B3.KG531Crit
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClSp4Inv
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

namespace KG531Sp4

open CFSG.ComponentClassification.CatFactsSp4

section Bridge

variable {S : Type} [Group S] [Finite S]

theorem isPCompIn_two_of_isCompIn_of_even {C K : Subgroup S} (hK : IsCompIn C K)
    (hev : 2 ∣ Nat.card ↥K) : IsPCompIn 2 C K := by
  refine ⟨hK.1, CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
    hK.2 fun hle => ?_⟩
  have h1 : Nat.card ↥(K.subgroupOf C) ∣ Nat.card ↥(pPrimeCore 2 ↥C) :=
    Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(K.subgroupOf C) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv
  rw [h2] at h1
  have h3 := Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have h4 := Nat.Coprime.eq_one_of_dvd h3 hev
  omega

end Bridge

section Config

variable {S : Type} [Group S] [Finite S] {t : S} {B₁ B₂ : Subgroup S} {p f : ℕ}

omit [Finite S] in
theorem two_dvd_card₁ (h : KG531Cfg t B₁ B₂ p f) : 2 ∣ Nat.card ↥B₁ := by
  have hz : Nat.card ↥(center ↥B₁) = 1 := by
    rw [h.center₁]
    exact Subgroup.card_bot
  have hc : Nat.card ↥B₁ = Nat.card (↥B₁ ⧸ center ↥B₁) * Nat.card ↥(center ↥B₁) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hz, mul_one, KG531Crit.card_psl_two h.prime h.odd h.model₁] at hc
  rw [hc]
  have hq := CFSG.GH74.Generic.S1.kl5_odd_pow (f := f) h.prime h.odd
  obtain ⟨m, hm⟩ := CFSG.GH74.Generic.S1.kl5_eight_dvd_sq_sub_one hq
  have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hpow, hm, show p ^ f * (8 * m) = 2 * (p ^ f * (4 * m)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
  exact ⟨2 * p ^ f * m, by ring⟩

omit [Finite S] in
theorem two_dvd_card₂ (h : KG531Cfg t B₁ B₂ p f) : 2 ∣ Nat.card ↥B₂ := by
  have := orderOf_dvd_natCard (⟨t, h.t_mem⟩ : ↥B₂)
  rwa [Subgroup.orderOf_mk, h.t_ord] at this

theorem isPCompIn₁ (h : KG531Cfg t B₁ B₂ p f) : IsPCompIn 2 (centralizer ({t} : Set S)) B₁ :=
  isPCompIn_two_of_isCompIn_of_even h.comp₁ (two_dvd_card₁ h)

theorem isPCompIn₂ (h : KG531Cfg t B₁ B₂ p f) : IsPCompIn 2 (centralizer ({t} : Set S)) B₂ :=
  isPCompIn_two_of_isCompIn_of_even h.comp₂ (two_dvd_card₂ h)

omit [Finite S] in
theorem transport {P : Type} [Group P] (ψ : S ≃* P) {B : Subgroup S}
    (hB : IsPCompIn 2 (centralizer ({t} : Set S)) B) :
    B.map ψ.toMonoidHom ≤ centralizer {ψ t} ∧
      CFSG.IsPComponent 2 ((B.map ψ.toMonoidHom).subgroupOf (centralizer {ψ t})) := by
  have hmap := isPComponent_map_subgroupOf 2 ψ hB.1 hB.2
  rw [map_centralizer_singleton] at hmap
  refine ⟨?_, hmap⟩
  have := Subgroup.map_mono (f := ψ.toMonoidHom) hB.1
  rwa [map_centralizer_singleton] at this

end Config

section Main

variable {S : Type} [Group S] [Finite S] {t : S} {B₁ B₂ : Subgroup S} {p f : ℕ}

theorem false_of_conj {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (ψ : S ≃* StatedProj (StatedSp 2 F)) (h : KG531Cfg t B₁ B₂ p f)
    (hψ : ψ t = u1 F ∨ ψ t = u2 F) : False := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hZ : Nat.card ↥(center ↥B₁) = 1 := by
    rw [h.center₁]
    exact Subgroup.card_bot
  obtain ⟨hle₁, hmap₁⟩ := transport ψ (isPCompIn₁ h)
  rcases hψ with hψ | hψ
  · rw [hψ] at hle₁ hmap₁
    obtain ⟨hE, -⟩ := pComponent_centralizer_u1 hodd hle₁ hmap₁
    have hcard : Nat.card ↥(center ↥B₁) = Nat.card ↥(center ↥(B₁.map ψ.toMonoidHom)) := by
      let e : ↥B₁ ≃* ↥(B₁.map ψ.toMonoidHom) :=
        B₁.equivMapOfInjective ψ.toMonoidHom ψ.injective
      have h1 := Subgroup.map_center_eq e
      rw [← h1]
      exact (Subgroup.card_map_of_injective e.injective).symm
    have hev : Even (Nat.card ↥(center ↥(B₁.map ψ.toMonoidHom))) := by
      rcases hE with hE | hE
      · rw [hE]
        exact CFSG.GH74.GLS.IVK.even_card_center_E1 h2
      · rw [hE]
        exact CFSG.GH74.GLS.IVK.even_card_center_E2 h2
    rw [← hcard, hZ] at hev
    exact Nat.not_even_one hev
  · rw [hψ] at hle₁ hmap₁
    obtain ⟨hL₁, -⟩ := pComponent_centralizer_u2 hodd hle₁ hmap₁
    obtain ⟨hle₂, hmap₂⟩ := transport ψ (isPCompIn₂ h)
    rw [hψ] at hle₂ hmap₂
    obtain ⟨hL₂, -⟩ := pComponent_centralizer_u2 hodd hle₂ hmap₂
    have hB : B₁ = B₂ :=
      Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective (hL₁.trans hL₂.symm)
    exact h.t_not_mem₁ (by rw [hB]; exact h.t_mem)

end Main

end KG531Sp4

theorem kg531_sp4 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (_hf : 1 ≤ f) :
    KG531Empty (fun X _ => LieModel X .PSp 2 p f) := by
  intro S _ _ hS hnab hL t B₁ B₂ p' f' h
  obtain ⟨-, -, F, _, _, hF, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hL
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have hu : orderOf (e₀ t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact h.t_ord
  obtain ⟨φ, hφ⟩ := CFSG.ComponentClassification.CatFactsSp4.exists_model_conj hodd hu
  exact KG531Sp4.false_of_conj hodd (e₀.trans φ) h hφ

end CFSG.GH74.Generic.BProg.B3
