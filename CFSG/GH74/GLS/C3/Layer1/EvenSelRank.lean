module

public import CFSG.GH74.GLS.C3.Layer1.Th2L625Rank
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.GH74.GLS.EvenSelP

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

section Aut

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem odd_card_fieldAutSub_of_fm9 (hF : L2Field F) (hfm : IsFM9 (Nat.card F))
    (h9 : Nat.card F ≠ 9) (e : K ≃* L2 F) : Odd (Nat.card ↥(fieldAutSub e)) := by
  obtain ⟨p, n, hp, -, -, hq⟩ := isOddPrimePower_of_L2Field hF
  rw [(ivk_1_2e F hF K e).2.2 p n hp hq]
  rcases hfm with h | ⟨hprime, -⟩
  · exact absurd h h9
  · rw [hq] at hprime
    rw [((Nat.Prime.pow_eq_iff hprime).1 rfl).2]
    exact odd_one

end Aut

section Rank

variable {G : Type} [Group G] [Finite G]

theorem exists_big_image {x : G} {K : Subgroup G}
    (hG4 : pRank 2 ↥(centralizer ({x} : Set G)) = 4)
    (hnorm : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hr1 : pRank 2 ↥(CxK x K) ≤ 1) :
    ∃ A : Subgroup (MulAut (kBar K)), IsElementaryAbelian 2 ↥A ∧ 8 ≤ Nat.card ↥A ∧
      ∀ a ∈ A, ∃ (f : G) (hf : f ∈ centralizer ({x} : Set G)), f * f = 1 ∧
        Back.actHom hnorm ⟨f, hf⟩ = a := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  let ψ : ↥C →* MulAut (kBar K) := Back.actHom hnorm
  have hker : ψ.ker = (CxK x K).subgroupOf C := Back.actHom_ker hnorm
  obtain ⟨E, hEC, hEel, hErk⟩ := Th2.exists_elemAbelian_pRank C
  have hEcard : Nat.card ↥E = 16 := by
    rw [Back.card_eq_two_pow_pRank hEel, hErk, hG4]
    norm_num
  obtain ⟨hEcomm, hEsq⟩ := Back.forall_of_isElementaryAbelian hEel
  set E' : Subgroup ↥C := E.subgroupOf C with hE'
  have hE'card : Nat.card ↥E' = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv).trans hEcard
  let ψE : ↥E' →* MulAut (kBar K) := ψ.comp E'.subtype
  have hEmem : ∀ k : ↥E', ((k : ↥C) : G) ∈ E := fun k => (Subgroup.mem_subgroupOf).mp k.2
  have hkk : ∀ k : ↥E', k * k = 1 := fun k =>
    Subtype.ext (Subtype.ext (hEsq _ (hEmem k)))
  have hRsq : ∀ a ∈ ψE.range, a * a = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← map_mul, hkk k, map_one]
  have hRcomm : ∀ a ∈ ψE.range, ∀ b ∈ ψE.range, a * b = b * a := by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subtype.ext (hEcomm _ (hEmem k) _ (hEmem l)))
  have hRel : IsElementaryAbelian 2 ↥ψE.range := Back.isElementaryAbelian_of_forall hRcomm hRsq
  have hprod := Subgroup.card_ker_mul_card_range ψE
  let ι : ↥E' →* G := C.subtype.comp E'.subtype
  have hι : Function.Injective ι := fun a b h => Subtype.ext (Subtype.ext h)
  have hle : ψE.ker.map ι ≤ CxK x K := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 : ψ ((k : ↥E') : ↥C) = 1 := hk
    have h2 : ((k : ↥E') : ↥C) ∈ ψ.ker := h1
    rw [hker] at h2
    exact (Subgroup.mem_subgroupOf).mp h2
  have hel : IsElementaryAbelian 2 ↥(ψE.ker.map ι) := by
    refine Back.isElementaryAbelian_of_forall ?_ ?_
    · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
      exact hEcomm _ (hEmem a) _ (hEmem b)
    · rintro _ ⟨a, -, rfl⟩
      exact hEsq _ (hEmem a)
  have hcard : Nat.card ↥(ψE.ker.map ι) = Nat.card ψE.ker :=
    Subgroup.card_map_of_injective hι
  have hpow := Back.card_eq_two_pow_pRank hel
  have hmono := Back.pRank_mono' hle
  have hker2 : Nat.card ψE.ker ≤ 2 := by
    have h1 : pRank 2 ↥(ψE.ker.map ι) ≤ 1 := hmono.trans hr1
    have h2 : 2 ^ pRank 2 ↥(ψE.ker.map ι) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  refine ⟨ψE.range, hRel, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    rw [hE'card] at hprod
    have hpos : 0 < Nat.card ψE.ker := Nat.card_pos
    have : Nat.card ψE.ker * Nat.card ψE.range ≤ 2 * 7 :=
      Nat.mul_le_mul hker2 (by omega)
    omega
  · rintro _ ⟨k, rfl⟩
    exact ⟨((k : ↥E') : ↥C), ((k : ↥E') : ↥C).2, hEsq _ (hEmem k), rfl⟩

theorem two_le_pRank_CxK_of_prime {x : G} {K : Subgroup G}
    (hG4 : pRank 2 ↥(centralizer ({x} : Set G)) = 4)
    (hnorm : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hL : HasL2Model (kBar K) (fun r => IsFM9 r ∧ r ≠ 9)) :
    2 ≤ pRank 2 ↥(CxK x K) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hAel, hA8, -⟩ := exists_big_image hG4 hnorm (by omega)
  obtain ⟨p, f, hp, hf, ⟨hq, h9⟩, hLie⟩ := hL
  obtain ⟨F, _, _, e0, hF, hFq⟩ :=
    exists_l2Field_of_hasL2Model hq ⟨p, f, hp, hf, rfl, hLie⟩
  have hn : Odd (Nat.card ↥(fieldAutSub e0)) :=
    odd_card_fieldAutSub_of_fm9 hF (hFq ▸ hq) (by rw [hFq]; exact h9) e0
  have h4 := Th2.L625.card_le_four_of_sq_aut_odd hF e0 hn A
    (Back.forall_of_isElementaryAbelian hAel).2
  omega

theorem two_le_pRank_CxK_or_fAut {x : G} {K : Subgroup G}
    (hG4 : pRank 2 ↥(centralizer ({x} : Set G)) = 4)
    (hnorm : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hL : HasL2Model (kBar K) IsFM9) :
    2 ≤ pRank 2 ↥(CxK x K) ∨ ∃ f : G, f ∈ centralizer ({x} : Set G) ∧ orderOf f = 2 ∧
      P34.InducesFAutL2A7 f K := by
  by_cases hr : 2 ≤ pRank 2 ↥(CxK x K)
  · exact Or.inl hr
  right
  push Not at hr
  obtain ⟨A, hAel, hA8, hAf⟩ := exists_big_image hG4 hnorm (by omega)
  obtain ⟨p, f, hp, hf, hq, hLie⟩ := hL
  obtain ⟨F, _, _, e0, hF, hFq⟩ :=
    exists_l2Field_of_hasL2Model hq ⟨p, f, hp, hf, rfl, hLie⟩
  have h8 := card_le_eight_of_elemAbelian e0 hF A hAel
  have hA8' : Nat.card ↥A = 8 := le_antisymm h8 hA8
  obtain ⟨a, haA, ha2, e', hae'⟩ := Th2.Bal.ivk_1_2k_b_same hF e0 A hAel hA8'
  obtain ⟨g, hgC, hgg, hga⟩ := hAf a haA
  have hg1 : g ≠ 1 := by
    rintro rfl
    have : Back.actHom hnorm ⟨(1 : G), hgC⟩ = 1 := by
      have h1 : (⟨(1 : G), hgC⟩ : ↥(centralizer ({x} : Set G))) = 1 := rfl
      rw [h1, map_one]
    rw [this] at hga
    rw [← hga, orderOf_one] at ha2
    omega
  have hg2 : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  refine ⟨g, hgC, hg2, U1a.mem_normalizer_of_norm hnorm hgC, ?_⟩
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ha2
    omega
  show P34.IsFAutL2A7 (kBar K) (Back.actHom hnorm ⟨g, hgC⟩)
  rw [hga]
  exact ⟨ha1, Or.inl ⟨F, inferInstance, inferInstance, e', hF.1, hae'⟩⟩

end Rank

end CFSG.GH74.GLS.EvenSelP
