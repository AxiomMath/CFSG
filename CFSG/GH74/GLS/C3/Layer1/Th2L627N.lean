module

public import CFSG.GH74.GLS.C3.Layer1.Th2L625c2

public section

namespace CFSG.GH74.GLS.Th2.L625

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

section Image

variable {X Y : Type} [Group X] [Group Y]

theorem isElementaryAbelian_map {U : Subgroup X} (hU : IsElementaryAbelian 2 ↥U) (f : X →* Y) :
    IsElementaryAbelian 2 ↥(U.map f) := by
  obtain ⟨hc, hs⟩ := Back.forall_of_isElementaryAbelian hU
  refine Back.isElementaryAbelian_of_forall ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hs a ha, map_one]

end Image

section Big

variable {G : Type} [Group G] [Finite G]

theorem exists_big_of_L2
    {x : G} {K : Subgroup G} (hxK : IsIL2Pair x K) (hL : HasL2Model (kBar K) Odd)
    {B : Subgroup G} (hBea : IsElementaryAbelian 2 ↥B) (hBle : B ≤ CxK x K) :
    ∃ (m : ℕ) (Q : Subgroup G), 2 ≤ m ∧ IsElementaryAbelian 2 ↥Q ∧
      Nat.card ↥Q = Nat.card ↥B * 2 ^ m := by
  have hsimple : IsSimpleGroup (kBar K) := Back.isSimpleGroup_of_hasL2Model hL
  obtain ⟨hZ, -⟩ := Bk.no_central_involution hxK.2 hsimple
  obtain ⟨V, hVel, hV4⟩ :=
    CFSG.StronglyEmbedded.SteinbergBU.exists_four_group_of_two_le_pRank (G := kBar K)
      (two_le_pRank_kBar (Or.inl hL))
  obtain ⟨-, hVsq⟩ := Back.forall_of_isElementaryAbelian hVel
  obtain ⟨m, Q, hm, hQsq, hQcard⟩ :=
    exists_big_elemAbelian K B hBea (hBle.trans inf_le_right) V hVsq
      (by rw [hV4]; exact ⟨1, by norm_num⟩) hZ
  exact ⟨m, Q, hm, isElementaryAbelian_two_of_mul_self Q hQsq, hQcard⟩

theorem normal_of_pRank_le_four
    (hG4 : pRank 2 G ≤ 4) {x : G} {K : Subgroup G} (hxK : IsIL2Pair x K)
    (hL : HasL2Model (kBar K) Odd) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  by_contra hnn
  push Not at hnn
  obtain ⟨c, hc, k, hk, hkc⟩ := hnn
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hxK.2
  have hx2 : x * x = 1 := by rw [← sq]; exact hxK.1 ▸ pow_orderOf_eq_one x
  have hK' : IsPCompIn 2 (centralizer ({x} : Set G)) (K.map (MulAut.conj c).toMonoidHom) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hK c
    rwa [Thm1.map_conj_eq_self_of_mem hc] at this
  have hne : K.map (MulAut.conj c).toMonoidHom ≠ K := by
    intro h
    apply hkc
    have hmem : c * k * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h] at hmem
  have hle : K.map (MulAut.conj c).toMonoidHom ≤ CxK x K :=
    le_inf hK'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hK' hK hne)
  obtain ⟨A, hAel, hA4⟩ := CFSG.StronglyEmbedded.SteinbergBU.exists_four_group_of_two_le_pRank
    (G := ↥K) (Thm1.two_le_pRank_of_shape (Or.inl hL))
  set U₀ : Subgroup G := A.map K.subtype with hU₀
  have hU₀el : IsElementaryAbelian 2 ↥U₀ := isElementaryAbelian_map hAel K.subtype
  have hU₀card : Nat.card ↥U₀ = 4 := by
    rw [hU₀, Subgroup.card_map_of_injective K.subtype_injective, hA4]
    norm_num
  have hU₀K : U₀ ≤ K := Subgroup.map_subtype_le A
  set B : Subgroup G := U₀.map (MulAut.conj c).toMonoidHom with hB
  have hBel : IsElementaryAbelian 2 ↥B := isElementaryAbelian_map hU₀el _
  have hBcard : Nat.card ↥B = 4 := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.conj c).injective, hU₀card]
  have hBle : B ≤ CxK x K := (Subgroup.map_mono hU₀K).trans hle
  have hKx : ∀ l ∈ K, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hl)).symm
  have hxN : x ∈ normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G)
      (Subgroup.mem_centralizer_iff.2 (fun h hh => (hKx h hh).symm))
  have hxC : x ∈ CxK x K :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hxN, TwoThin.mem_normalizer_pPrimeCoreOf hxN,
      fun l hl => by
        have : ⁅l, x⁆ = 1 := commutatorElement_eq_one_iff_commute.2 (hKx l hl).symm
        rw [this]; exact one_mem _⟩
  have hBx : ∀ b ∈ B, b * x = x * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.1 (hBle hb).1
  set B' : Subgroup G := B ⊔ zpowers x with hB'
  have hB'el : IsElementaryAbelian 2 ↥B' := isElementaryAbelian_sup_zpowers hBel hx2 hBx
  have hB'le : B' ≤ CxK x K := sup_le hBle (Subgroup.zpowers_le.2 hxC)
  obtain ⟨m, Q, hm, hQel, hQcard⟩ := exists_big_of_L2 hxK hL hB'el hB'le
  have hB'pow := Back.card_eq_two_pow_pRank hB'el
  have hrk := le_pRank_group_of_elem hQel (k := pRank 2 ↥B' + m)
    (by rw [hQcard, hB'pow, pow_add])
  have hp : pRank 2 ↥B' ≤ 2 := by omega
  have hB'4 : Nat.card ↥B' ≤ Nat.card ↥B := by
    rw [hB'pow, hBcard]
    calc 2 ^ pRank 2 ↥B' ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hp
      _ = 4 := by norm_num
  have hBB' : B = B' := Subgroup.eq_of_le_of_card_ge le_sup_left hB'4
  have hxB : x ∈ B := by
    rw [hBB']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨u, hu, hux⟩ := hxB
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  have hu' : u = x := by
    have h1 : c * u * c⁻¹ = x := hux
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = c⁻¹ * x * c := by rw [h1]
      _ = x := by
        calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
          _ = c⁻¹ * (c * x) := by rw [hcx]
          _ = x := by group
  have hxK' : x ∈ K := hu' ▸ hU₀K hu
  have hsimple : IsSimpleGroup (kBar K) := Back.isSimpleGroup_of_hasL2Model hL
  obtain ⟨-, hZ⟩ := Bk.no_central_involution hK hsimple
  refine hZ x hxK' hxK.1 (fun l hl => ?_)
  have : ⁅x, l⁆ = 1 := commutatorElement_eq_one_iff_commute.2 (hKx l hl)
  rw [this]
  exact one_mem _

end Big

end CFSG.GH74.GLS.Th2.L625
