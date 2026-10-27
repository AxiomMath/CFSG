module

public import CFSG.GH74.Uniqueness.Section6AGroup
public import CFSG.GH74.Uniqueness.Section4Struct

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Key

theorem mem_sylow_of_mem_normalizer_of_mul_self_eq_one {K : Type} [Group K] (S : Sylow 2 K) {g : K}
    (hg : g ∈ normalizer ((S : Subgroup K) : Set K)) (hg2 : g * g = 1) :
    g ∈ (S : Subgroup K) := by
  set H₀ : Subgroup K := (S : Subgroup K) ⊔ zpowers g with hH₀
  have hP : IsPGroup 2 H₀ := by
    intro x
    have hsq : (x : K) * (x : K) ∈ (S : Subgroup K) :=
      mul_self_mem_of_mem_sup_zpowers hg2 hg x.2
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨(x : K) * (x : K), hsq⟩
    refine ⟨k + 1, ?_⟩
    apply Subtype.ext
    have h1 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
    rw [pow_succ', pow_mul, sq]
    exact h1
  have hle : (S : Subgroup K) ≤ H₀ := le_sup_left
  have heq : H₀ = (S : Subgroup K) := S.is_maximal' hP hle
  have hgH : g ∈ H₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  rwa [heq] at hgH

variable {X : Type} [Group X] [Finite X]

theorem XData.odd_mem_of_mem_zHull {Z : Set X} {M L D O : Subgroup X} {u : X}
    (hD : XData Z M L D O u) (hZ : IsInvariantInvolutionSet Z)
    (hZL : ∀ y ∈ Z, y ∈ M → y ∈ L) {x : X} (hx : x ∈ zHull Z M) (hodd : Odd (orderOf x)) :
    x ∈ O := by
  obtain ⟨K, instK, φ, hsurj, hker, hB, S₂, hS⟩ := hD.bar
  have hu2 : u * u = 1 := hD.sq
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set T : Subgroup X := ((S₂ : Subgroup K).comap φ).map D.subtype with hT
  have hmemT : ∀ d : X, ∀ hd : d ∈ D, d ∈ T ↔ φ ⟨d, hd⟩ ∈ (S₂ : Subgroup K) := by
    intro d hd
    constructor
    · rintro ⟨d', hd', rfl⟩
      exact hd'
    · intro h
      exact ⟨⟨d, hd⟩, h, rfl⟩
  have hTD : T ≤ D := Subgroup.map_subtype_le _
  have hOT : O ≤ T := by
    intro o ho
    refine (hmemT o (hD.O_le ho)).mpr ?_
    rw [(map_eq_one_iff_mem_of_ker hker (hD.O_le ho)).mpr ho]
    exact (S₂ : Subgroup K).one_mem
  have huT : u ∈ normalizer (T : Set X) := by
    refine Section6A.mem_normalizer_of_conj_mem hu2 fun a ha => ?_
    have haD : a ∈ D := hTD ha
    have hc : u * a * u⁻¹ * a⁻¹ ∈ O := hD.comm a haD
    have e : u * a * u⁻¹ = (u * a * u⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact T.mul_mem (hOT hc) ha
  have hgen : ∀ y ∈ Z, y ∈ M → y ∈ T ⊔ zpowers u := by
    intro y hy hyM
    have hyL := hZL y hy hyM
    obtain ⟨⟨d, hdD, hyd⟩, -⟩ := hD.zset y hy hyL
    have hdM : d ∈ M := by
      have e : d = u⁻¹ * y := by rw [hyd]; group
      rw [e]
      exact M.mul_mem (M.inv_mem hD.mem_M) hyM
    have hdN : φ ⟨d, hdD⟩ ∈ normalizer ((S₂ : Subgroup K) : Set K) := by
      rw [← hS]
      exact ⟨⟨d, hdD⟩, (Subgroup.mem_subgroupOf).mpr hdM, rfl⟩
    have hyy : y * y = 1 := hZ.mul_self_eq_one hy
    have hdd : d * d ∈ O := by
      have hc := hD.comm d hdD
      have h1 : u * d * u⁻¹ * d⁻¹ * (d * d) = 1 := by
        calc u * d * u⁻¹ * d⁻¹ * (d * d) = (u * d) * (u⁻¹ * d) := by group
          _ = (u * d) * (u * d) := by rw [hui]
          _ = 1 := by rw [← hyd]; exact hyy
      have h2 : d * d = (u * d * u⁻¹ * d⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact O.inv_mem hc
    have hφ2 : φ ⟨d, hdD⟩ * φ ⟨d, hdD⟩ = 1 := by
      rw [← map_mul]
      exact (map_eq_one_iff_mem_of_ker hker (D.mul_mem hdD hdD)).mpr hdd
    have hdS : φ ⟨d, hdD⟩ ∈ (S₂ : Subgroup K) :=
      mem_sylow_of_mem_normalizer_of_mul_self_eq_one S₂ hdN hφ2
    have hdT : d ∈ T := (hmemT d hdD).mpr hdS
    rw [hyd]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
      (Subgroup.mem_sup_left hdT)
  have hle : zHull Z M ≤ T ⊔ zpowers u := by
    rw [zHull, Subgroup.closure_le]
    rintro y ⟨hy, hyM⟩
    exact hgen y hy hyM
  have hxT : x ∈ T ⊔ zpowers u := hle hx
  have hxx : x * x ∈ T := mul_self_mem_of_mem_sup_zpowers hu2 huT hxT
  have hxT' : x ∈ T := mem_of_mul_self_mem_of_odd_orderOf hodd hxx
  have hxD : x ∈ D := hTD hxT'
  have hφx : φ ⟨x, hxD⟩ ∈ (S₂ : Subgroup K) := (hmemT x hxD).mp hxT'
  have hφ1 : φ ⟨x, hxD⟩ = 1 := by
    have hodvd : orderOf (φ ⟨x, hxD⟩) ∣ orderOf x := by
      have h1 := orderOf_map_dvd φ (⟨x, hxD⟩ : ↥D)
      have h2 : orderOf (⟨x, hxD⟩ : ↥D) = orderOf x := Subgroup.orderOf_mk _ _
      rwa [h2] at h1
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp S₂.isPGroup' ⟨φ ⟨x, hxD⟩, hφx⟩
    have hk' : orderOf (φ ⟨x, hxD⟩) = 2 ^ k := by
      rw [← Subgroup.orderOf_mk (φ ⟨x, hxD⟩) hφx]
      exact hk
    have hodd2 : Odd (2 ^ k) := Odd.of_dvd_nat hodd (hk' ▸ hodvd)
    have hk0 : k = 0 := by
      by_contra hk0
      exact absurd (even_iff_two_dvd.mpr (dvd_pow_self 2 hk0)) (Nat.not_even_iff_odd.mpr hodd2)
    rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.mp hk'
  exact (map_eq_one_iff_mem_of_ker hker hxD).mp hφ1

end Key

end CFSG.GH74.Uniqueness
