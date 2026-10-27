module

public import CFSG.GH74.GLS.Stage2.Local.P34Bar
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift
import CFSG.GH74.GLS.Stage2.Local.Lemma23e

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.LocalCores

theorem perf_bar {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G} (hxH : x ∈ H)
    (hx2 : orderOf x = 2) {K₁ K₂ : Subgroup G} (hK₁ : K₁ ≤ H) (hK₂ : K₂ ≤ H)
    (hperf : ∀ P : Subgroup G, P ≤ centralizer ({x} : Set G) → ⁅P, P⁆ = P → P ≤ K₁ ⊔ K₂)
    {M : Subgroup (HBar H)} (hM : ⁅M, M⁆ = M)
    (hMC : M ≤ centralizer ({mkH H ⟨x, hxH⟩} : Set (HBar H))) :
    M ≤ barIn H K₁ ⊔ barIn H K₂ := by
  set C₀ : Subgroup ↥H := (centralizer ({x} : Set G)).subgroupOf H
  let f : ↥C₀ →* HBar H := (mkH H).comp C₀.subtype
  have hrange : f.range = barIn H (Cen x) := by
    show ((mkH H).comp C₀.subtype).range = C₀.map (mkH H)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hMle : M ≤ f.range := by
    rw [hrange, ← centralizer_mk_eq H hx2 hxH]
    exact hMC
  obtain ⟨P, hPM, hPP⟩ := IVK.Proofs2.Ivk93Adapt.exists_perfect_lift f hM hMle
  set P' : Subgroup G := (P.map C₀.subtype).map H.subtype with hP'
  have hP'C : P' ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩
    exact a.2
  have hP'perf : ⁅P', P'⁆ = P' := by
    rw [hP', ← Subgroup.map_commutator, ← Subgroup.map_commutator, hPP]
  have hle := hperf P' hP'C hP'perf
  rintro m hm
  rw [← hPM] at hm
  obtain ⟨a, ha, rfl⟩ := hm
  have haP' : (((a : ↥C₀) : ↥H) : G) ∈ P' := ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  have hmem : ((a : ↥C₀) : ↥H) ∈ (K₁ ⊔ K₂).subgroupOf H := hle haP'
  rw [Subgroup.subgroupOf_sup hK₁ hK₂] at hmem
  have : f a ∈ ((K₁.subgroupOf H) ⊔ (K₂.subgroupOf H)).map (mkH H) := ⟨_, hmem, rfl⟩
  rw [Subgroup.map_sup] at this
  exact this

theorem eq_one_of_mul_self_of_odd_orderOf {M : Type} [Group M] {u : M} (hu : u * u = 1)
    (ho : Odd (orderOf u)) : u = 1 := by
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at ho
    exact absurd ho (by decide)

theorem cent_barIn_core {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G} (hxH : x ∈ H)
    (hx2 : orderOf x = 2) {K : Subgroup G} (hKH : K ≤ H) (hxK : x ∈ K) {q : ℕ}
    (hsl : HasSL2Model (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q)) (hqodd : Odd q) :
    ∀ u ∈ barIn H K, (∀ k ∈ barIn H K, u * k = k * u) → u * u = 1 →
      u = 1 ∨ u = mkH H ⟨x, hxH⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥K →* HBar H := (mkH H).comp (Subgroup.inclusion hKH)
  have hodd : ∀ y ∈ ρ.ker, Odd (orderOf y) := by
    intro y hy
    have h1 : Subgroup.inclusion hKH y ∈ pPrimeCore 2 ↥H :=
      (mkH_eq_one_iff H).1 (MonoidHom.mem_ker.1 hy)
    have h2 := odd_orderOf_of_mem_core H h1
    rwa [orderOf_injective _ (Subgroup.inclusion_injective hKH)] at h2
  have hker : ρ.ker ≤ pPrimeCore 2 ↥K :=
    GroupTheory.le_pPrimeCore_of_normal (MonoidHom.normal_ker ρ)
      (Nat.coprime_two_left.2 (IVK.Proofs2.Ivk93Adapt.odd_card_of_forall_odd ρ.ker hodd))
  let π : ↥K →* (↥K ⧸ pPrimeCore 2 ↥K) := QuotientGroup.mk' _
  let xK : ↥K := ⟨x, hxK⟩
  have hxK2 : orderOf xK = 2 := by rw [← Subgroup.orderOf_coe]; exact hx2
  have hxsq : xK * xK = 1 := by
    have h := pow_orderOf_eq_one xK
    rwa [hxK2, pow_two] at h
  have hρx : ρ xK = mkH H ⟨x, hxH⟩ := rfl
  have hπx2 : π xK * π xK = 1 := by rw [← map_mul, hxsq, map_one]
  have hπx1 : π xK ≠ 1 := by
    intro h
    have h' : xK ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff xK).1 h
    have := odd_orderOf_of_mem_pPrimeCore h'
    rw [hxK2] at this
    exact absurd this (by decide)
  have hπx : orderOf (π xK) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hπx2) hπx1
  have hsl' : HasSL2Model ↥(⊤ : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) (fun r => r = q) := by
    obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := hsl
    exact ⟨F, hF, hFin, hFq, ⟨Subgroup.topEquiv.trans e⟩⟩
  have huniq := (sl2_model_center_inv hqodd hsl').2
  intro u hu hcen hu2
  obtain ⟨k, hk, hku⟩ := hu
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
  let k' : ↥K := ⟨(k : G), hkK⟩
  have hρk : ρ k' = u := hku
  have hkk : k' * k' ∈ pPrimeCore 2 ↥K := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, hρk]
    exact hu2
  have hπk2 : π k' * π k' = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).2 hkk
  by_cases h1 : π k' = 1
  · left
    have hk'O : k' ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff k').1 h1
    have hodd' := odd_orderOf_of_mem_pPrimeCore hk'O
    refine eq_one_of_mul_self_of_odd_orderOf hu2 ?_
    rw [← hρk]
    exact Odd.of_dvd_nat hodd' (orderOf_map_dvd ρ k')
  · right
    have hπk : orderOf (π k') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hπk2) h1
    have heq : π k' = π xK := huniq _ (Subgroup.mem_top _) _ (Subgroup.mem_top _) hπk hπx
    have hdiff : k' * xK⁻¹ ∈ pPrimeCore 2 ↥K := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      show π (k' * xK⁻¹) = 1
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    have hodd' := odd_orderOf_of_mem_pPrimeCore hdiff
    have hxbar : mkH H ⟨x, hxH⟩ ∈ barIn H K :=
      Subgroup.mem_map.2 ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.2 hxK, rfl⟩
    have hc : Commute u (mkH H ⟨x, hxH⟩) := hcen _ hxbar
    have hxb2 : mkH H ⟨x, hxH⟩ * mkH H ⟨x, hxH⟩ = 1 := by
      rw [← hρx, ← map_mul, hxsq, map_one]
    have hv : (u * (mkH H ⟨x, hxH⟩)⁻¹) * (u * (mkH H ⟨x, hxH⟩)⁻¹) = 1 := by
      have hc' : Commute u (mkH H ⟨x, hxH⟩)⁻¹ := hc.inv_right
      rw [← pow_two, hc'.mul_pow, inv_pow, pow_two, hu2, pow_two, hxb2, inv_one, one_mul]
    have hvo : Odd (orderOf (u * (mkH H ⟨x, hxH⟩)⁻¹)) := by
      have : ρ (k' * xK⁻¹) = u * (mkH H ⟨x, hxH⟩)⁻¹ := by
        rw [map_mul, map_inv, hρk, hρx]
      rw [← this]
      exact Odd.of_dvd_nat hodd' (orderOf_map_dvd ρ _)
    exact mul_inv_eq_one.1 (eq_one_of_mul_self_of_odd_orderOf hv hvo)

theorem cent_barIn {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G} (hxH : x ∈ H)
    (hx2 : orderOf x = 2) {K : Subgroup G} (hKH : K ≤ H) (hKC : K ≤ centralizer ({x} : Set G))
    (hq : IsQuasisimple ↥K) (hxK : x ∈ K) {q : ℕ}
    (hsl : HasSL2Model (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q)) (hqodd : Odd q) (h5 : 5 ≤ q) :
    ∀ u ∈ barIn H K, (∀ k ∈ barIn H K, u * k = k * u) → u * u = 1 →
      u = 1 ∨ u = mkH H ⟨x, hxH⟩ := by
  have _ := hKC
  have _ := hq
  have _ := h5
  exact cent_barIn_core hxH hx2 hKH hxK hsl hqodd

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
