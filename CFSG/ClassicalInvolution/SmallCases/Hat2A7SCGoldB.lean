module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCGoldA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Inv


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

@[expose] def invIn (Ω : Set (Subgroup G)) (P : Subgroup G) : Set G :=
  {x | x ∈ P ∧ ∃ M ∈ Ω, IsUniqueInvolution M x}

theorem invIn_conj (hΩ : HypOmegaGen Ω) {P : Subgroup G} {x : G} (hx : x ∈ invIn Ω P) {g : G}
    (hg : g * x * g⁻¹ ∈ P) : g * x * g⁻¹ ∈ invIn Ω P := by
  obtain ⟨-, M, hM, hxM⟩ := hx
  exact ⟨hg, conjSub g M, hΩ.conjInvariant g M hM, hxM.conj g⟩

theorem exists_nbr_of_mem_invIn (hs : Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {P : Subgroup G} (hPC : P ≤ Subgroup.centralizer ({z} : Set G))
    {x : G} (hx : x ∈ invIn Ω P) (hxz : x ≠ z) : ∃ N ∈ omegaNbr Ω K, IsUniqueInvolution N x := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hxP, M, hM, hxM⟩ := hx
  have hcomm : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hPC hxP)
  have hzC : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hzN : z ∈ Subgroup.normalizer (M : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) hxM hzC
  have hMK : M ∈ KPerp Ω K :=
    (mem_kPerp_iff_normalizes_a7 hΩ hs.classical hK hM hz hxM).mpr hzN
  rcases hMK with h | h
  · exfalso
    rw [h] at hxM
    exact hxz (hxM.eq hz)
  · exact ⟨M, h, hxM⟩

theorem eq_of_ne_of_two {α : Type*} {a b c d e : α} (hab : a ≠ b) (hc : c = a ∨ c = b)
    (hd : d = a ∨ d = b) (he : e = a ∨ e = b) (hdc : d ≠ c) (hec : e ≠ c) : d = e := by
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> simp_all

theorem exists_partner (hs : Pre2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hnoI : ¬ Hat2A7S8.IndepTri Ω K z) {J₁ J₂ : Subgroup G} (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (hne : T8.layerImg Ω z J₁ ≠ T8.layerImg Ω z J₂)
    {N : Subgroup G} (hN : N ∈ omegaNbr Ω K) {t : G} (ht : IsUniqueInvolution N t) :
    ∃ M, M ∈ omegaNbr Ω K ∧ T8.layerImg Ω z M ≠ T8.layerImg Ω z N ∧
      IsUniqueInvolution M (z * t) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  rcases layerImg_cases hs hnt hK hz hnoI hJ₁ hJ₂ hN hne with h | h
  · have hne' : T8.layerImg Ω z N ≠ T8.layerImg Ω z J₂ := by
      rw [h]
      exact hne
    obtain ⟨M, hMK, hMN, hMimg⟩ := exists_common_nbr_of_layerImg_ne hs hnt hK hz hN hJ₂ hne'
    obtain ⟨tM, htM⟩ := Sec6Gen.exists_uniqueInvolution hΩ hMK.1
    have h1 : tM = z * t := involution_eq_mul_of_common_nbr hΩ hnt hK hz hnoI hN ht hMK hMN htM
    refine ⟨M, hMK, ?_, by rw [← h1]; exact htM⟩
    rw [hMimg]
    exact hne'.symm
  · have hne' : T8.layerImg Ω z N ≠ T8.layerImg Ω z J₁ := by
      rw [h]
      exact hne.symm
    obtain ⟨M, hMK, hMN, hMimg⟩ := exists_common_nbr_of_layerImg_ne hs hnt hK hz hN hJ₁ hne'
    obtain ⟨tM, htM⟩ := Sec6Gen.exists_uniqueInvolution hΩ hMK.1
    have h1 : tM = z * t := involution_eq_mul_of_common_nbr hΩ hnt hK hz hnoI hN ht hMK hMN htM
    refine ⟨M, hMK, ?_, by rw [← h1]; exact htM⟩
    rw [hMimg]
    exact hne'.symm

theorem invIn_cases (hs : Pre2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hnoI : ¬ Hat2A7S8.IndepTri Ω K z) {J₁ J₂ : Subgroup G} (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (hne : T8.layerImg Ω z J₁ ≠ T8.layerImg Ω z J₂)
    {P : Subgroup G} (hP2 : IsPGroup 2 P) (hPC : P ≤ Subgroup.centralizer ({z} : Set G))
    (hzP : z ∈ P) {u x : G} (hu : u ∈ invIn Ω P) (hx : x ∈ invIn Ω P) (huz : u ≠ z)
    (hxz : x ≠ z) : x = u ∨ x = z * u := by
  obtain ⟨Nu, hNu, htu⟩ := exists_nbr_of_mem_invIn hs hnt hK hz hPC hu huz
  obtain ⟨Nx, hNx, htx⟩ := exists_nbr_of_mem_invIn hs hnt hK hz hPC hx hxz
  by_cases heq : T8.layerImg Ω z Nu = T8.layerImg Ω z Nx
  · left
    exact (involution_eq_of_layerImg_eq hs hK hz hP2 hNu hNx heq htu htx hu.1 hx.1).symm
  · right
    obtain ⟨M, hMK, hMne, htM⟩ := exists_partner hs hnt hK hz hnoI hJ₁ hJ₂ hne hNu htu
    have himg : T8.layerImg Ω z M = T8.layerImg Ω z Nx :=
      eq_of_ne_of_two hne (layerImg_cases hs hnt hK hz hnoI hJ₁ hJ₂ hNu hne)
        (layerImg_cases hs hnt hK hz hnoI hJ₁ hJ₂ hMK hne)
        (layerImg_cases hs hnt hK hz hnoI hJ₁ hJ₂ hNx hne) hMne (fun h => heq h.symm)
    exact (involution_eq_of_layerImg_eq hs hK hz hP2 hMK hNx himg htM htx
      (P.mul_mem hzP hu.1) hx.1).symm

theorem mul_mem_invIn (hs : Pre2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hnoI : ¬ Hat2A7S8.IndepTri Ω K z) {J₁ J₂ : Subgroup G} (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (hne : T8.layerImg Ω z J₁ ≠ T8.layerImg Ω z J₂)
    {P : Subgroup G} (hPC : P ≤ Subgroup.centralizer ({z} : Set G)) (hzP : z ∈ P) {u : G}
    (hu : u ∈ invIn Ω P) (huz : u ≠ z) : z * u ∈ invIn Ω P := by
  obtain ⟨Nu, hNu, htu⟩ := exists_nbr_of_mem_invIn hs hnt hK hz hPC hu huz
  obtain ⟨M, hMK, -, htM⟩ := exists_partner hs hnt hK hz hnoI hJ₁ hJ₂ hne hNu htu
  exact ⟨P.mul_mem hzP hu.1, M, hMK.1, htM⟩

theorem exists_pair (hs : Pre2A7 Ω K₀) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hnoI : ¬ Hat2A7S8.IndepTri Ω K z) {J₁ J₂ : Subgroup G} (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (hne : T8.layerImg Ω z J₁ ≠ T8.layerImg Ω z J₂)
    {P : Subgroup G} (hP2 : IsPGroup 2 P) (hPC : P ≤ Subgroup.centralizer ({z} : Set G))
    (hzP : z ∈ P) :
    ∃ u : G, u ∈ invIn Ω P ∧ u * u = 1 ∧ u * z = z * u ∧ (z * u = 1 ∨ z * u ∈ invIn Ω P) ∧
      ∀ x ∈ invIn Ω P, x = z ∨ x = u ∨ x = z * u := by
  by_cases h : ∃ u ∈ invIn Ω P, u ≠ z
  · obtain ⟨u, hu, huz⟩ := h
    have hsq : u * u = 1 := by
      obtain ⟨-, M, -, hM⟩ := hu
      exact hM.sq
    have hcomm : u * z = z * u := Subgroup.mem_centralizer_singleton_iff.mp (hPC hu.1)
    refine ⟨u, hu, hsq, hcomm,
      Or.inr (mul_mem_invIn hs hnt hK hz hnoI hJ₁ hJ₂ hne hPC hzP hu huz), fun x hx => ?_⟩
    by_cases hxz : x = z
    · exact Or.inl hxz
    · rcases invIn_cases hs hnt hK hz hnoI hJ₁ hJ₂ hne hP2 hPC hzP hu hx huz hxz with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
  · push Not at h
    have hzin : z ∈ invIn Ω P := ⟨hzP, K, hK, hz⟩
    exact ⟨z, hzin, hz.sq, rfl, Or.inl hz.sq, fun x hx => Or.inl (h x hx)⟩

end Inv

end CFSG.ClassicalInvolution.Hat2A7S

