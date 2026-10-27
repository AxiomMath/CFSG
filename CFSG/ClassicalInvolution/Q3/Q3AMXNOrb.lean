module

public import CFSG.ClassicalInvolution.Q3.Q3KXOrbit

set_option autoImplicit false
set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Dichotomy

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.conjSub_mem_omegaNbr (h : BadStd8 Ω K J S R T W z t) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) :
    conjSub c M ∈ omegaNbr Ω K := by
  have hΩ : HypOmegaMod Ω := h.std.stand.hyp
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := h.normalizer_eq_centralizer ▸ hc
  have hcK : conjSub c K = K := mem_normalizer_iff_conjSub_eq.mp hcN
  have h1 := omegaNbr_conj hΩ.conjInvariant hM c
  rwa [hcK] at h1

theorem BadStd8.nbr_dichotomy (h : BadStd8 Ω K J S R T W z t) {J' : Subgroup G}
    (hJ' : J' ∈ omegaNbr Ω K) :
    (∃ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c J' = J) ∨
      ∃ c ∈ Subgroup.centralizer ({z} : Set G),
        conjSub c J' ∈ omegaNbr Ω K ∧ conjSub c J' ∈ omegaNbr Ω J := by
  classical
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    h.normalizer_eq_centralizer
  obtain ⟨hJΩ, hJK, T₀, hT₀, hT₀J, hT₀N⟩ := hs.hJ
  obtain ⟨hJ'Ω, hJ'K, T₁, hT₁, hT₁J', hT₁N⟩ := hJ'
  have hT₀s : IsSylow2In T₀ J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT₀ hT₀J
  have hT₁s : IsSylow2In T₁ J' := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJ'Ω hT₁ hT₁J'
  have hT₀C : T₀ ≤ Subgroup.centralizer ({z} : Set G) := hNC ▸ hT₀N
  have hT₁C : T₁ ≤ Subgroup.centralizer ({z} : Set G) := hNC ▸ hT₁N
  obtain ⟨c, hcC, hc2⟩ := exists_conj_isPGroup_sup hT₀C hT₁C hT₀s.2.1 hT₁s.2.1
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hNC ▸ hcC
  have hcK : conjSub c K = K := mem_normalizer_iff_conjSub_eq.mp hcN
  have hc'K : conjSub c⁻¹ K = K := mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ hcN)
  obtain ⟨S', hS'⟩ := hc2.exists_le_sylow
  have hT₁c : conjSub c T₁ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hT₁ c
  have hJ''Ω : conjSub c J' ∈ Ω := hΩ.conjInvariant c J' hJ'Ω
  have hT₁cJ'' : conjSub c T₁ ≤ conjSub c J' := conjSub_mono hT₁J'
  by_cases hTeq : T₀ = conjSub c T₁
  ·
    have hJeq : J = conjSub c J' :=
      hΩ.eq_of_le_of_le hJΩ hJ''Ω hT₀s.2.1 (by have := hΩ.eight_le_of_mem_RSet hT₀; omega)
        hT₀J (hTeq ▸ hT₁cJ'')
    exact Or.inl ⟨c, hcC, hJeq.symm⟩
  ·
    have hcomm : Commutes T₀ (conjSub c T₁) :=
      Q3CP.l67Gen G Ω hΩ S' T₀ hT₀ (conjSub c T₁) hT₁c (le_sup_left.trans hS')
        (le_sup_right.trans hS') hTeq
    have hKK' : conjSub c J' ∈ omegaNbr Ω K := by
      refine ⟨hJ''Ω, fun e => hJ'K ?_, conjSub c T₁, hT₁c, hT₁cJ'', ?_⟩
      · have := congrArg (conjSub c⁻¹) e
        rwa [conjSub_inv_conjSub, hc'K] at this
      · rintro _ ⟨y, hy, rfl⟩
        have hy' : y ∈ Subgroup.normalizer (K : Set G) := hT₁N hy
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hy') (Subgroup.inv_mem _ hcN)
    have h4 : 4 ≤ Nat.card T₀ := by have := hΩ.eight_le_of_mem_RSet hT₀; omega
    have hnormJ : conjSub c T₁ ≤ Subgroup.normalizer (J : Set G) := by
      intro y hy
      have hJy : conjSub y J ∈ Ω := hΩ.conjInvariant y J hJΩ
      have hT₀y : T₀ ≤ conjSub y J := by
        intro x hx
        rw [mem_conjSub_iff]
        have hxy : y⁻¹ * x * y = x := by
          have := hcomm x hx y hy
          calc y⁻¹ * x * y = y⁻¹ * (y * x) := by rw [← this]; group
            _ = x := by group
        rw [hxy]
        exact hT₀J hx
      exact mem_normalizer_iff_conjSub_eq.mpr
        (hΩ.eq_of_le_of_le hJΩ hJy hT₀s.2.1 h4 hT₀J hT₀y).symm
    have hJ''J : conjSub c J' ≠ J := by
      intro e
      have hT₁cJ : conjSub c T₁ ≤ J := e ▸ hT₁cJ''
      have hpg : IsPGroup 2 ↥(T₀ ⊔ conjSub c T₁) := S'.isPGroup'.to_le hS'
      have h1 : T₀ ⊔ conjSub c T₁ = T₀ := hT₀s.2.2 _ (sup_le hT₀J hT₁cJ) hpg le_sup_left
      have hle : conjSub c T₁ ≤ T₀ := h1 ▸ le_sup_right
      have hT₁cs : IsSylow2In (conjSub c T₁) J := by
        have := hT₁s.conj c
        rwa [e] at this
      exact hTeq (hT₁cs.2.2 T₀ hT₀J hT₀s.2.1 hle)
    exact Or.inr ⟨c, hcC, hKK', ⟨hJ''Ω, hJ''J, conjSub c T₁, hT₁c, hT₁cJ'', hnormJ⟩⟩

theorem BadStd8.nbr_mem_orbit_of_noTriangle (h : BadStd8 Ω K J S R T W z t)
    (hN : ∀ K' ∈ omegaNbr Ω K, K' ∉ omegaNbr Ω J) {J' : Subgroup G} (hJ' : J' ∈ omegaNbr Ω K) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), J' = conjSub c J := by
  rcases h.nbr_dichotomy hJ' with ⟨c, hc, h1⟩ | ⟨c, hc, h2, h3⟩
  · refine ⟨c⁻¹, Subgroup.inv_mem _ hc, ?_⟩
    rw [← h1, conjSub_inv_conjSub]
  · exact absurd h3 (hN _ h2)

end Dichotomy

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
