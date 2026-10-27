module

public import CFSG.ClassicalInvolution.Q3.Q3T8B00

set_option autoImplicit false
set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_isPGroup_sup {H A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H)
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) :
    ∃ c ∈ H, IsPGroup 2 ↥(A ⊔ conjSub c B) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A' : Subgroup H := A.subgroupOf H
  let B' : Subgroup H := B.subgroupOf H
  have hA' : IsPGroup 2 ↥A' :=
    hA.of_surjective (Subgroup.subgroupOfEquivOfLe hAH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAH).symm.surjective
  have hB' : IsPGroup 2 ↥B' :=
    hB.of_surjective (Subgroup.subgroupOfEquivOfLe hBH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hBH).symm.surjective
  obtain ⟨Q₁, hQ₁⟩ := hA'.exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := hB'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q₂ Q₁
  refine ⟨(g : G), g.2, ?_⟩
  set T : Subgroup G := (Q₁ : Subgroup H).map H.subtype with hT
  have hTp : IsPGroup 2 ↥T :=
    Q₁.isPGroup'.of_surjective ((Q₁ : Subgroup H).equivMapOfInjective H.subtype
      H.subtype_injective).toMonoidHom ((Q₁ : Subgroup H).equivMapOfInjective H.subtype
      H.subtype_injective).surjective
  refine hTp.to_le (sup_le ?_ ?_)
  · intro a ha
    have : (⟨a, hAH ha⟩ : H) ∈ A' := ha
    exact ⟨_, hQ₁ this, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    have hbB' : (⟨b, hBH hb⟩ : H) ∈ B' := hb
    have h1 := hQ₂ hbB'
    have h2 : (Q₂ : Subgroup H).map (MulAut.conj g).toMonoidHom = (Q₁ : Subgroup H) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      ext x
      simp [Subgroup.pointwise_smul_def]
    have h3 : (MulAut.conj g) ⟨b, hBH hb⟩ ∈ (Q₁ : Subgroup H) := by
      rw [← h2]
      exact ⟨_, h1, rfl⟩
    exact ⟨_, h3, rfl⟩

end Sylow

section Orbit


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.normalizer_eq_centralizer (h : BadStd8 Ω K J S R T W z t) :
    Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) := by
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  refine le_antisymm (fun n hn => ?_)
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz)
  have h1 := hs.hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hn)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [h1]

theorem BadStd8.omega_orbit_two [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {J' : Subgroup G} {t' : G} (hJ' : J' ∈ omegaNbr Ω K) (ht' : IsUniqueInvolution J' t') :
    ∃ c : G, c * z * c⁻¹ = z ∧ (c * t * c⁻¹ = t' ∨ c * (z * t) * c⁻¹ = t') := by
  classical
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    h.normalizer_eq_centralizer
  obtain ⟨hJΩ, hJK, T₀, hT₀, hT₀J, hT₀N⟩ := hs.hJ
  obtain ⟨hJ'Ω, hJ'K, T₁, hT₁, hT₁J', hT₁N⟩ := hJ'
  have hT₀s : IsSylow2In T₀ J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT₀ hT₀J
  have hT₁s : IsSylow2In T₁ J' := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJ'Ω hT₁ hT₁J'
  have hT₀C : T₀ ≤ Subgroup.centralizer ({z} : Set G) := hNC ▸ hT₀N
  have hT₁C : T₁ ≤ Subgroup.centralizer ({z} : Set G) := hNC ▸ hT₁N
  obtain ⟨c, hcC, hc2⟩ := exists_conj_isPGroup_sup hT₀C hT₁C hT₀s.2.1 hT₁s.2.1
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hcC
    calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [this]
      _ = z := by group
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hNC ▸ hcC
  have hcK : conjSub c K = K := mem_normalizer_iff_conjSub_eq.mp hcN
  have hc'K : conjSub c⁻¹ K = K := mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ hcN)
  have hcz' : c⁻¹ * z * c⁻¹⁻¹ = z := by
    have hcomm : c * z = z * c := by
      calc c * z = (c * z * c⁻¹) * c := by group
        _ = z * c := by rw [hcz]
    calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [hcomm]
      _ = z := by group
  obtain ⟨S', hS'⟩ := hc2.exists_le_sylow
  have hT₁c : conjSub c T₁ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hT₁ c
  have hJ''Ω : conjSub c J' ∈ Ω := hΩ.conjInvariant c J' hJ'Ω
  have hT₁cJ'' : conjSub c T₁ ≤ conjSub c J' := conjSub_mono hT₁J'
  have hu : IsUniqueInvolution (conjSub c J') (c * t' * c⁻¹) := ht'.conj c
  by_cases hTeq : T₀ = conjSub c T₁
  ·
    have hJeq : J = conjSub c J' :=
      hΩ.eq_of_le_of_le hJΩ hJ''Ω hT₀s.2.1 (by have := hΩ.eight_le_of_mem_RSet hT₀; omega)
        hT₀J (hTeq ▸ hT₁cJ'')
    have htt : t = c * t' * c⁻¹ := hs.ht.eq (hJeq ▸ hu)
    refine ⟨c⁻¹, hcz', Or.inl ?_⟩
    rw [htt]
    group
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
    have hJK' : conjSub c J' ∈ omegaNbr Ω J := ⟨hJ''Ω, hJ''J, conjSub c T₁, hT₁c, hT₁cJ'', hnormJ⟩
    have hmul : c * t' * c⁻¹ = z * t := h.eq_mul_of_nbr_nbr hKK' hJK' hu
    refine ⟨c⁻¹, hcz', Or.inr ?_⟩
    rw [← hmul]
    group

end Orbit

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
