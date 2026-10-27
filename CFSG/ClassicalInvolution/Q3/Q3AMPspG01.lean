module

public import CFSG.ClassicalInvolution.Q3.Q3KXAxis

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Layer



variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.omega_orbit_layer [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {J' : Subgroup G} {t' : G} (hJ' : J' ∈ omegaNbr Ω K) (ht' : IsUniqueInvolution J' t') :
    ∃ c ∈ Q3NL.exactLayer3 Ω z, c * z * c⁻¹ = z ∧
      (c * t * c⁻¹ = t' ∨ c * (z * t) * c⁻¹ = t') := by
  classical
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    h.normalizer_eq_centralizer
  have hJtq : J ∈ Q3NL.tqMembers3 Ω z := mem_tqMembers3_of_omegaNbr hΩ hnt hs.hz hs.hJ hs.ht
  have hJ'tq : J' ∈ Q3NL.tqMembers3 Ω z := mem_tqMembers3_of_omegaNbr hΩ hnt hs.hz hJ' ht'
  obtain ⟨hJΩ, hJK, T₀, hT₀, hT₀J, hT₀N⟩ := hs.hJ
  obtain ⟨hJ'Ω, hJ'K, T₁, hT₁, hT₁J', hT₁N⟩ := hJ'
  have hT₀s : IsSylow2In T₀ J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT₀ hT₀J
  have hT₁s : IsSylow2In T₁ J' := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJ'Ω hT₁ hT₁J'
  have hT₀C : T₀ ≤ Subgroup.centralizer ({z} : Set G) := hNC ▸ hT₀N
  have hT₁C : T₁ ≤ Subgroup.centralizer ({z} : Set G) := hNC ▸ hT₁N
  have hT₀Y : T₀ ≤ Q3NL.exactLayer3 Ω z := fun x hx =>
    Q3NL.exactCore3_le_exactLayer3 hJtq ⟨hT₀J hx, hT₀C hx⟩
  have hT₁Y : T₁ ≤ Q3NL.exactLayer3 Ω z := fun x hx =>
    Q3NL.exactCore3_le_exactLayer3 hJ'tq ⟨hT₁J' hx, hT₁C hx⟩
  obtain ⟨c, hcY, hc2⟩ := exists_conj_isPGroup_sup hT₀Y hT₁Y hT₀s.2.1 hT₁s.2.1
  have hcC : c ∈ Subgroup.centralizer ({z} : Set G) := Q3NL.exactLayer3_le_centralizer Ω z hcY
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
  have hcinv : c⁻¹ ∈ Q3NL.exactLayer3 Ω z := (Q3NL.exactLayer3 Ω z).inv_mem hcY
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
    refine ⟨c⁻¹, hcinv, hcz', Or.inl ?_⟩
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
    refine ⟨c⁻¹, hcinv, hcz', Or.inr ?_⟩
    rw [← hmul]
    group

theorem BadStd8.false_of_localAxis_layer_rank [IsSimpleGroup G]
    (h : BadStd8 Ω K J S R T W z t) {B : Subgroup G} (hbal : RankThreeBalance B)
    (hpair : Subgroup.closure ({t, z} : Set G) ≤ B)
    (hgen : Q3NL.exactLayer3 Ω z ≤ rankTwoSpan B) : False := by
  have hF : Subgroup.closure ({t, z} : Set G) ∈ signalizerFunctorEk 2 2 B :=
    ⟨hpair, by simpa using h.isElemAbelian2_pair.1⟩
  have hAF : Balance.Theorem5.alphaFrame B = alphaCore (Subgroup.closure ({t, z} : Set G)) :=
    Balance.Theorem5.alphaFrame_eq_alphaCore hbal hF
  have hodd : Odd (Nat.card ↥(alphaCore (Subgroup.closure ({t, z} : Set G)))) := by
    rw [← hAF]
    exact Balance.Theorem5.odd_card_alphaFrame hbal
  have hnormB : ∀ c ∈ rankTwoSpan B, conjSub c (alphaCore (Subgroup.closure ({t, z} : Set G))) =
      alphaCore (Subgroup.closure ({t, z} : Set G)) := by
    intro c hc
    have := Balance.Theorem5.rankTwoSpan_le_normalizer_alphaFrame hbal hc
    rw [hAF] at this
    exact mem_normalizer_iff_conjSub_eq.mp this
  refine h.false_of_linkConstCore ?_ hodd
  intro J' hJ' t' ht'
  obtain ⟨c, hcY, hcz, hct⟩ := h.omega_orbit_layer hJ' ht'
  have hpairEq : Subgroup.closure ({t', z} : Set G) =
      conjSub c (Subgroup.closure ({t, z} : Set G)) := by
    rcases hct with e | e
    · rw [conjSub_closure_pair, hcz, e]
    · rw [← closure_mul_pair_eq z t, conjSub_closure_pair, hcz, e]
  rw [hpairEq, alphaCore_conjSub, hnormB c (hgen hcY)]

theorem BadStd8.false_of_localAxis_layer [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {B : Subgroup G} (hB : Hyp51 B) (hpair : Subgroup.closure ({t, z} : Set G) ≤ B)
    (hgen : Q3NL.exactLayer3 Ω z ≤ rankTwoSpan B) : False :=
  h.false_of_localAxis_layer_rank (lemma52 G B hB) hpair hgen

end Layer

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
