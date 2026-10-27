module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUTq
import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

structure BlockGeom4 {K : Type} [Group K] (𝓕 : Set (Subgroup K)) : Prop where
  uniq : ∀ R ∈ 𝓕, ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, (∀ r ∈ R, ∀ s ∈ R₁, r * s = s * r) →
    (∀ r ∈ R, ∀ s ∈ R₂, r * s = s * r) → R₁ = R₂
  centralizes : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ≠ 1 →
    (∀ s ∈ R', r * s * r⁻¹ * s⁻¹ ∈ Subgroup.center K) →
    R' = R ∨ ∀ s ∈ R', ∀ s' ∈ R, s * s' = s' * s

section Basic

variable {G : Type} [Group G] [Finite G]

theorem eq_of_oddQuotMk_eq' {c u v : G} (hu : u ∈ Subgroup.centralizer ({c} : Set G))
    (hv : v ∈ Subgroup.centralizer ({c} : Set G)) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (huv : u * v = v * u) (h : oddQuotMk c ⟨u, hu⟩ = oddQuotMk c ⟨v, hv⟩) : u = v := by
  have hx : (⟨u * v, Subgroup.mul_mem _ hu hv⟩ : ↥(Subgroup.centralizer ({c} : Set G))) *
      ⟨u * v, Subgroup.mul_mem _ hu hv⟩ = 1 := by
    apply Subtype.ext
    show (u * v) * (u * v) = 1
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, one_mul]
  have h1 : oddQuotMk c ⟨u * v, Subgroup.mul_mem _ hu hv⟩ = 1 := by
    have e : (⟨u * v, Subgroup.mul_mem _ hu hv⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
        ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e, map_mul, h, ← map_mul]
    have : (⟨v, hv⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨v, hv⟩ = 1 :=
      Subtype.ext hv2
    rw [this, map_one]
  have h2 := eq_one_of_oddQuotMk_eq_one hx h1
  have h3 : u * v = 1 := congrArg Subtype.val h2
  exact (inv_eq_of_mul_eq_one_right hv2) ▸ (eq_inv_of_mul_eq_one_left h3)

omit [Finite G] in
theorem modOdd_conjSub_of_mem_oddCoreIn {c o : G}
    (ho : o ∈ oddCoreIn (Subgroup.centralizer ({c} : Set G))) (E : Subgroup G) :
    modOdd c (conjSub o E) = modOdd c E := by
  have hoC : o ∈ Subgroup.centralizer ({c} : Set G) := oddCoreIn_le _ ho
  have ho1 : oddQuotMk c ⟨o, hoC⟩ = 1 := by
    apply oddQuotMk_eq_one_iff.mpr
    obtain ⟨o', ho', rfl⟩ := ho
    exact ho'
  have key : ∀ (u : G) (hu : u ∈ Subgroup.centralizer ({c} : Set G)),
      oddQuotMk c ⟨o * u * o⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hoC hu)
        (Subgroup.inv_mem _ hoC)⟩ = oddQuotMk c ⟨u, hu⟩ := by
    intro u hu
    have e : (⟨o * u * o⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hoC hu)
        (Subgroup.inv_mem _ hoC)⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
        ⟨o, hoC⟩ * ⟨u, hu⟩ * ⟨o, hoC⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, ho1]
    group
  ext y
  constructor
  · rintro ⟨⟨u, hu⟩, hmem, rfl⟩
    have hmem' : o⁻¹ * u * o⁻¹⁻¹ ∈ E := by
      have := (mem_conjSub_iff.mp hmem)
      simpa using this
    have huC : o⁻¹ * u * o⁻¹⁻¹ ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hoC) hu) (by simpa using hoC)
    refine ⟨⟨o⁻¹ * u * o⁻¹⁻¹, huC⟩, hmem', ?_⟩
    have := key (o⁻¹ * u * o⁻¹⁻¹) huC
    rw [← this]
    congr 2
    simp [mul_assoc]
  · rintro ⟨⟨u, hu⟩, hmem, rfl⟩
    refine ⟨⟨o * u * o⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hoC hu)
      (Subgroup.inv_mem _ hoC)⟩, conj_mem_conjSub hmem, key u hu⟩

end Basic

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem ChainCtx.exists_member_normalized (C : ChainCtx p f Ω z)
    (hT : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hBC : B ≤ Subgroup.centralizer ({z} : Set G)) {L : Subgroup G} (hL : L ∈ tqMembers Ω z)
    (hBL : ∀ x : G, ∀ hx : x ∈ B, ∀ y ∈ modOdd z (exactCore z L),
      oddQuotMk z ⟨x, hBC hx⟩ * y = y * oddQuotMk z ⟨x, hBC hx⟩) :
    ∃ L₁ ∈ tqMembers Ω z, modOdd z (exactCore z L₁) = modOdd z (exactCore z L) ∧
      B ≤ Subgroup.normalizer (L₁ : Set G) := by
  obtain ⟨w, hw⟩ := C.hΩ.classical L hL.1
  have hwE := C.involution_mem_exactCore hL hw
  have hwC := C.involution_mem_centralizer hL hw
  have hw2 : w * w = 1 := (isCentralInvolution_of_isClassicalMember hw).sq
  set Cz : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCz
  have hcomm : ∀ x ∈ B, (x * w * x⁻¹) * w ∈ oddCoreIn Cz := by
    intro x hx
    have hxC := hBC hx
    have h1 := hBL x hx _ (oddQuotMk_mem_modOdd hwE hwC)
    have hmem : (x * w * x⁻¹) * w ∈ Cz :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxC hwC) (Subgroup.inv_mem _ hxC))
        hwC
    have e : (⟨(x * w * x⁻¹) * w, hmem⟩ : ↥Cz) = ⟨x, hxC⟩ * ⟨w, hwC⟩ * ⟨x, hxC⟩⁻¹ * ⟨w, hwC⟩ := rfl
    have hwb2 : oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨w, hwC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨w, hwC⟩ : ↥Cz) * ⟨w, hwC⟩ = 1 := Subtype.ext hw2
      rw [this, map_one]
    have h2 : oddQuotMk z ⟨(x * w * x⁻¹) * w, hmem⟩ = 1 := by
      rw [e, map_mul, map_mul, map_mul, map_inv]
      calc oddQuotMk z ⟨x, hxC⟩ * oddQuotMk z ⟨w, hwC⟩ * (oddQuotMk z ⟨x, hxC⟩)⁻¹ *
          oddQuotMk z ⟨w, hwC⟩
          = (oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨x, hxC⟩) * (oddQuotMk z ⟨x, hxC⟩)⁻¹ *
            oddQuotMk z ⟨w, hwC⟩ := by rw [h1]
        _ = oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨w, hwC⟩ := by group
        _ = 1 := hwb2
    exact ⟨⟨_, hmem⟩, oddQuotMk_eq_one_iff.mp h2, rfl⟩
  have hBN : B ≤ Subgroup.normalizer (oddCoreIn Cz : Set G) :=
    fun x hx => normalizer_oddCoreIn Cz (hBC hx)
  have hB2 : IsPGroup 2 ↥B := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using hB.2 x x.2
  obtain ⟨o, ho, hcommo⟩ := exists_conj_involution_commuting (odd_card_oddCoreIn Cz) hBN hB2 hw2
    hcomm
  have hoC : o ∈ Cz := oddCoreIn_le _ ho
  have hoz : o * z * o⁻¹ = z := conj_eq_of_mem_centralizer_singleton hoC
  have hL1 : conjSub o L ∈ tqMembers Ω z := by
    refine ⟨C.hΩ.conjInvariant o L hL.1, ?_⟩
    have h := trivialOnQuot_conjSub hL.2 o
    rwa [hoz] at h
  have hw1 : IsClassicalMember p f (conjSub o L) (o * w * o⁻¹) := hw.conj o
  refine ⟨conjSub o L, hL1, ?_, fun x hx => ?_⟩
  · have h1 : exactCore z (conjSub o L) = conjSub o (exactCore z L) := by
      have := exactCore_conjSub o z L
      rwa [hoz] at this
    rw [h1]
    exact modOdd_conjSub_of_mem_oddCoreIn ho _
  · exact mem_normalizer_of_commutes_involution C.hΩ.conjInvariant hT hL1.1
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq hw1) (hcommo x hx)

theorem ChainCtx.exists_fund_big (C : ChainCtx p f Ω z)
    (hT : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {N : Subgroup G} (hN : N ∈ tqMembers Ω z)
    (hNK : N ≠ C.K) :
    ∃ R ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D,
      modOdd z (exactCore z N) = R.map (C.psi C.i₁) := by
  obtain ⟨κ, R, hR, hmod⟩ := C.exists_fund_of_mem hN
  rcases C.eq_i₀_or_i₁ κ with rfl | rfl
  · exfalso
    obtain ⟨w, hw⟩ := C.hΩ.classical N hN.1
    have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
    have hKN : C.K ∈ tqMembers Ω z := ⟨C.hK, C.hKtq⟩
    have hmod' : modOdd z (exactCore z N) = modOdd z (exactCore z C.K) := by
      rw [← hmod, C.fund_eq_top₀ hR, Subgroup.map_top, C.modOdd_K_eq_range]
    have hU1 := C.isUniqueInvolution_modOdd hN hw
    have hU2 := C.isUniqueInvolution_modOdd hKN hKcl
    rw [hmod'] at hU1
    have heq := hU1.eq hU2
    have hwC := C.involution_mem_centralizer hN hw
    have hwz : w = z := eq_of_oddQuotMk_eq' hwC ChainLift.hzC
      (isCentralInvolution_of_isClassicalMember hw).sq C.hz2
      (Subgroup.mem_centralizer_singleton_iff.mp hwC) heq
    subst hwz
    exact hNK (hT C.K C.hK N ⟨hN.1, w, C.hKz,
      ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq hw⟩)
  · exact ⟨R, hR, hmod.symm⟩

end Members

section Image

variable {K : Type} [Group K] {X : Type} [Group X]

theorem false_of_same_image (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K) {R R' : Subgroup K}
    (hperf : ⁅R, R⁆ = R) {x : K} (hx : x ∈ R) (hx1 : x ≠ 1)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R', r * s = s * r) (himg : R.map ψ = R'.map ψ) : False := by
  have hab : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ψ r₁ * ψ r₂ = ψ r₂ * ψ r₁ := by
    intro r₁ h₁ r₂ h₂
    have : ψ r₂ ∈ R'.map ψ := himg ▸ ⟨r₂, h₂, rfl⟩
    obtain ⟨s, hs, hsr⟩ := this
    rw [← hsr, ← map_mul, ← map_mul, hcomm r₁ h₁ s hs]
  have hcen : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ⁅r₁, r₂⁆ ∈ Subgroup.center K := by
    intro r₁ h₁ r₂ h₂
    apply hker
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      hab r₁ h₁ r₂ h₂]
    group
  have hRc : ∀ r ∈ R, r ∈ Subgroup.center K := by
    intro r hr
    rw [← hperf] at hr
    refine Subgroup.closure_induction (p := fun r _ => r ∈ Subgroup.center K) ?_ (one_mem _) ?_
      ?_ hr
    · rintro _ ⟨r₁, h₁, r₂, h₂, rfl⟩
      exact hcen r₁ h₁ r₂ h₂
    · intro a b _ _ ha hb
      exact mul_mem ha hb
    · intro a _ ha
      exact inv_mem ha
  have hbot : ⁅R, R⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro r₁ h₁ r₂ h₂
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hRc r₁ h₁) r₂).symm
  rw [hperf] at hbot
  exact hx1 (by simpa [hbot] using hx)

end Image

end CFSG.ClassicalInvolution.Asc77
