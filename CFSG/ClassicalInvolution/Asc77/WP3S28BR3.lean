module

public import CFSG.ClassicalInvolution.Asc77.WP3S28BR3Z
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
public import CFSG.ClassicalInvolution.Asc77.WP3SCVPart


public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28B

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.SCV CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

section Rank3

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

theorem rank3_model_facts (hp2 : p ≠ 2) :
    ∀ (t : StatedLieTag) (n e : ℕ), (t = .PSL ∨ t = .PSU) → n = 3 → 5 ≤ p ^ e →
      StatedLieAdmissible t n p e →
      ⁅(⊤ : Subgroup (modelUniv t n p e Fact.out).K),
          (⊤ : Subgroup (modelUniv t n p e Fact.out).K)⁆ = ⊤ ∧
        ∀ g ∈ Subgroup.center (modelUniv t n p e Fact.out).K, g * g = 1 → g = 1 := by
  intro t n e ht hn hq hadm
  subst hn
  refine ⟨?_, fun g hg h2 => center_no_involution_rank3 hp2 hq ht hadm hg h2⟩
  have hfund : IsFundTag t := by rcases ht with rfl | rfl <;> trivial
  exact (ModelFacts.modelClauseZero t 3 p e Fact.out hfund hadm).1.1

theorem no_third_member_rank3_of_ctx (C : ChainCtx p f Ω z) (hr : C.D.rank C.i₁ = 3)
    {J N : Subgroup G} {t w : G} (hJΩ : J ∈ Ω) (hJt : IsUniqueInvolution J t)
    (hzJ : z ∈ trivialOnQuot J) (hNΩ : N ∈ Ω) (hw : IsUniqueInvolution N w)
    (hzN : z ∈ trivialOnQuot N) (htN : t ∈ trivialOnQuot N) (hNK : N ≠ C.K) (htz : t ≠ z)
    (htw : t * w = w * t) (hNJ : N ≠ J)
    (hnoTwins : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) : False := by
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  have hNcl : IsClassicalMember p f N w := isClassicalMember_of_twin C.hΩ hNΩ hw
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin C.hΩ hJΩ hJt
  have hNtq : N ∈ tqMembers Ω z := ExactLayer.mem_tqMembers_iff.mpr ⟨hNΩ, hzN⟩
  have hJtq : J ∈ tqMembers Ω z := ExactLayer.mem_tqMembers_iff.mpr ⟨hJΩ, hzJ⟩
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) := C.involution_mem_centralizer hJtq hJcl
  have hwC : w ∈ Subgroup.centralizer ({z} : Set G) := C.involution_mem_centralizer hNtq hNcl
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hi0 : ∀ {M : Subgroup G} {a : G}, M ∈ tqMembers Ω z → IsClassicalMember p f M a →
      ∀ {R : Subgroup (compModel C.D C.i₀).K},
        R ∈ fundamentalSubgroups (C.D.tag C.i₀) (compModel C.D C.i₀).D →
        R.map (C.psi C.i₀) = modOdd z (exactCore z M) → a = z := by
    intro M a hM ha R hR hmod
    have hR' := C.fund_eq_top₀ hR
    have hmod' : modOdd z (exactCore z M) = modOdd z (exactCore z C.K) := by
      rw [← hmod, hR', Subgroup.map_top, C.modOdd_K_eq_range]
    have hU1 := C.isUniqueInvolution_modOdd hM ha
    have hU2 := C.isUniqueInvolution_modOdd ⟨C.hK, C.hKtq⟩ hKcl
    rw [hmod'] at hU1
    have heq := hU1.eq hU2
    have haC := C.involution_mem_centralizer hM ha
    have hza : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haC
    have ha2 : a * a = 1 := (isCentralInvolution_of_isClassicalMember ha).sq
    have hx2 : (⟨a * z, Subgroup.mul_mem _ haC hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) *
        ⟨a * z, Subgroup.mul_mem _ haC hzC⟩ = 1 := by
      apply Subtype.ext
      show a * z * (a * z) = 1
      calc a * z * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [← hza]
        _ = (a * a) * (z * z) := by group
        _ = 1 := by rw [ha2, hKcl.isCentralInvolution.sq, one_mul]
    have hx1 : oddQuotMk z ⟨a * z, Subgroup.mul_mem _ haC hzC⟩ = 1 := by
      have e : (⟨a * z, Subgroup.mul_mem _ haC hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
          ⟨a, haC⟩ * ⟨z, hzC⟩ := rfl
      rw [e, map_mul, heq, ← map_mul]
      have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨z, hzC⟩ = 1 :=
        Subtype.ext hKcl.isCentralInvolution.sq
      rw [this, map_one]
    have h1 := eq_one_of_oddQuotMk_eq_one hx2 hx1
    have h1' : a * z = 1 := congrArg Subtype.val h1
    rw [eq_inv_of_mul_eq_one_left h1']
    exact inv_eq_of_mul_eq_one_right hKcl.isCentralInvolution.sq
  obtain ⟨kN, RN, hRN, hmodN⟩ := C.exists_fund_of_mem hNtq
  obtain ⟨kJ, RJ, hRJ, hmodJ⟩ := C.exists_fund_of_mem hJtq
  rcases C.eq_i₀_or_i₁ kJ with hkJ | hkJ
  · subst hkJ
    exact htz (hi0 hJtq hJcl hRJ hmodJ)
  rcases C.eq_i₀_or_i₁ kN with hkN | hkN
  · subst hkN
    exact hNK (hnoTwins C.K C.hK N ⟨hNΩ, z, C.hKz, (hi0 hNtq hNcl hRN hmodN) ▸ hw⟩)
  subst hkJ
  subst hkN
  obtain ⟨xN, hxNR, hxNc, hxN1, hxNbar⟩ :=
    C.exists_central_lift hNtq hNcl C.i₁ C.tag₁ hRN hmodN.symm
  obtain ⟨xJ, hxJR, hxJc, hxJ1, hxJbar⟩ :=
    C.exists_central_lift hJtq hJcl C.i₁ C.tag₁ hRJ hmodJ.symm
  have hquasi : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z N)) := by
    rw [← hmodN]
    exact isQuasisimple_map_of_ker_le_center _ (C.psi_ker C.i₁)
      (fundQuasisimple_core C.hp (C.D.isFundTag C.i₁) (C.D.admissible C.i₁)
        (C.four_le C.i₁ C.tag₁) RN hRN)
  have hcen := oddQuotMk_centralizes_modOdd_exactCore hNcl C.hc2 hzN htN htC hquasi
  have hvR : ∀ s ∈ RN, oddQuotMk z ⟨t, htC⟩ * C.psi C.i₁ s =
      C.psi C.i₁ s * oddQuotMk z ⟨t, htC⟩ := by
    intro s hs
    apply hcen
    rw [← hmodN]
    exact ⟨s, hs, rfl⟩
  have htt : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨t, htC⟩ = 1 :=
    Subtype.ext hJt.sq
  have hww : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨w, hwC⟩ = 1 :=
    Subtype.ext hw.sq
  have hv2 : oddQuotMk z ⟨t, htC⟩ * oddQuotMk z ⟨t, htC⟩ = 1 := by
    rw [← map_mul, htt, map_one]
  have hvmem : oddQuotMk z ⟨t, htC⟩ ∈ (C.psi C.i₁).range := ⟨xJ, hxJbar.symm⟩
  have hv : oddQuotMk z ⟨t, htC⟩ ∈
      Subgroup.normalizer (((C.psi C.i₁).range : Subgroup (OddQuot z)) : Set (OddQuot z)) :=
    Subgroup.le_normalizer hvmem
  obtain ⟨hperf, hnoinv⟩ := rank3_model_facts C.hp (C.D.tag C.i₁) (C.D.rank C.i₁) (C.D.exp C.i₁)
    C.tag₁ hr (by rw [C.exp_eq C.i₁ C.tag₁]; exact C.hq) (C.D.admissible C.i₁)
  have hfin : Finite (compModel C.D C.i₁).K :=
    ModelFacts.finite_modelUniv C.hp Fact.out (C.D.isFundTag C.i₁) (C.D.admissible C.i₁)
  rcases C.rank3_involution hr hRN hxNR hxNc hxN1 hv hv2 hvR with h | h
  ·
    have hx1 : (C.psi C.i₁) xJ = 1 := by
      refine image_trivial_of_central_involution (C.psi C.i₁) (C.psi_ker C.i₁) hperf hnoinv
        (u := xJ) (fun g => ?_) ?_
      · rw [← hxJbar]
        exact h _ ⟨g, rfl⟩
      · rw [← hxJbar]
        exact hv2
    rw [← hxJbar] at hx1
    have := eq_one_of_oddQuotMk_eq_one htt hx1
    exact hJt.ne_one (congrArg Subtype.val this)
  ·
    have hcomm : oddQuotMk z ⟨t, htC⟩ * oddQuotMk z ⟨w, hwC⟩ =
        oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨t, htC⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk z) (Subtype.ext htw)
    have hx1 : (C.psi C.i₁) (xJ * xN) = 1 := by
      refine image_trivial_of_central_involution (C.psi C.i₁) (C.psi_ker C.i₁) hperf hnoinv
        (u := xJ * xN) (fun g => ?_) ?_
      · rw [map_mul, ← hxJbar]
        exact h _ ⟨g, rfl⟩
      · rw [map_mul, ← hxJbar, ← hxNbar]
        calc oddQuotMk z ⟨t, htC⟩ * oddQuotMk z ⟨w, hwC⟩ *
              (oddQuotMk z ⟨t, htC⟩ * oddQuotMk z ⟨w, hwC⟩)
            = oddQuotMk z ⟨t, htC⟩ * (oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨t, htC⟩) *
                oddQuotMk z ⟨w, hwC⟩ := by group
          _ = oddQuotMk z ⟨t, htC⟩ * (oddQuotMk z ⟨t, htC⟩ * oddQuotMk z ⟨w, hwC⟩) *
                oddQuotMk z ⟨w, hwC⟩ := by rw [hcomm]
          _ = (oddQuotMk z ⟨t, htC⟩ * oddQuotMk z ⟨t, htC⟩) *
                (oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨w, hwC⟩) := by group
          _ = 1 := by
            rw [← map_mul, ← map_mul, htt, hww, map_one, one_mul]
    rw [map_mul, ← hxJbar, ← hxNbar] at hx1
    have hx2 : (⟨t, htC⟩ * ⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) *
        (⟨t, htC⟩ * ⟨w, hwC⟩) = 1 := by
      have e : (⟨t, htC⟩ * ⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
          ⟨w, hwC⟩ * ⟨t, htC⟩ := Subtype.ext htw
      calc (⟨t, htC⟩ * ⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) *
            (⟨t, htC⟩ * ⟨w, hwC⟩)
          = ⟨t, htC⟩ * (⟨w, hwC⟩ * ⟨t, htC⟩) * ⟨w, hwC⟩ := by group
        _ = ⟨t, htC⟩ * (⟨t, htC⟩ * ⟨w, hwC⟩) * ⟨w, hwC⟩ := by rw [e]
        _ = (⟨t, htC⟩ * ⟨t, htC⟩) * (⟨w, hwC⟩ * ⟨w, hwC⟩ :
              ↥(Subgroup.centralizer ({z} : Set G))) := by group
        _ = 1 := by rw [htt, hww, one_mul]
    have hx3 : oddQuotMk z (⟨t, htC⟩ * ⟨w, hwC⟩) = 1 := by rw [map_mul]; exact hx1
    have h4 := eq_one_of_oddQuotMk_eq_one hx2 hx3
    have h5 : t * w = 1 := congrArg Subtype.val h4
    have hwt : w = t := by
      rw [eq_inv_of_mul_eq_one_right h5]
      exact inv_eq_of_mul_eq_one_right hJt.sq
    exact hNJ (hnoTwins J hJΩ N ⟨hNΩ, t, hJt, hwt ▸ hw⟩)

theorem no_third_member_rank3 (hs : ChainFrameSetting p f Ω K J K' z t z')
    (hr3 : ChainShapeRank p f 3 Ω z) {N : Subgroup G} (hN : N ∈ Ω) (hNK : N ≠ K) (hNJ : N ≠ J)
    (hzN : z ∈ trivialOnQuot N) (htN : t ∈ trivialOnQuot N) {w : G}
    (hw : IsUniqueInvolution N w) : False := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hr3
  have hpair : ChainPair (fundamentalSubgroups (D.tag i₁) (compModel D i₁).D) :=
    chainPair_model hs.odd (D.tag i₁) (D.rank i₁) (D.exp i₁) ht₁ (by omega) (D.admissible i₁)
  have htw : t * w = w * t := by
    have := conj_eq_of_isUniqueInvolution hw htN.1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  exact no_third_member_rank3_of_ctx
    { K := K, hK := hs.frame.mem, hKz := hs.frame.hz, hΩ := hs.hyp, hp := hs.odd, hq := hs.five,
      D := D, card_eq := hcard, i₀ := i₀, i₁ := i₁, ne := hne, tag₁ := ht₁, tag₀ := ht₀,
      rank₀ := hr₀, pair := hpair }
    hr₁ hs.frame.memJ hs.frame.ht (hs.frame.tq_z_J hs.odd hs.five hs.hyp) hN hw hzN htN hNK
    (hs.frame.t_ne_z hs.odd hs.five hs.hyp) htw hNJ hs.noTwins

theorem thirdZTMod_of_rank3 (hs : ChainFrameSetting p f Ω K J K' z t z')
    (hr3 : ChainShapeRank p f 3 Ω z) {N : Subgroup G} (hN : N ∈ Ω) (hNK : N ≠ K) (hNJ : N ≠ J)
    (hzN : z ∈ trivialOnQuot N) (htN : t ∈ trivialOnQuot N) {w : G}
    (hw : IsUniqueInvolution N w) :
    z * t * w ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
  (no_third_member_rank3 hs hr3 hN hNK hNJ hzN htN hw).elim

end Rank3

end CFSG.ClassicalInvolution.Asc77.S28B
