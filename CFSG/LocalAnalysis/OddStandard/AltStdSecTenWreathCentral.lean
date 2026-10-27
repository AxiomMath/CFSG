module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathFusion
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathTwoPart

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G} {x : G}

private theorem mul_self_eq_one_of_eq_tau0 (hx : x = ι τ₀) : x * x = 1 := by
  rw [hx, ← map_mul, τ₀_mul_self, map_one]

private theorem ne_one_of_eq_tau0 (hC : CentData z ι) (hx : x = ι τ₀) : x ≠ 1 := by
  intro h1
  have h2 : τ₀ = 1 := hC.inj (by rw [← hx, h1, map_one])
  have h3 : (9 : Fin 10) = 8 := by
    have h := congrArg (fun f : Perm (Fin 10) => f 8) h2
    rw [τ₀_apply_eight] at h
    simpa using h
  exact absurd h3 (by decide)

private theorem not_isConj_z_of_eq_tau0 (hN : NoSwapConj z ι) (hx : x = ι τ₀) :
    ¬ IsConj z x := by
  rw [hx]
  exact (hN τ₀ isSwap_τ₀).1

private theorem mk_selfC_eq_one :
    (QuotientGroup.mk (selfC x) : TwoSec x) = 1 :=
  (QuotientGroup.eq_one_iff (selfC x)).2 (Subgroup.mem_zpowers (selfC x))

private theorem zbar_mul_self (hC : CentData z ι) (hx : x = ι τ₀) :
    zbar hC hx * zbar hC hx = 1 := by
  have h : (⟨z, z_mem_centralizer_of_eq hC hx⟩ : ↥(centralizer ({x} : Set G))) *
      ⟨z, z_mem_centralizer_of_eq hC hx⟩ = 1 := Subtype.ext hC.mul_self
  change (QuotientGroup.mk' (zpowers (selfC x)))
        (⟨z, z_mem_centralizer_of_eq hC hx⟩ : ↥(centralizer ({x} : Set G))) *
      (QuotientGroup.mk' (zpowers (selfC x)))
        (⟨z, z_mem_centralizer_of_eq hC hx⟩ : ↥(centralizer ({x} : Set G))) = 1
  rw [← map_mul, h, map_one]

private theorem sigmaX_mul_self_of_isSwap (hx : x = ι τ₀) {ρ : Perm (Fin 8)}
    (hρ : ρ.IsSwap) : sigmaX (ι := ι) hx ρ * sigmaX (ι := ι) hx ρ = 1 := by
  obtain ⟨a, b, _hab, hρab⟩ := hρ
  rw [← map_mul, hρab, swap_mul_self, map_one]

theorem exists_swap_of_isConj (hC : CentData z ι) (hN : NoSwapConj z ι) (hx : x = ι τ₀)
    (hO : CFSG.oddCore (TwoSec x) = ⊥) {K : Subgroup (TwoSec x)}
    (hE : ExactShape (zbar hC hx) (diagSub (ι := ι) hx) 8)
    (hK : WreathK (zbar hC hx) (diagSub (ι := ι) hx) K) {u : G} (hu : IsConj x u)
    (hzu : z * u = u * z) (hxu : x * u = u * x) :
    ∃ σ : Perm (Fin 10), σ.IsSwap ∧ σ * τ₀ = τ₀ * σ ∧ (u = ι σ ∨ u = z * ι σ) := by
  have hx2 : x * x = 1 := mul_self_eq_one_of_eq_tau0 hx
  have hx1 : x ≠ 1 := ne_one_of_eq_tau0 hC hx
  have hxz : ¬ IsConj z x := not_isConj_z_of_eq_tau0 hN hx
  obtain ⟨g, hg_eq⟩ := isConj_iff.1 hu
  have hg : g⁻¹ * z * g ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h := congrArg (fun y : G => g⁻¹ * y * g) hzu
    rw [← hg_eq] at h
    calc (g⁻¹ * z * g) * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * z) * g := h
      _ = x * (g⁻¹ * z * g) := by group
  have hmk := mk_conj_notMem_normalizer hC hN hx hO hE hK g hg
  obtain ⟨σ, hσ2, _hσ1, hk1, hk5, hux, hpair⟩ := exists_perm_of_conj_mem hC hx2 hx1 hxz g hg
  have hN10 : N10 (Multiset.card σ.cycleType) = N10 1 := by rw [← hpair, hmk.2]
  have hk_eq : Multiset.card σ.cycleType = 1 := eq_one_of_N10_eq_N10_one hk1 hk5 hN10
  have hσswap : σ.IsSwap := isSwap_of_card_cycleType_eq_one hσ2 hk_eq
  have hσcomm : σ * τ₀ = τ₀ * σ := by
    rcases hux with h | h
    · have huι : u = ι σ := by rw [← hg_eq]; exact h
      have hc : ι (τ₀ * σ) = ι (σ * τ₀) := by
        have h1 := hxu
        rw [hx, huι] at h1
        simpa only [map_mul] using h1
      exact (hC.inj hc).symm
    · have huz : u = z * ι σ := by rw [← hg_eq]; exact h
      have hc : ι (τ₀ * σ) = ι (σ * τ₀) := by
        have h1 := hxu
        rw [hx, huz] at h1
        have h2 : z * ι (τ₀ * σ) = z * ι (σ * τ₀) := by
          calc z * ι (τ₀ * σ) = z * (ι τ₀ * ι σ) := by rw [map_mul]
            _ = (z * ι τ₀) * ι σ := by group
            _ = (ι τ₀ * z) * ι σ := by rw [hC.comm τ₀]
            _ = ι τ₀ * (z * ι σ) := by group
            _ = (z * ι σ) * ι τ₀ := h1
            _ = z * (ι σ * ι τ₀) := by group
            _ = z * ι (σ * τ₀) := by rw [map_mul]
        exact mul_left_cancel h2
      exact (hC.inj hc).symm
  have huσ' : u = ι σ ∨ u = z * ι σ := by
    rcases hux with h | h
    · exact Or.inl (by rw [← hg_eq]; exact h)
    · exact Or.inr (by rw [← hg_eq]; exact h)
  exact ⟨σ, hσswap, hσcomm, huσ'⟩

theorem exists_sylow_le_centralizer_mk {T₁ : Subgroup G} (hT₁x : T₁ ≤ centralizer ({x} : Set G))
    (hT₁ : IsPGroup 2 T₁)
    (hidx : ¬ 2 ∣ (T₁.subgroupOf (centralizer ({x} : Set G))).index) {u : G}
    (hu₁ : u ∈ T₁) (hu₂ : ∀ p ∈ T₁, p * u = u * p) :
    ∃ T : Subgroup (TwoSec x), IsPGroup 2 T ∧ ¬ 2 ∣ T.index ∧
      T ≤ centralizer ({(QuotientGroup.mk ⟨u, hT₁x hu₁⟩ : TwoSec x)} : Set (TwoSec x)) := by
  let C : Subgroup G := centralizer ({x} : Set G)
  let ψ : ↥C →* TwoSec x := QuotientGroup.mk' (zpowers (selfC x))
  refine ⟨(T₁.subgroupOf C).map ψ, ?_, ?_, ?_⟩
  · exact (hT₁.of_equiv (Subgroup.subgroupOfEquivOfLe hT₁x).symm).map ψ
  · exact not_two_dvd_index_map_of_surjective ψ
      (QuotientGroup.mk'_surjective (N := zpowers (selfC x))) hidx
  · intro t ht
    rw [Subgroup.mem_map] at ht
    obtain ⟨p, hpP, rfl⟩ := ht
    rw [mem_centralizer_singleton_iff]
    change ψ p * ψ (⟨u, hT₁x hu₁⟩ : ↥C) = ψ (⟨u, hT₁x hu₁⟩ : ↥C) * ψ p
    have hpu : p * (⟨u, hT₁x hu₁⟩ : ↥C) = (⟨u, hT₁x hu₁⟩ : ↥C) * p := by
      apply Subtype.ext
      show (p : G) * u = u * (p : G)
      exact hu₂ (p : G) (Subgroup.mem_subgroupOf.mp hpP)
    rw [← map_mul, ← map_mul, hpu]

theorem eq_of_mem_fgrp_of_isConj (hC : CentData z ι) (hN : NoSwapConj z ι) (hx : x = ι τ₀)
    (hO : CFSG.oddCore (TwoSec x) = ⊥) {K : Subgroup (TwoSec x)}
    (hE : ExactShape (zbar hC hx) (diagSub (ι := ι) hx) 8)
    (hK : WreathK (zbar hC hx) (diagSub (ι := ι) hx) K) {T₁ : Subgroup G}
    (hT₁x : T₁ ≤ centralizer ({x} : Set G)) (hT₁ : IsPGroup 2 T₁) (hzT : z ∈ T₁)
    (hidx : ¬ 2 ∣ (T₁.subgroupOf (centralizer ({x} : Set G))).index) {u : G}
    (hu₁ : u ∈ T₁) (hu₂ : ∀ p ∈ T₁, p * u = u * p) (hconj : IsConj x u) : u = x := by
  have hzu : z * u = u * z := hu₂ z hzT
  have hxu : x * u = u * x := (mem_centralizer_singleton_iff.1 (hT₁x hu₁)).symm
  obtain ⟨σ, hσswap, hσcomm, huσ⟩ :=
    exists_swap_of_isConj hC hN hx hO hE hK hconj hzu hxu
  obtain ⟨T, hTp, hTidx, hTc⟩ := exists_sylow_le_centralizer_mk hT₁x hT₁ hidx hu₁ hu₂
  rcases eq_τ₀_or_mem_stab2_of_isSwap hσswap hσcomm with hστ | hσstab
  · rcases huσ with huι | huz
    · rw [huι, hστ]
      exact hx.symm
    · exfalso
      have hū : (QuotientGroup.mk ⟨u, hT₁x hu₁⟩ : TwoSec x) = zbar hC hx := by
        let C : Subgroup G := centralizer ({x} : Set G)
        let ψ : ↥C →* TwoSec x := QuotientGroup.mk' (zpowers (selfC x))
        have hψz : ψ (⟨z, z_mem_centralizer_of_eq hC hx⟩ : ↥C) = zbar hC hx := rfl
        have hψx : ψ (selfC x) = 1 := mk_selfC_eq_one
        have h₁ : (⟨u, hT₁x hu₁⟩ : ↥C) =
            (⟨z, z_mem_centralizer_of_eq hC hx⟩ : ↥C) * selfC x := by
          apply Subtype.ext
          rw [Subgroup.coe_mul]
          show u = z * x
          rw [huz, hστ, hx]
        calc (QuotientGroup.mk ⟨u, hT₁x hu₁⟩ : TwoSec x)
            = ψ (⟨u, hT₁x hu₁⟩ : ↥C) := rfl
          _ = ψ ((⟨z, z_mem_centralizer_of_eq hC hx⟩ : ↥C) * selfC x) := by rw [h₁]
          _ = ψ (⟨z, z_mem_centralizer_of_eq hC hx⟩ : ↥C) * ψ (selfC x) := map_mul _ _ _
          _ = zbar hC hx * 1 := by rw [hψz, hψx]
          _ = zbar hC hx := mul_one _
      have hTc' : T ≤ centralizer ({zbar hC hx} : Set (TwoSec x)) := hū ▸ hTc
      exact WreathK.not_le_centralizer_of_two_part hK (zbar_mul_self hC hx) rfl
        (Or.inl (WreathK.t_notMem_normalizer hK)) hTp hTidx hTc'
  · exfalso
    obtain ⟨ρ, hρswap, hlift⟩ := exists_isSwap_liftS8_eq hσswap hσstab
    rcases huσ with huι | huz
    · have hū : (QuotientGroup.mk ⟨u, hT₁x hu₁⟩ : TwoSec x) = sigmaX (ι := ι) hx ρ := by
        have h₁ : (⟨u, hT₁x hu₁⟩ : ↥(centralizer ({x} : Set G))) =
            liftS8Centralizer (ι := ι) hx ρ := by
          apply Subtype.ext
          rw [liftS8Centralizer_apply]
          show u = ι (liftS8 ρ)
          rw [huι, ← hlift]
        calc QuotientGroup.mk ⟨u, hT₁x hu₁⟩
            = QuotientGroup.mk (liftS8Centralizer (ι := ι) hx ρ) := congrArg QuotientGroup.mk h₁
          _ = sigmaX (ι := ι) hx ρ := rfl
      have hTc' : T ≤ centralizer ({sigmaX (ι := ι) hx ρ} : Set (TwoSec x)) := hū ▸ hTc
      exact WreathK.not_le_centralizer_of_two_part hK
        (sigmaX_mul_self_of_isSwap (ι := ι) hx hρswap)
        (zbar_comm_sigmaX hC hx ρ).symm
        (Or.inr (card_diagSub_inf_centralizer_swap hC hx hρswap)) hTp hTidx hTc'
    · have hū : (QuotientGroup.mk ⟨u, hT₁x hu₁⟩ : TwoSec x) =
          zbar hC hx * sigmaX (ι := ι) hx ρ := by
        have h₁ : (⟨u, hT₁x hu₁⟩ : ↥(centralizer ({x} : Set G))) =
            (⟨z, z_mem_centralizer_of_eq hC hx⟩ : ↥(centralizer ({x} : Set G))) *
              liftS8Centralizer (ι := ι) hx ρ := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, liftS8Centralizer_apply]
          show u = z * ι (liftS8 ρ)
          rw [huz, ← hlift]
        calc QuotientGroup.mk ⟨u, hT₁x hu₁⟩
            = QuotientGroup.mk ((⟨z, z_mem_centralizer_of_eq hC hx⟩ :
                ↥(centralizer ({x} : Set G))) * liftS8Centralizer (ι := ι) hx ρ) :=
                congrArg QuotientGroup.mk h₁
          _ = QuotientGroup.mk (⟨z, z_mem_centralizer_of_eq hC hx⟩ :
                ↥(centralizer ({x} : Set G))) *
                QuotientGroup.mk (liftS8Centralizer (ι := ι) hx ρ) := by
                rw [QuotientGroup.mk_mul]
          _ = zbar hC hx * sigmaX (ι := ι) hx ρ := rfl
      have hz2 : zbar hC hx * zbar hC hx = 1 := zbar_mul_self hC hx
      have hρ2 : sigmaX (ι := ι) hx ρ * sigmaX (ι := ι) hx ρ = 1 :=
        sigmaX_mul_self_of_isSwap (ι := ι) hx hρswap
      have hcomm : zbar hC hx * sigmaX (ι := ι) hx ρ =
          sigmaX (ι := ι) hx ρ * zbar hC hx := zbar_comm_sigmaX hC hx ρ
      have hs2 : (zbar hC hx * sigmaX (ι := ι) hx ρ) *
          (zbar hC hx * sigmaX (ι := ι) hx ρ) = 1 := by
        calc (zbar hC hx * sigmaX (ι := ι) hx ρ) * (zbar hC hx * sigmaX (ι := ι) hx ρ)
            = zbar hC hx * (sigmaX (ι := ι) hx ρ * zbar hC hx) *
                sigmaX (ι := ι) hx ρ := by group
          _ = zbar hC hx * (zbar hC hx * sigmaX (ι := ι) hx ρ) *
                sigmaX (ι := ι) hx ρ := by rw [← hcomm]
          _ = (zbar hC hx * zbar hC hx) *
                (sigmaX (ι := ι) hx ρ * sigmaX (ι := ι) hx ρ) := by group
          _ = 1 := by rw [hz2, hρ2, one_mul]
      have hst : (zbar hC hx * sigmaX (ι := ι) hx ρ) * zbar hC hx =
          zbar hC hx * (zbar hC hx * sigmaX (ι := ι) hx ρ) := by
        calc (zbar hC hx * sigmaX (ι := ι) hx ρ) * zbar hC hx
            = zbar hC hx * (sigmaX (ι := ι) hx ρ * zbar hC hx) := by group
          _ = zbar hC hx * (zbar hC hx * sigmaX (ι := ι) hx ρ) := by rw [← hcomm]
      have hTc' : T ≤ centralizer ({zbar hC hx * sigmaX (ι := ι) hx ρ} :
          Set (TwoSec x)) := hū ▸ hTc
      exact WreathK.not_le_centralizer_of_two_part hK hs2 hst
        (Or.inr (card_diagSub_inf_centralizer_zbar_mul_swap hC hx hρswap)) hTp hTidx hTc'

theorem exists_sylow_central (hC : CentData z ι) (hN : NoSwapConj z ι) (hx : x = ι τ₀)
    (hO : CFSG.oddCore (TwoSec x) = ⊥) {K : Subgroup (TwoSec x)}
    (hE : ExactShape (zbar hC hx) (diagSub (ι := ι) hx) 8)
    (hK : WreathK (zbar hC hx) (diagSub (ι := ι) hx) K) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ ¬ 2 ∣ T.index ∧ T ≤ centralizer ({x} : Set G) ∧ z ∈ T := by
  have hx2 : x * x = 1 := mul_self_eq_one_of_eq_tau0 hx
  obtain ⟨T₁, hT₁x, hT₁, hidx, hzT, hxT⟩ :=
    exists_sylow_two_centralizer hx2 (z_mem_centralizer_of_eq hC hx) hC.mul_self
  refine ⟨T₁, hT₁, ?_, hT₁x, hzT⟩
  refine not_two_dvd_index_of_fgrp_conj hT₁ hT₁x hidx hxT ?_
  intro u hu huconj
  have hu_inf : u ∈ centralizer (T₁ : Set G) ⊓ T₁ := hu
  exact eq_of_mem_fgrp_of_isConj hC hN hx hO hE hK hT₁x hT₁ hzT hidx hu_inf.2
    (fun p hp => (Subgroup.mem_centralizer_iff.1 hu_inf.1) p hp) huconj

end CFSG.OddStandard.AltStdSec.SwapPattern
