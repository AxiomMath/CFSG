module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.Frame
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.Consistency
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.P1Sylow
public import CFSG.Goldschmidt.Steps.Sec87c

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

theorem ys04c_of_centData (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP1 : IsConj z (z * ι τ₀)) : False := by
  obtain ⟨Q, hQ⟩ := exists_goodQ
  have hTpg : IsPGroup 2 (Tgrp z ι Q) := Tgrp_isPGroup hC hQ.pgroup
  have hidx : ¬ 2 ∣ (Tgrp z ι Q).index := not_two_dvd_index_Tgrp_P1 hC hx hP1 hQ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := hTpg.toSylow hidx
  have hScoe : (S : Subgroup G) = Tgrp z ι Q := by simp [S]
  have hzF : z ∈ Fgrp (Tgrp z ι Q) := (mem_Fgrp_iff hC hQ).mpr ⟨1, 0, 0, by simp⟩
  have hzρF : z * ι ρ₄ ∈ Fgrp (Tgrp z ι Q) := (mem_Fgrp_iff hC hQ).mpr ⟨1, 0, 1, by simp⟩
  have hz_cent : z ∈ centralizer ((Tgrp z ι Q) : Set G) := (Subgroup.mem_inf.mp hzF).1
  have hzρ_cent : z * ι ρ₄ ∈ centralizer ((Tgrp z ι Q) : Set G) :=
    (Subgroup.mem_inf.mp hzρF).1
  have hSb : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hScoe]
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hz_cent t ht
  have hζ : IsConj z (z * ι ρ₄) := isConj_z_mul_ρ₄ hC hx hP1
  obtain ⟨c, hc⟩ := isConj_iff.1 hζ
  let g : G := c⁻¹
  have hg : g⁻¹ * z * g = z * ι ρ₄ := by
    dsimp only [g]
    rw [inv_inv]
    exact hc
  have hSc : (S : Subgroup G) ≤ Subgroup.centralizer ({g⁻¹ * z * g} : Set G) := by
    rw [hg, hScoe]
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzρ_cent t ht
  obtain ⟨n, hn, hnconj⟩ :=
    CFSG.Goldschmidt.Sec8.exists_conj_normalizer_of_le (S := S) (b := z) (g := g) hSb hSc
  have hnT : n ∈ Subgroup.normalizer ((Tgrp z ι Q) : Set G) := by
    simpa only [hScoe] using hn
  have hn'T : n⁻¹ ∈ Subgroup.normalizer ((Tgrp z ι Q) : Set G) := Subgroup.inv_mem _ hnT
  have hmem : z * ι ρ₄ ∈ ({z, ι τ₀, z * ι τ₀} : Set G) := by
    have hpres := normalizer_Tgrp_preserves_Esharp hC hx hP1 hQ (g := n⁻¹) hn'T z (by simp)
    rwa [inv_inv, hnconj, hg] at hpres
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exfalso
    have h1 : ι ρ₄ = 1 := mul_left_cancel (by rw [mul_one]; exact h)
    have hρ : ρ₄ = 1 := hC.inj (by simpa using h1)
    exact absurd hρ (by decide)
  · exfalso
    have hιρ : ι ρ₄ = z * ι τ₀ := by
      calc ι ρ₄ = 1 * ι ρ₄ := by rw [one_mul]
        _ = (z * z) * ι ρ₄ := by rw [hC.mul_self]
        _ = z * (z * ι ρ₄) := by group
        _ = z * ι τ₀ := by rw [h]
    have hz : z = ι (ρ₄ * τ₀⁻¹) := by
      have h' : z = ι ρ₄ * (ι τ₀)⁻¹ := by
        calc z = z * 1 := by rw [mul_one]
          _ = z * (ι τ₀ * (ι τ₀)⁻¹) := by rw [mul_inv_cancel]
          _ = (z * ι τ₀) * (ι τ₀)⁻¹ := by group
          _ = ι ρ₄ * (ι τ₀)⁻¹ := by rw [← hιρ]
      rwa [← map_inv, ← map_mul] at h'
    exact hC.ne_z (ρ₄ * τ₀⁻¹) hz.symm
  · exfalso
    have hρτ : ρ₄ = τ₀ := hC.inj (mul_left_cancel h)
    exact absurd hρτ (by decide)

theorem ys04c {L Q : Subgroup G} {h : Setting G L 10} {d : Cyc L Q z}
    (F : SwapFrame h d ι) (hP1 : IsConj z (z * ι τ₀)) : False := by
  exact ys04c_of_centData F.cent F.conj hP1

end CFSG.OddStandard.AltStdSec.SwapPartner
