module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.FrameD

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem tw_swap01_mul_self (f : Perm (Fin 10) →* G) :
    f (swap 0 1) * f (swap 0 1) = 1 := by
  have h : (swap 0 1 : Perm (Fin 10)) * swap 0 1 = 1 := by decide
  calc f (swap 0 1) * f (swap 0 1)
      = f ((swap 0 1 : Perm (Fin 10)) * swap 0 1) :=
        (map_mul f (swap 0 1) (swap 0 1)).symm
    _ = f 1 := by rw [h]
    _ = 1 := map_one f

private theorem tw_swap01_comm_τ₀ (f : Perm (Fin 10) →* G) :
    f (swap 0 1) * f τ₀ = f τ₀ * f (swap 0 1) := by
  simp only [← map_mul]
  congr 1
  decide

private theorem tw_liftS8_apply_castLE (ρ : Perm (Fin 8)) (j : Fin 8) :
    liftS8 ρ (Fin.castLE (by norm_num : 8 ≤ 10) j) =
      Fin.castLE (by norm_num : 8 ≤ 10) (ρ j) := by
  show ρ.viaEmbedding (Fin.castLEEmb (by norm_num : 8 ≤ 10))
      (Fin.castLE (by norm_num : 8 ≤ 10) j) =
    Fin.castLE (by norm_num : 8 ≤ 10) (ρ j)
  exact Equiv.Perm.viaEmbedding_apply ρ (Fin.castLEEmb (by norm_num : 8 ≤ 10)) j

private theorem tw_liftS8_apply_castLE_self {ρ : Perm (Fin 8)} {j : Fin 8} (hj : ρ j = j) :
    liftS8 ρ (Fin.castLE (by norm_num : 8 ≤ 10) j) =
      Fin.castLE (by norm_num : 8 ≤ 10) j := by
  rw [tw_liftS8_apply_castLE, hj]

private theorem tw_liftS8_apply_zero {ρ : Perm (Fin 8)} (h0 : ρ 0 = 0) :
    liftS8 ρ (0 : Fin 10) = 0 :=
  tw_liftS8_apply_castLE_self (ρ := ρ) (j := (0 : Fin 8)) h0

private theorem tw_liftS8_apply_one {ρ : Perm (Fin 8)} (h1 : ρ 1 = 1) :
    liftS8 ρ (1 : Fin 10) = 1 :=
  tw_liftS8_apply_castLE_self (ρ := ρ) (j := (1 : Fin 8)) h1

private def tw_c1 : Perm (Fin 8) := swap 2 3 * swap 3 4

private def tw_c2 : Perm (Fin 8) := swap 2 5 * swap 5 6

private def tw_c3 : Perm (Fin 8) := swap 3 5 * swap 5 7

private def tw_c4 : Perm (Fin 8) := swap 4 6 * swap 6 7

private theorem tw_liftS8_c1 : liftS8 tw_c1 = swap 2 3 * swap 3 4 := by
  rw [tw_c1]
  simp only [map_mul, liftS8_swap]
  decide

private theorem tw_liftS8_c2 : liftS8 tw_c2 = swap 2 5 * swap 5 6 := by
  rw [tw_c2]
  simp only [map_mul, liftS8_swap]
  decide

private theorem tw_liftS8_c3 : liftS8 tw_c3 = swap 3 5 * swap 5 7 := by
  rw [tw_c3]
  simp only [map_mul, liftS8_swap]
  decide

private theorem tw_liftS8_c4 : liftS8 tw_c4 = swap 4 6 * swap 6 7 := by
  rw [tw_c4]
  simp only [map_mul, liftS8_swap]
  decide

private theorem tw_support_c1 : (liftS8 tw_c1).support = ({2, 3, 4} : Finset (Fin 10)) := by
  rw [tw_liftS8_c1]; decide

private theorem tw_support_c2 : (liftS8 tw_c2).support = ({2, 5, 6} : Finset (Fin 10)) := by
  rw [tw_liftS8_c2]; decide

private theorem tw_support_c3 : (liftS8 tw_c3).support = ({3, 5, 7} : Finset (Fin 10)) := by
  rw [tw_liftS8_c3]; decide

private theorem tw_support_c4 : (liftS8 tw_c4).support = ({4, 6, 7} : Finset (Fin 10)) := by
  rw [tw_liftS8_c4]; decide

private theorem tw_c1_even : tw_c1 ∈ alternatingGroup (Fin 8) := by
  rw [tw_c1]
  exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    ⟨2, 3, by decide, rfl⟩ ⟨3, 4, by decide, rfl⟩

private theorem tw_c2_even : tw_c2 ∈ alternatingGroup (Fin 8) := by
  rw [tw_c2]
  exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    ⟨2, 5, by decide, rfl⟩ ⟨5, 6, by decide, rfl⟩

private theorem tw_c3_even : tw_c3 ∈ alternatingGroup (Fin 8) := by
  rw [tw_c3]
  exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    ⟨3, 5, by decide, rfl⟩ ⟨5, 7, by decide, rfl⟩

private theorem tw_c4_even : tw_c4 ∈ alternatingGroup (Fin 8) := by
  rw [tw_c4]
  exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    ⟨4, 6, by decide, rfl⟩ ⟨6, 7, by decide, rfl⟩

private theorem tw_c1_zero : tw_c1 0 = 0 := by rw [tw_c1]; decide
private theorem tw_c1_one : tw_c1 1 = 1 := by rw [tw_c1]; decide
private theorem tw_c2_zero : tw_c2 0 = 0 := by rw [tw_c2]; decide
private theorem tw_c2_one : tw_c2 1 = 1 := by rw [tw_c2]; decide
private theorem tw_c3_zero : tw_c3 0 = 0 := by rw [tw_c3]; decide
private theorem tw_c3_one : tw_c3 1 = 1 := by rw [tw_c3]; decide
private theorem tw_c4_zero : tw_c4 0 = 0 := by rw [tw_c4]; decide
private theorem tw_c4_one : tw_c4 1 = 1 := by rw [tw_c4]; decide

private theorem tw_inter_c12 :
    (liftS8 tw_c1).support ∩ (liftS8 tw_c2).support = ({2} : Finset (Fin 10)) := by
  rw [tw_support_c1, tw_support_c2]; decide

private theorem tw_inter_c13 :
    (liftS8 tw_c1).support ∩ (liftS8 tw_c3).support = ({3} : Finset (Fin 10)) := by
  rw [tw_support_c1, tw_support_c3]; decide

private theorem tw_inter_c14 :
    (liftS8 tw_c1).support ∩ (liftS8 tw_c4).support = ({4} : Finset (Fin 10)) := by
  rw [tw_support_c1, tw_support_c4]; decide

private theorem tw_inter_c23 :
    (liftS8 tw_c2).support ∩ (liftS8 tw_c3).support = ({5} : Finset (Fin 10)) := by
  rw [tw_support_c2, tw_support_c3]; decide

private theorem tw_inter_c24 :
    (liftS8 tw_c2).support ∩ (liftS8 tw_c4).support = ({6} : Finset (Fin 10)) := by
  rw [tw_support_c2, tw_support_c4]; decide

private theorem tw_inter_c34 :
    (liftS8 tw_c3).support ∩ (liftS8 tw_c4).support = ({7} : Finset (Fin 10)) := by
  rw [tw_support_c3, tw_support_c4]; decide

private theorem tw_fix_of_mem_support_inter {σ c c' : Perm (Fin 10)} {a : Fin 10}
    (h : σ * c = c * σ) (h' : σ * c' = c' * σ) (ha : a ∈ c.support) (ha' : a ∈ c'.support)
    (hint : c.support ∩ c'.support = {a}) : σ a = a := by
  have h1 : σ a ∈ c.support := (Equiv.Perm.mem_support_iff_of_commute h a).2 ha
  have h2 : σ a ∈ c'.support := (Equiv.Perm.mem_support_iff_of_commute h' a).2 ha'
  have hm : σ a ∈ c.support ∩ c'.support := Finset.mem_inter.2 ⟨h1, h2⟩
  rw [hint] at hm
  simpa using hm

theorem seven_dvd_card_pair_d_x₂ (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2) :
    7 ∣ Nat.card ↥(centralizer ({ι (swap 0 1)} : Set G) ⊓ centralizer ({z * ι τ₀} : Set G)) := by
  obtain ⟨ιd, hCd, -, -, h2⟩ := exists_frame_at_d hC hx hP2
  have hτ : τ₀ * τ₀ = 1 := by decide
  have hτsign : sign τ₀ = -1 := by
    rw [τ₀]; exact Equiv.Perm.sign_swap (by decide : (8 : Fin 10) ≠ 9)
  have hιdτ : ιd τ₀ = ι τ₀ * (z * ι (swap 0 1)) := by
    have h := h2 hp τ₀ (by decide) (by decide)
    rw [hτsign] at h
    simpa using h
  have hkey : z * ι τ₀ = ι (swap 0 1) * ιd τ₀ := by
    rw [hιdτ]
    symm
    calc ι (swap 0 1) * (ι τ₀ * (z * ι (swap 0 1)))
        = (ι (swap 0 1) * ι τ₀) * (z * ι (swap 0 1)) := by group
      _ = (ι τ₀ * ι (swap 0 1)) * (z * ι (swap 0 1)) := by rw [tw_swap01_comm_τ₀ ι]
      _ = ι τ₀ * ((ι (swap 0 1) * z) * ι (swap 0 1)) := by group
      _ = ι τ₀ * ((z * ι (swap 0 1)) * ι (swap 0 1)) := by
            rw [(hC.comm (swap 0 1)).symm]
      _ = ι τ₀ * (z * (ι (swap 0 1) * ι (swap 0 1))) := by group
      _ = ι τ₀ * z := by rw [tw_swap01_mul_self ι]; group
      _ = z * ι τ₀ := (hC.comm τ₀).symm
  rw [hkey, hCd.card_inf_centralizer_mul τ₀, two_mul_card_centralizer_perm_ten hτ]
  have hcard : Multiset.card τ₀.cycleType = 1 :=
    card_cycleType_of_isSwap ⟨8, 9, by decide, rfl⟩
  rw [hcard, N10_one]
  norm_num

theorem eq_one_of_pow_seven_of_commute (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2) {u : G}
    (hu : u ∈ centralizer ({ι (swap 0 1)} : Set G)) (hu7 : u ^ 7 = 1)
    (hcomm : ∀ ρ ∈ alternatingGroup (Fin 8), ρ 0 = 0 → ρ 1 = 1 →
      u * ι (liftS8 ρ) = ι (liftS8 ρ) * u) : u = 1 := by
  obtain ⟨ιd, hCd, -, -, h2⟩ := exists_frame_at_d hC hx hP2
  have hd2 : (ι (swap 0 1)) ^ 2 = 1 := by
    rw [pow_two]; exact tw_swap01_mul_self ι
  rcases hCd.cases u hu with ⟨σ, hσ | hσ⟩
  · have hσ_eq : u = ιd σ := hσ
    have key : ∀ ρ : Perm (Fin 8), ρ ∈ alternatingGroup (Fin 8) → ρ 0 = 0 → ρ 1 = 1 →
        σ * liftS8 ρ = liftS8 ρ * σ := by
      intro ρ hρ hρ0 hρ1
      have hsgn : sign (liftS8 ρ) = 1 := by
        rw [sign_liftS8]
        exact Equiv.Perm.mem_alternatingGroup.1 hρ
      have hagree : ιd (liftS8 ρ) = ι (liftS8 ρ) := by
        have hfix0 : liftS8 ρ (0 : Fin 10) = 0 := tw_liftS8_apply_zero hρ0
        have hfix1 : liftS8 ρ (1 : Fin 10) = 1 := tw_liftS8_apply_one hρ1
        have h := h2 hp (liftS8 ρ) hfix0 hfix1
        rw [hsgn] at h
        simpa using h
      have hc := hcomm ρ hρ hρ0 hρ1
      apply hCd.inj
      simp only [map_mul, hagree]
      rw [← hσ_eq]
      exact hc
    have hk1 := key tw_c1 tw_c1_even tw_c1_zero tw_c1_one
    have hk2 := key tw_c2 tw_c2_even tw_c2_zero tw_c2_one
    have hk3 := key tw_c3 tw_c3_even tw_c3_zero tw_c3_one
    have hk4 := key tw_c4 tw_c4_even tw_c4_zero tw_c4_one
    have hfix2 : σ 2 = 2 :=
      tw_fix_of_mem_support_inter (a := (2 : Fin 10)) hk1 hk2
        (by rw [tw_support_c1]; decide) (by rw [tw_support_c2]; decide) tw_inter_c12
    have hfix3 : σ 3 = 3 :=
      tw_fix_of_mem_support_inter (a := (3 : Fin 10)) hk1 hk3
        (by rw [tw_support_c1]; decide) (by rw [tw_support_c3]; decide) tw_inter_c13
    have hfix4 : σ 4 = 4 :=
      tw_fix_of_mem_support_inter (a := (4 : Fin 10)) hk1 hk4
        (by rw [tw_support_c1]; decide) (by rw [tw_support_c4]; decide) tw_inter_c14
    have hfix5 : σ 5 = 5 :=
      tw_fix_of_mem_support_inter (a := (5 : Fin 10)) hk2 hk3
        (by rw [tw_support_c2]; decide) (by rw [tw_support_c3]; decide) tw_inter_c23
    have hfix6 : σ 6 = 6 :=
      tw_fix_of_mem_support_inter (a := (6 : Fin 10)) hk2 hk4
        (by rw [tw_support_c2]; decide) (by rw [tw_support_c4]; decide) tw_inter_c24
    have hfix7 : σ 7 = 7 :=
      tw_fix_of_mem_support_inter (a := (7 : Fin 10)) hk3 hk4
        (by rw [tw_support_c3]; decide) (by rw [tw_support_c4]; decide) tw_inter_c34
    have hfix : ∀ a : Fin 10, a ∈ ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)) → σ a = a := by
      intro a ha
      fin_cases a
      · exact absurd ha (by decide)
      · exact absurd ha (by decide)
      · exact hfix2
      · exact hfix3
      · exact hfix4
      · exact hfix5
      · exact hfix6
      · exact hfix7
      · exact absurd ha (by decide)
      · exact absurd ha (by decide)
    have hcompl : ({0, 1, 8, 9} : Finset (Fin 10))ᶜ =
        ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)) := by decide
    have hsupp : σ.support ⊆ ({0, 1, 8, 9} : Finset (Fin 10)) := by
      intro x hx
      rw [Equiv.Perm.mem_support] at hx
      by_contra hx'
      exact hx (hfix x (by rw [← hcompl]; exact Finset.mem_compl.2 hx'))
    have hcard : σ.support.card ≤ 4 := by
      calc σ.support.card ≤ ({0, 1, 8, 9} : Finset (Fin 10)).card := Finset.card_le_card hsupp
        _ = 4 := by decide
    have hσ7 : σ ^ 7 = 1 := by
      have hι7 : ιd (σ ^ 7) = 1 := by
        calc ιd (σ ^ 7) = (ιd σ) ^ 7 := map_pow ιd σ 7
          _ = u ^ 7 := by rw [← hσ_eq]
          _ = 1 := hu7
      exact hCd.inj (hι7.trans (map_one ιd).symm)
    have hct : σ.cycleType = 0 := by
      by_contra hne
      obtain ⟨n, hn⟩ := Multiset.exists_mem_of_ne_zero hne
      have hn2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
      have hndvd : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
      have h7dvd : orderOf σ ∣ 7 := orderOf_dvd_of_pow_eq_one hσ7
      have hn7 : n ∣ 7 := hndvd.trans h7dvd
      have hnle : n ≤ σ.support.card := Equiv.Perm.le_card_support_of_mem_cycleType hn
      rcases Nat.prime_seven.eq_one_or_self_of_dvd n hn7 with h | h
      · omega
      · omega
    have hσ1 : σ = 1 := Equiv.Perm.cycleType_eq_zero.1 hct
    rw [hσ_eq, hσ1, map_one]
  · exfalso
    have hd7 : (ι (swap 0 1)) ^ 7 = ι (swap 0 1) := by
      rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num, pow_succ, pow_mul, hd2, one_pow, one_mul]
    have hcomm_dσ : Commute (ι (swap 0 1)) (ιd σ) := hCd.comm σ
    have hpow : u ^ 7 = ι (swap 0 1) * ιd (σ ^ 7) := by
      rw [hσ, hcomm_dσ.mul_pow 7, hd7, ← map_pow]
    have h1 : ι (swap 0 1) * ιd (σ ^ 7) = 1 := by
      rw [← hpow]; exact hu7
    have hd_eq : ι (swap 0 1) = ιd ((σ ^ 7)⁻¹) := by
      have h2' : ι (swap 0 1) = (ιd (σ ^ 7))⁻¹ := by
        calc ι (swap 0 1) = ι (swap 0 1) * (ιd (σ ^ 7) * (ιd (σ ^ 7))⁻¹) := by group
          _ = (ι (swap 0 1) * ιd (σ ^ 7)) * (ιd (σ ^ 7))⁻¹ := by group
          _ = 1 * (ιd (σ ^ 7))⁻¹ := by rw [h1]
          _ = (ιd (σ ^ 7))⁻¹ := by group
      rw [h2', map_inv]
    exact hCd.ne_z ((σ ^ 7)⁻¹) hd_eq.symm

end CFSG.OddStandard.AltStdSec.SwapPartner
