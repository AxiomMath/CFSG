module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import TauCeti.GroupTheory.FrobeniusKernel

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped Pointwise

private lemma frob18_card (a b : ℕ) (h : a * b = 18) (ha : 1 < a) (hb : 1 < b)
    (hd : b ∣ a - 1) : a = 9 ∧ b = 2 := by
  obtain ⟨k, hk⟩ := hd
  have hb9 : b ≤ 9 := by
    have : 2 * b ≤ a * b := Nat.mul_le_mul_right b (by omega)
    omega
  interval_cases b <;> omega

theorem y6_frob18_no_normal_two {Φ : Type} [Group Φ] (h : IsFrobeniusOfOrder 18 Φ)
    (P : Subgroup Φ) (hP : P.Normal) (hP2 : IsPGroup 2 ↥P) : P = ⊥ := by
  obtain ⟨hcard, W, D, hWn, hsup, hinf, hWne, hDne, hfree⟩ := h
  haveI : W.Normal := hWn
  haveI : Finite Φ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hmul : ((W : Set Φ) * (D : Set Φ)) = Set.univ := by
    rw [← Subgroup.normal_mul W D, hsup]
    rfl
  have hcompl : W.IsComplement' D :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) hmul
  have hfpf : ∀ d : ↥D, d ≠ 1 →
      MonoidHom.FixedPointFree (MulAut.conjNormal (d : Φ) : MulAut ↥W) := by
    intro d hd w hw
    have hcomm : (d : Φ) * (w : Φ) = (w : Φ) * (d : Φ) := by
      have hh : ((MulAut.conjNormal (d : Φ)) w : Φ) = (w : Φ) := congrArg Subtype.val hw
      rw [MulAut.conjNormal_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hd1 : (d : Φ) ≠ 1 := fun h1 => hd (Subtype.ext h1)
    exact Subtype.ext (hfree (d : Φ) d.2 hd1 (w : Φ) w.2 hcomm)
  have hTI : TauCeti.IsTISubgroup D :=
    TauCeti.isTISubgroup_of_isComplement'_of_fixedPointFree (N := W) (H := D) hcompl hfpf
  have hdvdD : Nat.card ↥D ∣ Nat.card ↥W - 1 := by
    have := hTI.card_dvd_index_sub_one
    rwa [hcompl.index_eq_card] at this
  have hprod : Nat.card ↥W * Nat.card ↥D = 18 := by
    rw [hcompl.card_mul_card, hcard]
  have hW1 : 1 < Nat.card ↥W := by
    have hne : Nat.card ↥W ≠ 1 := fun h1 => hWne (Subgroup.card_eq_one.mp h1)
    have hne0 : Nat.card ↥W ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hprod
      norm_num at hprod
    omega
  have hD1 : 1 < Nat.card ↥D := by
    have hne : Nat.card ↥D ≠ 1 := fun h1 => hDne (Subgroup.card_eq_one.mp h1)
    have hne0 : Nat.card ↥D ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hprod
      norm_num at hprod
    omega
  obtain ⟨hW9, hD2⟩ := frob18_card _ _ hprod hW1 hD1 hdvdD
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hdvd18 : Nat.card ↥P ∣ 18 := by
    have := Subgroup.card_subgroup_dvd_card P
    rwa [hcard] at this
  have hcardP : Nat.card ↥P = 1 ∨ Nat.card ↥P = 2 := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    have hdvd : (2 : ℕ) ^ n ∣ 18 := by rw [← hn]; exact hdvd18
    have hn2 : n ≤ 1 := by
      by_contra h'
      have h2n : 2 ≤ n := by omega
      have h4 : (2 : ℕ) ^ 2 ∣ (2 : ℕ) ^ n := pow_dvd_pow 2 h2n
      have h4' : (2 : ℕ) ^ 2 ∣ 18 := h4.trans hdvd
      norm_num at h4'
    interval_cases n
    · left; rw [hn]; norm_num
    · right; rw [hn]; norm_num
  rcases hcardP with hP1 | hPcard2
  · exact Subgroup.card_eq_one.mp hP1
  · exfalso
    have huniq : ∃! y : ↥P, y ≠ 1 := (Nat.card_eq_two_iff' (1 : ↥P)).mp hPcard2
    obtain ⟨i, hi_ne, huniq_i⟩ := huniq
    have hi_ne' : (i : Φ) ≠ 1 := fun h1 => hi_ne (Subtype.ext h1)
    have hcentral : ∀ g : Φ, g * (i : Φ) * g⁻¹ = (i : Φ) := by
      intro g
      have hj_ne : (⟨g * (i : Φ) * g⁻¹, hP.conj_mem (i : Φ) i.2 g⟩ : ↥P) ≠ 1 := by
        intro hh
        exact hi_ne (Subtype.ext (by
          have h1 : g * (i : Φ) * g⁻¹ = 1 := congrArg Subtype.val hh
          calc (i : Φ) = g⁻¹ * (g * (i : Φ) * g⁻¹) * g := by group
            _ = 1 := by rw [h1]; group))
      exact congrArg Subtype.val (huniq_i _ hj_ne)
    have hcentral_i : ∀ g : Φ, (i : Φ) * g = g * (i : Φ) :=
      fun g => (mul_inv_eq_iff_eq_mul.mp (hcentral g)).symm
    have hi_notin_W : (i : Φ) ∉ W := by
      intro hiW
      have hmem : (i : Φ) ∈ P ⊓ W := ⟨i.2, hiW⟩
      have hne : P ⊓ W ≠ ⊥ := fun hbot => by
        have : (i : Φ) ∈ (⊥ : Subgroup Φ) := hbot ▸ hmem
        exact hi_ne' (by simpa using this)
      have hdvdW : Nat.card ↥(P ⊓ W) ∣ Nat.card ↥W := Subgroup.card_dvd_of_le inf_le_right
      rw [hW9] at hdvdW
      have hdvdP : Nat.card ↥(P ⊓ W) ∣ Nat.card ↥P := Subgroup.card_dvd_of_le inf_le_left
      rw [hPcard2] at hdvdP
      have hne1 : Nat.card ↥(P ⊓ W) ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.mp h1)
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvdP with h1 | h2
      · exact hne1 h1
      · rw [h2] at hdvdW
        norm_num at hdvdW
    have hi_mul : (i : Φ) ∈ ((W : Set Φ) * (D : Set Φ)) := hmul ▸ Set.mem_univ (i : Φ)
    obtain ⟨w, hwW, d, hdD, hwd⟩ := Set.mem_mul.mp hi_mul
    have hd_ne : d ≠ 1 := by
      intro hd1
      exact hi_notin_W (by rw [← hwd, hd1, mul_one]; exact hwW)
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hcommW : ∀ a b : ↥W, a * b = b * a := fun a b =>
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
        (by rw [hW9]; norm_num)).is_comm.comm a b
    haveI : Nontrivial ↥W := (Finite.one_lt_card_iff_nontrivial).mp hW1
    obtain ⟨x, hx_ne⟩ := exists_ne (1 : ↥W)
    have hwx : w * (x : Φ) = (x : Φ) * w :=
      congrArg Subtype.val (hcommW ⟨w, hwW⟩ x)
    have hcx : d * (x : Φ) = (x : Φ) * d := by
      have h := hcentral_i (x : Φ)
      rw [← hwd] at h
      have h' : (w : Φ) * (d * (x : Φ)) = (w : Φ) * ((x : Φ) * d) := by
        calc (w : Φ) * (d * (x : Φ)) = (w : Φ) * d * (x : Φ) := by group
          _ = (x : Φ) * ((w : Φ) * d) := h
          _ = ((x : Φ) * (w : Φ)) * d := by group
          _ = ((w : Φ) * (x : Φ)) * d := by rw [hwx]
          _ = (w : Φ) * ((x : Φ) * d) := by group
      exact mul_left_cancel h'
    exact hx_ne (Subtype.ext (hfree d hdD hd_ne (x : Φ) x.2 hcx))

end CFSG.OddStandard.HigherRank.YamadaG23
