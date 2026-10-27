module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S7c

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

variable {G : Type*} [Group G]

theorem conj_zpow_eq (y x : G) (k : ℤ) : y * x ^ k * y⁻¹ = (y * x * y⁻¹) ^ k := by
  simp

theorem sq_zpow_eq (p : G) (s : ℤ) : (p ^ 2) ^ s = p ^ (2 * s) := by
  rw [← zpow_natCast, ← zpow_mul]
  norm_num

end Eight

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

section Seven

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
  (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma)
  {y : H} (hyS : y ∈ h.S) (hya : y⁻¹ * h.a * y = h.a) (hyz : y⁻¹ * d.z * y = d.z)
  (hyσ : y⁻¹ * d.sigma * y = h.a * d.z * d.sigma)
include hv I F h3 hyS hya hyz hyσ

theorem P_dihedral_fusion (hFO : CF81FieldOrd) (hDg : CF81Diag) :
    d.b * d.p * d.b⁻¹ = d.p⁻¹ ∧
      ∀ π ∈ h.P, π * π = 1 → π ≠ 1 → π ≠ h.a → ∃ c : H, c⁻¹ * d.b * c = π := by
  obtain ⟨β, hP⟩ := d.pres
  obtain ⟨π₀, hπ₀, hπ₀not⟩ := y_nontrivial_P hv I F h3 hyS hya hyz hyσ hFO hDg
  have hn2 : (2 : ℤ) ∣ (orderOf d.p : ℤ) := by
    obtain ⟨m, hm⟩ := hP.four_dvd
    exact ⟨2 * m, by rw [hm]; push_cast; ring⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (d.S_p y hyS)
  obtain ⟨l, hl⟩ := mem_zpowers_iff.mp (d.S_p y⁻¹ (inv_mem hyS))
  rw [inv_inv] at hl
  have hkodd : Odd k := by
    by_contra hke
    rw [Int.not_odd_iff_even] at hke
    have h1 : d.p ^ (1 : ℤ) = d.p ^ (l * k) := by
      calc d.p ^ (1 : ℤ) = y⁻¹ * (y * d.p * y⁻¹) * y := by rw [zpow_one]; group
        _ = y⁻¹ * d.p ^ k * y := by rw [hk]
        _ = y⁻¹ * d.p ^ k * y⁻¹⁻¹ := by rw [inv_inv]
        _ = (y⁻¹ * d.p * y⁻¹⁻¹) ^ k := Eight.conj_zpow_eq y⁻¹ d.p k
        _ = (d.p ^ l) ^ k := by rw [inv_inv, ← hl]
        _ = d.p ^ (l * k) := (zpow_mul d.p l k).symm
    rw [Eight.MC.Pres.zpow_eq_zpow_iff (p := d.p)] at h1
    have h2k : (2 : ℤ) ∣ k := even_iff_two_dvd.mp hke
    have h3' := dvd_add (dvd_trans hn2 h1) (dvd_mul_of_dvd_right h2k l)
    rw [sub_add_cancel] at h3'
    norm_num at h3'
  have hybP : y * d.b * y⁻¹ ∈ h.P := h.toHyp52.conj_mem_P' hyS d.b_mem_P
  have hyb2 : y * d.b * y⁻¹ * (y * d.b * y⁻¹) = 1 := by
    rw [show y * d.b * y⁻¹ * (y * d.b * y⁻¹) = y * (d.b * d.b) * y⁻¹ by group, d.b_mul_self]
    group
  have hba : d.b ≠ h.a := fun h1 => hP.b_not (h1 ▸ d.p_a ▸ pow_mem (mem_zpowers _) _)
  obtain ⟨j, hj | hj⟩ := hP.mem_cases hybP
  · exfalso
    rcases hP.eq_one_or_a (hj ▸ zpow_mem (mem_zpowers _) j) (hj ▸ hyb2) with h1 | h1
    · have : d.b = 1 := by
        calc d.b = y⁻¹ * (y * d.b * y⁻¹) * y := by group
          _ = 1 := by rw [h1]; group
      exact absurd d.b_ord (by rw [this, orderOf_one]; norm_num)
    · apply hba
      rw [d.p_a] at h1
      calc d.b = y⁻¹ * (y * d.b * y⁻¹) * y := by group
        _ = y⁻¹ * h.a * y := by rw [h1]
        _ = h.a := hya
  have hjodd : Odd j := by
    by_contra hje
    rw [Int.not_odd_iff_even] at hje
    apply hπ₀not
    obtain ⟨t, ht⟩ := hkodd
    obtain ⟨u, hu⟩ := hje
    obtain ⟨i, hi | hi⟩ := hP.mem_cases hπ₀
    · subst hi
      rw [Eight.conj_zpow_eq, ← hk, ← zpow_mul, ← zpow_neg, ← zpow_add,
        show k * i + -i = 2 * (t * i) by rw [ht]; ring, ← Eight.sq_zpow_eq]
      exact zpow_mem (mem_zpowers _) _
    · subst hi
      rw [show y * (d.p ^ i * d.b) * y⁻¹ * (d.p ^ i * d.b)⁻¹ =
          y * d.p ^ i * y⁻¹ * (y * d.b * y⁻¹) * d.b⁻¹ * (d.p ^ i)⁻¹ by group,
        Eight.conj_zpow_eq, ← hk, hj]
      have e : (d.p ^ k) ^ i * (d.p ^ j * d.b) * d.b⁻¹ * (d.p ^ i)⁻¹ =
          d.p ^ (k * i + j + -i) := by
        rw [← zpow_mul, ← zpow_neg]
        group
      rw [e, show k * i + j + -i = 2 * (t * i + u) by rw [ht, hu]; ring, ← Eight.sq_zpow_eq]
      exact zpow_mem (mem_zpowers _) _
  have hβ : β = -1 := by
    rcases hP.beta with hβ | hβ
    · exact hβ
    · exfalso
      have h1 := hP.sq_zpow_mul_b j
      rw [← hj, hyb2, hβ, show (1 + ((orderOf d.p : ℤ) / 2 - 1)) * j =
        (orderOf d.p : ℤ) / 2 * j by ring, zpow_mul, ← Eight.MC.Pres.a_eq_zpow (p := d.p)] at h1
      exact (Int.not_even_iff_odd.mpr hjodd) ((hP.a_zpow_eq_one_iff j).mp h1.symm)
  refine ⟨by rw [hP.rel, hβ, zpow_neg_one], fun π hπ hπ2 hπ1 hπa => ?_⟩
  have hconj : ∀ m s : ℤ, d.p ^ m * (d.p ^ s * d.b) * (d.p ^ m)⁻¹ = d.p ^ (s + 2 * m) * d.b := by
    intro m s
    have h1 := hP.b_mul_zpow (-m)
    rw [hβ, show (-1 : ℤ) * -m = m by ring] at h1
    calc d.p ^ m * (d.p ^ s * d.b) * (d.p ^ m)⁻¹ = d.p ^ m * d.p ^ s * (d.b * d.p ^ (-m)) := by
          group
      _ = d.p ^ m * d.p ^ s * (d.p ^ m * d.b) := by rw [h1]
      _ = d.p ^ (s + 2 * m) * d.b := by group
  obtain ⟨i, hi | hi⟩ := hP.mem_cases hπ
  · exfalso
    rcases hP.eq_one_or_a (hi ▸ zpow_mem (mem_zpowers _) i) hπ2 with h1 | h1
    · exact hπ1 h1
    · exact hπa (h1.trans d.p_a)
  · rcases Int.even_or_odd i with ⟨m, hm⟩ | hiodd
    · refine ⟨(d.p ^ m)⁻¹, ?_⟩
      have h1 := hconj m 0
      rw [zpow_zero, one_mul, zero_add] at h1
      rw [inv_inv, hi, hm, h1, show 2 * m = m + m by ring]
    · obtain ⟨m, hm⟩ : Even (i - j) := Int.even_sub.mpr
        ⟨fun hi' => absurd hi' (Int.not_even_iff_odd.mpr hiodd),
          fun hj' => absurd hj' (Int.not_even_iff_odd.mpr hjodd)⟩
      refine ⟨y⁻¹ * (d.p ^ m)⁻¹, ?_⟩
      rw [hi, show (y⁻¹ * (d.p ^ m)⁻¹)⁻¹ * d.b * (y⁻¹ * (d.p ^ m)⁻¹) =
        d.p ^ m * (y * d.b * y⁻¹) * (d.p ^ m)⁻¹ by group, hj, hconj,
        show j + 2 * m = i by omega]

end Seven

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
