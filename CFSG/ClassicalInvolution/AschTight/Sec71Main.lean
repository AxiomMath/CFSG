module

public import CFSG.ClassicalInvolution.AschTight.Sec71D12
public import CFSG.ClassicalInvolution.Asc77.WP1Section7
public import CFSG.ClassicalInvolution.AschTight.Sec71Cap3
public import CFSG.ClassicalInvolution.AschTight.Sec71Good2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

theorem l7_1_proved (p f : ℕ) [Fact p.Prime] : Asc77.L7_1 p f := by
  intro hp hq G _ _ Ω hΩ hAe W hW R hR T hT u r v t hu hRur hv hTvt
  obtain ⟨K, z, hd⟩ := exists_dData hp hq hΩ hW hR hu hRur
  obtain ⟨J, j, hd'⟩ := exists_dData hp hq hΩ hW hT hv hTvt
  have hW2 := Sec7.isPGroup_of_mem_WSet hW
  have hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    obtain ⟨η, hη, hWη⟩ := id hW
    rw [hWη]
    obtain ⟨S, hS, hinv⟩ := hη
    exact ((l6_9_proved p f hp hq G Ω hΩ S).2 η hS hinv).1
  by_cases hKJ : K = J
  · subst hKJ
    exact ⟨cap_case_one hΩ hd hd' hW2 hWc, Or.inl ⟨K, hd.memK, hd.le, hd'.le⟩⟩
  obtain ⟨i, hi⟩ := hd.exists_rel hd'.u_memW (hd.le_normalizer hd'.u_memW)
  obtain ⟨k, hk⟩ := hd'.exists_rel hd.u_memW (hd'.le_normalizer hd.u_memW)
  by_cases hzj : z = j
  · obtain ⟨hJ, hc⟩ := case_two_of_twin hΩ hd hd' hKJ hzj
    exact ⟨cap_case_two hd hd' hW2 hWc hc,
      Or.inr (Or.inl ⟨K, hd.memK, J, hd'.memK, hd.le, hd'.le, hJ, hc⟩)⟩
  by_cases hie : Even i
  · have hke := even_of_even hp hq hΩ hd hd' hWc hzj hi hk hie
    obtain ⟨hJ, hc⟩ := case_two_of_even hp hq hΩ hd hd' hWc hKJ hzj hi hk hie hke
    exact ⟨cap_case_two hd hd' hW2 hWc hc,
      Or.inr (Or.inl ⟨K, hd.memK, J, hd'.memK, hd.le, hd'.le, hJ, hc⟩)⟩
  have hio : Odd i := Int.not_even_iff_odd.mp hie
  have hko : Odd k := by
    by_contra hko'
    exact hie (even_of_even hp hq hΩ hd' hd hWc (Ne.symm hzj) hk hi
      (Int.not_odd_iff_even.mp hko'))
  obtain ⟨hJs, hJn⟩ := case_three_of_odd hp hq hΩ hd hd' hWc hKJ hk hko
  have h4 : (4 : ℤ) ∣ i * k - 1 := by
    by_contra hbad
    exact false_of_not_four_dvd hp hq hΩ hd hd' hWc hKJ hzj hi hk hio hko hbad
      (hAe K hd.memK)
  have hL := conj_eq_of_four_dvd hΩ hd hd' hW2 hWc hzj hi hk hio h4
  have hik := rel_of_conj_eq hΩ hd hd' hWc hzj hi hk hL
  have hbraid := braid_of_conj_eq hΩ hd hd' hWc hi hk hL
  refine ⟨cap_case_three hd hd' hW2 hWc hzj hi hk hko hbraid, Or.inr (Or.inr ⟨K, hd.memK, J,
    hd'.memK, hd.le, hd'.le, hJs, hJn, v ^ k, ?_, ?_, ?_⟩)⟩
  · obtain ⟨n, hn⟩ := hd'.orderOf_eq
    exact zpowers_zpow_eq_of_odd hn hko
  · rw [hd'.conj_inv_eq hWc hd.u_memW, hk, mul_inv_cancel]
    exact Subgroup.one_mem _
  · have hvk : v ^ k ∈ W := W.zpow_mem hd'.u_memW k
    have huv : Commute u v := hWc u hd.u_memW v hd'.u_memW
    rw [hd.conj_inv_eq hWc hvk, ← conj_zpow, hi, ((huv.zpow_left i).symm).mul_zpow, ← zpow_mul,
      hik, mul_inv_cancel]
    exact Subgroup.one_mem _

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
