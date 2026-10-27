module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzHyp31A
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.SuzN0 Cover

theorem suzAutCentralizerN0_proved :
    SuzAutCentralizerN0 := by
  intro H _ _ L K u N₀ hcov hQ hcan
  have hP := suzPair_quotient hcov hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
  obtain ⟨-, -, -, hKtu, hKtperf, hKtcard⟩ := hP
  have hodd : Odd (Nat.card ↥(center ↥L)) := hcov.odd_center
  have hLperf : Group.IsPerfect ↥L := hcov.1.1
  obtain ⟨f⟩ := suz_equiv_of_isSporadic hcov.2.2
  have hũ2 : orderOf (q ↥L ⟨u, hu⟩) = 2 := hcov.orderOf_q_involution hu hu2
  have hdvd : 20160 ∣ Nat.card ↥(centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L))) := by
    have hle : (K.subgroupOf L).map (q ↥L) ≤
        centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L)) := fun k hk =>
      mem_centralizer_singleton_iff.2 (hKtu k hk)
    have := Subgroup.card_dvd_of_le hle
    rwa [hKtcard] at this
  obtain ⟨Ψ, hΨinj, hΨM, hΨR, hΨu⟩ := suz_exists_model_aux f _ hũ2 hdvd
  set Kh : Subgroup (Equiv.Perm (Fin 1782)) := ((K.subgroupOf L).map (q ↥L)).map Ψ with hKh
  have hKhE : Kh ≤ invE 0 := by
    rintro _ ⟨k, hk, rfl⟩
    refine mem_invE_zero.2 ⟨hΨM k, ?_⟩
    rw [← hΨu, ← map_mul, ← map_mul, hKtu k hk]
  have hKhperf : ⁅Kh, Kh⁆ = Kh := by
    have := hKtperf
    exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.map _)
  have hKhcard : Nat.card ↥Kh = 20160 := by
    rw [hKh, Subgroup.card_map_of_injective hΨinj]
    exact hKtcard
  set KC : Subgroup ↥(invE 0) := Kh.comap (invE 0).subtype with hKC
  have hKCmap : KC.map (invE 0).subtype = Kh := by
    rw [hKC, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.2 hKhE]
  have hKCperf : ⁅KC, KC⁆ = KC := by
    apply Subgroup.map_injective (invE 0).subtype_injective
    rw [Subgroup.map_commutator, hKCmap]
    exact hKhperf
  have hKCcard : Nat.card ↥KC = Nat.card suzD := by
    have h1 : Nat.card ↥(KC.map (invE 0).subtype) = Nat.card ↥KC :=
      Subgroup.card_map_of_injective (invE 0).subtype_injective
    rw [← h1, hKCmap, hKhcard, card_suzD]
  have hodd_mem : ∀ x ∈ invE 0, Odd (orderOf x) → x ∈ Kh := by
    intro x hx ho
    have h := suz_quot2Data.odd_mem (Subgroup.isPerfect_iff.2 hKCperf) hKCcard
      (c := ⟨x, hx⟩) (by rwa [Subgroup.orderOf_mk])
    rw [← hKCmap]
    exact ⟨⟨x, hx⟩, h, rfl⟩
  have hr : ∀ i < 4, rElt i ∈ Kh := fun i hi =>
    Kh.mul_mem (hodd_mem _ (oddElt_mem _ (by omega)) (odd_orderOf (by omega)))
      (hodd_mem _ (oddElt_mem _ (by omega)) (odd_orderOf (by omega)))
  have hw : wElt ∈ Kh := hodd_mem _ (oddElt_mem 8 (by norm_num)) (odd_orderOf (by norm_num))
  have hRRle : RR ≤ Kh := RR_le hr
  have hKtc : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 2 ^ 6 * 315 := by
    rw [hKtcard]
    norm_num
  obtain ⟨d, hd, hconj⟩ := canLoc_conj_elts hodd hKL hcan Ψ hΨinj (a := 6) (m := 315)
    (by decide) hKtc RR hRRle (by rw [card_RR]; norm_num)
    {x | (∃ i < 4, x = rElt i) ∨ x = wElt}
    (by
      rintro x (⟨i, hi, rfl⟩ | rfl)
      · exact hr i hi
      · exact hw)
    (by
      rintro x (⟨i, hi, rfl⟩ | rfl) y hy
      · exact RR.mul_mem (RR.mul_mem (rElt_mem_RR hi) hy) (RR.inv_mem (rElt_mem_RR hi))
      · exact wElt_conj_RR hy)
  have hdM : d ∈ suzM := (mem_invE_zero.1 (hKhE hd)).1
  obtain ⟨hsolv, h2, hinner⟩ := suz_autFixing Ψ hΨinj hΨM hΨR
    ((N₀.subgroupOf L).map (q ↥L)) d hdM
    (fun i hi => hconj _ (Or.inl ⟨i, hi, rfl⟩)) (hconj _ (Or.inr rfl))
  exact ⟨autCentralizer_solvable_of_quotient hLperf hsolv,
    autCentralizer_twoExp_of_quotient hLperf h2, autCentralizer_inner_of_quotient hLperf hinner⟩

end CFSG.EvenSporadicStandard.Induction
