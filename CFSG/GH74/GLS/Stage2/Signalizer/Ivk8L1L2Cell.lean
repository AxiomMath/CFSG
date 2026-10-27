module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L2
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgFin
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltY
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Cbar
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Swap

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section FL2Swap

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem fl2_five_false (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hnc : ¬ Vb ≤ centralizer (J : Set A)) {F : Type} [Field F] [Finite F]
    (hF5 : Nat.card F = 5) (e : (↥J ⧸ center ↥J) ≃* IVK.L2 F) : False := by
  obtain ⟨-, hcfg⟩ := hfr.sylCfg hJ hnc
  obtain ⟨eP⟩ := (LinearGroups.five_field_linear_two_alternating_five_model F hF5).1
  exact altY_not_sylCfg' 5 (Or.inl rfl) _ ((e.trans (IVK.L2.equivPSL F)).trans eP) hcfg

omit [Finite A] in
theorem inf_le_center_map {J' : Subgroup A} (hcomm : ∀ a ∈ J', ∀ b ∈ J, a * b = b * a) :
    J ⊓ J' ≤ (center ↥J).map J.subtype := by
  intro x hx
  obtain ⟨hxJ, hxJ'⟩ := Subgroup.mem_inf.mp hx
  refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
  show (⟨x, hxJ⟩ : ↥J) ∈ center ↥J
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact (hcomm x hxJ' g g.2).symm

theorem fl2_nine_false (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) (hZ : center ↥J ≠ ⊥)
    (hns : ¬ Sb ≤ normalizer (J : Set A)) (hcard : Nat.card (↥J ⧸ center ↥J) = 360) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hsS, hsN⟩ := Set.not_subset.mp hns
  have hs : cs s J ≠ J := fun h => hsN (cs_eq_iff_mem_normalizer.mp h)
  obtain ⟨hzJ, hzJ'⟩ := swap_zb hfr hJ hZ hsS hs
  have hJ' : IsComponent (cs s J) := isComponent_cs hJ s
  have hcomm : ∀ a ∈ cs s J, ∀ b ∈ J, a * b = b * a := Gen.comm_of_ne_components hJ' hJ hs
  have hEbot : pPrimeCore 2 ↥(J ⊔ cs s J) = ⊥ :=
    pPrimeCore_eq_bot_of_invariant hfr (sup_invariant hfr hJ hs)
  have hEzb : J ⊔ cs s J ≤ centralizer ({zb} : Set A) := by
    refine sup_le (fun j hj => ?_) (fun j hj => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hzJ j hj).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hzJ' j hj).symm
  have h9 : 3 ^ 2 ∣ Nat.card ↥J := by
    have h1 : Nat.card ↥J = Nat.card (↥J ⧸ center ↥J) * Nat.card ↥(center ↥J) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥J)
    rw [h1, hcard]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  set P : Subgroup A := P₀.map J.subtype with hP
  have hPJ : P ≤ J := Subgroup.map_subtype_le _
  have hPcard : Nat.card ↥P = 3 ^ 2 := by
    rw [hP, Subgroup.card_map_of_injective J.subtype_injective]
    exact hP₀
  set P' : Subgroup A := cs s P with hP'
  have hP'J' : P' ≤ cs s J := Subgroup.map_mono hPJ
  have hP'card : Nat.card ↥P' = 3 ^ 2 := by
    rw [hP', ← hPcard]
    exact Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    have hPab : IsMulCommutative ↥P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hPcard
    intro x hx y hy
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥P) ⟨y, hy⟩)
  have hP'c : ∀ x ∈ P', ∀ y ∈ P', x * y = y * x := by
    have hP'ab : IsMulCommutative ↥P' := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP'card
    intro x hx y hy
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥P') ⟨y, hy⟩)
  have hPP' : ∀ a ∈ P, ∀ b ∈ P', a * b = b * a := fun a ha b hb =>
    (hcomm b (hP'J' hb) a (hPJ ha)).symm
  have hinf : P ⊓ P' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxP'⟩ := Subgroup.mem_inf.mp hx
    have hxZ : x ∈ (center ↥J).map J.subtype :=
      inf_le_center_map hcomm (Subgroup.mem_inf.mpr ⟨hPJ hxP, hP'J' hxP'⟩)
    have h9' : orderOf x ∣ 9 := by
      have := orderOf_dvd_natCard (⟨x, hxP⟩ : ↥P)
      rwa [Subgroup.orderOf_mk, hPcard] at this
    obtain ⟨y, hy, rfl⟩ := hxZ
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (hfr.isPGroup_center_two hJ) ⟨y, hy⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk' : orderOf (J.subtype y) = 2 ^ k := by
      rw [show J.subtype y = (y : A) from rfl, Subgroup.orderOf_coe]
      exact hk
    have h2k : 2 ^ k ∣ 9 := hk' ▸ h9'
    have hk1 : 2 ^ k = 1 :=
      Nat.Coprime.eq_one_of_dvd ((by norm_num : Nat.Coprime 2 9).pow_left k) h2k
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (hk'.trans hk1))
  obtain ⟨hprod, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute P P' hPP'
  rw [hinf, Subgroup.card_bot, mul_one, hPcard, hP'card] at hprod
  have hQc : ∀ x ∈ P ⊔ P', ∀ y ∈ P ⊔ P', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Odd87.exists_mul_of_mem_sup' hPP' hx
    obtain ⟨a', ha', b', hb', rfl⟩ := Odd87.exists_mul_of_mem_sup' hPP' hy
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hPP' a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [hPc a ha a' ha', hP'c b hb b' hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hPP' a ha b' hb']
      _ = a' * b' * (a * b) := by group
  exact no_abelian_81_of_cbar hfr hfr.zb_ord hEzb hEbot (P := P ⊔ P') (sup_le_sup hPJ hP'J')
    hQc (by rw [hprod]; norm_num)

theorem fl2_swap_false (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hnc : ¬ Vb ≤ centralizer (J : Set A)) (hY : FL2 (↥J ⧸ center ↥J))
    (hns : ¬ Sb ≤ normalizer (J : Set A)) : False := by
  obtain ⟨s, hsS, hsN⟩ := Set.not_subset.mp hns
  have hs : cs s J ≠ J := fun h => hsN (cs_eq_iff_mem_normalizer.mp h)
  by_cases hZ : center ↥J = ⊥
  · obtain ⟨U, hUJ, hU⟩ := exists_four_le_of_FL2 hZ hY
    exact hs (hfr.comp_unique_of_four hJ hUJ hU _ (isComponent_cs hJ s))
  · obtain ⟨F, _, _, hFL, ⟨e⟩⟩ := fl2_model hY
    have hsq := swap_card_sq hfr hJ hZ hns
    have hcardY := card_of_model hFL e
    rw [hcardY] at hsq
    rcases q_cases (Nat.card F) hFL.1 hFL.2 hsq with h5 | h9
    · exact fl2_five_false hfr hJ hnc h5 e
    · refine fl2_nine_false hfr hJ hZ hns ?_
      rw [hcardY, h9]
      norm_num

theorem cellAbs_FL2 : CellAbs FL2 := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hY
  exfalso
  by_cases hsw : Sb ≤ normalizer (J : Set A)
  · exact fl2_of_normalizes hfr hJ hY hsw
  · exact fl2_swap_false hfr hJ hnc hY hsw

end FL2Swap

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
