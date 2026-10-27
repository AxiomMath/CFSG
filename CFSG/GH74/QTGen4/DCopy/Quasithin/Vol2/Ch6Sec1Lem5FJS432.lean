module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FGS432
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FJ

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_le_factor_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hfF : FactorFacts_ch615 F)
    (hTF : autI hU T ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hDF : autI hU D ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hKF : autI hU (oTwoUpper H) ≤ F) (hS : IsSylowTwoOf (autI hU T ⊓ F) F)
    (hKJ : autI hU (oTwoUpper H) ≤ ⁅autI hU (oTwoUpper H), autI hU T ⊓ F⁆)
    (hfix : fixV F ≠ ⊥) : False := by
  classical
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHN : H ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_right.trans hXN
  have hKne := c.autI_oTwoUpper_ne_bot_ch615 hU
  have hgen : ∀ x ∈ H, Odd (orderOf x) → ∀ hxN : x ∈ Subgroup.normalizer (UX615 T L H : Set G),
      convI hU ⟨x, hxN⟩ ∈ autI hU (oTwoUpper H) ∧ Odd (orderOf (convI hU ⟨x, hxN⟩)) :=
    fun x hxH hxo hxN => ⟨convI_mem_autI hU (mem_oTwoUpper_of_odd hxH hxo) hxN,
      Odd.of_dvd_nat hxo (by
        have := orderOf_map_dvd (convI hU) ⟨x, hxN⟩
        rwa [Subgroup.orderOf_mk] at this)⟩
  have hKle : ∀ C : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      (∀ y ∈ autI hU (oTwoUpper H), Odd (orderOf y) → y ∈ C) → autI hU (oTwoUpper H) ≤ C := by
    intro C hC
    refine autI_le_of_le_preI615 ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hxH, hxo⟩
    obtain ⟨h1, h2⟩ := hgen x hxH hxo (hHN hxH)
    exact mem_preI615 (hHN hxH) (hC _ h1 h2)
  rcases hfF.kind with h6 | hB | hC
  ·
    obtain ⟨P, hPF, hP3, hPx⟩ := exists_sylow_three_of_card_six_ch615 h6
    have hKP : autI hU (oTwoUpper H) ≤ P := hKle P fun y hy hyo => by
      refine hPx y (hKF hy) (orderOf_dvd_iff_pow_eq_one.mp ?_)
      have h6' : orderOf y ∣ 6 := h6 ▸ Subgroup.orderOf_dvd_natCard F (hKF hy)
      exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hyo)
        (by simpa using h6'))
    have hKeq : autI hU (oTwoUpper H) = P := by
      have hdvd : Nat.card (autI hU (oTwoUpper H)) ∣ 3 := hP3 ▸ Subgroup.card_dvd_of_le hKP
      have hne : Nat.card (autI hU (oTwoUpper H)) ≠ 1 := fun h1 =>
        hKne (Subgroup.eq_bot_of_card_eq _ h1)
      have h3 : Nat.card (autI hU (oTwoUpper H)) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd h hne
        · exact h
      exact Subgroup.eq_of_le_of_card_ge hKP (by rw [h3, hP3])
    apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    rw [hKeq] at hk ⊢
    refine hPx _ ((Subgroup.mem_normalizer_iff.mp (hDF hy) k).mp (hPF hk)) ?_
    have hk3 : k ^ 3 = 1 := by
      rw [← hP3]
      exact (Subgroup.orderOf_dvd_natCard P hk).trans (by rfl) |> orderOf_dvd_iff_pow_eq_one.mp
    rw [conj_pow, hk3, mul_one, mul_inv_cancel]
  ·
    obtain ⟨-, hout, hNS, hself⟩ := hB
    by_cases hDc : autI hU D ≤ Subgroup.centralizer (F : Set (MulAut _))
    · apply c.not_hall_normalizes_ch615 hU hD hN
      intro y hy k hk
      rw [← Subgroup.mem_centralizer_iff.mp (hDc hy) k (hKF hk), mul_inv_cancel_right]
      exact hk
    have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
      have hodd : Odd (Nat.card (autI hU D)) := by
        rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
        exact hD.2.1
      exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
    obtain ⟨d, hdD, hdF, hd1, -⟩ := exists_mem_of_not_le_centralizer_ch615 hout hfF.center
      hS.isPGroup hS.le (hNS _ hS) (hself _ hS) (inf_le_left.trans (autI_mono hU le_sup_right))
      (autI_mono hU (hD.1.trans le_sup_left)) (c.isSolvable_autI_ch615 hU) hDF hDsodd
      (fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho)
      (fun p hp hp2 x hx y hy hxp hyp hxy hx1 =>
        c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hx hy hxp hyp hxy hx1) hDc
    obtain ⟨w, hwF, hw1, hwT⟩ := exists_fix_ch615 IntMod.sq_eq_one (c.isPGroup_autI_ch615 hU)
      hfix fun t ht w hw => mem_fixV_of_conj_ch615 (hTF ht) hw
    exact c.false_of_fix_ch615_F4 h432 hU hD hw1 hwT (fun k hk => hwF k (hKF hk)) hdD hd1
      (hwF d hdF)
  ·
    obtain ⟨-, hBor⟩ := hC
    have hTK : autI hU T ⊓ F ≤ Subgroup.normalizer (autI hU (oTwoUpper H) : Set (MulAut _)) := by
      have hTK' : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
        c.hH.1.1.trans (le_normalizer_oTwoUpper H)
      intro y hy
      refine Subgroup.mem_normalizer_iff.mpr fun a =>
        ⟨fun ha => C124.autI_conj_mem hU hTK' y hy.1 a ha, fun ha => ?_⟩
      have := C124.autI_conj_mem hU hTK' y⁻¹ ((autI hU T).inv_mem hy.1) _ ha
      simpa [mul_assoc] using this
    have hKs := c.isSolvable_autI_oTwoUpper_ch615 hU
    have hT2s : Group.IsSolvable ↥(autI hU T ⊓ F) := by
      have := hS.isPGroup.isNilpotent
      infer_instance
    have hRs : Group.IsSolvable ↥(autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F)) :=
      A3.isSolvable_sup_of_le_normalizer hTK
    have hnorm := hBor _ hS _ le_sup_right (sup_le hKF inf_le_right) hRs
    have hKT : autI hU (oTwoUpper H) ≤ autI hU T ⊓ F := by
      refine hKJ.trans (Subgroup.commutator_le.mpr fun k hk s hs => ?_)
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (hnorm k (Subgroup.mem_sup_left hk) s hs)
        (Subgroup.inv_mem _ hs)
    apply hKne
    rw [eq_bot_iff]
    refine hKle ⊥ fun y hy hyo => ?_
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_mem_l32_ch615 hS.isPGroup (hKT hy) hyo)

end Cx615C

end CFSG.Quasithin.H13
