module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBar
import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem barM_le_centralizer_barM_of_ne {M H A B : Subgroup G}
    (hA : A ∈ weakBlockSet M H) (hB : B ∈ weakBlockSet M H) (hAB : A ≠ B) :
    barM M A ≤ Subgroup.centralizer (barM M B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      hA.toIsTwoPrimeComponent.component hB.toIsTwoPrimeComponent.component
      fun he => hAB (hA.toIsTwoPrimeComponent.eq_of_barM_eq hB.toIsTwoPrimeComponent he))

theorem le_normalizer_of_mem_weakBlockSet {M H A B : Subgroup G}
    (hA : A ∈ weakBlockSet M H) (hB : B ∈ weakBlockSet M H) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  by_cases h : A = B
  · subst h
    exact Subgroup.le_normalizer
  · exact hB.toIsTwoPrimeComponent.le_normalizer
      (fun _ hy => Subgroup.centralizer_le_normalizer _
        (barM_le_centralizer_barM_of_ne hA hB h hy))
      hA.toIsTwoPrimeComponent.le

omit [Finite G] in
theorem center_barM_eq_bot_of_isTwoPrimeComponent {M A : Subgroup G}
    (hAcomp : IsTwoPrimeComponent M A)
    (hL3A : ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥A ⧸ pCore 2 ↥A)) :
    Subgroup.center (↥(barM M A)) = ⊥ := by
  have hperfect : Group.IsPerfect ↥(barM M A) := ⟨hAcomp.component.2.2.1⟩
  have hsimple : IsSimpleGroup ↥(barM M A) := by
    obtain ⟨n, -, hL3n⟩ := hL3A
    have hsimpleQ : IsSimpleGroup (↥A ⧸ pCore 2 ↥A) := hL3n.isSimpleGroup
    obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
      hAcomp.le hAcomp.inf_twoCore
    exact @MulEquiv.isSimpleGroup ↥(barM M A) _
      (↥A ⧸ pCore 2 ↥A) _ hsimpleQ e.symm
  have hnonab : ∃ a b : ↥(barM M A), a * b ≠ b * a := by
    simpa only [isMulCommutative_iff, not_forall] using
      @Group.IsPerfect.not_isMulCommutative ↥(barM M A) _
        hsimple.toNontrivial hperfect
  exact @CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup
    ↥(barM M A) _ hsimple hnonab

theorem dvd_card_barM_of_isTwoPrimeComponent {M A : Subgroup G} {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) (hAcomp : IsTwoPrimeComponent M A)
    (hdvdA : d ∣ Nat.card A) : d ∣ Nat.card (barM M A) := by
  have hAO : ¬ d ∣ Nat.card (pCore 2 ↥A) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥A)).exists_card_eq
    rw [hk]
    intro h
    exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow h))
  have hdvdAQ : d ∣ Nat.card (↥A ⧸ pCore 2 ↥A) := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥A)
    rw [hcard] at hdvdA
    rcases hd.dvd_mul.mp hdvdA with h | h
    · exact h
    · exact absurd h hAO
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
    hAcomp.le hAcomp.inf_twoCore
  rw [← Nat.card_congr e.toEquiv]
  exact hdvdAQ

theorem exists_orderOf_eq_not_commute_barM {M A : Subgroup G} {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) (hAcomp : IsTwoPrimeComponent M A)
    (hL3A : ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥A ⧸ pCore 2 ↥A))
    (hdvdA : d ∣ Nat.card A) :
    ∃ y : ↥(barM M A), orderOf y = d ∧ ∃ l : ↥(barM M A), y * l ≠ l * y := by
  have hdvd := dvd_card_barM_of_isTwoPrimeComponent hd hd2 hAcomp hdvdA
  obtain ⟨y, hyord⟩ := @exists_prime_orderOf_dvd_card' ↥(barM M A) _ _ d ⟨hd⟩ hdvd
  have hyne : y ≠ 1 := by
    intro h
    have h1 : orderOf y = 1 := by rw [h, orderOf_one]
    rw [hyord] at h1
    exact hd.ne_one h1
  have hcenter := center_barM_eq_bot_of_isTwoPrimeComponent hAcomp hL3A
  refine ⟨y, hyord, ?_⟩
  by_contra h
  push Not at h
  have hc : y ∈ Subgroup.center (↥(barM M A)) :=
    Subgroup.mem_center_iff.mpr fun l => (h l).symm
  rw [hcenter] at hc
  exact hyne (Subgroup.mem_bot.mp hc)

theorem barM_centralizer_inf_eq {M W : Subgroup G} (hWM : W ≤ M) (hW : Nat.card W = 3) :
    barM M (Subgroup.centralizer (W : Set G) ⊓ M) =
      Subgroup.centralizer (barM M W) := by
  have hnormal : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hWp : IsPGroup 3 W :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [hW]; norm_num)
  have hcop : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
    rw [hk]
    intro h
    exact (by norm_num : (3 : ℕ) ≠ 2)
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h))
  have hWsub : IsPGroup 3 (W.subgroupOf M) := hWp.comap_subtype
  have hcent := @CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq ↥M _ 3
    ⟨Nat.prime_three⟩ (CFSG.pCore 2 ↥M) hnormal _ hcop (W.subgroupOf M) hWsub
  have hcentWM : Subgroup.centralizer ((W.subgroupOf M : Subgroup ↥M) : Set ↥M) =
      (Subgroup.centralizer (W : Set G)).subgroupOf M := by
    ext z
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hz w hw
      exact congrArg Subtype.val (hz ⟨w, hWM hw⟩ (Subgroup.mem_subgroupOf.mpr hw))
    · intro hz w hw
      exact Subtype.ext (hz (w : G) (Subgroup.mem_subgroupOf.mp hw))
  have hXcent : (Subgroup.centralizer (W : Set G) ⊓ M).subgroupOf M =
      Subgroup.centralizer (W.subgroupOf M : Set ↥M) := by
    rw [hcentWM]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  rw [barM, hXcent, ← hcent]
  rfl

theorem TwelveFiveData.barM_jSub_eq {M H : Subgroup G} {d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    barM M (jSub M H) = barM M L₁ ⊔ barM M L₂ ⊔ barM M L₃ := by
  rw [hd.join_eq, CFSG.AGLEmbedding.barM_sup (sup_le hd.mem₁.le hd.mem₂.le) hd.mem₃.le,
    CFSG.AGLEmbedding.barM_sup hd.mem₁.le hd.mem₂.le]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
