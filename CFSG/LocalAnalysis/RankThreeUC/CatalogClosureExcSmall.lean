module

public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcBasic
import CFSG.RankThree.PartTwo.Census.Carrier.G2Even
import CFSG.RankThree.PartTwo.Census.Carrier.D4EvenRank
import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Local
import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert
import CFSG.RankThree.PartOne.Q1327C.BNoCube
import CFSG.RankThree.PartOne.KF.ClsSz
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.Assembly.OpenBridges
public import CFSG.LieType.Ree.Duality

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.Open
  CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Census

@[expose] def SmallExceptionalTwoCase (G : Type) [Group G] : Prop :=
  (∃ f : ℕ, SuzukiModel G 2 f) ∨
    (∃ f : ℕ, ChevalleyExceptionalModel G .G2 2 f) ∨
    (∃ f : ℕ, ChevalleyExceptionalModel G .trialityD4 2 f) ∨
    (∃ f : ℕ, ReeTitsModel G .twistedF4 2 f) ∨ ∃ f : ℕ, ReeTitsModel G .Tits 2 f

section Suzuki

variable {G : Type} [Group G] [Finite G]

theorem evenRank_le_one_of_suzukiModel {p f : ℕ} (h : SuzukiModel G p f) :
    CFSG.Assembly.evenRank G ≤ 1 := by
  obtain ⟨rfl, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  let e' : G ≃* Sz a :=
    e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  have : Finite (Sz a) := Finite.of_equiv _ e'.toEquiv
  refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
  rw [localRank_eq_of_mulEquiv e' hr]
  exact CFSG.RankThree.PartOne.KFU.localRank_le_one_of_fusionBenderBorel
    (bender_suzuki_borel_full a ha) hr hr2

end Suzuki

section Certified

set_option linter.unusedSectionVars false


variable {G : Type} [Group G] [Finite G]

theorem evenRank_le_two_of_G2 {f : ℕ} (h : ChevalleyExceptionalModel G .G2 2 f) :
    CFSG.Assembly.evenRank G ≤ 2 := by
  obtain ⟨-, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  have : CharP K 2 := charP_two_of_card hK
  refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
  by_cases hr3 : r = 3
  · subst hr3
    rw [localRank_eq_of_mulEquiv e hr]
    exact CFSG.RankThree.PartTwo.Census.Carrier.G2Even.localRank_three_adjointQuotient K
  · refine localRank_le_two_of_no_cube hr fun E hE hcard => ?_
    let e2 : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
      (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot
    let e3 := e.trans e2
    refine CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_G2_five K hr
      (five_le_of_prime_ne hr hr2 hr3) ?_ (E := E.map e3.toMonoidHom) ?_ ?_
    · rw [hK]
      intro hd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
    · rintro _ ⟨y, hy, rfl⟩
      change (e3 y) ^ r = 1
      rw [← map_pow, hE y hy, map_one]
    · rw [Subgroup.card_map_of_injective e3.injective, hcard]

theorem evenRank_le_two_of_D4 {f : ℕ} (h : ChevalleyExceptionalModel G .trialityD4 2 f) :
    CFSG.Assembly.evenRank G ≤ 2 := by
  have h' := h
  obtain ⟨hadm, hm⟩ := h
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  have : CharP K 2 := charP_two_of_card (f := f * 3) (by rw [hK3, ← pow_mul])
  refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
  by_cases hr3 : r = 3
  · subst hr3
    rw [localRank_eq_of_mulEquiv e hr]
    exact CFSG.RankThree.PartTwo.Census.Carrier.D4Even.localRank_three_derivedCentralQuotient f
      hadm.2.1 hK3 σ hσ
  · refine localRank_le_two_of_no_cube hr fun E hE hcard => ?_
    exact CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_triality_five h' hr
      (five_le_of_prime_ne hr hr2 hr3) hE hcard

theorem evenRank_le_two_of_ree {f : ℕ} (h : ReeTitsModel G .twistedF4 2 f) :
    CFSG.Assembly.evenRank G ≤ 2 := by
  have h' := h
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KEXC.exists_gamma_of_model h
  refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
  by_cases hr3 : r = 3
  · subst hr3
    rw [localRank_eq_of_mulEquiv e hr]
    exact CFSG.RankThree.PartTwo.Census.Carrier.ReeF4.localRank_three_reeGamma ha
      (by rw [hK, hfa])
  · refine localRank_le_two_of_no_cube hr fun E hE hcard => ?_
    exact CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_ree_five h' hr
      (five_le_of_prime_ne hr hr2 hr3) hE hcard

theorem not_pow_three_dvd_card_reeFixed_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 3 ∣ 35942400 := by
  intro h
  have e : (35942400 : ℕ) = 2 ^ 12 * (3 ^ 3 * (5 ^ 2 * 13)) := by norm_num
  rw [e] at h
  have hpd : p ∣ 2 ^ 12 * (3 ^ 3 * (5 ^ 2 * 13)) :=
    (dvd_pow_self p three_ne_zero).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    omega
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      omega
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h3)
        norm_num at h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h3
        norm_num at h

theorem evenRank_le_two_of_tits {f : ℕ} (h : ReeTitsModel G .Tits 2 f) :
    CFSG.Assembly.evenRank G ≤ 2 := by
  obtain ⟨⟨-, -, -, -, hf1⟩, a, hf, hmodel⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have ha : a = 0 := by omega
  subst ha
  have hK2 : Nat.card K = 2 := by rw [hK, hf1, pow_one]
  have hc : CharP K 2 := charP_two_of_card (f := 1) (by rw [hK2, pow_one])
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hc
  let e' := e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (CFSG.LieType.Ree.reeFixedGroup_eq_map_reeFixed
        CFSG.LieType.Ree.ReeTag.F4 K 0)).trans
      ((CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0).equivMapOfInjective _
        Subtype.val_injective).symm))
  have hcardG : Nat.card G ∣ 35942400 := by
    rw [Nat.card_congr e'.toEquiv]
    exact (Subgroup.card_quotient_dvd_card _).trans
      ((Subgroup.card_subgroup_dvd_card _).trans
        (by rw [CFSG.RankThree.PartTwo.Census.Carrier.Tits.card_reeFixed hK2]))
  refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
  by_cases hr3 : r = 3
  · subst hr3
    rw [localRank_eq_of_mulEquiv e' hr]
    exact CFSG.RankThree.PartTwo.Census.Carrier.Tits.localRank_three_commutator_quotient_center hK2
  · refine localRank_le_two_of_no_cube hr fun E _ hcard => ?_
    exact not_pow_three_dvd_card_reeFixed_two hr (five_le_of_prime_ne hr hr2 hr3)
      (hcard ▸ (Subgroup.card_subgroup_dvd_card E).trans hcardG)

theorem evenRank_le_two_of_smallExceptionalTwoCase (h : SmallExceptionalTwoCase G) :
    CFSG.Assembly.evenRank G ≤ 2 := by
  rcases h with ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩
  · exact (evenRank_le_one_of_suzukiModel h).trans (by norm_num)
  · exact evenRank_le_two_of_G2 h
  · exact evenRank_le_two_of_D4 h
  · exact evenRank_le_two_of_ree h
  · exact evenRank_le_two_of_tits h

theorem not_standing_of_smallExceptionalTwoCase (hS : Standing G)
    (h : SmallExceptionalTwoCase G) : False := by
  have h2 := evenRank_le_two_of_smallExceptionalTwoCase h
  have h3 := hS.rank
  rw [← CFSG.Assembly.evenRank_eq_open] at h3
  omega

end Certified

end CFSG.LocalAnalysis.RankThreeUC
