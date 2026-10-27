module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Reach
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum
import CFSG.LocalAnalysis.ComponentClassification.CatFC.FixedComponent
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreGriess
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
import CFSG.LieType.Simplicity.LieModelFinite
import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.Open CFSG.EvenSporadicStandard.Induction
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatFC CFSG.Blueprint.Multiplier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)
open CFSG.ComponentClassification.HarrisLit.T1.SporRow (not_oddLieOrder_E62)

@[expose] def Seitz29OddCat : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Blueprint.Catalog ↥N' → HasEvenCover ↥N' →
    ∀ P : Subgroup Y, SolStd P → CFSG.IsQuasisimple ↥P → Odd (Nat.card ↥(center ↥P)) →
      LieModel (↥P ⧸ center ↥P) .twistedE6 0 2 1 →
        LieModel ↥N' .twistedE6 0 2 1 ∨ LieModel ↥N' .E6 0 2 2 ∨
          IsSporadic ↥N' .B ∨ IsSporadic ↥N' .M

namespace Seitz29Cat

theorem card_twistedE6_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .twistedE6 0 2 1) : Nat.card X = 76532479683774853939200 := by
  obtain ⟨-, h1, -⟩ := hO X .twistedE6 0 2 1 h.admissible h
  have hd : lieOrderDivisor .twistedE6 0 (2 ^ 1) = 3 := by decide +kernel
  have hn : lieOrderNumerator .twistedE6 0 (2 ^ 1) = 229597439051324561817600 := by decide +kernel
  rw [hd, hn] at h1
  omega

theorem factorial_div_two_ne (k : ℕ) : k.factorial / 2 ≠ 76532479683774853939200 := by
  intro h
  by_cases hk : k < 23
  · interval_cases k <;> simp [Nat.factorial] at h
  · have h23 : 23 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h2 : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h3 : k.factorial = 2 * (k.factorial / 2) := (Nat.mul_div_cancel' h2).symm
    rw [h] at h3
    rw [h3] at h23
    revert h23
    decide +kernel

theorem dvd_sporOrder (s : TauCeti.SporadicName) (h : 76532479683774853939200 ∣ sporOrder s) :
    s = .B ∨ s = .M := by
  cases s <;> first
    | (left; rfl)
    | (right; rfl)
    | exact absurd h (by
        unfold sporOrder CFSG.ComponentClassification.GSThmB.QPUSpor.sporFactors
        decide +kernel)

theorem exceptionalOrders_even_cases {t : StatedLieTag} {n f : ℕ}
    (h : 2 ∣ (exceptionalOrders t n 2 f).1) :
    (t = .twistedE6 ∧ n = 0 ∧ f = 1) ∨
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨
    (t = .PSU ∧ n = 4 ∧ f = 1) ∨ (t = .PSp ∧ n = 3 ∧ f = 1) ∨ (t = .G2 ∧ n = 0 ∧ f = 2) ∨
    (t = .F4 ∧ n = 0 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨
    (t = .PSU ∧ n = 6 ∧ f = 1) ∨ (t = .twistedB2 ∧ n = 0 ∧ f = 3) ∨
    (t = .PSL ∧ n = 3 ∧ f = 2) := by
  unfold exceptionalOrders at h
  split at h <;> first | simp_all | (revert h; decide)

theorem card_lt_of_exceptional {c : ℕ} {t : StatedLieTag} {n f : ℕ}
    (h : (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨
    (t = .PSU ∧ n = 4 ∧ f = 1) ∨ (t = .PSp ∧ n = 3 ∧ f = 1) ∨ (t = .G2 ∧ n = 0 ∧ f = 2) ∨
    (t = .F4 ∧ n = 0 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨
    (t = .PSU ∧ n = 6 ∧ f = 1) ∨ (t = .twistedB2 ∧ n = 0 ∧ f = 3) ∨
    (t = .PSL ∧ n = 3 ∧ f = 2))
    (h1 : c * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) :
    c < 76532479683774853939200 := by
  have hd : 0 < lieOrderDivisor t n (2 ^ f) ∧
      lieOrderNumerator t n (2 ^ f) < 76532479683774853939200 := by
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide +kernel
  obtain ⟨hpos, hlt⟩ := hd
  calc c = c * 1 := (mul_one c).symm
    _ ≤ c * lieOrderDivisor t n (2 ^ f) := Nat.mul_le_mul_left c hpos
    _ = lieOrderNumerator t n (2 ^ f) := h1
    _ < _ := hlt

theorem exceptional_of_evenCover
    {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ} (hmodel : LieModel X t n 2 f)
    (hev : HasEvenCover X) : 2 ∣ (exceptionalOrders t n 2 f).1 := by
  by_contra h2
  have hadm := hmodel.admissible
  have he₁ : Odd (exceptionalOrders t n 2 f).1 := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have he₂ : Odd (exceptionalOrders t n 2 f).2 :=
    Odd.of_dvd_nat he₁ (CFSG.ComponentClassification.Foote5.exceptionalOrders_snd_dvd_fst t n 2 f)
  have hfin : Finite X := CFSG.LieType.Simplicity.finite_of_native_lieModel hmodel
  have hodd := CFSG.ComponentClassification.Foote5.oddMultiplier_of_griessRow
    (CFSG.ComponentClassification.Foote5.griessRow_of_char_two hmodel h2)
    (CFSG.ComponentClassification.Foote5.odd_genericOrders_two hadm) (Nat.odd_mul.mpr ⟨he₁, he₂⟩)
  obtain ⟨Q₀, _, hq, hevQ, ⟨e⟩⟩ := hev
  have : Finite Q₀ :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hq e
  exact (Nat.not_even_iff_odd.mpr (hodd Q₀ hq.1.commutator_eq_top ⟨e⟩)) hevQ

theorem false_of_oddLie_fixedComponent (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] (hodd : OddLieType S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : CFSG.IsComponent D) (hc : Nat.card (↥D ⧸ center ↥D) = 76532479683774853939200) :
    False := by
  rcases odd_arm hGLS hodd hσ hD with ⟨τ', n', p, f', hp, hp2, hadm', hmod'⟩ | hL
  · obtain ⟨-, h1, h2⟩ := hO _ τ' n' p f' hadm' hmod'
    rw [hc] at h1 h2
    exact not_oddLieOrder_E62 ⟨τ', n', p, f', hp, hp2, hadm', h1, h2⟩
  · have hadmL : StatedLieAdmissible .PSL 2 2 3 :=
      ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩
    obtain ⟨-, h1, -⟩ := hO _ .PSL 2 2 3 hadmL hL
    have h504 : Nat.card ↥D = 504 := by
      simp only [lieOrderDivisor, lieOrderNumerator] at h1
      norm_num [Finset.Icc_self] at h1
      omega
    have hle : Nat.card (↥D ⧸ center ↥D) ≤ Nat.card ↥D :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [hc, h504] at hle
    omega

end Seitz29Cat

open Seitz29Cat in
theorem seitz29OddCat_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = sporOrder s)
    (hExc : ∀ (X : Type) [Group X] (t : StatedLieTag) (n f : ℕ), LieModel X t n 2 f →
      HasEvenCover X → 2 ∣ (exceptionalOrders t n 2 f).1) : Seitz29OddCat := by
  intro Y _ _ N' hF hidx hcat hev P hP hq hodd hE6
  have hnorm := hF.normal
  have hSimple := hF.isSimpleGroup
  have hna := hF.nonabelian
  have hPN : P ≤ N' := le_of_perfect_of_index_le_two hidx hq.1
  obtain ⟨t, ht, hPc⟩ := hP.exists_involution
  obtain ⟨σ, D, hσ, hD, -, ⟨e⟩⟩ := exists_fixedComponent hF ht hPc hPN
  have hKcard : Nat.card (↥P ⧸ center ↥P) = 76532479683774853939200 := card_twistedE6_two hO hE6
  have hDcard : Nat.card (↥D ⧸ center ↥D) = 76532479683774853939200 := by
    rw [Nat.card_congr (quotientCenterEquiv e).toEquiv, hKcard]
  have hdvd : 76532479683774853939200 ∣ Nat.card ↥N' := by
    rw [← hKcard]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hPN)
  have hpos : 0 < Nat.card ↥N' := Nat.card_pos
  have hge : 76532479683774853939200 ≤ Nat.card ↥N' := Nat.le_of_dvd hpos hdvd
  rcases (Milestones.ct_catalog_nonabelian_type_partition ↥N' hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hoddL | ⟨t', n', f', hadm, hmod⟩ | ⟨s, ⟨es⟩⟩
  · by_cases hn6 : n = 6
    · subst hn6
      exact (false_of_oddLie_fixedComponent hGLS hO (oddLieType_of_alternating_six ⟨θ⟩) hσ hD
        hDcard).elim
    · obtain ⟨k, hk5, -, -, ⟨eA⟩⟩ := alt_arm hn hn6 θ hσ hD
      haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
      have hk : Nat.card (↥D ⧸ center ↥D) = k.factorial / 2 := by
        rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      exact (factorial_div_two_ne k (hk.symm.trans hDcard)).elim
  · exact (false_of_oddLie_fixedComponent hGLS hO hoddL hσ hD hDcard).elim
  · have h2 : 2 ∣ (exceptionalOrders t' n' 2 f').1 := hExc ↥N' t' n' f' hmod hev
    rcases exceptionalOrders_even_cases h2 with ⟨rfl, rfl, rfl⟩ | hother
    · exact Or.inl hmod
    · exfalso
      obtain ⟨-, h1, -⟩ := hO ↥N' t' n' 2 f' hadm hmod
      have hlt := card_lt_of_exceptional hother h1
      omega
  · by_cases hsM : s = .M
    · subst hsM
      exact Or.inr (Or.inr (Or.inr ⟨es⟩))
    · have hcs : Nat.card ↥N' = sporOrder s := (Nat.card_congr es.toEquiv).trans (hcard s hsM)
      rw [hcs] at hdvd
      rcases dvd_sporOrder s hdvd with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨es⟩))
      · exact absurd rfl hsM

theorem seitz29OddCat_holds
    : Seitz29OddCat :=
  seitz29OddCat_of_inputs CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.ComponentClassification.GSThmB.QPUSpor.card_carrier_eq_sporOrder
    (fun _ _ _ _ _ hm hev => Seitz29Cat.exceptional_of_evenCover hm hev)

end CFSG.EvenSporadicStandard.Induction.Hyp
