module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Strong
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xFinal
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Plane

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankSylowTwo SmallRankCover smallRankD
  Lemma628Concl Lemma629Concl Lemma630Concl Lemma631Concl KFactAbelianSylowRankThree
  false_of_closing_paragraph)
open CFSG.Yardstones.Md8ed6d263d89 (YSPEmptyStrongOfPlaneLocals)
open scoped commutatorElement

@[expose] def StepL622 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → Prop614At M x z →
      ∀ T : Subgroup G, SmallRankSylowTwo P M T → SmallRankCover p M x

@[expose] def StepL628 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → Prop614At M x z →
      ∀ T : Subgroup G, SmallRankSylowTwo P M T → SmallRankCover p M x →
        Lemma628Concl p M x z T

@[expose] def StepL629 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → Prop614At M x z →
      ∀ T : Subgroup G, SmallRankSylowTwo P M T → SmallRankCover p M x →
        Lemma628Concl p M x z T → ∀ f : ℕ, f.Prime → f ≠ 2 → pCoreOf f (smallRankD p x) ≠ ⊥ →
          Lemma629Concl p M x z T f

@[expose] def StepL630 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → Prop614At M x z →
      ∀ T : Subgroup G, SmallRankSylowTwo P M T → SmallRankCover p M x →
        Lemma628Concl p M x z T → ∀ f : ℕ, f.Prime → f ≠ 2 → pCoreOf f (smallRankD p x) ≠ ⊥ →
          Lemma629Concl p M x z T f → Lemma630Concl p x z T f

@[expose] def StepL631 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → Prop614At M x z →
      ∀ T : Subgroup G, SmallRankSylowTwo P M T → SmallRankCover p M x →
        Lemma628Concl p M x z T → ∀ f : ℕ, f.Prime → f ≠ 2 → pCoreOf f (smallRankD p x) ≠ ⊥ →
          Lemma629Concl p M x z T f → Lemma630Concl p x z T f → Lemma631Concl p f x

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

private theorem exists_prime_pCoreOf_ne_bot {D : Subgroup G} (hO : rankThreePrimeCore 2 D ≠ ⊥) :
    ∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ pCoreOf f D ≠ ⊥ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hND, hDN, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D
  set N : Subgroup G := rankThreePrimeCore 2 D with hNdef
  have hodd : Odd (Nat.card N) := Nat.coprime_two_left.1 hcop
  have hsolv : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  classical
  have hex : ∃ n, derivedSeries ↥N n = ⊥ := hsolv.solvable
  have hk : derivedSeries ↥N (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hk
    refine hO (eq_bot_iff.2 fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥N) ∈ (⊥ : Subgroup ↥N) := hk ▸ Subgroup.mem_top _
    simpa using congrArg Subtype.val (Subgroup.mem_bot.1 this)
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  let A : Subgroup ↥N := derivedSeries ↥N m
  have hchar : A.Characteristic := derivedSeries_characteristic ↥N m
  have hAne : A ≠ ⊥ := Nat.find_min hex (by omega)
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have hc : ⁅x, y⁆ ∈ ⁅A, A⁆ := Subgroup.commutator_mem_commutator hx hy
    have : ⁅A, A⁆ = ⊥ := by
      have := hk
      rw [hm, derivedSeries_succ] at this
      exact this
    rw [this, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  have hAcard : Nat.card A ≠ 1 := fun h => hAne (Subgroup.card_eq_one.1 h)
  obtain ⟨f, hfp, hfA⟩ := Nat.exists_prime_and_dvd hAcard
  have hf2 : f ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 (hfA.trans (Subgroup.card_subgroup_dvd_card A)))
  have : Fact f.Prime := ⟨hfp⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' f hfA
  let A' : Subgroup G := A.map N.subtype
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hAab x hx y hy)
  let V : Subgroup G :=
    { carrier := {x | x ∈ A' ∧ x ^ f = 1}
      one_mem' := ⟨one_mem _, one_pow f⟩
      mul_mem' := fun {u v} hu hv => ⟨mul_mem hu.1 hv.1, by
        rw [(show Commute u v from hA'comm u hu.1 v hv.1).mul_pow, hu.2, hv.2, one_mul]⟩
      inv_mem' := fun {u} hu => ⟨inv_mem hu.1, by rw [inv_pow, hu.2, inv_one]⟩ }
  have hVD : V ≤ D := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx.1
    exact hND y.2
  have hVp : IsPGroup f V := fun x => ⟨1, Subtype.ext (by simpa using x.2.2)⟩
  have hnormA' : ∀ d ∈ D, d ∈ normalizer (A' : Set G) := fun d hd =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic A (hDN hd)
  have hconj : ∀ d ∈ D, ∀ x ∈ V, d * x * d⁻¹ ∈ V := by
    intro d hd x hx
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hnormA' d hd) x).1 hx.1, ?_⟩
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  have hnormV : D ≤ normalizer (V : Set G) := fun d hd => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj d hd x, fun hx => ?_⟩
    have := hconj d⁻¹ (inv_mem hd) _ hx
    simpa [mul_assoc] using this
  have hVnormal : (V.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hVD).2 hnormV
  have hle : V ≤ pCoreOf f D := CFSG.LieType.BorelTits.le_pCoreOf f hVD hVnormal hVp
  have hcN : ((c : ↥A) : ↥N) ^ f = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc] at this
    exact congrArg Subtype.val this
  have hcG : (((c : ↥A) : ↥N) : G) ∈ V :=
    ⟨⟨(c : ↥A).1, (c : ↥A).2, rfl⟩, by simpa using congrArg Subtype.val hcN⟩
  have hc1 : (((c : ↥A) : ↥N) : G) ≠ 1 := by
    intro h1
    have hc1' : c = 1 := Subtype.ext (Subtype.ext h1)
    rw [hc1', orderOf_one] at hc
    exact hfp.one_lt.ne hc
  refine ⟨f, hfp, hf2, fun h0 => hc1 ?_⟩
  have := hle hcG
  rw [h0, Subgroup.mem_bot] at this
  exact this

private theorem isKGroup_centralizer (hS : Situation G p P M) {a : G} (ha : a ≠ 1) :
    CFSG.IsKGroup ↥(centralizer ({a} : Set G)) := by
  have : IsSimpleGroup G := hS.simple
  refine CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1
      hS.toGlobal.d1Global.kProper) _ ?_
  intro htop
  have hc : a ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({a} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact ha (by simpa [h] using hc)
  · obtain ⟨b, c, hbc⟩ := hS.nonab
    exact hbc (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) c).symm

theorem false_of_residues (hK : KFactAbelianSylowRankThree) (h628 : StepL628) (h629 : StepL629)
    (h630 : StepL630) (h631 : StepL631) (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) (h614 : Prop614At M x z) {T : Subgroup G} (hT : SmallRankSylowTwo P M T)
    (hcov : SmallRankCover p M x) : False := by
  have h28 := h628 G p P M x z hS hx hz h614 T hT hcov
  have hO : rankThreePrimeCore 2 (smallRankD p x) ≠ ⊥ := by
    intro hbot
    apply hx.not_le
    refine hcov.trans (sup_le inf_le_left ?_)
    have : rankThreePrimeCore 2 (rankThreePrimeCore p (centralizer ({x} : Set G))) = ⊥ := hbot
    rw [this]
    exact bot_le
  obtain ⟨f, hfp, hf2, hfD⟩ := exists_prime_pCoreOf_ne_bot hO
  have h29 := h629 G p P M x z hS hx hz h614 T hT hcov h28 f hfp hf2 hfD
  have h30 := h630 G p P M x z hS hx hz h614 T hT hcov h28 f hfp hf2 hfD h29
  have h31 := h631 G p P M x z hS hx hz h614 T hT hcov h28 f hfp hf2 hfD h29 h30
  obtain ⟨a, haF, ha1, J, hJ, hJ3, hFJ⟩ := h31
  obtain ⟨⟨E, -, hEp, -, -, hEc, -, hEi⟩, hN⟩ := h30
  exact false_of_closing_paragraph hK hfp hf2 h29.2.2.2.1 h29.2.2.2.2.1 hEp hEi hEc hN haF ha1
    (isKGroup_centralizer hS ha1) hJ hJ3 hFJ

theorem ysPEmptyStrongOfPlaneLocals_of_steps (hK : KFactAbelianSylowRankThree)
    (h622 : StepL622) (h628 : StepL628) (h629 : StepL629) (h630 : StepL630)
    (h631 : StepL631) : YSPEmptyStrongOfPlaneLocals := by
  intro G _ _ _ hnonab hKp hchar he hpre hD1 hD2 hFC h57 p P M hp5 hIH hloc hPM h614
  by_contra hns
  have hglob : Global G := ⟨⟨inferInstance, hnonab, hKp, hchar, he, hpre⟩, hD1, hD2, hFC, h57⟩
  have hS : Situation G p P M := ⟨hglob, hp5, hIH, hloc, hPM⟩
  obtain ⟨x, hx⟩ := exists_point hS hns
  obtain ⟨z, hz, -, -, -, hB⟩ := exists_central_generator hS hx
  have h614' : Prop614At M x z := fun H hH hBH ⟨S, hSHM, hS1, hS2, hBS⟩ =>
    h614 x hx.mem hx.order hx.not_le hx.sylow H hH (by rw [hB]; exact hBH)
      ⟨S, hSHM, hS1, hS2, by rw [hB]; exact hBS⟩
  obtain ⟨T, hT⟩ := exists_sylowTwo hS
  exact false_of_residues hK h628 h629 h630 h631 hS hx hz h614' hT
    (h622 G p P M x z hS hx hz h614' T hT)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
