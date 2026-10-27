module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PrimeInduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTheoremE
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83SmallRankPrimeThree (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → (∀ y : G, ¬ IsLargeObstruction p M y) →
      LargerPrimesUnique G p → p = 3

@[expose] def GL83SmallRankStructure (G : Type) [Group G] [Finite G] : Prop :=
  3 ∈ rankThreeSigmaA G → ∀ (P : Sylow 3 G) (M : Subgroup G), IsCoreMaxLocal 3 P M →
    ¬ rankThreeGamma 1 3 (P : Subgroup G) ≤ M → (∀ y : G, ¬ IsLargeObstruction 3 M y) →
      Group.IsSolvable M ∧
        Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))

@[expose] def GL83SmallRankQ8 (G : Type) [Group G] [Finite G] : Prop :=
  3 ∈ rankThreeSigmaA G → ∀ (P : Sylow 3 G) (M : Subgroup G), IsCoreMaxLocal 3 P M →
    ¬ rankThreeGamma 1 3 (P : Subgroup G) ≤ M → (∀ y : G, ¬ IsLargeObstruction 3 M y) →
      Group.IsSolvable M →
      Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
      ∀ Y : Subgroup G, Y ≤ P → Nat.card Y = 3 → ¬ Y ≤ thompsonSubgroup (P : Subgroup G) →
        ∃ Q : Subgroup G, Q ≤ rankThreePrimeCore 3 M ∧ IsPGroup 2 Q ∧
          ¬ 2 ∣ (Q.subgroupOf (rankThreePrimeCore 3 M)).index ∧
          (P : Subgroup G) ≤ normalizer (Q : Set G) ∧
          ∃ m : ℕ, 1 ≤ m ∧ rankThreeIsQ8CentralCyclic (Q ⊓ centralizer (Y : Set G)) m

@[expose] def GL83SmallRankUniquePlane (G : Type) [Group G] [Finite G] : Prop :=
  3 ∈ rankThreeSigmaA G → ∀ (P : Sylow 3 G) (M : Subgroup G), IsCoreMaxLocal 3 P M →
    ¬ rankThreeGamma 1 3 (P : Subgroup G) ≤ M → (∀ y : G, ¬ IsLargeObstruction 3 M y) →
      Group.IsSolvable M →
      Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
      ∀ x z : G, x ∈ (P : Subgroup G) → x ≠ 1 → x ^ 3 = 1 → ¬ centralizer ({x} : Set G) ≤ M →
        z ∈ (P : Subgroup G) → z ∈ centralizer ((P : Subgroup G) : Set G) → z ≠ 1 → z ^ 3 = 1 →
          ∀ H : Subgroup G, IsTwoLocal H → zpowers x ⊔ zpowers z ≤ H → H ≤ M

theorem normalizer_le_of_three_le_pRank_sup_centralizer (hS : Setting G) (hU0 : FullCoreLocal G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) (hempty : ∀ y : G, ¬ IsLargeObstruction p M y)
    {Q : Subgroup G} (hQP : Q ≤ P) (hQ : Q ≠ ⊥)
    (h3 : 3 ≤ CFSG.Open.pRank p (Q ⊔ ((P : Subgroup G) ⊓ centralizer (Q : Set G)))) :
    normalizer (Q : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hQp : IsPGroup p Q := P.isPGroup'.to_le hQP
  by_cases hQc : IsCyclic Q
  ·
    obtain ⟨z, hzQ, -, hzord⟩ := exists_mem_centralizer_orderOf_eq hQp hQ
    have hQ1 : 1 ≤ CFSG.Open.pRank p Q := by
      have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
      have hze : CFSG.IsElementaryAbelian p (zpowers z) :=
        CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hzp
      unfold CFSG.Open.pRank
      exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨_, zpowers_le.mpr hzQ,
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hze,
        by rw [Nat.card_zpowers, hzord, pow_one]⟩
    obtain ⟨y, hyQ, hy1, hyp, hNQy⟩ :=
      exists_pow_eq_one_normalizer_le_of_isCyclic hprime hQp hQc hQ1
    have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
      intro a ha b hb
      have := (hQc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
      exact congrArg Subtype.val this
    have hle : Q ⊔ ((P : Subgroup G) ⊓ centralizer (Q : Set G)) ≤
        (P : Subgroup G) ⊓ centralizer ({y} : Set G) := by
      refine sup_le (le_inf hQP fun a ha => mem_centralizer_singleton_iff.mpr
        (hQab a ha y hyQ)) (le_inf inf_le_left fun a ha => ?_)
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ha.2 y hyQ).symm
    have hy3 := h3.trans (pRank_mono p hprime.one_lt hle)
    have hCM : centralizer ({y} : Set G) ≤ M := by
      by_contra hCM
      exact hempty y ⟨hPM (hQP hyQ), hy1, hyp,
        hy3.trans (pRank_mono p hprime.one_lt inf_le_right), hCM⟩
    exact hNQy.trans (normalizer_zpowers_le_of_centralizer_le hS hU0 hp hM (by omega) hCM)
  · exact normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hQp (hQP.trans hPM)
      (two_le_pRank_of_not_isCyclic hprime (sigmaA_odd p hp) hQp hQc)

omit [Finite G] in
theorem SmallRankPlane.mem_of_mem_centralizer_singleton {p : ℕ} {P : Subgroup G} {x z : G}
    (hB : SmallRankPlane p P x z) (hzc : z ∈ centralizer (P : Set G)) {w : G} (hwP : w ∈ P)
    (hwx : w ∈ centralizer ({x} : Set G)) (hwp : w ^ p = 1) : w ∈ zpowers x ⊔ zpowers z := by
  refine hB.mem_of_mem_centralizer w ?_ hwp
  have hle : zpowers x ⊔ zpowers z ≤ centralizer ({w} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp hwx).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hzc w hwP).symm))
  exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_singleton_iff.mp (hle hb)

theorem le_of_two_le_pRank_of_largeObstruction_empty (hS : Setting G) (hD2 : TheoremD2 G)
    (hU0 : FullCoreLocal G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M : Subgroup G} (hM : IsCoreMaxLocal p P M) (hempty : ∀ y : G, ¬ IsLargeObstruction p M y)
    (hD2three : 3 ∈ rankThreeSigmaA G → ∀ P₃ : Sylow 3 G, IsCoreMaxLocal 3 P₃ M →
      ¬ Group.IsSolvable M → rankThreeGamma 1 3 (P₃ : Subgroup G) ≤ M)
    (hplane : ∀ x z : G, x ∈ (P : Subgroup G) → x ≠ 1 → x ^ p = 1 →
      ¬ centralizer ({x} : Set G) ≤ M → z ∈ (P : Subgroup G) →
      z ∈ centralizer ((P : Subgroup G) : Set G) → z ≠ 1 → z ^ p = 1 →
      ∀ H : Subgroup G, IsTwoLocal H → zpowers x ⊔ zpowers z ≤ H → H ≤ M)
    {H : Subgroup G} (hH : IsTwoLocal H) (h2 : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) : H ≤ M := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  refine le_of_two_le_pRank_of_elemAbelian_obstructed hS hD2 hU0 hp hM (fun h3 P₃ hM₃ =>
    ⟨fun Q hQP hQne hQ3 => ?_, hD2three h3 P₃ hM₃⟩) ?_ hH h2
  · have hempty₃ : ∀ y : G, ¬ IsLargeObstruction 3 M y := by
      obtain rfl := eq_three_of_three_mem_sigmaA hS.rank h3 hp
      exact hempty
    exact normalizer_le_of_three_le_pRank_sup_centralizer hS hU0 h3 hM₃ hempty₃ hQP hQne hQ3
  intro R hRP hRe k hk hRc y hyR hy1 hyp hyM H' hH' hRH'
  obtain ⟨z, hzP, hzc, hzord⟩ := exists_mem_centralizer_orderOf_eq P.isPGroup'
    (fun h => hy1 (mem_bot.mp (h ▸ hRP hyR)))
  have hz1 : z ≠ 1 := fun h => hprime.one_lt.ne' (by rw [← hzord, h, orderOf_one])
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hB := smallRankPlane_of_largeObstruction_empty hS hp hM hempty (hRP hyR) hy1 hyp hyM
    hzP hzc hz1 hzp
  have hRB : R ≤ zpowers y ⊔ zpowers z := fun w hw =>
    hB.mem_of_mem_centralizer_singleton hzc (hRP hw)
      (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (hRe.1.is_comm.comm ⟨w, hw⟩ ⟨y, hyR⟩))) (hRe.2 w hw)
  have hBR : zpowers y ⊔ zpowers z ≤ R := by
    refine (Subgroup.eq_of_le_of_card_ge hRB ?_).ge
    rw [hB.card_eq, hRc]
    exact Nat.pow_le_pow_right hprime.pos hk
  exact hplane y z (hRP hyR) hy1 hyp hyM hzP hzc hz1 hzp H' hH' (hBR.trans hRH')

omit [Finite G] in
private theorem thompsonSubgroup_le' (S : Subgroup G) : thompsonSubgroup S ≤ S :=
  CFSG.ambientMaxCardThompson_le S

theorem smallRankCase_of_inputs (hS : Setting G) (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G)
    (hA : GL83SmallRankPrimeThree G) (hB : GL83SmallRankStructure G) (hC : GL83SmallRankQ8 G)
    (hD : GL83SmallRankUniquePlane G) : SmallRankCase G := by
  intro p hp P M hM hfail hempty hIH
  obtain rfl := hA p hp P M hM hfail hempty hIH
  obtain ⟨hsolv, ⟨e⟩⟩ := hB hp P M hM hfail hempty
  have hPM := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hΓJ : rankThreeGamma 1 3 (thompsonSubgroup (P : Subgroup G)) ≤ M :=
    gamma_one_le_of_forall_centralizer_le hS hU0 hp hM (thompsonSubgroup_le' _)
      fun y hy hy1 hy3 => by
        by_contra hCM
        exact hempty y ⟨hPM (thompsonSubgroup_le' _ hy), hy1, hy3,
          (three_le_pRank_inf_centralizer_of_mem_thompsonSubgroup e hy).trans
            (pRank_mono 3 (by norm_num) inf_le_right), hCM⟩
  refine ⟨Or.inr (Or.inr ⟨rfl, hsolv, ⟨e⟩, hΓJ, hC hp P M hM hfail hempty hsolv ⟨e⟩⟩),
    fun H hH h2 => ?_⟩
  exact le_of_two_le_pRank_of_largeObstruction_empty hS hD2 hU0 hp hM hempty
    (fun _ _ _ h => absurd hsolv h) (hD hp P M hM hfail hempty hsolv ⟨e⟩) hH h2

end CFSG.LocalAnalysis.RankThreeTheoremC
