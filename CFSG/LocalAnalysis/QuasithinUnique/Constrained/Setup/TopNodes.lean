module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopPacket
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced

public section

namespace CFSG.QuasithinUnique.Setup.Top

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Lift
open scoped Pointwise

variable {G : Type} [Group G]

theorem ffHyp_of_offender [Finite G] {S P V : Subgroup G} (hR : ReducedAction G S P V)
    {A : Subgroup G} (hA : IsReducedOffender S V A) :
    @FFHyp V (commGroupOfElemAbelian hR.isElemAbelian) inferInstance (autOn P V) (autOn S V)
      (autOn (uniqueMaxOver S P) V) (autOn A V) := by
  have hV := hR.isElemAbelian
  have hAP : A ≤ P := hA.1.1.trans hR.sylow_le
  have hAn : A ≤ Subgroup.normalizer (V : Set G) := hAP.trans hR.le_normalizer
  have hAe := isElemAbelian2_autOn hV hA.1.2.1 hAn
  let _ : CommGroup V := commGroupOfElemAbelian hV
  refine ⟨fun v => ?_, fun N hNH hNn hN2 => ?_, hR.image_sylow, hR.image_not_normal, hR.image_max,
    autOn_le_autOn V hAP, autOn_ne_bot_of_not_le_centralizer hAn hA.2.1, hAe.1, hAe.2, ?_⟩
  · exact Subtype.ext (by simpa [sq] using hV.2 v v.2)
  · exact le_bot_iff.mp (hR.image_pCore ▸
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 N _ hNH hNn hN2)
  · rw [card_autOn_eq_relIndex hAn, card_fixV_autOn_eq hV hAn]
    exact hA.2.2.2

theorem exists_compList {A : Type} [Group A] [Finite A] (H : Subgroup A) :
    ∃ (r : ℕ) (L : Fin r → Subgroup A), IsCompList H r L := by
  classical
  have hfin : Set.Finite {D : Subgroup A | IsComp D H} := Set.toFinite _
  let s := hfin.toFinset
  let e := s.equivFin
  refine ⟨s.card, fun i => (e.symm i).1, ⟨?_, ?_, ?_⟩⟩
  · intro i j h
    exact e.symm.injective (Subtype.ext h)
  · intro i
    exact hfin.mem_toFinset.mp (e.symm i).2
  · intro D hD
    exact ⟨e ⟨D, hfin.mem_toFinset.mpr hD⟩, by simp⟩

theorem not_isSolvable_of_isComp {A : Type} [Group A] {H D : Subgroup A} (hD : IsComp D H) :
    ¬ Group.IsSolvable H := by
  intro hH
  have hq := isQuasisimple_of_isComp hD
  have hDH : D ≤ H := hD.1
  have : Group.IsSolvable ↥H := hH
  have : Group.IsSolvable ↥D :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hDH)
  have : Nontrivial ↥D := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥D
  rw [Group.isPerfect_def.mp hq.1] at hlt
  exact lt_irrefl _ hlt

theorem not_noEvenSL2Component_iff {A : Type} [Group A] {H : Subgroup A} :
    ¬ NoEvenSL2Component H ↔ HasEvenSL2Component H := by
  constructor
  · intro hno
    by_contra hcon
    apply hno
    intro D hD F _ hFin a ha hcard e
    exact hcon ⟨D, a, F, inferInstance, hD, ha, hcard, e⟩
  · rintro ⟨D, n, F, _, hD, hn, hcard, e⟩ hno
    have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    exact hno D hD F n hn hcard e

theorem solvable_packet [Finite G] (hSolv : SolvableA3Family) {S P : Subgroup G}
    (h : PushUpObstruction S P) (hsolv : Group.IsSolvable (autOn P (reducedModule S P))) :
    ∃ (r : ℕ) (L : Fin r → Subgroup G), BlockPacket S P r L ∧ SolvableRefinement r L := by
  obtain ⟨r, K, hpre, halt, hdirect⟩ := hSolv G S P h hsolv
  have hcard : ∀ i, 3 ∣ Nat.card ↥(K i) := fun i => by
    obtain ⟨e⟩ := halt i
    have : Nat.card ↥(K i) = 12 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [this]
    norm_num
  have hord : ∀ i, ∃ x ∈ K i, orderOf x = 3 := fun i => by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (hcard i)
    exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩
  have hKP : ∀ i, K i ≤ P := fun i => (hpre.le_odd i).trans (oddOrderSubgroup_le P)
  have hrank : r ≤ CFSG.Open.pRank 3 P :=
    le_pRank_of_independent Nat.prime_three K hKP hpre.commute hdirect hord
  have hsqt : CFSG.pRank 3 ↥P ≤ 2 := h.sqtk.1 3 Nat.prime_three (by norm_num)
  rw [CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank] at hsqt
  exact ⟨r, K, blockPacket_of_prePacket h hpre (hrank.trans hsqt),
    ⟨halt, fun i => isAltType_three_of_alt4 (hpre.chi0 i) (halt i), hdirect⟩⟩

theorem evenSL2_setting [Finite G] {S P : Subgroup G} (h : PushUpObstruction S P) {n : ℕ}
    {F : Type} [Field F] (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {D : Subgroup (MulAut (reducedModule S P))} (hD : IsComp D (autOn P (reducedModule S P)))
    (hiso : Nonempty (CQ D ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    EvenSL2Setting P S (uniqueMaxOver S P) (reducedModule S P) n F := by
  have hR := reducedAction_of_pushUpObstruction h
  refine ⟨hn, hF, h.sylow, ?_, uniqueMaxOver_spec h.minParabolic, hR.reduced, ?_,
    not_isSolvable_of_isComp hD, ⟨D, hD, hiso⟩⟩
  · intro hnorm
    exact h.minParabolic.2.1 ((Subgroup.normal_subgroupOf_iff_le_normalizer h.sylow.1).mp hnorm)
  · intro hbot
    exact hR.thompson_not_le_centralizer (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)

theorem oddOrderSubgroup_mono {A B : Subgroup G} (h : A ≤ B) :
    oddOrderSubgroup A ≤ oddOrderSubgroup B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem prePacket_of_output [Finite G] {S P : Subgroup G}
    (hX : P ≤ Subgroup.normalizer (reducedModule S P : Set G)) {n r : ℕ}
    {Lc : Fin r → Subgroup (MulAut (reducedModule S P))}
    (out : EvenSL2BlockOutput P S (reducedModule S P) hX n r Lc) :
    PrePacket S P r (fun i => blockOf P S (reducedModule S P) hX (Lc i)) where
  pow_two := out.rank.1
  injective := out.injective
  le_odd i := oddOrderSubgroup_mono (inf_le_right.trans (rhoPreimage_le hX _))
  permuted := out.permuted
  transitive := out.transitive
  chi0 := out.chi0
  commute := out.commute
  odd_eq := out.product.1
  central := out.product.2
  perfect := out.perfect
  gen := out.gen
  u_le i := by
    show ⁅CFSG.Open.pCoreOf 2 (blockOf P S (reducedModule S P) hX (Lc i)),
      blockOf P S (reducedModule S P) hX (Lc i)⁆ ≤ _
    rw [(out.coreComm i).1]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨a, -, v, rfl⟩
    exact Subgroup.mul_mem _ (a v).2 (Subgroup.inv_mem _ v.2)


end CFSG.QuasithinUnique.Setup.Top
