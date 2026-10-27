module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Aux
import CFSG.Sporadic.Schreier.PairMcLOut
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem card_center_eq_card_inf_centralizer {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card (center H) = Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) := by
  have h : (center H).map H.subtype = H ⊓ centralizer (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (mem_center_iff.mp hy ⟨t, ht⟩)⟩
    · rintro ⟨hxH, hxC⟩
      exact ⟨⟨x, hxH⟩, mem_center_iff.mpr fun t =>
        Subtype.ext (mem_centralizer_iff.mp hxC t t.2), rfl⟩
  rw [← h, card_map_of_injective H.subtype_injective]

theorem threeFourTwoNoneAt_of_normalizer_maximal {p : ℕ} {X : Type*} [Group X]
    (hX : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (hT : ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* X) →
      ¬ p ∣ Nat.card (Outer K) ∧ ∀ T : Sylow p K, 2 ≤ CFSG.Open.pRank p (T : Subgroup K) ∧
        Nat.card ((T : Subgroup K) ⊓ centralizer ((T : Subgroup K) : Set K) : Subgroup K) = p ∧
        Group.IsSolvable (normalizer ((T : Subgroup K) : Set K)) ∧
        ∀ H : Subgroup K, normalizer ((T : Subgroup K) : Set K) ≤ H →
          H = normalizer ((T : Subgroup K) : Set K) ∨ H = ⊤) :
    ThreeFourTwoNoneAt p X := by
  refine threeFourTwoNoneAt_of_inf hX hnab hout ?_
  intro Y _ _ K Y₀ E R hp _ hKn hKX _ _ _ hER hE hEc hcore _ hKY₀
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hKn
  obtain ⟨hpK, hTK⟩ := hT K hKX
  obtain ⟨e⟩ := hKX
  have hZK : K ⊓ centralizer (K : Set Y) = ⊥ := by
    haveI : IsSimpleGroup K := MulEquiv.isSimpleGroup e
    obtain ⟨a, b, hab⟩ := hnab
    have hZ := CFSG.ComponentClassification.Helpers.center_eq_bot K
      ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
    rw [eq_bot_iff]
    rintro z ⟨hzK, hzC⟩
    have h : (⟨z, hzK⟩ : K) ∈ center K :=
      mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp hzC g g.2)
    rw [hZ, mem_bot] at h
    exact mem_bot.mpr (congrArg Subtype.val h)
  obtain ⟨T, hT₀⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨h2, hZ, hsol, hmax⟩ := hTK T
  have h2' : 2 ≤ CFSG.Open.pRank p ((R : Subgroup Y) ⊓ K) := by
    rw [← hT₀]
    exact h2.trans (CFSG.SectionRank.pRank_le_map hp.one_lt K.subtype K.subtype_injective _)
  have hZ' : Nat.card (center ((R : Subgroup Y) ⊓ K : Subgroup Y)) = p := by
    rw [← hT₀]
    refine (Nat.card_congr (Subgroup.centerCongr
      ((T : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).symm).toEquiv).trans ?_
    rw [card_center_eq_card_inf_centralizer]
    exact hZ
  have hN := normalizer_inf_le_of_card_center_eq R hER hE hEc hcore hZK hpK h2' hZ'
  have hle : normalizer ((T : Subgroup K) : Set K) ≤ Y₀.subgroupOf K := fun k hk => by
    refine mem_subgroupOf.mpr (hN ?_)
    have h := le_normalizer_map K.subtype (mem_map_of_mem K.subtype hk)
    rwa [hT₀] at h
  refine Or.inl ?_
  rcases hmax _ hle with h | h
  · haveI : Group.IsSolvable (Y₀.subgroupOf K) := by
      rw [h]
      exact hsol
    let f : (K ⊓ Y₀ : Subgroup Y) →* Y₀.subgroupOf K :=
      { toFun := fun x => ⟨⟨x, x.2.1⟩, mem_subgroupOf.mpr x.2.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy =>
      Subtype.ext (congrArg (fun z : Y₀.subgroupOf K => ((z : K) : Y)) hxy)
  · exact absurd (fun k hk => mem_subgroupOf.mp (h ▸ mem_top (⟨k, hk⟩ : K))) hKY₀

theorem isSolvable_and_not_dvd_of_card_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Group.IsSolvable G ∧ ¬ p ∣ Nat.card G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  refine ⟨?_, fun hdvd => ?_⟩
  · have h2 : IsPGroup 2 G := by
      rcases (by omega : Nat.card G = 2 ^ 0 ∨ Nat.card G = 2 ^ 1) with hc | hc
      · exact IsPGroup.of_card hc
      · exact IsPGroup.of_card hc
    haveI := h2.isNilpotent
    infer_instance
  · have hle := Nat.le_of_dvd hpos hdvd
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    omega

open CFSG.Blueprint.NativeSporadic (Carrier) in
theorem sporadicIndex_facts_of_bridge {s : TauCeti.SporadicName}
    (hb : Nonempty (Carrier s ≃* s.Group)) [Finite (Carrier s)] (hs : IsSimpleGroup (Carrier s))
    (hO : Nat.card (Outer (Carrier s)) ≤ 2) {p : ℕ} (hp : p.Prime)
    (hsq : p ^ 2 ∣ Nat.card (Carrier s)) :
    IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group ∧
      (∃ a b : (TauCeti.CFSGIndex.sporadic s).Group, a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (TauCeti.CFSGIndex.sporadic s).Group) := by
  obtain ⟨b⟩ := hb
  haveI := hs
  haveI hX : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group := b.symm.isSimpleGroup
  haveI : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv _ b.toEquiv
  haveI : Finite (MulAut (TauCeti.CFSGIndex.sporadic s).Group) := MulEquiv.finite_left
  have hcard : Nat.card (TauCeti.CFSGIndex.sporadic s).Group = Nat.card (Carrier s) :=
    (Nat.card_congr b.toEquiv).symm
  have hO' : Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) ≤ 2 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b).toEquiv]
    exact hO
  refine ⟨hX, exists_mul_ne_of_sq_dvd_card hp (hcard ▸ hsq) (hcard ▸ Nat.card_pos.ne'),
    (isSolvable_and_not_dvd_of_card_le_two hO' Nat.prime_three (by norm_num)).1⟩

open CFSG.Blueprint.NativeSporadic (Carrier) in
theorem nonempty_mulEquiv_carrier_of_sporadicIndex {s : TauCeti.SporadicName}
    (hb : Nonempty (Carrier s ≃* s.Group)) {K : Type*} [Group K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group)) : Nonempty (K ≃* Carrier s) :=
  ⟨hK.some.trans hb.some.symm⟩

theorem threeFourTwoNoneAt_mcl :
    ThreeFourTwoNoneAt 5 (TauCeti.CFSGIndex.sporadic .McL).Group := by
  have hO : Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .McL)) ≤ 2 :=
    CFSG.Sporadic.Schreier.McL_outer_card_le_two.1
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    CFSG.Sporadic.McL.fam_mcl_simplicity.1
  have hsq : 5 ^ 2 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) := by
    show 5 ^ 2 ∣ Nat.card CFSG.Blueprint.NativeSporadic.McL
    rw [CFSG.Sporadic.McL.card_McL]
    norm_num
  obtain ⟨hX, hnab, hout⟩ := sporadicIndex_facts_of_bridge (s := .McL)
    CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
    CFSG.Sporadic.McL.fam_mcl_simplicity.2.2 hO Nat.prime_five hsq
  refine threeFourTwoNoneAt_of_normalizer_maximal hX hnab hout fun K _ _ hK => ?_
  obtain ⟨e⟩ := nonempty_mulEquiv_carrier_of_sporadicIndex (s := .McL)
    CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv hK
  haveI : Finite (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .McL)) := MulEquiv.finite_left
  refine ⟨?_, fun T => ?_⟩
  · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact (isSolvable_and_not_dvd_of_card_le_two hO Nat.prime_five (by norm_num)).2
  obtain ⟨hc, hmax, -, hZ, -, hexp, hsol, -⟩ :=
    CFSG.AGLEmbeddingD2.heisLocal_mclP (e.trans CFSG.RankThree.Native.mcl275Equiv) T
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨B, hBT, hB, hBc⟩ := exists_isElemAbelian_card_sq_of_card_cube hc hexp
  exact ⟨CFSG.SectionRank.le_pRank (by norm_num) hBT hB hBc, hZ, hsol, hmax⟩

theorem threeFourTwoNoneAt_j4 :
    ThreeFourTwoNoneAt 11 (TauCeti.CFSGIndex.sporadic .J4).Group := by
  have hO : Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .J4)) ≤ 2 :=
    CFSG.AGLEmbedding.card_outer_J4.le.trans (by norm_num)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.fam_j4_simplicity.1
  have hsq : 11 ^ 2 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) := by
    show 11 ^ 2 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J4
    rw [CFSG.Sporadic.J4.card_J4]
    norm_num
  obtain ⟨hX, hnab, hout⟩ := sporadicIndex_facts_of_bridge (s := .J4)
    CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
    CFSG.Sporadic.J4.fam_j4_simplicity.2.2 hO (by norm_num) hsq
  refine threeFourTwoNoneAt_of_normalizer_maximal hX hnab hout fun K _ _ hK => ?_
  obtain ⟨e⟩ := hK
  haveI : IsSimpleGroup K := MulEquiv.isSimpleGroup e
  have hCK : centralizer ((⊤ : Subgroup K) : Set K) = ⊥ := by
    obtain ⟨a, b, hab⟩ := hnab
    rw [coe_top, centralizer_univ, CFSG.ComponentClassification.Helpers.center_eq_bot K
      ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩]
  have hloc := fun T : Sylow 11 K =>
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4 K ⊤ normal_top hCK
      ⟨Subgroup.topEquiv.trans e⟩ 11 rfl T
  refine ⟨?_, fun T => ?_⟩
  · obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 11 K))
    rw [← Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence Subgroup.topEquiv).toEquiv]
    exact (hloc T).1
  obtain ⟨-, hc, hmax, -, hZ, -, hexp, hsol, -⟩ := hloc T
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨B, hBT, hB, hBc⟩ := exists_isElemAbelian_card_sq_of_card_cube hc hexp
  exact ⟨CFSG.SectionRank.le_pRank (by norm_num) hBT hB hBc, hZ, hsol, hmax⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
