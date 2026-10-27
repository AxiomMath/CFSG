module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)

variable {K : Type} [Field K] {k : Type} [Field k] [Algebra k K]

theorem subsystemGroup_inf_facts
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    commutator ↥(subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) =
        ⊤ ∧
      IsSimpleGroup ↥(subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ∧
      center ↥(subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) = ⊥ ∧
      CFSG.Open.IsQuasisimple
        ↥(subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, -, -, hmodel,
    -⟩⟩ := even_E6_graph_finite_Levi_intersections f hf k K hk hK σ hσ
  set L := subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ with hLdef
  have hs : IsSimpleGroup ↥L := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 6 2 f hmodel).2
  have hperf : Group.IsPerfect ↥L := by
    have : Group.IsPerfect (unitarySL σ) := isPerfect_unitarySL hK hσ
    refine Group.IsPerfect.ofSurjective
      (f := ((realize (two_eq_zero_of_card_sq hf hK)).comp (unitarySL σ).subtype).codRestrict L
        fun B => by rw [hL]; exact ⟨B, B.2, rfl⟩) ?_
    rintro ⟨y, hy⟩
    rw [hL] at hy
    obtain ⟨B, hB, rfl⟩ := hy
    exact ⟨⟨B, hB⟩, rfl⟩
  have hcomm : commutator ↥L = ⊤ := hperf.commutator_eq_top
  have hZ : center ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥L) with h | h
    · exact h
    · exfalso
      have hab : commutator ↥L = ⊥ := by
        rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [mem_centralizer_iff]
        intro y _
        exact (mem_center_iff.1 (h ▸ mem_top x) y)
      obtain ⟨a, b, hab'⟩ := hs.toNontrivial.exists_pair_ne
      have : (⊤ : Subgroup ↥L) = ⊥ := hcomm ▸ hab
      exact hab' ((mem_bot.1 (this ▸ mem_top a)).trans (mem_bot.1 (this ▸ mem_top b)).symm)
  refine ⟨hcomm, hs, hZ, hcomm, ?_⟩
  have e : ↥L ⧸ center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have := hs
  exact e.isSimpleGroup

omit [Algebra k K] in
theorem card_thetaTorus_twisted
    (h2 : (2 : K) = 0) (ι : k →+* K) :
    Nat.card (thetaTorus ι) = Nat.card kˣ := by
  have hinj : Function.Injective ((thetaTorusHom K).comp (Units.map ι.toMonoidHom)) :=
    (thetaTorusHom_injective h2).comp fun a b h =>
      Units.ext (ι.injective (by simpa using congrArg Units.val h))
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

omit [Algebra k K] in
theorem commutator_thetaRankOneGroup_twisted
    [Finite k] (h2 : (2 : K) = 0) (ι : k →+* K)
    (hk4 : 4 ≤ Nat.card k) :
    ⁅thetaRankOneGroup ι, thetaRankOneGroup ι⁆ = thetaRankOneGroup ι := by
  have hp := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k hk4
  rw [thetaRankOneGroup_eq_range h2, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    hp.commutator_eq_top]

theorem exists_mul_of_commute_thetaTorusHom
    (h2 : (2 : K) = 0) {c : Kˣ} (hc : c ≠ 1)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ adjointGroup TwistTag.E6.tag K)
    (hgc : g * thetaTorusHom K c = thetaTorusHom K c * g) :
    ∃ h ∈ torusGroup TwistTag.E6.tag K, h⁻¹ * g ∈ subsystemGroup TwistTag.E6.tag K setA := by
  have hc2 := RootTorus.sq_ne_one_of_two h2 hc
  have hmem : g ∈ toralCentralizer TwistTag.E6.tag K (Pi.mulSingle (e6Idx 1) c) := by
    refine Subgroup.mem_inf.2 ⟨hg, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ rfl
    exact hgc.symm
  exact RootTorus.exists_mul_of_mem_toralCentralizer _
    (RootTorus.rootCharKernel_mulSingle_subset (e6Idx 1) (fun _ hα => RootTorus.coef_e6 hα) hc
      hc2)
    (RootTorus.rootCharStabilizer_mulSingle_subset (e6Idx 1) isRoot_e6HighestRoot
      iform_e6HighestRoot (fun _ hβ hne => RootTorus.check_e6 hβ hne) hc hc2) hmem

theorem exists_mul_of_mem_centralizer_thetaTorus_twisted
    {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {t : kˣ} (ht : t ≠ 1) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (hgc : g * thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) =
      thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) * g) :
    ∃ h ∈ thetaTorus (algebraMap k K), h⁻¹ * g ∈
      subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hcommLH, huniq, -⟩⟩ :=
    even_E6_graph_finite_Levi_intersections f hf k K hk hK σ hσ
  have hu : Units.map (algebraMap k K).toMonoidHom t ≠ 1 := fun h =>
    ht (Units.ext ((algebraMap k K).injective (by simpa using congrArg Units.val h)))
  have hgG : g ∈ adjointGroup TwistTag.E6.tag K :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ hg)).1
  obtain ⟨h, hh, hhg⟩ := exists_mul_of_commute_thetaTorusHom h2 hu hgG hgc
  have hM : g ∈ parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
    refine mem_inf.2 ⟨?_, hg⟩
    rw [show g = h * (h⁻¹ * g) by group]
    exact mul_mem (torusGroup_le_parabolicLevi setA hh) (subsystemGroup_le_parabolicLevi' hhg)
  obtain ⟨⟨l, h'⟩, ⟨hl, hh', rfl⟩, -⟩ := huniq g hM
  refine ⟨h', hh', ?_⟩
  dsimp only
  rw [hcommLH l hl h' hh', inv_mul_cancel_left]
  exact hl

theorem center_eq_bot_and_isQuasisimple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hp : commutator G = ⊤) : center G = ⊥ ∧ CFSG.Open.IsQuasisimple G := by
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exfalso
      have hab : commutator G = ⊥ := by
        rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [mem_centralizer_iff]
        intro y _
        exact (mem_center_iff.1 (h ▸ mem_top x) y)
      obtain ⟨a, b, hab'⟩ := hs.toNontrivial.exists_pair_ne
      have : (⊤ : Subgroup G) = ⊥ := hp ▸ hab
      exact hab' ((mem_bot.1 (this ▸ mem_top a)).trans (mem_bot.1 (this ▸ mem_top b)).symm)
  refine ⟨hZ, hp, ?_⟩
  have e : G ⧸ center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have := hs
  exact e.isSimpleGroup

theorem eq_bot_of_le_subsystemGroup_inf
    [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (S : Subgroup (ModGL TwistTag.E6.tag K))
    (hSL : S ≤ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ)
    (hS2 : IsPGroup 2 S)
    (hSn : subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤
      normalizer (S : Set (ModGL TwistTag.E6.tag K))) :
    S = ⊥ := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨-, -, hZ, hq⟩ := subsystemGroup_inf_facts (k := k) hf hk hK hσ
  have hbot := E6EvenRootTorus.eq_bot_of_isPGroup_two hq (by rw [hZ, card_bot]; exact odd_one)
    (M := S.subgroupOf (subsystemGroup TwistTag.E6.tag K setA ⊓
      graphFixedRootGroup TwistTag.E6 K σ))
    ⟨fun n hn g => (mem_normalizer_iff.1 (hSn g.2) _).1 hn⟩
    (hS2.comap_subtype (K := subsystemGroup TwistTag.E6.tag K setA ⊓
      graphFixedRootGroup TwistTag.E6 K σ))
  rw [eq_bot_iff]
  intro s hs
  have h := (Subgroup.eq_bot_iff_forall _).1 hbot ⟨s, hSL hs⟩ hs
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h)

theorem subgroupOf_facts
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    center ↥((subsystemGroup TwistTag.E6.tag K setA ⊓
        graphFixedRootGroup TwistTag.E6 K σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) =
        ⊥ ∧
      CFSG.Open.IsQuasisimple
        ↥((subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ)) := by
  obtain ⟨hcommL, hsL, -, -⟩ := subsystemGroup_inf_facts (k := k) hf hk hK hσ
  let eL := subgroupOfEquivOfLe (inf_le_right : subsystemGroup TwistTag.E6.tag K setA ⊓
    graphFixedRootGroup TwistTag.E6 K σ ≤ graphFixedRootGroup TwistTag.E6 K σ)
  have hsL' := by
    have := hsL
    exact eL.isSimpleGroup
  have : Group.IsPerfect ↥(subsystemGroup TwistTag.E6.tag K setA ⊓
    graphFixedRootGroup TwistTag.E6 K σ) := ⟨hcommL⟩
  exact center_eq_bot_and_isQuasisimple hsL'
    (Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective).1

theorem statedClassicalModel_of_mulEquiv_twisted
    {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {L : Type} [Group L]
    (e : L ≃* rankTwoQuot
      ((subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ))) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSU 6 2 f := by
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmodel,
    -⟩⟩ := even_E6_graph_finite_Levi_intersections f hf k K hk hK σ hσ
  obtain ⟨hadm, K', hF, hFin, hK', ⟨e'⟩⟩ := hmodel
  obtain ⟨hZ, -⟩ := subgroupOf_facts (k := k) hf hk hK hσ
  let e₁ := ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
    (subgroupOfEquivOfLe (inf_le_right : subsystemGroup TwistTag.E6.tag K setA ⊓
      graphFixedRootGroup TwistTag.E6 K σ ≤ graphFixedRootGroup TwistTag.E6 K σ))
  exact ⟨hadm, K', hF, hFin, hK', ⟨(e.trans e₁).trans e'⟩⟩

theorem leviData_twisted
    [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {j : graphFixedRootGroup TwistTag.E6 K σ}
    (hj : (j : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA) :
    LeviData (zx j)
      ((thetaRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((thetaTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((thetaTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have hf1 : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf1 hK
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨-, ⟨hXC, -, -, -, hcomm, -, -⟩⟩ :=
    even_E6_graph_root_SL2_normalizer f hf1 k K hk hK σ hσ
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hcommLH, -⟩⟩ :=
    even_E6_graph_finite_Levi_intersections f hf1 k K hk hK σ hσ
  have hHX : thetaTorus (algebraMap k K) ≤ thetaRankOneGroup (algebraMap k K) :=
    thetaTorus_le_thetaRankOneGroup h2 _
  have hHC : thetaTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ := hHX.trans hXC
  have hF := centralizer_thetaRankOneGroup_twisted hf1 hk hK hσ
  set L := subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ with hLdef
  have hLC : L ≤ graphFixedRootGroup TwistTag.E6 K σ := inf_le_right
  have hjL0 : (j : ModGL TwistTag.E6.tag K) ∈ L := mem_inf.2 ⟨hj, j.2⟩
  have hXj : ∀ d ∈ (thetaRankOneGroup (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ), d ∈ cent j := fun d hd =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (hcomm _ (mem_subgroupOf.1 hd) _ hjL0))
  obtain ⟨t, ht⟩ := E6EvenRootTorus.exists_units_ne_one hf hk
  obtain ⟨hZL, hqL⟩ := subgroupOf_facts (k := k) hf1 hk hK hσ
  refine
    { D_perfect := Exc.commutator_subgroupOf_of_perfect hXC
        (commutator_thetaRankOneGroup_twisted h2 _ h4)
      D_le := fun d hd => mem_centralizer_iff.2 fun w hw => hw.2.1 d (hXj d hd)
      Q_le := fun s hs => mem_subgroupOf.2 (hHX (mem_subgroupOf.1 hs))
      Q_ne_bot := ?_
      odd_Q := ?_
      Q_le_H := le_rfl
      H_comm := fun a ha b hb => ?_
      H_le := fun h hh => ?_
      L_le := fun l hl => mem_centralizer_iff.2 fun s hs => Subtype.ext
        (hcommLH _ (mem_subgroupOf.1 hl) _ (mem_subgroupOf.1 hs)).symm
      cent_eq := fun c hc => ?_
      quasisimple := hqL
      odd_center := by rw [hZL, card_bot]; exact odd_one
      Z_le := fun w hw => ?_ }
  · intro hbot
    have hmem : (⟨_, hHC ⟨t, rfl⟩⟩ : graphFixedRootGroup TwistTag.E6 K σ) ∈
        (thetaTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :=
      mem_subgroupOf.2 ⟨t, rfl⟩
    rw [hbot, mem_bot] at hmem
    have h1 := congrArg Subtype.val hmem
    have h1' : thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) =
        thetaTorusHom K 1 := h1.trans (map_one _).symm
    have hu := thetaTorusHom_injective h2 h1'
    exact ht (Units.ext ((algebraMap k K).injective (by simpa using congrArg Units.val hu)))
  · rw [Nat.card_congr (subgroupOfEquivOfLe hHC).toEquiv, card_thetaTorus_twisted h2,
      Nat.card_units, hk]
    exact E6EvenRootTorus.odd_two_pow_sub_one hf1
  · obtain ⟨x, hx⟩ := mem_subgroupOf.1 ha
    obtain ⟨y, hy⟩ := mem_subgroupOf.1 hb
    refine Subtype.ext ?_
    change (a : ModGL TwistTag.E6.tag K) * b = b * a
    rw [← hx, ← hy, ← map_mul, mul_comm, map_mul]
  · rw [mem_normalizer_iff]
    intro n
    have hc : ∀ m ∈ L.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), h * m = m * h :=
      fun m hm => Subtype.ext (hcommLH _ (mem_subgroupOf.1 hm) _ (mem_subgroupOf.1 hh)).symm
    constructor
    · intro hn
      rw [hc n hn, mul_inv_cancel_right]
      exact hn
    · intro hn
      have e : h * n * h⁻¹ = n := mul_left_cancel ((hc _ hn).trans (by group))
      rwa [e] at hn
  · have hcθ : (c : ModGL TwistTag.E6.tag K) *
        thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) =
          thetaTorusHom K (Units.map (algebraMap k K).toMonoidHom t) * c :=
      (congrArg Subtype.val (mem_centralizer_iff.1 hc ⟨_, hHC ⟨t, rfl⟩⟩
        (mem_subgroupOf.2 ⟨t, rfl⟩))).symm
    obtain ⟨h, hh, hhc⟩ :=
      exists_mul_of_mem_centralizer_thetaTorus_twisted hf1 hk hK hσ ht c.2 hcθ
    exact ⟨⟨h, hHC hh⟩, mem_subgroupOf.2 hh, mem_subgroupOf.2 hhc⟩
  · obtain ⟨-, hwz, -⟩ := hw
    rw [mem_subgroupOf, ← hF]
    refine mem_inf.2 ⟨w.2, mem_centralizer_iff.2 fun y hy => ?_⟩
    exact (congrArg Subtype.val (hwz ⟨y, hXC hy⟩ (hXj ⟨y, hXC hy⟩ (mem_subgroupOf.2 hy)))).symm

end CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
