module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzBal
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.TwistDiag
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.G2Pair
public import CFSG.HardMathSupport.Dickson.Bal207.SU38G2
public import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Classes
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TwistedRankE6
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClassDescent
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Global
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHsyl
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.PartOne.KF4.B2Frame
public import CFSG.RankThree.PartOne.KLR.StarRad
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail17
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.RankThree.PartTwo.Sec4.E27.Core
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate8166
public import Certificates.Certificate9530
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux
open CFSG.HardMathSupport.Lang.D4Three (d4Graph d4P coe_d4Graph)
open scoped commutatorElement

section Sylow

variable {H : Type} [Group H] [Finite H]

theorem exists_commute_three {x y : H} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : Commute x y)
    (hx1 : x ≠ 1) (hy : y ∉ Subgroup.zpowers x) {d : H} (hd3 : d ^ 3 = 1) :
    ∃ z : H, z ^ 3 = 1 ∧ Commute z d ∧ z ∉ Subgroup.zpowers d := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hd1 : d = 1
  · subst hd1
    refine ⟨x, hx3, Commute.one_right x, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]
    exact hx1
  have hdord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdp : IsPGroup 3 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hdord, pow_one])
  obtain ⟨P, hdP⟩ := hdp.exists_le_sylow
  have hdP' : d ∈ (P : Subgroup H) := hdP (Subgroup.mem_zpowers d)
  set V := Bal209F4Aux.pairSub hxy with hV
  have hVp : IsPGroup 3 V := by
    intro g
    obtain ⟨i, j, hg⟩ := Bal209F4Aux.mem_pairSub.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    have hxi : (x ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast (x ^ i) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hyj : (y ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast (y ^ j) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
    rw [Subgroup.coe_pow, hg, pow_one, OneMemClass.coe_one, (hxy.zpow_zpow i j).mul_pow, hxi, hyj,
      one_mul]
  obtain ⟨Q, hVQ⟩ := hVp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  have hconj : ∀ v ∈ V, g * v * g⁻¹ ∈ (P : Subgroup H) := by
    intro v hv
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨v, hVQ hv, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  have hxV : x ∈ V := Bal209F4Aux.mem_pairSub.2 ⟨1, 0, by simp⟩
  have hyV : y ∈ V := Bal209F4Aux.mem_pairSub.2 ⟨0, 1, by simp⟩
  have hgx := hconj x hxV
  have hgy := hconj y hyV
  by_cases hdc : ∀ w ∈ (P : Subgroup H), Commute w d
  ·
    by_cases hxd : g * x * g⁻¹ ∈ Subgroup.zpowers d
    · refine ⟨g * y * g⁻¹, ?_, hdc _ hgy, fun hyd => hy ?_⟩
      · rw [conj_pow, hy3]; group
      · have hgx1 : g * x * g⁻¹ ≠ 1 := by
          intro h
          apply hx1
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        have hgx3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
        have hd_mem : d ∈ Subgroup.zpowers (g * x * g⁻¹) := by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxd
          have hk3 : ¬ (3 : ℤ) ∣ k := by
            rintro ⟨m, rfl⟩
            apply hgx1
            rw [← hk, zpow_mul, show d ^ (3 : ℤ) = 1 by simpa using hd3, one_zpow]
          exact Bal209F4Aux.mem_of_zpow_mem hd3 hd1 hk3 (by rw [hk]; exact Subgroup.mem_zpowers _)
        have hyx : g * y * g⁻¹ ∈ Subgroup.zpowers (g * x * g⁻¹) :=
          Subgroup.zpowers_le.2 hd_mem hyd
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyx
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        have h1 : g * x ^ k * g⁻¹ = g * y * g⁻¹ := by rw [← hk, conj_zpow]
        have h2 := congrArg (fun t => g⁻¹ * t * g) h1
        simpa [mul_assoc] using h2
    · exact ⟨g * x * g⁻¹, by rw [conj_pow, hx3]; group, hdc _ hgx, hxd⟩
  ·
    push Not at hdc
    obtain ⟨w₀, hw₀P, hw₀d⟩ := hdc
    haveI : Nontrivial (P : Subgroup H) := ⟨⟨⟨d, hdP'⟩, 1, fun h => hd1 (congrArg Subtype.val h)⟩⟩
    have hPp : IsPGroup 3 (P : Subgroup H) := P.isPGroup'
    have hZnt : Nontrivial (Subgroup.center (P : Subgroup H)) := hPp.center_nontrivial
    have hZp : IsPGroup 3 (Subgroup.center (P : Subgroup H)) := hPp.to_subgroup _
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hZp
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' hm
    have h3dvd : 3 ∣ Nat.card (Subgroup.center (P : Subgroup H)) := by
      rw [hm]; exact dvd_pow_self 3 hm0
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
    have hwc : ∀ u : (P : Subgroup H), (w : (P : Subgroup H)) * u = u * w :=
      fun u => (Subgroup.mem_center_iff.1 w.2 u).symm
    refine ⟨((w : (P : Subgroup H)) : H), ?_, ?_, fun hwd => ?_⟩
    · have h1 : w ^ 3 = 1 := by have h0 := pow_orderOf_eq_one w; rwa [hw] at h0
      have h2 := congrArg (fun t : Subgroup.center (P : Subgroup H) => ((t : (P : Subgroup H)) : H)) h1
      simpa using h2
    · exact congrArg Subtype.val (hwc ⟨d, hdP'⟩)
    ·
      have hw1 : ((w : (P : Subgroup H)) : H) ≠ 1 := by
        intro h
        have : w = 1 := Subtype.ext (Subtype.ext h)
        rw [this, orderOf_one] at hw
        norm_num at hw
      have hw3 : ((w : (P : Subgroup H)) : H) ^ 3 = 1 := by
        have h1 : w ^ 3 = 1 := by have h0 := pow_orderOf_eq_one w; rwa [hw] at h0
        have h2 := congrArg (fun t : Subgroup.center (P : Subgroup H) => ((t : (P : Subgroup H)) : H)) h1
        simpa using h2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hwd
      have hk3 : ¬ (3 : ℤ) ∣ k := by
        rintro ⟨m', rfl⟩
        apply hw1
        rw [← hk, zpow_mul, show d ^ (3 : ℤ) = 1 by simpa using hd3, one_zpow]
      have hdw : d ∈ Subgroup.zpowers ((w : (P : Subgroup H)) : H) :=
        Bal209F4Aux.mem_of_zpow_mem hd3 hd1 hk3 (by rw [hk]; exact Subgroup.mem_zpowers _)
      obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.1 hdw
      apply hw₀d
      rw [← hk']
      have hcw : Commute w₀ ((w : (P : Subgroup H)) : H) :=
        (congrArg Subtype.val (hwc ⟨w₀, hw₀P⟩)).symm
      exact hcw.zpow_right k'

end Sylow

theorem mem_of_isSCp_of_commute {X : Type*} [Group X] {K B : Subgroup X}
    (hSC : IsSCp 3 (K ⊔ B) B) {z : X} (hzK : z ∈ K) (hzB : ∀ b ∈ B, Commute z b)
    (hz3 : z ^ 3 = 1) : z ∈ B := by
  have hE : IsElemAbelian 3 (B ⊔ Subgroup.zpowers z) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hSC.2.1 (CFSG.Open.isElemAbelian_zpowers hz3)
      fun b hb w hw => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        exact ((hzB b hb).zpow_left k).eq.symm
  have hle : B ⊔ Subgroup.zpowers z ≤ K ⊔ B :=
    sup_le le_sup_right (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left hzK))
  have heq := hSC.2.2 _ hle hE le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

section Generic

variable {X : Type} [Group X]

open CFSG.LieType.SeitzGeneration.ExcWideThree

theorem mk_injective_of_center_bot {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥) :
    Function.Injective (QuotientGroup.mk : ↥K → ↥K ⧸ Subgroup.center ↥K) := by
  intro a b h
  rw [QuotientGroup.eq, hZ, Subgroup.mem_bot] at h
  exact inv_mul_eq_one.1 h

theorem actHom_of_mem {X : Type} [Group X] {K : Subgroup X} {k : X} (hk : k ∈ K)
    (hkN : k ∈ Subgroup.normalizer (K : Set X)) :
    actHom K ⟨k, hkN⟩ = MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ Subgroup.center ↥K) := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [actHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1

theorem conj_eq_of_actHom_eq {X : Type} [Group X] {J : Subgroup X}
    (hZ : Subgroup.center ↥J = ⊥) {u v : X} (hu : u ∈ Subgroup.normalizer (J : Set X))
    (hv : v ∈ Subgroup.normalizer (J : Set X)) (huv : actHom J ⟨u, hu⟩ = actHom J ⟨v, hv⟩)
    {x : X} (hx : x ∈ J) : u * x * u⁻¹ = v * x * v⁻¹ := by
  have h1 := congrArg (fun φ : MulAut (↥J ⧸ Subgroup.center ↥J) =>
    φ (QuotientGroup.mk (⟨x, hx⟩ : ↥J))) huv
  simp only [actHom_mk] at h1
  have h2 := congrArg Subtype.val (mk_injective_of_center_bot hZ h1)
  simpa [coe_normalizerMonoidHom] using h2

theorem card_of_isLieQuot_d4Two {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥)
    (h : IsLieQuot Y IsD4TwoIndex) : Nat.card Y = ordD 4 2 := by
  obtain ⟨⟨d, hv⟩, hd, ⟨f⟩⟩ := h
  cases d with
  | D r q =>
    obtain ⟨rfl, hp, he⟩ := hd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hp f
    rw [hp, he] at hm
    have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.1 rfl
    rw [← Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, h1]
    norm_num
  | _ => exact hd.elim

theorem center_eq_bot_of_quasisimple {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hq : CFSG.Open.IsQuasisimple Y) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    have hab : ∀ u v : Y, u * v = v * u := fun u v =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top v) u)
    have h1 : commutator Y = ⊥ := by
      rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
      intro u _ v _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab u v
    have h2 := hq.1
    rw [h1] at h2
    obtain ⟨u, hu⟩ := exists_ne (1 : Y)
    exact hu (Subgroup.mem_bot.1 (h2 ▸ Subgroup.mem_top u))

theorem congr_conj_eq {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (g : G) :
    MulAut.congr φ (MulAut.conj g) = MulAut.conj (φ g) := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem not_ordG2_eight_dvd_ordD : ¬ ordG2 8 ∣ ordD 4 2 := by
  intro h
  have h1 := Nat.le_of_dvd (by simp only [ordD]; decide) h
  revert h1
  simp only [ordG2, ordD]
  decide

theorem three_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] {H L : Subgroup G}
    (hL : IsPGroup 3 L) (hHL : H ≤ L) (hne : H ≠ L) : 3 * Nat.card H ≤ Nat.card L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hL.exists_card_eq
  obtain ⟨n, hn⟩ := (hL.to_le hHL).exists_card_eq
  have hdvd : Nat.card H ∣ Nat.card L := Subgroup.card_dvd_of_le hHL
  rw [hm, hn] at hdvd
  have hnm : n ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hnm' : n ≠ m := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hHL (by rw [hm, hn]))
  rw [hn, hm]
  calc 3 * 3 ^ n = 3 ^ (n + 1) := by ring
    _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem isElemAbelian_autImage {X : Type} [Group X] {B J : Subgroup X}
    (hBel : IsElemAbelian 3 B) : IsElemAbelian 3 (autImage B J) := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩
  · obtain ⟨x, hx, hxB, hxu⟩ := mem_autImage.1 u.2
    obtain ⟨y, hy, hyB, hyv⟩ := mem_autImage.1 v.2
    apply Subtype.ext
    change (u : MulAut (↥J ⧸ Subgroup.center ↥J)) * v = v * u
    rw [← hxu, ← hyv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Bal209F4Aux.commute_of_elemAbelian hBel hxB hyB).eq
  · obtain ⟨x, hx, hxB, rfl⟩ := mem_autImage.1 hu
    rw [← map_pow]
    have h1 : (⟨x, hx⟩ : Subgroup.normalizer (J : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hBel.2 x hxB)
    rw [h1, map_one]

theorem autImageRankThree_of_outer {X : Type} [Group X] [Finite X] {B H J : Subgroup X}
    (hBel : IsElemAbelian 3 B) (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hZ : Subgroup.center ↥J = ⊥) (hfaith : ∀ c ∈ H, (∀ x ∈ J, c * x = x * c) → c = 1)
    {b d₁ d₂ : X} (hbB : b ∈ B) (hd₁B : d₁ ∈ B) (hd₁H : d₁ ∈ H) (hd₂B : d₂ ∈ B) (hd₂H : d₂ ∈ H)
    (hd₁ : d₁ ≠ 1) (hd₂ : d₂ ∉ Subgroup.zpowers d₁)
    (hout : ¬ ∃ h ∈ H, ∀ x ∈ J, b * x * b⁻¹ = h * x * h⁻¹) :
    KSF4SU3.AutImageRankThree B J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := B ⊓ H with hD
  have hDN : D ≤ Subgroup.normalizer (J : Set X) := fun x hx => hBJ hx.1
  let ψ : ↥D →* MulAut (↥J ⧸ Subgroup.center ↥J) := (actHom J).comp (Subgroup.inclusion hDN)
  have hψ : ∀ x : ↥D, ψ x = actHom J ⟨x, hDN x.2⟩ := fun x => rfl
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).2 fun x hx => ?_
    have h1 : actHom J ⟨(x : X), hDN x.2⟩ = actHom J ⟨1, one_mem _⟩ := by
      rw [← hψ, hx]; exact (map_one (actHom J)).symm
    have h2 : ∀ y ∈ J, (x : X) * y = y * x := by
      intro y hy
      have h3 := conj_eq_of_actHom_eq hZ (hDN x.2) (one_mem _) h1 hy
      rw [one_mul, inv_one, mul_one] at h3
      calc (x : X) * y = ((x : X) * y * (x : X)⁻¹) * x := by group
        _ = y * x := by rw [h3]
    exact Subtype.ext (hfaith _ x.2.2 h2)
  have hDp : IsPGroup 3 D := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hBel.2 _ g.2.1)⟩
  have hZ1D : Subgroup.zpowers d₁ ≤ D := (Subgroup.zpowers_le).2 ⟨hd₁B, hd₁H⟩
  have hZ1ne : Subgroup.zpowers d₁ ≠ D := fun h => hd₂ (h ▸ ⟨hd₂B, hd₂H⟩)
  have hZ1card : Nat.card (Subgroup.zpowers d₁) = 3 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (hBel.2 d₁ hd₁B) hd₁
  have hD9 : 9 ≤ Nat.card D := by
    have := three_mul_card_le_of_lt hDp hZ1D hZ1ne
    rw [hZ1card] at this
    omega
  have hcardP : Nat.card ψ.range = Nat.card D :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hPA : ψ.range ≤ autImage B J := by
    rintro _ ⟨x, rfl⟩
    exact mem_autImage.2 ⟨x, hDN x.2, x.2.1, rfl⟩
  have hbA : actHom J ⟨b, hBJ hbB⟩ ∈ autImage B J := mem_autImage.2 ⟨b, hBJ hbB, hbB, rfl⟩
  have hbP : actHom J ⟨b, hBJ hbB⟩ ∉ ψ.range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨x, x.2.2, fun y hy => ?_⟩
    exact (conj_eq_of_actHom_eq hZ (hDN x.2) (hBJ hbB) (by rw [← hψ]; exact hx) hy).symm
  have hAel := isElemAbelian_autImage (J := J) hBel
  have hAp : IsPGroup 3 (autImage B J) :=
    CFSG.HardMathSupport.Dickson.Bal207.su38_isPGroup_three hAel
  have h27 : 27 ≤ Nat.card (autImage B J) := by
    have := three_mul_card_le_of_lt hAp hPA (fun h => hbP (h ▸ hbA))
    rw [hcardP] at this
    omega
  obtain ⟨E, hEA, hE27⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.exists_subgroup_card_twentySeven hAel h27
  exact ⟨E, hEA, CFSG.HardMathSupport.Dickson.Bal207.su38_isElemAbelian_of_le hAel hEA, hE27⟩

theorem le_normalizer_inf_centralizer {X : Type} [Group X] {K B : Subgroup X} {a : X}
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) (haB : a ∈ B) :
    B ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X) :=
  fun x hx => Bal209F4Aux.mem_normalizer_inf_centralizer (hBN hx) (hBN haB) (by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (Bal209F4Aux.commute_of_elemAbelian hBel hx haB)]
    exact Subgroup.one_mem _)

theorem mem_inf_centralizer_of_mem {X : Type} [Group X] {K B : Subgroup X} {a d : X}
    (hBel : IsElemAbelian 3 B) (haB : a ∈ B) (hdB : d ∈ B) (hdK : d ∈ K) :
    d ∈ K ⊓ Subgroup.centralizer ({a} : Set X) :=
  Subgroup.mem_inf.2 ⟨hdK, Subgroup.mem_centralizer_singleton_iff.2
    (Bal209F4Aux.commute_of_elemAbelian hBel hdB haB).eq⟩

@[expose] def primePowerEight : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩

theorem valid_G2_eight : (TauCeti.LieTypeIndex.G2 primePowerEight).Valid := by
  simp [TauCeti.LieTypeIndex.valid_iff, primePowerEight, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.PrimePower.card_def]

theorem exists_conj_of_inner {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥) {M : Type*}
    [Group M] (e : (↥K ⧸ Subgroup.center ↥K) ≃* M) {z : X}
    (hz : z ∈ Subgroup.normalizer (K : Set X)) {g : M}
    (hg : MulAut.congr e (actHom K ⟨z, hz⟩) = MulAut.conj g) :
    ∃ k : ↥K, ∀ x : ↥K, z * (x : X) * z⁻¹ = k * x * k⁻¹ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm g)
  refine ⟨k, fun x => ?_⟩
  have h1 : e (actHom K ⟨z, hz⟩ (QuotientGroup.mk x)) =
      e (QuotientGroup.mk (k * x * k⁻¹)) := by
    have h2 : e (actHom K ⟨z, hz⟩ (QuotientGroup.mk x)) = g * e (QuotientGroup.mk x) * g⁻¹ := by
      have h := congrArg (fun φ : MulAut M => φ (e (QuotientGroup.mk x))) hg
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.conj_apply] at h
      exact h
    rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hk, MulEquiv.apply_symm_apply]
  have h3 := mk_injective_of_center_bot hZ (e.injective h1)
  have h4 := congrArg Subtype.val h3
  simpa using h4

theorem eq_one_of_central {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥) {c : X} (hcK : c ∈ K)
    (hc : ∀ x ∈ K, c * x = x * c) : c = 1 := by
  have hmem : (⟨c, hcK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (hc x x.2).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem mem_of_acts_as_conj {K B : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hSC : IsSCp 3 (K ⊔ B) B) {β' : X} (hβ'B : β' ∈ B) {κ : X} (hκK : κ ∈ K)
    (hk : ∀ x ∈ K, β' * x * β'⁻¹ = κ * x * κ⁻¹) : κ ∈ B := by
  have hkc : ∀ β'' ∈ B, Commute κ β'' := by
    intro β'' hβ''
    have hβ''N := hBN hβ''
    have hcomm : β'' * β' = β' * β'' := Bal209F4Aux.commute_of_elemAbelian hBel hβ'' hβ'B
    have hκ'K : β'' * κ * β''⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hβ''N κ).1 hκK
    have hk' : ∀ x ∈ K, (β'' * κ * β''⁻¹) * x * (β'' * κ * β''⁻¹)⁻¹ = κ * x * κ⁻¹ := by
      intro x hx
      have hx' : β''⁻¹ * x * β'' ∈ K := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hβ''N) x).1 hx
        simpa using h1
      have h1 := hk _ hx'
      have h2 : β'' * β' * β''⁻¹ = β' := by rw [hcomm]; group
      calc (β'' * κ * β''⁻¹) * x * (β'' * κ * β''⁻¹)⁻¹
          = β'' * (κ * (β''⁻¹ * x * β'') * κ⁻¹) * β''⁻¹ := by group
        _ = β'' * (β' * (β''⁻¹ * x * β'') * β'⁻¹) * β''⁻¹ := by rw [h1]
        _ = (β'' * β' * β''⁻¹) * x * (β'' * β' * β''⁻¹)⁻¹ := by group
        _ = β' * x * β'⁻¹ := by rw [h2]
        _ = κ * x * κ⁻¹ := hk x hx
    have hc : κ⁻¹ * (β'' * κ * β''⁻¹) = 1 := by
      refine eq_one_of_central hZ (mul_mem (inv_mem hκK) hκ'K) fun x hx => ?_
      have h1 := hk' x hx
      calc κ⁻¹ * (β'' * κ * β''⁻¹) * x
          = κ⁻¹ * ((β'' * κ * β''⁻¹) * x * (β'' * κ * β''⁻¹)⁻¹) * (β'' * κ * β''⁻¹) := by group
        _ = κ⁻¹ * (κ * x * κ⁻¹) * (β'' * κ * β''⁻¹) := by rw [h1]
        _ = x * (κ⁻¹ * (β'' * κ * β''⁻¹)) := by group
    have h1 : β'' * κ * β''⁻¹ = κ := (inv_mul_eq_one.1 hc).symm
    calc κ * β'' = (β'' * κ * β''⁻¹) * β'' := by rw [h1]
      _ = β'' * κ := by group
  refine mem_of_isSCp_of_commute hSC hκK hkc ?_
  have hβ'3 : β' ^ 3 = 1 := hBel.2 β' hβ'B
  have hκβ : Commute κ β' := hkc β' hβ'B
  have hck : ∀ x ∈ K, (β' * κ⁻¹) * x = x * (β' * κ⁻¹) := by
    intro x hx
    have hx' : κ⁻¹ * x * κ ∈ K := mul_mem (mul_mem (inv_mem hκK) hx) hκK
    have h1 := hk _ hx'
    calc (β' * κ⁻¹) * x = β' * (κ⁻¹ * x * κ) * β'⁻¹ * (β' * κ⁻¹) := by group
      _ = κ * (κ⁻¹ * x * κ) * κ⁻¹ * (β' * κ⁻¹) := by rw [h1]
      _ = x * (β' * κ⁻¹) := by group
  have hκ3 : κ ^ 3 = (κ * β'⁻¹) ^ 3 := by
    rw [(hκβ.inv_right).mul_pow, inv_pow, hβ'3, inv_one, mul_one]
  refine eq_one_of_central hZ (pow_mem hκK 3) fun x hx => ?_
  rw [hκ3]
  have h3 : κ * β'⁻¹ = (β' * κ⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
  have h2 : Commute (κ * β'⁻¹) x := by
    rw [h3]
    exact Commute.inv_left (hck x hx)
  exact (h2.pow_left 3).eq

@[expose] noncomputable def quotEquivOfCenterBot {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥) :
    ↥K ≃* ↥K ⧸ Subgroup.center ↥K :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

theorem congr_actHom_apply {K : Subgroup X} {M : Type*} [Group M]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* M) {z : X} (hz : z ∈ Subgroup.normalizer (K : Set X))
    (x : ↥K) : MulAut.congr e (actHom K ⟨z, hz⟩) (e (QuotientGroup.mk x)) =
      e (QuotientGroup.mk (K.normalizerMonoidHom ⟨z, hz⟩ x)) := by
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem conj_eq_of_congr_fixed {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥) {M : Type*}
    [Group M] (e : (↥K ⧸ Subgroup.center ↥K) ≃* M) {z : X}
    (hz : z ∈ Subgroup.normalizer (K : Set X)) {x : ↥K}
    (hx : MulAut.congr e (actHom K ⟨z, hz⟩) (e (QuotientGroup.mk x)) = e (QuotientGroup.mk x)) :
    z * (x : X) * z⁻¹ = x := by
  rw [congr_actHom_apply] at hx
  have h1 := mk_injective_of_center_bot hZ (e.injective hx)
  have h2 := congrArg Subtype.val h1
  simpa using h2

end Generic

section G2Props

set_option linter.unusedSectionVars false


theorem g2Props {Y : Type} [Group Y] {F' : Type} [Field F'] [Finite F'] (hF' : Nat.card F' = 2 ^ 3)
    (Fg : Y ≃* ↥(adjointGroup Tag.G2 F')) :
    IsSimpleGroup Y ∧ CFSG.Open.IsQuasisimple Y ∧
      IsLieQuot Y CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex ∧ Nat.card Y = ordG2 8 := by
  have hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.G2 F') :=
    CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card F' (by rw [hF']; norm_num)
  have hZG : Subgroup.center ↥(adjointGroup Tag.G2 F') = ⊥ := center_adjointGroup_eq_bot
  have hsG : IsSimpleGroup ↥(adjointGroup Tag.G2 F') :=
    (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq hZG).trans
      QuotientGroup.quotientBot)).1 hq.2.1
  have hsY : IsSimpleGroup Y := (MulEquiv.isSimpleGroup_congr Fg).2 hsG
  have hZY : Subgroup.center Y = ⊥ := D4FixedAux.center_eq_bot_of_mulEquiv Fg hZG
  have hquasi : CFSG.Open.IsQuasisimple Y := by
    obtain ⟨hperf, hsimp, -⟩ := CFSG.IsQuasisimple.of_mulEquiv Fg hq
    exact ⟨hperf.commutator_eq_top, hsimp⟩
  have hcard : Nat.card Y = ordG2 8 := by
    rw [Nat.card_congr Fg.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF']
    norm_num
  have hKq : Nat.card F' = primePowerEight.card := by
    rw [hF', TauCeti.PrimePower.card_def]; rfl
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 primePowerEight valid_G2_eight
    rfl F' hKq
  let eFix : Y ⧸ Subgroup.center Y ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.G2 primePowerEight, valid_G2_eight⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZY).trans QuotientGroup.quotientBot).trans
      (Fg.trans (((QuotientGroup.quotientMulEquivOfEq hZG).trans
        QuotientGroup.quotientBot).symm.trans eB))
  exact ⟨hsY, hquasi, ⟨⟨_, valid_G2_eight⟩, ⟨rfl, rfl⟩, ⟨eFix⟩⟩, hcard⟩

end G2Props

section Frame

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)

variable {F : Type} [Field F]

theorem sl2At_injective (i : Fin Tag.D4.rank) : Function.Injective (sl2At F i) := by
  intro A A' h
  apply CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_field Tag.D4 i
  have h1 := congrArg (fun g : ↥(adjointGroup Tag.D4 F) => (g : ModGL Tag.D4 F)) h
  simpa only [coe_sl2At] using h1

theorem eq_one_of_mem_center_cube {A : SL2 F} (hA : A ∈ Subgroup.center (SL2 F))
    (h3 : A ^ 3 = 1) : A = 1 := by
  have h2 := sq_eq_one_of_mem_center hA
  calc A = A ^ 3 * (A * A)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem mem_center_of_commute_sl2At {i : Fin Tag.D4.rank} {B : SL2 F}
    (h : ∀ X : SL2 F, Commute (sl2At F i B) (sl2At F i X)) : B ∈ Subgroup.center (SL2 F) := by
  rw [Subgroup.mem_center_iff]
  intro X
  apply sl2At_injective i
  rw [map_mul, map_mul]
  exact (h X).eq.symm

theorem frameK₁_injective : Function.Injective (frameK₁ F) := by
  intro A A' h
  have e : ∀ X : SL2 F, frameK₁ F X =
      MulAut.conj (nW (K := F) ⟨0, by decide⟩ * nW ⟨1, by decide⟩)
        (sl2At F ⟨2, by decide⟩ X) := fun X => rfl
  have h1 : MulAut.conj (nW (K := F) ⟨0, by decide⟩ * nW ⟨1, by decide⟩)
      (sl2At F ⟨2, by decide⟩ A) = MulAut.conj (nW (K := F) ⟨0, by decide⟩ * nW ⟨1, by decide⟩)
      (sl2At F ⟨2, by decide⟩ A') := by rw [← e, ← e]; exact h
  exact sl2At_injective _ ((MulAut.conj _).injective h1)

theorem frameK₂_injective : Function.Injective (frameK₂ F) := by
  intro A A' h
  have e : ∀ X : SL2 F, frameK₂ F X = d4Graph F 1 (d4Graph F 1 (frameK₁ F X)) := fun X => rfl
  have h1 : d4Graph F 1 (d4Graph F 1 (frameK₁ F A)) = d4Graph F 1 (d4Graph F 1 (frameK₁ F A')) := by
    rw [← e, ← e]; exact h
  exact frameK₁_injective ((d4Graph F 1).injective ((d4Graph F 1).injective h1))

theorem frameDiag_ne_one {B : SL2 F} (hB : B ∉ Subgroup.center (SL2 F)) : frameDiag B ≠ 1 := by
  intro h
  apply hB
  rw [Subgroup.mem_center_iff]
  intro X
  have h1 := frameDiag_conj_frameK₂ B X
  rw [h, one_mul, inv_one, mul_one] at h1
  have h2 : B * X * B⁻¹ = X := (frameK₂_injective h1).symm
  calc X * B = B * X * B⁻¹ * B := by rw [h2]
    _ = B * X := by group

theorem not_mem_center_of_cube {B : SL2 F} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) :
    B ∉ Subgroup.center (SL2 F) := fun h => hB1 (eq_one_of_mem_center_cube h hB3)

theorem frame_pair {B : SL2 F} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) :
    sl2At F ⟨2, by decide⟩ B ^ 3 = 1 ∧ frameDiag B ^ 3 = 1 ∧
      Commute (sl2At F ⟨2, by decide⟩ B) (frameDiag B) ∧ sl2At F ⟨2, by decide⟩ B ≠ 1 ∧
      frameDiag B ∉ Subgroup.zpowers (sl2At F ⟨2, by decide⟩ B) := by
  have hBc := not_mem_center_of_cube hB3 hB1
  refine ⟨by rw [← map_pow, hB3, map_one], ?_, (frameDiag_commute_sl2Two B B).symm, ?_, ?_⟩
  · rw [← frameDiagHom_apply, ← map_pow, hB3, map_one]
  · intro h
    apply hB1
    apply sl2At_injective ⟨2, by decide⟩
    rw [h, map_one]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← map_zpow] at hk
    have hcen : B ^ k ∈ Subgroup.center (SL2 F) :=
      mem_center_of_commute_sl2At fun X => by rw [hk]; exact frameDiag_commute_sl2Two B X
    have hBk3 : (B ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast (B ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hB3, one_zpow]
    have hBk := eq_one_of_mem_center_cube hcen hBk3
    rw [hBk, map_one] at hk
    exact frameDiag_ne_one hBc hk.symm

theorem outer_pair {B : SL2 F} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) :
    sl2At F ⟨0, by decide⟩ B ^ 3 = 1 ∧ sl2At F ⟨1, by decide⟩ B ^ 3 = 1 ∧
      Commute (sl2At F ⟨0, by decide⟩ B) (sl2At F ⟨1, by decide⟩ B) ∧
      sl2At F ⟨0, by decide⟩ B ≠ 1 ∧
      sl2At F ⟨1, by decide⟩ B ∉ Subgroup.zpowers (sl2At F ⟨0, by decide⟩ B) := by
  have hBc := not_mem_center_of_cube hB3 hB1
  refine ⟨by rw [← map_pow, hB3, map_one], by rw [← map_pow, hB3, map_one],
    sl2At_commute (by decide) (by decide) (by decide) B B, ?_, ?_⟩
  · intro h
    apply hB1
    apply sl2At_injective ⟨0, by decide⟩
    rw [h, map_one]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← map_zpow] at hk
    apply hBc
    refine mem_center_of_commute_sl2At (i := ⟨1, by decide⟩) fun X => ?_
    rw [← hk]
    exact sl2At_commute (by decide) (by decide) (by decide) (B ^ k) X

end Frame

section PairFix

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)

theorem eq_zero_or_one_of_card_two {F₀ : Type} [Field F₀] [Finite F₀] (h2 : Nat.card F₀ = 2)
    (c : F₀) : c = 0 ∨ c = 1 := by
  classical
  have : Fintype F₀ := Fintype.ofFinite F₀
  have hc2 : c ^ 2 = c := by
    have h := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, h2] at h
  have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hc2, sub_self]
  rcases mul_eq_zero.1 h0 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.1 h)

theorem ringEquiv_eq_one_of_card_two {F₀ : Type} [Field F₀] [Finite F₀] (h2 : Nat.card F₀ = 2)
    (σ : F₀ ≃+* F₀) : σ = 1 := by
  refine RingEquiv.ext fun c => ?_
  rcases eq_zero_or_one_of_card_two h2 c with rfl | rfl
  · rw [map_zero]; rfl
  · rw [map_one]; rfl

theorem exists_pair_fix_D4_two {F₀ : Type} [Field F₀] [Finite F₀] (h2 : Nat.card F₀ = 2)
    {α₀ : MulAut ↥(adjointGroup Tag.D4 F₀)} (hα₀3 : α₀ ^ 3 = 1) :
    ∃ x y : ↥(adjointGroup Tag.D4 F₀), α₀ x = x ∧ α₀ y = y ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧
      Commute x y ∧ x ≠ 1 ∧ y ∉ Subgroup.zpowers x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcharP : CharP F₀ 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 1) le_rfl (by rw [h2]; norm_num)
  have hchar : ringChar F₀ = 2 := ringChar.eq F₀ 2
  set B₁ : SL2 F₀ := uSL 1 * vSL 1 with hB₁
  have hB₁3 : B₁ ^ 3 = 1 := uSL_mul_vSL_pow_three
  have hB₁1 : B₁ ≠ 1 := uSL_mul_vSL_ne_one
  obtain ⟨hu3, hv3, huv, hu1, hvu⟩ := outer_pair hB₁3 hB₁1
  by_cases hin : ∃ c : ↥(adjointGroup Tag.D4 F₀), α₀ = MulAut.conj c
  · obtain ⟨c, rfl⟩ := hin
    have hc3 : c ^ 3 = 1 := by
      apply conj_injective_D4
      rw [map_pow, hα₀3, map_one]
    by_cases hc1 : c = 1
    · subst hc1
      refine ⟨_, _, ?_, ?_, hu3, hv3, huv, hu1, hvu⟩ <;> simp
    · obtain ⟨z, hz3, hzc, hzn⟩ := exists_commute_three hu3 hv3 huv hu1 hvu hc3
      refine ⟨c, z, by rw [MulAut.conj_apply]; group, ?_, hc3, hz3, hzc.symm, hc1, hzn⟩
      rw [MulAut.conj_apply, ← hzc.eq]
      group
  · obtain ⟨g, a, σ', ε, hε, hσ'3, hα₀eq⟩ :=
      CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma α₀ hα₀3
    have hσ'1 : σ' = 1 := ringEquiv_eq_one_of_card_two h2 σ'
    subst hσ'1
    have hε0 : ε ≠ 0 := by
      rintro rfl
      apply hin
      have hmem := CFSG.HardMathSupport.Lang.E6Descent.mem_inner_of_normal_form_one g a
        (hα₀eq ▸ hα₀3)
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, hα₀eq.trans hc.symm⟩
    have hD : CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α₀
        fun ε σ => ε ≠ 0 ∧ σ = 1 := ⟨g, a, 1, ε, hε, one_pow 3, ⟨hε0, rfl⟩, hα₀eq⟩
    have hcarry : ∀ (ψ β : MulAut ↥(adjointGroup Tag.D4 F₀)) (B : SL2 F₀), B ^ 3 = 1 → B ≠ 1 →
        ψ * α₀ * ψ⁻¹ = β → β (sl2At F₀ ⟨2, by decide⟩ B) = sl2At F₀ ⟨2, by decide⟩ B →
        β (frameDiag B) = frameDiag B →
        ∃ x y : ↥(adjointGroup Tag.D4 F₀), α₀ x = x ∧ α₀ y = y ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧
          Commute x y ∧ x ≠ 1 ∧ y ∉ Subgroup.zpowers x := by
      intro ψ β B hB3 hB1 hψ hx hy
      obtain ⟨hx3, hy3, hxy, hx1, hyx⟩ := frame_pair hB3 hB1
      have hα₀ : α₀ = ψ⁻¹ * β * ψ := by rw [← hψ]; group
      refine ⟨ψ⁻¹ (sl2At F₀ ⟨2, by decide⟩ B), ψ⁻¹ (frameDiag B), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hα₀, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hx]
      · rw [hα₀, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hy]
      · rw [← map_pow, hx3, map_one]
      · rw [← map_pow, hy3, map_one]
      · exact hxy.map ψ⁻¹
      · intro h
        apply hx1
        rw [← map_one ψ⁻¹] at h
        exact ψ⁻¹.injective h
      · intro hmem
        apply hyx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ψ⁻¹.injective ?_⟩
        rw [map_zpow, hk]
    have hgammaP_two : ∀ B : SL2 F₀,
        gammaP F₀ B (sl2At F₀ ⟨2, by decide⟩ B) = sl2At F₀ ⟨2, by decide⟩ B := by
      intro B
      rw [gammaP, MulAut.mul_apply, d4Graph_one_sl2Two, MulAut.conj_apply]
      group
    rcases isG2Type_or_isA2Type_of_charTwo F₀ hchar α₀ hα₀3 hD with ⟨ψ, h | h⟩ |
        ⟨ψ, B, hB3, hB1, h | h⟩
    · exact hcarry ψ _ B₁ hB₁3 hB₁1 h (d4Graph_one_sl2Two B₁) (d4Graph_frameDiag B₁)
    · have htwo : ∀ x : ↥(adjointGroup Tag.D4 F₀), d4Graph F₀ 1 x = x → d4Graph F₀ 2 x = x := by
        intro x hx
        rw [show (2 : ℕ) = 1 + 1 from rfl, CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
          MulAut.mul_apply, hx, hx]
      exact hcarry ψ _ B₁ hB₁3 hB₁1 h (htwo _ (d4Graph_one_sl2Two B₁))
        (htwo _ (d4Graph_frameDiag B₁))
    · exact hcarry ψ _ B hB3 hB1 h (hgammaP_two B) (gammaP_frameDiag B B)
    · refine hcarry ψ _ B hB3 hB1 h ?_ ?_
      · have h1 := hgammaP_two B
        calc (gammaP F₀ B)⁻¹ (sl2At F₀ ⟨2, by decide⟩ B)
            = (gammaP F₀ B)⁻¹ (gammaP F₀ B (sl2At F₀ ⟨2, by decide⟩ B)) := by rw [h1]
          _ = sl2At F₀ ⟨2, by decide⟩ B := MulAut.inv_apply_self _ _ _
      · have h1 := gammaP_frameDiag B B
        calc (gammaP F₀ B)⁻¹ (frameDiag B) = (gammaP F₀ B)⁻¹ (gammaP F₀ B (frameDiag B)) := by
              rw [h1]
          _ = frameDiag B := MulAut.inv_apply_self _ _ _

theorem exists_pair_fix_field_D4 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    {σ : F ≃+* F} (hσ1 : σ ≠ 1) {α : MulAut ↥(adjointGroup Tag.D4 F)} (hα3 : α ^ 3 = 1)
    (hcomm : α * entrywiseAdjointAut Tag.D4 σ = entrywiseAdjointAut Tag.D4 σ * α) :
    ∃ x y : ↥(adjointGroup Tag.D4 F), α x = x ∧ α y = y ∧
      entrywiseAdjointAut Tag.D4 σ x = x ∧ entrywiseAdjointAut Tag.D4 σ y = y ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ Commute x y ∧ x ≠ 1 ∧ y ∉ Subgroup.zpowers x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 3) (by norm_num) hF
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨hdvd, hcardfix⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield
    Nat.prime_two (f := 3) (by norm_num) hF σ
  have hord : orderOf σ = 3 := by
    have h1 : orderOf σ ≠ 1 := fun h => hσ1 (orderOf_eq_one_iff.1 h)
    exact ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left h1
  have h2 : Nat.card ↥(fixSubfield σ) = 2 := by rw [hcardfix, hord]; norm_num
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
    (τ := Tag.D4) (Or.inr (Or.inr (Or.inl rfl))) hchar σ
  set L := fixedSubgroup (entrywiseAdjointAut Tag.D4 σ) with hLdef
  let E4 : ↥L ≃* ↥(adjointGroup Tag.D4 (fixSubfield σ)) :=
    CFSG.LieType.SeitzGeneration.ExcOuterLeOne.fixedEquivOfEq (τ := Tag.D4) σ hΓJ
  have hcomm' : α * entrywiseAdjointAut Tag.D4 σ * α⁻¹ = entrywiseAdjointAut Tag.D4 σ := by
    rw [hcomm]; group
  have hL : L.map (α : ↥(adjointGroup Tag.D4 F) →* ↥(adjointGroup Tag.D4 F)) = L := by
    have h1 := D4FixedAux.fixed_map_conj α (entrywiseAdjointAut Tag.D4 σ)
    rw [hcomm'] at h1
    exact h1
  let αL : MulAut ↥L := (α.subgroupMap L).trans (MulEquiv.subgroupCongr hL)
  have hαL : ∀ u : ↥L, ((αL u : ↥L) : ↥(adjointGroup Tag.D4 F)) = α u := fun u => rfl
  set α₀ : MulAut ↥(adjointGroup Tag.D4 (fixSubfield σ)) := MulAut.congr E4 αL with hα₀def
  have hαL3 : αL ^ 3 = 1 := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    have h1 : ∀ n : ℕ, (((αL ^ n) u : ↥L) : ↥(adjointGroup Tag.D4 F)) = (α ^ n) u := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ', MulAut.mul_apply, hαL, ih, pow_succ', MulAut.mul_apply]
    rw [h1, hα3]
    rfl
  have hα₀3 : α₀ ^ 3 = 1 := by rw [hα₀def, ← map_pow, hαL3, map_one]
  obtain ⟨x₀, y₀, hx₀, hy₀, hx₀3, hy₀3, hxy₀, hx₀1, hy₀x⟩ := exists_pair_fix_D4_two h2 hα₀3
  have hfixL : ∀ w₀ : ↥(adjointGroup Tag.D4 (fixSubfield σ)), α₀ w₀ = w₀ →
      α ((E4.symm w₀ : ↥L) : ↥(adjointGroup Tag.D4 F)) = (E4.symm w₀ : ↥L) := by
    intro w₀ hw₀
    rw [← hαL]
    congr 1
    have h1 : E4 (αL (E4.symm w₀)) = w₀ := hw₀
    exact E4.injective (h1.trans (E4.apply_symm_apply w₀).symm)
  have hσL : ∀ u : ↥L, entrywiseAdjointAut Tag.D4 σ (u : ↥(adjointGroup Tag.D4 F)) = u :=
    fun u => mem_fixedSubgroup.1 u.2
  set ι : ↥(adjointGroup Tag.D4 (fixSubfield σ)) →* ↥(adjointGroup Tag.D4 F) :=
    L.subtype.comp E4.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp E4.symm.injective
  refine ⟨ι x₀, ι y₀, hfixL x₀ hx₀, hfixL y₀ hy₀, hσL _, hσL _, by rw [← map_pow, hx₀3, map_one],
    by rw [← map_pow, hy₀3, map_one], hxy₀.map ι, fun h => hx₀1 (hιinj (h.trans (map_one ι).symm)),
    fun hmem => hy₀x ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  exact Subgroup.mem_zpowers_iff.2 ⟨k, hιinj (by rw [map_zpow, hk])⟩

end PairFix

section Action

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz (exists_frobenius_eight
  fieldAutD4_of_fieldType center_eq_bot_of_d4EightComp hasNF_pow d4ElemType_of_hasNF
  sigma_cube_of_hasNF entrywiseAdjointAut_D4_eq)

variable {X : Type} [Group X]

theorem exists_inner_part [Finite X] {K B : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hSC : IsSCp 3 (K ⊔ B) B) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) {a b : X} (haB : a ∈ B)
    (hbB : b ∈ B)
    (hA : D4ElemType (MulAut.congr e (actHom K ⟨a, hBN haB⟩)) fun ε σ => ε ≠ 0 ∧ σ = 1)
    (hBf : D4ElemType (MulAut.congr e (actHom K ⟨b, hBN hbB⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1)
    {β : X} (hβ : β ∈ B) :
    ∃ (i j : ℕ) (κ : X), κ ∈ B ∧ κ ∈ K ∧ ∀ x ∈ K,
      (β * a ^ i * b ^ j) * x * (β * a ^ i * b ^ j)⁻¹ = κ * x * κ⁻¹ := by
  classical
  have hord : ∀ {z : X} (hz : z ∈ B), MulAut.congr e (actHom K ⟨z, hBN hz⟩) ^ 3 = 1 := by
    intro z hz
    have h1 : (⟨z, hBN hz⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hBel.2 z hz)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨g₁, c₁, σ₁, ε₁, hε₁, -, ⟨hε₁0, hσ₁⟩, hαa⟩ := hA
  subst hσ₁
  obtain ⟨g₂, c₂, σ₂, ε₂, -, hσ₂3, ⟨hε₂, hσ₂1⟩, hαb⟩ := hBf
  subst hε₂
  obtain ⟨g₃, c₃, σ₃, ε₃, hε₃, hσ₃3, hαβ⟩ :=
    CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma _ (hord hβ)
  have hNa : HasNF (MulAut.congr e (actHom K ⟨a, hBN haB⟩)) ε₁ 1 := ⟨g₁, c₁, hαa⟩
  have hNb : HasNF (MulAut.congr e (actHom K ⟨b, hBN hbB⟩)) 0 σ₂ := ⟨g₂, c₂, hαb⟩
  have hNβ : HasNF (MulAut.congr e (actHom K ⟨β, hBN hβ⟩)) ε₃ σ₃ := ⟨g₃, c₃, hαβ⟩
  obtain ⟨T, hT, hT3, hT1, hσ₂T⟩ := exists_frobenius_eight hF hσ₂3 hσ₂1
  have hTinv : T⁻¹ = T ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']; exact hT3
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, σ₃ = σ₂ ^ j₀ := by
    by_cases h3 : σ₃ = 1
    · exact ⟨0, by rw [h3, pow_zero]⟩
    · obtain ⟨T', hT', -, -, hσ₃T'⟩ := exists_frobenius_eight hF hσ₃3 h3
      have hTT : T' = T := RingEquiv.ext fun c => by rw [hT, hT']
      subst hTT
      rcases hσ₂T with h₂ | h₂ <;> rcases hσ₃T' with h₃ | h₃
      · exact ⟨1, by rw [h₂, h₃, pow_one]⟩
      · exact ⟨2, by rw [h₂, h₃, hTinv]⟩
      · refine ⟨2, ?_⟩
        rw [h₂, h₃, inv_pow, ← hTinv, inv_inv]
      · exact ⟨1, by rw [h₂, h₃, pow_one]⟩
  set i := 2 * ((ε₃ * ε₁) % 3) with hi
  set j := 2 * j₀ with hj
  have hNγ := (hNβ.mul (hasNF_pow hNa i)).mul (hasNF_pow hNb j)
  have hε : (ε₃ + i * ε₁ + j * 0) % 3 = 0 := by
    have h1 : ε₁ = 1 ∨ ε₁ = 2 := by omega
    rcases h1 with rfl | rfl <;> interval_cases ε₃ <;> simp [hi]
  have hσ : σ₃ * 1 ^ i * σ₂ ^ j = 1 := by
    rw [one_pow, mul_one, hj₀, hj, ← pow_add, show j₀ + 2 * j₀ = 3 * j₀ by ring, pow_mul, hσ₂3,
      one_pow]
  obtain ⟨g, c, hγ⟩ := hNγ.mod_three
  rw [hε, hσ] at hγ
  have hβ'B : β * a ^ i * b ^ j ∈ B := mul_mem (mul_mem hβ (pow_mem haB i)) (pow_mem hbB j)
  have hγeq : MulAut.congr e (actHom K ⟨β, hBN hβ⟩) * MulAut.congr e (actHom K ⟨a, hBN haB⟩) ^ i *
      MulAut.congr e (actHom K ⟨b, hBN hbB⟩) ^ j =
        MulAut.congr e (actHom K ⟨β * a ^ i * b ^ j, hBN hβ'B⟩) := by
    have h1 : (⟨β * a ^ i * b ^ j, hBN hβ'B⟩ : Subgroup.normalizer (K : Set X)) =
        ⟨β, hBN hβ⟩ * ⟨a, hBN haB⟩ ^ i * ⟨b, hBN hbB⟩ ^ j :=
      Subtype.ext (by simp)
    rw [h1, map_mul, map_mul, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow]
  have h3γ := hord hβ'B
  rw [← hγeq, hγ] at h3γ
  obtain ⟨ĝ, hĝ⟩ := CFSG.HardMathSupport.Lang.E6Descent.mem_inner_of_normal_form_one g c h3γ
  rw [← hγ, hγeq] at hĝ
  obtain ⟨κ, hκ⟩ := exists_conj_of_inner hZ e (hBN hβ'B) hĝ.symm
  have hκ' : ∀ x ∈ K, (β * a ^ i * b ^ j) * x * (β * a ^ i * b ^ j)⁻¹ = κ * x * (κ : X)⁻¹ :=
    fun x hx => hκ ⟨x, hx⟩
  exact ⟨i, j, κ, mem_of_acts_as_conj hZ hBel hBN hSC hβ'B κ.2 hκ', κ.2, hκ'⟩

theorem exists_two_inner [Finite X] {K B : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hSC : IsSCp 3 (K ⊔ B) B) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) {a b : X} (haB : a ∈ B)
    (hbB : b ∈ B)
    (hA : D4ElemType (MulAut.congr e (actHom K ⟨a, hBN haB⟩)) fun ε σ => ε ≠ 0 ∧ σ = 1)
    (hBf : D4ElemType (MulAut.congr e (actHom K ⟨b, hBN hbB⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1) :
    ∃ d₁ d₂ : X, d₁ ∈ B ∧ d₁ ∈ K ∧ d₂ ∈ B ∧ d₂ ∈ K ∧ d₁ ≠ 1 ∧ d₂ ∉ Subgroup.zpowers d₁ := by
  classical
  have hab : a * b = b * a := Bal209F4Aux.commute_of_elemAbelian hBel haB hbB
  have hord : ∀ {z : X} (hz : z ∈ B), actHom K ⟨z, hBN hz⟩ ^ 3 = 1 := by
    intro z hz
    have h1 : (⟨z, hBN hz⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hBel.2 z hz)
    rw [← map_pow, h1, map_one]
  obtain ⟨F', _, _, e₀, σ, γ, hF', hσ1, hmat⟩ :=
    fieldAutD4_of_fieldType hF e (hord hbB) hBf
  set e₂ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F') := e₀.trans γ with he₂
  have hαb : MulAut.congr e₂ (actHom K ⟨b, hBN hbB⟩) = entrywiseAdjointAut Tag.D4 σ := by
    refine MulEquiv.ext fun g => ?_
    obtain ⟨g', hg', hg''⟩ := hmat g
    have h1 : MulAut.congr e₂ (actHom K ⟨b, hBN hbB⟩) g =
        (γ * MulAut.congr e₀ (actHom K ⟨b, hBN hbB⟩) * γ⁻¹) g := rfl
    rw [h1, hg'']
    exact Subtype.ext hg'
  have hcomm : MulAut.congr e₂ (actHom K ⟨a, hBN haB⟩) * entrywiseAdjointAut Tag.D4 σ =
      entrywiseAdjointAut Tag.D4 σ * MulAut.congr e₂ (actHom K ⟨a, hBN haB⟩) := by
    rw [← hαb, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext hab
  have hα3 : MulAut.congr e₂ (actHom K ⟨a, hBN haB⟩) ^ 3 = 1 := by
    rw [← map_pow, hord haB, map_one]
  obtain ⟨x', y', hx'a, hy'a, hx'b, hy'b, hx'3, hy'3, hxy', hx'1, hy'x'⟩ :=
    exists_pair_fix_field_D4 hF' hσ1 hα3 hcomm
  set ψK : ↥K ≃* ↥(adjointGroup Tag.D4 F') := (quotEquivOfCenterBot hZ).trans e₂ with hψK
  have hψK : ∀ x : ↥K, ψK x = e₂ (QuotientGroup.mk x) := fun x => rfl
  set x₀ := ψK.symm x' with hx₀
  set y₀ := ψK.symm y' with hy₀
  have hfix : ∀ {z : X} (hz : z ∈ B) {w : ↥K},
      MulAut.congr e₂ (actHom K ⟨z, hBN hz⟩) (ψK w) = ψK w → z * (w : X) * z⁻¹ = w := by
    intro z hz w hw
    rw [hψK] at hw
    exact conj_eq_of_congr_fixed hZ e₂ (hBN hz) hw
  have hx₀a : a * (x₀ : X) * a⁻¹ = x₀ := hfix haB (by rw [hx₀, ψK.apply_symm_apply]; exact hx'a)
  have hy₀a : a * (y₀ : X) * a⁻¹ = y₀ := hfix haB (by rw [hy₀, ψK.apply_symm_apply]; exact hy'a)
  have hx₀b : b * (x₀ : X) * b⁻¹ = x₀ :=
    hfix hbB (by rw [hx₀, ψK.apply_symm_apply, hαb]; exact hx'b)
  have hy₀b : b * (y₀ : X) * b⁻¹ = y₀ :=
    hfix hbB (by rw [hy₀, ψK.apply_symm_apply, hαb]; exact hy'b)
  set H := K ⊓ Subgroup.centralizer ({a} : Set X) ⊓ Subgroup.centralizer ({b} : Set X) with hH
  have hmemH : ∀ {w : X}, w ∈ K → a * w * a⁻¹ = w → b * w * b⁻¹ = w → w ∈ H := by
    intro w hwK hwa hwb
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hwK, Subgroup.mem_centralizer_iff.2 ?_⟩,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    · intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      calc a * w = (a * w * a⁻¹) * a := by group
        _ = w * a := by rw [hwa]
    · intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      calc b * w = (b * w * b⁻¹) * b := by group
        _ = w * b := by rw [hwb]
  have hxH : (x₀ : X) ∈ H := hmemH x₀.2 hx₀a hx₀b
  have hyH : (y₀ : X) ∈ H := hmemH y₀.2 hy₀a hy₀b
  have hψinj : Function.Injective (fun w : ↥K => (w : X)) := Subtype.val_injective
  set xH : ↥H := ⟨x₀, hxH⟩
  set yH : ↥H := ⟨y₀, hyH⟩
  have hxH3 : xH ^ 3 = 1 := by
    apply Subtype.ext
    show ((x₀ : X)) ^ 3 = 1
    have h1 : x₀ ^ 3 = 1 := by
      rw [hx₀, ← map_pow, hx'3, map_one]
    exact congrArg Subtype.val h1
  have hyH3 : yH ^ 3 = 1 := by
    apply Subtype.ext
    show ((y₀ : X)) ^ 3 = 1
    have h1 : y₀ ^ 3 = 1 := by
      rw [hy₀, ← map_pow, hy'3, map_one]
    exact congrArg Subtype.val h1
  have hxyH : Commute xH yH := by
    apply Subtype.ext
    show (x₀ : X) * y₀ = y₀ * x₀
    have h1 : x₀ * y₀ = y₀ * x₀ := by
      rw [hx₀, hy₀, ← map_mul, ← map_mul, hxy'.eq]
    exact congrArg Subtype.val h1
  have hxH1 : xH ≠ 1 := by
    intro h
    apply hx'1
    have h1 : x₀ = 1 := Subtype.ext (by
      have h2 := congrArg Subtype.val h
      simpa [xH] using h2)
    rw [← ψK.apply_symm_apply x', ← hx₀, h1, map_one]
  have hyxH : yH ∉ Subgroup.zpowers xH := by
    intro hmem
    apply hy'x'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : x₀ ^ k = y₀ := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    rw [← ψK.apply_symm_apply x', ← ψK.apply_symm_apply y', ← map_zpow, ← hx₀, ← hy₀, h1]
  by_contra hcon
  push Not at hcon
  obtain ⟨d, hdB, hdK, hdcov⟩ : ∃ d : X, d ∈ B ∧ d ∈ K ∧
      ∀ w : X, w ∈ B → w ∈ K → w ∈ Subgroup.zpowers d := by
    by_cases hne : ∃ d₁ : X, d₁ ∈ B ∧ d₁ ∈ K ∧ d₁ ≠ 1
    · obtain ⟨d₁, h1, h2, h3⟩ := hne
      exact ⟨d₁, h1, h2, fun w hwB hwK => hcon d₁ w h1 h2 hwB hwK h3⟩
    · push Not at hne
      refine ⟨1, one_mem _, one_mem _, fun w hwB hwK => ?_⟩
      rw [hne w hwB hwK]
      exact one_mem _
  have hdH : d ∈ H := by
    refine hmemH hdK ?_ ?_
    · rw [Bal209F4Aux.commute_of_elemAbelian hBel haB hdB]; group
    · rw [Bal209F4Aux.commute_of_elemAbelian hBel hbB hdB]; group
  have hd3 : (⟨d, hdH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by
    show d ^ 3 = 1
    exact hBel.2 d hdB)
  obtain ⟨z, hz3, hzd, hzn⟩ := exists_commute_three hxH3 hyH3 hxyH hxH1 hyxH hd3
  have hzK : (z : X) ∈ K := z.2.1.1
  have hza : a * (z : X) = z * a := by
    have := Subgroup.mem_centralizer_iff.1 z.2.1.2 a (Set.mem_singleton a)
    exact this
  have hzb : b * (z : X) = z * b := by
    have := Subgroup.mem_centralizer_iff.1 z.2.2 b (Set.mem_singleton b)
    exact this
  have hzd' : Commute (z : X) d := congrArg Subtype.val hzd
  have hzB : ∀ β ∈ B, Commute (z : X) β := by
    intro β hβ
    obtain ⟨i, j, κ, hκB, hκK, hκ⟩ := exists_inner_part hZ hBel hBN hSC hF e haB hbB hA hBf hβ
    have hκd : κ ∈ Subgroup.zpowers d := hdcov κ hκB hκK
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hκd
    have hzκ : Commute (z : X) κ := by rw [← hm]; exact hzd'.zpow_right m
    have hzai : Commute (z : X) (a ^ i) := (Commute.pow_right hza.symm i)
    have hzbj : Commute (z : X) (b ^ j) := (Commute.pow_right hzb.symm j)
    have h1 := hκ z hzK
    have h2 : (β * a ^ i * b ^ j) * (z : X) * (β * a ^ i * b ^ j)⁻¹ = z := by
      rw [h1, ← hzκ.eq]; group
    have h3 : β * (z : X) * β⁻¹ = z := by
      have e1 : (β * a ^ i * b ^ j) * (z : X) * (β * a ^ i * b ^ j)⁻¹ =
          β * ((a ^ i * b ^ j) * (z : X) * (a ^ i * b ^ j)⁻¹) * β⁻¹ := by group
      have e2 : (a ^ i * b ^ j) * (z : X) * (a ^ i * b ^ j)⁻¹ = z := by
        rw [mul_assoc (a ^ i), ← hzbj.eq, ← mul_assoc, ← hzai.eq]; group
      rw [e1, e2] at h2
      exact h2
    show (z : X) * β = β * z
    calc (z : X) * β = (β * z * β⁻¹) * β := by rw [h3]
      _ = β * z := by group
  have hz3' : (z : X) ^ 3 = 1 := congrArg Subtype.val hz3
  have hzBmem := mem_of_isSCp_of_commute hSC hzK hzB hz3'
  apply hzn
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hdcov z hzBmem hzK)
  refine Subgroup.mem_zpowers_iff.2 ⟨m, Subtype.ext ?_⟩
  simpa using hm

end Action

section G2Case

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz (exists_frobenius_eight
  fieldAutD4_of_fieldType center_eq_bot_of_d4EightComp hasNF_pow d4ElemType_of_hasNF
  sigma_cube_of_hasNF entrywiseAdjointAut_D4_eq fixSubgroupD4GraphEquivG2)

theorem nonempty_fixEquiv {X : Type} [Group X] [Finite X] {K : Subgroup X} {a : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (hK : CFSG.Open.IsComponentOf K ⊤)
    (hLie : IsLieQuot ↥K OuterFourAux.IsD4EightIndex) {F : Type} [Field F]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) :
    Nonempty (↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ≃*
      ↥(fixedSubgroup (MulAut.congr e (actHom K ⟨a, ha⟩)))) := by
  classical
  have hZK := center_eq_bot_of_d4EightComp hK hLie
  let eKq : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZK.symm)
  let eD : K ≃* ↥(adjointGroup Tag.D4 F) := eKq.trans e
  set β : MulAut ↥(adjointGroup Tag.D4 F) := MulAut.congr eD (D4FixedAux.conjOnNormal K a ha)
    with hβdef
  have hβact : MulAut.congr e (actHom K ⟨a, ha⟩) = β := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have h2 : eD.symm (e (QuotientGroup.mk k)) = k := (MulEquiv.symm_apply_eq eD).2 rfl
    simp only [hβdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h2]
    rfl
  have E1 : ↥(fixedSubgroup (D4FixedAux.conjOnNormal K a ha)) ≃*
      ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) :=
    (MulEquiv.subgroupCongr (D4FixedAux.fixedSubgroup_conjOnNormal K a ha)).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have E2 : ↥(fixedSubgroup (D4FixedAux.conjOnNormal K a ha)) ≃* ↥(fixedSubgroup β) :=
    (Subgroup.equivMapOfInjective _ eD.toMonoidHom eD.injective).trans
      (MulEquiv.subgroupCongr (D4FixedAux.fixed_map_congr eD (D4FixedAux.conjOnNormal K a ha)))
  have hsub : fixedSubgroup β = fixedSubgroup (MulAut.congr e (actHom K ⟨a, ha⟩)) := by
    rw [hβact]
  exact ⟨E1.symm.trans (E2.trans (MulEquiv.subgroupCongr hsub))⟩

theorem not_inner_of_faithful {X : Type} [Group X] [Finite X] {K : Subgroup X} {b : X}
    (hb : b ∈ Subgroup.normalizer (K : Set X)) (hK : CFSG.Open.IsComponentOf K ⊤)
    (hLie : IsLieQuot ↥K OuterFourAux.IsD4EightIndex) (hb3 : b ^ 3 = 1)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F))
    (hBf : D4ElemType (MulAut.congr e (actHom K ⟨b, hb⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1)
    {H J : Subgroup X} (hHK : H ≤ K) (hJH : J ≤ H)
    (hHJ : ∀ h ∈ H, ∀ x ∈ J, h * x * h⁻¹ ∈ J) (hbH : ∀ h ∈ H, b * h * b⁻¹ ∈ H)
    (hfaith : ∀ c ∈ H, (∀ x ∈ J, c * x = x * c) → c = 1)
    (hcard : ¬ Nat.card J ∣ ordD 4 2) :
    ¬ ∃ h ∈ H, ∀ x ∈ J, b * x * b⁻¹ = h * x * h⁻¹ := by
  classical
  rintro ⟨h, hhH, hh⟩
  have hhK : h ∈ K := hHK hhH
  have hpow : ∀ n : ℕ, ∀ x ∈ J, b ^ n * x * (b ^ n)⁻¹ = h ^ n * x * (h ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      calc b ^ (n + 1) * x * (b ^ (n + 1))⁻¹ = b ^ n * (b * x * b⁻¹) * (b ^ n)⁻¹ := by
            rw [pow_succ]; group
        _ = b ^ n * (h * x * h⁻¹) * (b ^ n)⁻¹ := by rw [hh x hx]
        _ = h ^ n * (h * x * h⁻¹) * (h ^ n)⁻¹ := ih _ (hHJ h hhH x hx)
        _ = h ^ (n + 1) * x * (h ^ (n + 1))⁻¹ := by rw [pow_succ]; group
  have hh3 : h ^ 3 = 1 := by
    refine hfaith _ (pow_mem hhH 3) fun x hx => ?_
    have h1 := hpow 3 x hx
    rw [hb3, one_mul, inv_one, mul_one] at h1
    calc h ^ 3 * x = (h ^ 3 * x * (h ^ 3)⁻¹) * h ^ 3 := by group
      _ = x * h ^ 3 := by rw [← h1]
  have hb2 : b⁻¹ = b ^ 2 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hb3)).symm
  have hbinv : ∀ x ∈ J, b⁻¹ * x * b ∈ J := by
    intro x hx
    have h2 : b⁻¹ * x * b = h ^ 2 * x * (h ^ 2)⁻¹ := by
      calc b⁻¹ * x * b = b ^ 2 * x * (b ^ 2)⁻¹ := by rw [← hb2, inv_inv]
        _ = h ^ 2 * x * (h ^ 2)⁻¹ := hpow 2 x hx
    rw [h2]
    exact hHJ _ (pow_mem hhH 2) x hx
  have hbh : b * h * b⁻¹ = h := by
    have hc : h⁻¹ * (b * h * b⁻¹) = 1 := by
      refine hfaith _ (mul_mem (inv_mem hhH) (hbH h hhH)) fun x hx => ?_
      have hy := hbinv x hx
      have h1 : h * (b⁻¹ * x * b) * h⁻¹ = x := by
        rw [← hh _ hy]; group
      have h2 : (b * h * b⁻¹) * x * (b * h * b⁻¹)⁻¹ = h * x * h⁻¹ := by
        calc (b * h * b⁻¹) * x * (b * h * b⁻¹)⁻¹ = b * (h * (b⁻¹ * x * b) * h⁻¹) * b⁻¹ := by
              group
          _ = b * x * b⁻¹ := by rw [h1]
          _ = h * x * h⁻¹ := hh x hx
      calc h⁻¹ * (b * h * b⁻¹) * x =
            h⁻¹ * ((b * h * b⁻¹) * x * (b * h * b⁻¹)⁻¹) * (b * h * b⁻¹) := by group
        _ = h⁻¹ * (h * x * h⁻¹) * (b * h * b⁻¹) := by rw [h2]
        _ = x * (h⁻¹ * (b * h * b⁻¹)) := by group
    calc b * h * b⁻¹ = h * (h⁻¹ * (b * h * b⁻¹)) := by group
      _ = h := by rw [hc, mul_one]
  have hbj : b * h = h * b := by
    calc b * h = (b * h * b⁻¹) * b := by group
      _ = h * b := by rw [hbh]
  have hhN : h ∈ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer hhK
  set w := b * h⁻¹ with hw
  have hwN : w ∈ Subgroup.normalizer (K : Set X) := mul_mem hb (inv_mem hhN)
  have hw3 : w ^ 3 = 1 := by
    have hc : Commute b h⁻¹ := Commute.inv_right hbj
    rw [hw, hc.mul_pow, inv_pow, hb3, hh3, inv_one, mul_one]
  have hJw : J ≤ K ⊓ Subgroup.centralizer ({w} : Set X) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hHK (hJH hx), Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [Set.mem_singleton_iff.1 hg]
    have hx' : h⁻¹ * x * h ∈ J := by
      have h0 := hHJ h⁻¹ (inv_mem hhH) x hx
      rwa [inv_inv] at h0
    have h1 := hh _ hx'
    have h2 : w * x * w⁻¹ = x := by
      calc w * x * w⁻¹ = b * (h⁻¹ * x * h) * b⁻¹ := by rw [hw]; group
        _ = h * (h⁻¹ * x * h) * h⁻¹ := h1
        _ = x := by group
    calc w * x = (w * x * w⁻¹) * w := by group
      _ = x * w := by rw [h2]
  obtain ⟨g₀, c₀, σ₀, ε₀, -, -, ⟨hε₀, hσ₀1⟩, hαb⟩ := hBf
  subst hε₀
  have hNb : HasNF (MulAut.congr e (actHom K ⟨b, hb⟩)) 0 σ₀ := ⟨g₀, c₀, hαb⟩
  have hwact : MulAut.congr e (actHom K ⟨w, hwN⟩) = MulAut.congr e (actHom K ⟨b, hb⟩) *
      MulAut.conj (e (QuotientGroup.mk ⟨h⁻¹, inv_mem hhK⟩)) := by
    have h1 : (⟨w, hwN⟩ : Subgroup.normalizer (K : Set X)) = ⟨b, hb⟩ * ⟨h⁻¹, inv_mem hhN⟩ := rfl
    rw [h1, map_mul, map_mul, actHom_of_mem (inv_mem hhK) (inv_mem hhN), congr_conj_eq]
  have hNw : HasNF (MulAut.congr e (actHom K ⟨w, hwN⟩)) 0 σ₀ := by
    have h1 := hNb.mul (hasNF_conj (e (QuotientGroup.mk ⟨h⁻¹, inv_mem hhK⟩)))
    rw [mul_one, add_zero] at h1
    rwa [hwact]
  have hw1 : (⟨w, hwN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hw3)
  have hact3 : actHom K ⟨w, hwN⟩ ^ 3 = 1 := by rw [← map_pow, hw1, map_one]
  have hw3' : MulAut.congr e (actHom K ⟨w, hwN⟩) ^ 3 = 1 := by
    rw [← map_pow, hact3, map_one]
  have hFA := fieldAutD4_of_fieldType hF e hact3 (d4ElemType_of_hasNF hNw hw3' ⟨rfl, hσ₀1⟩)
  obtain ⟨hsW, hqW, -, hLieW⟩ := d4FieldFixed_holds X K w hwN hK hLie hw3 hFA
  have hcardW := card_of_isLieQuot_d4Two (center_eq_bot_of_quasisimple hsW hqW) hLieW
  have hdvd := Subgroup.card_dvd_of_le hJw
  rw [hcardW] at hdvd
  exact hcard hdvd

end G2Case

section G2Kill

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz (center_eq_bot_of_d4EightComp)

theorem g2Branch {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hLie : IsLieQuot ↥K OuterFourAux.IsD4EightIndex)
    (hSC : IsSCp 3 (K ⊔ B) B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) {a b : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (hb : b ∈ Subgroup.normalizer (K : Set X))
    (haB : a ∈ B) (hbB : b ∈ B)
    (hA : D4ElemType (MulAut.congr e (actHom K ⟨a, ha⟩)) fun ε σ => ε ≠ 0 ∧ σ = 1)
    (hBf : D4ElemType (MulAut.congr e (actHom K ⟨b, hb⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1)
    {F' : Type} [Field F'] [Finite F'] (hF' : Nat.card F' = 2 ^ 3)
    (Fg : ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) ≃* ↥(adjointGroup Tag.G2 F'))
    {J : Subgroup X} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced 3 B a J := by
  have hBel : IsElemAbelian 3 B := hSC.2.1
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  obtain ⟨hsJ, hqJ, hLieJ, hcardJ⟩ := g2Props hF' Fg
  have hJeq := Bal209F4Aux.eq_of_glaPComponent hsJ hJ
  subst hJeq
  set J := K ⊓ Subgroup.centralizer ({a} : Set X) with hJdef
  have hBJ : B ≤ Subgroup.normalizer (J : Set X) := le_normalizer_inf_centralizer hBel hBN haB
  have hZK := center_eq_bot_of_d4EightComp hK hLie
  have hZJ : Subgroup.center ↥J = ⊥ := center_eq_bot_of_quasisimple hsJ hqJ
  have hfaith : ∀ c ∈ J, (∀ x ∈ J, c * x = x * c) → c = 1 := by
    intro c hc hcx
    have hmem : (⟨c, hc⟩ : ↥J) ∈ Subgroup.center ↥J :=
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (hcx y y.2).symm
    rw [hZJ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨d₁, d₂, hd₁B, hd₁K, hd₂B, hd₂K, hd₁, hd₂⟩ :=
    exists_two_inner hZK hBel hBN hSC hF e haB hbB hA hBf
  have hout : ¬ ∃ h ∈ J, ∀ x ∈ J, b * x * b⁻¹ = h * x * h⁻¹ := by
    intro hex
    obtain ⟨j, hjJ, hj⟩ := hex
    refine not_inner_of_faithful hb hK hLie hb3 hF e hBf inf_le_left le_rfl
      (fun h hh x hx => mul_mem (mul_mem hh hx) (inv_mem hh))
      (fun h hh => (hj h hh).symm ▸ mul_mem (mul_mem hjJ hh) (inv_mem hjJ)) hfaith
      (by rw [hcardJ]; exact not_ordG2_eight_dvd_ordD) ⟨j, hjJ, hj⟩
  have hE := autImageRankThree_of_outer hBel hBJ hZJ hfaith hbB hd₁B
    (mem_inf_centralizer_of_mem hBel haB hd₁B hd₁K) hd₂B
    (mem_inf_centralizer_of_mem hBel haB hd₂B hd₂K) hd₁ hd₂ hout
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hqJ.1⟩
  refine ⟨hBJ, KSF4Kit.isStronglyLocallyOneBalanced_of_centralizes fun S hS hcop hBS => ?_⟩
  exact CFSG.HardMathSupport.Dickson.Bal207.centralizes_of_autImageRankThree_g28 hperf hLieJ hE
    (hS.trans inf_le_left) hcop hBS

end G2Kill

structure PGUThreeEightData (C : Type) [Group C] (M : Subgroup C) : Prop where
  normal : M.Normal
  comm : ∀ x y : C, x * y * x⁻¹ * y⁻¹ ∈ M
  faithful : ∀ x : C, (∀ m ∈ M, x * m = m * x) → x = 1
  simple : IsSimpleGroup ↥M
  model : Nonempty (↥M ≃* ↥(CFSG.PGLModel.projSU 3 2 3))

theorem PGUThreeEightData.map {C C' : Type} [Group C] [Group C'] {M : Subgroup C}
    (h : PGUThreeEightData C M) (φ : C ≃* C') : PGUThreeEightData C' (M.map φ.toMonoidHom) where
  normal := h.normal.map φ.toMonoidHom φ.surjective
  comm x y := by
    refine ⟨_, h.comm (φ.symm x) (φ.symm y), ?_⟩
    simp
  faithful x hx := by
    have h1 : φ.symm x = 1 := h.faithful _ fun m hm => by
      apply φ.injective
      have h2 := hx (φ m) ⟨m, hm, rfl⟩
      simpa using h2
    simpa using congrArg φ h1
  simple := (MulEquiv.isSimpleGroup_congr
    (Subgroup.equivMapOfInjective M φ.toMonoidHom φ.injective)).1 h.simple
  model := ⟨(Subgroup.equivMapOfInjective M φ.toMonoidHom φ.injective).symm.trans h.model.some⟩

theorem eq_of_glaPComponent_of_comm {X : Type} [Group X] {H M J : Subgroup X} (hMH : M ≤ H)
    (hsM : IsSimpleGroup ↥M) (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ M)
    (hJ : GLAPComponent 3 H J) : J = M := by
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJM : J ≤ M := by
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact hcomm x (hJ.1 hx) y (hJ.1 hy)
  have hsn : CFSG.Open.IsSubnormal J M := isSubnormal_of_le_of_le hJ.2.1 hJM hMH
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn hsM with h0 | h0
  · exfalso
    obtain ⟨-, -, hIC, -⟩ := hJ
    obtain ⟨⟨g, hgL⟩, hg1⟩ := Bal209F4Aux.exists_ne_one_of_isQuasisimple hIC.2.2
    rw [h0, Subgroup.bot_subgroupOf, Subgroup.map_bot, Subgroup.mem_bot] at hgL
    exact hg1 (Subtype.ext hgL)
  · exact h0

theorem not_ordU38_dvd_ordD : ¬ (5515776 : ℕ) ∣ ordD 4 2 := by
  simp only [ordD]
  decide

section PGUKill

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz (center_eq_bot_of_d4EightComp)

theorem pguBranch_aux {X : Type} [Group X] [Finite X] {K B H : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hLie : IsLieQuot ↥K OuterFourAux.IsD4EightIndex)
    (hSC : IsSCp 3 (K ⊔ B) B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) {a b : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (hb : b ∈ Subgroup.normalizer (K : Set X))
    (haB : a ∈ B) (hbB : b ∈ B)
    (hA : D4ElemType (MulAut.congr e (actHom K ⟨a, ha⟩)) fun ε σ => ε ≠ 0 ∧ σ = 1)
    (hBf : D4ElemType (MulAut.congr e (actHom K ⟨b, hb⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1)
    (hHK : H ≤ K) (hBH : ∀ β ∈ B, ∀ h ∈ H, β * h * β⁻¹ ∈ H)
    (hDH : ∀ d ∈ B, d ∈ K → d ∈ H) {M : Subgroup ↥H} (hM : PGUThreeEightData ↥H M)
    {J : Subgroup X} (hJ : GLAPComponent 3 H J)
    (hconj : ∀ β ∈ B, GLAPComponent 3 H (GLBConj β J)) :
    B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced 3 B a J := by
  classical
  have hBel : IsElemAbelian 3 B := hSC.2.1
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  set JX : Subgroup X := M.map H.subtype with hJXdef
  have hJXH : JX ≤ H := Subgroup.map_subtype_le M
  have hmemJX : ∀ {x : X}, x ∈ JX → ∃ hx : x ∈ H, (⟨x, hx⟩ : ↥H) ∈ M := by
    rintro x ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  have hHJ : ∀ h ∈ H, ∀ x ∈ JX, h * x * h⁻¹ ∈ JX := by
    intro h hh x hx
    obtain ⟨hxH, hxM⟩ := hmemJX hx
    exact ⟨⟨h, hh⟩ * ⟨x, hxH⟩ * ⟨h, hh⟩⁻¹, hM.normal.conj_mem _ hxM _, rfl⟩
  have hcommX : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ JX := fun x hx y hy =>
    ⟨⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹, hM.comm _ _, rfl⟩
  have hfaithX : ∀ c ∈ H, (∀ x ∈ JX, c * x = x * c) → c = 1 := by
    intro c hc hcx
    have h1 := hM.faithful ⟨c, hc⟩ fun m hm => Subtype.ext (hcx m ⟨m, hm, rfl⟩)
    exact congrArg Subtype.val h1
  let eJ : ↥M ≃* ↥JX := Subgroup.equivMapOfInjective M H.subtype H.subtype_injective
  have hsJ : IsSimpleGroup ↥JX := (MulEquiv.isSimpleGroup_congr eJ).1 hM.simple
  have hZJ : Subgroup.center ↥JX = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine hfaithX _ (hJXH z.2) fun x hx => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, hx⟩).symm
  have hperf : ⁅JX, JX⁆ = JX := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥JX) with h | h
    · exfalso
      have hab : ∀ u v : ↥JX, u * v = v * u := fun u v => by
        have h1 : ⁅u, v⁆ ∈ commutator ↥JX :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)
        rw [h, Subgroup.mem_bot] at h1
        exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
      have htriv : ∀ u : ↥JX, u = 1 := fun u => by
        apply Subtype.ext
        exact hfaithX _ (hJXH u.2) fun x hx => congrArg Subtype.val (hab u ⟨x, hx⟩)
      obtain ⟨u, v, huv⟩ := hsJ.toNontrivial.exists_pair_ne
      exact huv ((htriv u).trans (htriv v).symm)
    · exact Subgroup.isPerfect_iff.1 ⟨h⟩
  obtain ⟨eM⟩ := hM.model
  have hcardJ : Nat.card ↥JX = 5515776 := by
    rw [← Nat.card_congr eJ.toEquiv, Nat.card_congr eM.toEquiv,
      CFSG.PGLModel.card_projSU_three_eight]
  have hJeq := eq_of_glaPComponent_of_comm hJXH hsJ hcommX hJ
  have hBJ : B ≤ Subgroup.normalizer (J : Set X) := by
    intro β hβ
    rw [mem_normalizer_iff_gLBConj_eq, eq_of_glaPComponent_of_comm hJXH hsJ hcommX (hconj β hβ),
      hJeq]
  subst hJeq
  have hZK := center_eq_bot_of_d4EightComp hK hLie
  obtain ⟨d₁, d₂, hd₁B, hd₁K, hd₂B, hd₂K, hd₁, hd₂⟩ :=
    exists_two_inner hZK hBel hBN hSC hF e haB hbB hA hBf
  have hout := not_inner_of_faithful hb hK hLie hb3 hF e hBf hHK hJXH hHJ (hBH b hbB) hfaithX
    (by rw [hcardJ]; exact not_ordU38_dvd_ordD)
  have hE := autImageRankThree_of_outer hBel hBJ hZJ hfaithX hbB hd₁B (hDH d₁ hd₁B hd₁K) hd₂B
    (hDH d₂ hd₂B hd₂K) hd₁ hd₂ hout
  have hmodel : Nonempty ((↥JX ⧸ Subgroup.center ↥JX) ≃* CFSG.PGLModel.projSU 3 2 3) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot).trans
      (eJ.symm.trans eM)⟩
  refine ⟨hBJ, KSF4Kit.isStronglyLocallyOneBalanced_of_centralizes fun S hS hcop hBS => ?_⟩
  exact KSF4SU3.centralizes_of_autImageRankThree hperf hmodel hE (hS.trans inf_le_left) hcop hBS

theorem pguBranch {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hLie : IsLieQuot ↥K OuterFourAux.IsD4EightIndex)
    (hSC : IsSCp 3 (K ⊔ B) B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) {a b : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (hb : b ∈ Subgroup.normalizer (K : Set X))
    (haB : a ∈ B) (hbB : b ∈ B)
    (hA : D4ElemType (MulAut.congr e (actHom K ⟨a, ha⟩)) fun ε σ => ε ≠ 0 ∧ σ = 1)
    (hBf : D4ElemType (MulAut.congr e (actHom K ⟨b, hb⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1)
    {M : Subgroup ↥(K ⊓ Subgroup.centralizer ({a} : Set X))}
    (hM : PGUThreeEightData ↥(K ⊓ Subgroup.centralizer ({a} : Set X)) M)
    {J : Subgroup X} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced 3 B a J := by
  have hBel : IsElemAbelian 3 B := hSC.2.1
  have hBH := le_normalizer_inf_centralizer hBel hBN haB
  refine pguBranch_aux hK hLie hSC hBN hF e ha hb haB hbB hA hBf inf_le_left
    (fun β hβ h hh => (Subgroup.mem_normalizer_iff.1 (hBH hβ) h).1 hh)
    (fun d hdB hdK => mem_inf_centralizer_of_mem hBel haB hdB hdK) hM hJ
    (fun β hβ => KSF4Kit.glaPComponent_gLBConj_centralizer (hBN hβ)
      (Bal209F4Aux.commute_of_elemAbelian hBel hβ haB).eq hJ)

end PGUKill

section PGUModel

open CFSG.RankThree.PartTwo

theorem pguModelData {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2) :
    PGUThreeEightData ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))
      ((CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)).subgroupOf
        (CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))) := by
  classical
  have hPi : Sec4.PiField false 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; rfl⟩
  have hq2 : 2 < 2 ^ 3 := by norm_num
  have hq : Sec4.ModThree false (2 ^ 3) := by show (2 ^ 3) % 3 = 2; norm_num
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K := hPi.unitary
  set P := CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K) with hP
  set S := CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K) with hS
  have hSP : S ≤ P := Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hU))
  have hcomm : commutator ↥P = S.subgroupOf P := Sec13.commutator_projImage_glPi hPi hq2
  haveI hperf : Group.IsPerfect ↥S := Sec13.isPerfect_projImage_slPi hPi hq2
  have hsS : IsSimpleGroup ↥S := Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hPi hq2
  have hmodel : Nonempty (↥S ≃* ↥(CFSG.PGLModel.projSU 3 2 3)) := by
    refine KSF4SU3.nonempty_equiv_projSU_of_model ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩,
      K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
    exact (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
      (Sec4.slPi false 3 (2 ^ 3) K)).symm
  exact {
    normal := by rw [← hcomm]; infer_instance
    comm := fun x y => by
      rw [← hcomm]
      have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rwa [commutatorElement_def] at h1
    faithful := fun x hx => by
      obtain ⟨w, hw, hxw⟩ := x.2
      have hscal : ∀ s ∈ Sec4.slPi false 3 (2 ^ 3) K,
          w * s * w⁻¹ * s⁻¹ ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K := by
        intro s hs
        rw [← Sec4.mk_eq_one_iff_mem_statedScalars]
        have hm : (⟨Matrix.ProjGenLinGroup.mk s, hSP ⟨s, hs, rfl⟩⟩ : ↥P) ∈ S.subgroupOf P :=
          Subgroup.mem_subgroupOf.2 ⟨s, hs, rfl⟩
        have h1 := congrArg Subtype.val (hx _ hm)
        simp only [Subgroup.coe_mul] at h1
        rw [← hxw] at h1
        simp only [map_mul, map_inv, MonoidHom.coe_coe]
        rw [h1]
        group
      have hw1 := Sec4.mem_statedScalars_of_comm_mod hPi hq hscal
      apply Subtype.ext
      rw [← hxw, Subgroup.coe_one]
      exact Sec4.mk_eq_one_iff_mem_statedScalars.2 hw1
    simple := (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe hSP)).2 hsS
    model := ⟨(Subgroup.subgroupOfEquivOfLe hSP).trans hmodel.some⟩ }

theorem pguData_of_isoPGUThree {C : Type} [Group C] (h : Sec8.IsoPGUThree C (2 ^ 3)) :
    ∃ M : Subgroup C, PGUThreeEightData C M := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨_, (pguModelData hK).map e.symm⟩

end PGUModel

section Classes

set_option linter.unusedSectionVars false


open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.KFacts
open CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)

theorem nonempty_fix_conj {G : Type} [Group G] (ψ β : MulAut G) :
    Nonempty (↥(fixedSubgroup β) ≃* ↥(fixedSubgroup (ψ * β * ψ⁻¹))) :=
  ⟨(Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr (D4FixedAux.fixed_map_conj ψ β))⟩

theorem fix_cases_sigma0 {K₃ : Type} [Field K₃] [Finite K₃] {Fr : K₃ ≃+* K₃}
    (hK₃ : Nat.card K₃ = (2 ^ 3) ^ 3) (hFr : ∀ c, Fr c = c ^ 2 ^ 3)
    (g : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)
    (hg3 : (MulAut.conj g * fieldActor (t := TwistTag.D4) Fr Fr) ^ 3 = 1) :
    (∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = 2 ^ 3 ∧
        Nonempty (↥(fixedSubgroup (MulAut.conj g * fieldActor (t := TwistTag.D4) Fr Fr)) ≃*
          ↥(adjointGroup Tag.G2 F'))) ∨
      IsoPGUThree ↥(fixedSubgroup (MulAut.conj g * fieldActor (t := TwistTag.D4) Fr Fr)) (2 ^ 3) := by
  obtain ⟨h, y, hy, hyy⟩ := exists_conj_eq_of_geom d4TrialityGeomClasses_holds
    d4DiagramCentIrred_holds d4SecondCentIrred_holds hK₃ hFr g hg3
  obtain ⟨E⟩ : Nonempty (↥(fixedSubgroup (MulAut.conj y * fieldActor (t := TwistTag.D4) Fr Fr)) ≃*
      ↥(fixedSubgroup (MulAut.conj g * fieldActor (t := TwistTag.D4) Fr Fr))) := by
    rw [hyy]
    exact nonempty_fix_conj _ _
  rcases hy with hy1 | hy0
  · left
    have hy1' : y = 1 := Subtype.ext hy1
    subst hy1'
    have hK3 : Nat.card K₃ = 2 ^ (3 * 3) := by rw [hK₃]; norm_num
    haveI : CharP K₃ 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hK3
    have hK2 : ringChar K₃ = 2 := ringChar.eq K₃ 2
    obtain ⟨eG⟩ := nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := Fr) hK2
    have hfix : fixedSubgroup (MulAut.conj (1 : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) *
        fieldActor (t := TwistTag.D4) Fr Fr) =
        (fieldActor (t := TwistTag.D4) Fr Fr).toMonoidHom.eqLocus (MonoidHom.id _) := by
      rw [map_one, one_mul]
      exact Subgroup.ext fun _ => Iff.rfl
    exact ⟨_, inferInstance, inferInstance, card_fixSubfield_of_cube (f := 3) (by norm_num) hK₃ hFr,
      ⟨E.symm.trans ((MulEquiv.subgroupCongr hfix).trans eG)⟩⟩
  · right
    have hy0' : y = d4TrialityY0Elt K₃ Fr := Subtype.ext hy0
    subst hy0'
    obtain ⟨K', hK'f, hK'fin, hK', ⟨eP⟩⟩ := kF82D4SecondCentY0_holds 3 (by decide) K₃ Fr hK₃ hFr
    exact ⟨K', hK'f, hK'fin, hK', ⟨E.symm.trans ((MulEquiv.subgroupCongr
      (Subgroup.ext fun _ => Iff.rfl)).trans eP)⟩⟩

theorem graphFix_cases {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    {α : MulAut ↥(adjointGroup Tag.D4 F)} (hα3 : α ^ 3 = 1)
    (hA : D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) :
    (∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = 2 ^ 3 ∧
        Nonempty (↥(fixedSubgroup α) ≃* ↥(adjointGroup Tag.G2 F'))) ∨
      IsoPGUThree ↥(fixedSubgroup α) (2 ^ 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, a, σ, ε, hε3, -, ⟨hε0, hσ1⟩, hαeq⟩ := hA
  subst hσ1
  have hε : ε = 1 ∨ ε = 2 := by omega
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e₁⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv
      (ℓ := 2) (f := 3) (by norm_num) F hF α hα3 g a hε hαeq
  have e₂ : ↥(fixedSubgroup α) ≃* ↥(fixedSubgroup φ) :=
    ((MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).trans e₁).trans
      (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl))
  have hφin : ¬ IsInnerAut φ := hφout
  obtain ⟨g', hg'⟩ : ∃ g' : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom,
      Nonempty (↥(fixedSubgroup φ) ≃*
        ↥(fixedSubgroup (MulAut.conj g' * fieldActor (t := TwistTag.D4) Fr Fr))) ∧
      (MulAut.conj g' * fieldActor (t := TwistTag.D4) Fr Fr) ^ 3 = 1 := by
    obtain ⟨g', hg' | hg'⟩ := Item8ModelProof.exists_conj_mul_sigma (n := 3) (by norm_num) hK₃ hFr
      hφ3 hφin
    · subst hg'
      exact ⟨g', ⟨MulEquiv.refl _⟩, hφ3⟩
    · have hinv : φ⁻¹ = MulAut.conj (fieldActor (t := TwistTag.D4) Fr Fr g'⁻¹) *
          fieldActor (t := TwistTag.D4) Fr Fr := by
        rw [hg', CFSG.HardMathSupport.Lang.E6Descent.inv_conj_mul_inv]
      refine ⟨fieldActor (t := TwistTag.D4) Fr Fr g'⁻¹, ⟨MulEquiv.subgroupCongr ?_⟩, ?_⟩
      · rw [← hinv]
        ext x
        change φ x = x ↔ φ⁻¹ x = x
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, eq_comm]
      · rw [← hinv, inv_pow, hφ3, inv_one]
  obtain ⟨⟨e₃⟩, h3⟩ := hg'
  rcases fix_cases_sigma0 hK₃ hFr g' h3 with ⟨F', hF'f, hF'fin, hF', ⟨eG⟩⟩ |
      ⟨K', hK'f, hK'fin, hK', ⟨eP⟩⟩
  · exact Or.inl ⟨F', hF'f, hF'fin, hF', ⟨(e₂.trans e₃).trans eG⟩⟩
  · exact Or.inr ⟨K', hK'f, hK'fin, hK', ⟨(e₂.trans e₃).trans eP⟩⟩

end Classes

section Main

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)

theorem d4EightGraphComp_holds : OuterFourSeitz.D4EightGraphComp := by
  intro X _ _ _ K B hK hLie hSC hBN F _ _ hF e a b ha hb haB hbB hA hBf J hJ
  have hBel : IsElemAbelian 3 B := hSC.2.1
  have hA3 : a ^ 3 = 1 := hBel.2 a haB
  have hα3 : MulAut.congr e (actHom K ⟨a, ha⟩) ^ 3 = 1 := by
    have h1 : (⟨a, ha⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hA3)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨Φ⟩ := nonempty_fixEquiv ha hK hLie e
  rcases graphFix_cases hF hα3 hA with ⟨F', _, _, hF', ⟨eG⟩⟩ | hP
  · exact g2Branch hK hLie hSC hBN hF e ha hb haB hbB hA hBf hF' (Φ.trans eG) hJ
  · obtain ⟨M, hM⟩ := pguData_of_isoPGUThree hP
    exact pguBranch hK hLie hSC hBN hF e ha hb haB hbB hA hBf (hM.map Φ.symm) hJ

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2
