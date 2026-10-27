module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicCoverReduce
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverWeakGen
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Suz
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi22
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi24prime
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Blueprint

theorem le_pRank_of_mulEquiv {S T : Type} [Group S] [Finite S] [Group T] {p k : ℕ} (hp : 1 < p)
    (e : T ≃* S) {E : Subgroup T} (hE : CFSG.Open.IsElemAbelian p E) (hc : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p (⊤ : Subgroup S) :=
  CFSG.SectionRank.le_pRank hp le_top (CFSG.SectionRank.isElemAbelian_map hE e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])

theorem sporadicThreeRankLe_of_carrier (s : TauCeti.SporadicName) (k : ℕ)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (h : ∀ [Finite (NativeSporadic.Carrier s)],
      CFSG.Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier s)) ≤ k) :
    SporadicThreeRankLe s k := by
  intro S _ _ ⟨e⟩
  obtain ⟨b⟩ := hbr
  let f : S ≃* NativeSporadic.Carrier s := e.trans b.symm
  have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv S f.toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) f]
  exact h

theorem sporadicThreeRankGe_of_carrier (s : TauCeti.SporadicName) (k : ℕ)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (hE : ∃ E : Subgroup (NativeSporadic.Carrier s), CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k) :
    SporadicThreeRankGe s k := by
  intro S _ _ ⟨e⟩
  obtain ⟨b⟩ := hbr
  obtain ⟨E, hE, hc⟩ := hE
  exact le_pRank_of_mulEquiv (by norm_num) (b.trans e.symm) hE hc

theorem card_nativeM22 : Nat.card NativeSporadic.M22 = 443520 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
    CFSG.Sporadic.Bridge.M22.le_card_native

theorem sporadicThreeRankLe_M22 : SporadicThreeRankLe .M22 2 :=
  sporadicThreeRankLe_of_carrier .M22 2 CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    (SporadicRank.pRank_le_of_not_dvd Nat.prime_three (by
      show ¬ 3 ^ 3 ∣ Nat.card NativeSporadic.M22
      rw [card_nativeM22]; norm_num))

theorem sporadicThreeRankLe_ONan :
    SporadicThreeRankLe .ONan 4 :=
  sporadicThreeRankLe_of_carrier .ONan 4 CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    (SporadicRank.pRank_le_of_not_dvd Nat.prime_three (by
      show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.ON
      rw [CFSG.Sporadic.ON.card_ON]; norm_num))

theorem sporadicThreeRankLe_J3 :
    SporadicThreeRankLe .J3 4 :=
  sporadicThreeRankLe_of_carrier .J3 4 CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv (by
    intro _
    show CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.J3) ≤ 4
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.RankThree.Asc83Table.J3.native_J3.1]
    norm_num)

theorem j3CoverRank_holds :
    J3CoverRank := by
  intro L _ _ hq he hZ3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  have hker : (QuotientGroup.mk' (Subgroup.center L)).ker = Subgroup.center L :=
    QuotientGroup.ker_mk' _
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 3
    (by rw [hZ3])
  have hzo : orderOf (z₀ : L) = 3 := (Subgroup.orderOf_coe z₀).trans hz₀
  obtain ⟨U, B, hUc, hU3, hUcard, hzU, hBU, ⟨t, htB, hto, htU⟩, -⟩ :=
    CFSG.AGLEmbedding.j3Cover_gen (QuotientGroup.mk' (Subgroup.center L))
      (QuotientGroup.mk'_surjective _) hker.le hperf he (hker.ge z₀.2) hzo
  have hcU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have htc : ∀ a ∈ U, t * a = a * t := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp (hBU htB) a ha).symm
  have ht3 : t ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [hto] at h1
  have hz1 : (z₀ : L) ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hzo; norm_num at hzo
  obtain ⟨u, huU, huz⟩ : ∃ u ∈ U, u ∉ Subgroup.zpowers (z₀ : L) := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (h : U ≤ Subgroup.zpowers (z₀ : L))
    rw [hUcard, Nat.card_zpowers, hzo] at h1
    omega
  exact CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens (p := 3) (hU3 _ hzU) (hU3 u huU) ht3
    (hcU _ hzU u huU) (htc _ hzU).symm (htc u huU).symm hz1
    (fun n hn => huz (hn ▸ Subgroup.npow_mem_zpowers _ n))
    (fun n m hnm => htU (hnm ▸ U.mul_mem (U.pow_mem hzU n) (U.pow_mem huU m)))

theorem sporadicThreeRankGe_McL :
    SporadicThreeRankGe .McL 4 :=
  sporadicThreeRankGe_of_carrier .McL 4 CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
    CFSG.SectionRank.McL_elementary_three_rank_four

theorem sporadicThreeRankGe_ONan :
    SporadicThreeRankGe .ONan 4 :=
  sporadicThreeRankGe_of_carrier .ONan 4 CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    CFSG.SectionRank.ON_elementary_three_rank_four

theorem sporadicThreeRankGe_Suz :
    SporadicThreeRankGe .Suz 4 :=
  sporadicThreeRankGe_of_carrier .Suz 4 CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
    CFSG.SectionRank.Suz_elementary_three_rank_four

theorem sporadicThreeRankGe_Fi22 :
    SporadicThreeRankGe .Fi22 4 :=
  sporadicThreeRankGe_of_carrier .Fi22 4 CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
    CFSG.SectionRank.Fi22_elementary_three_rank_four

theorem sporadicThreeRankGe_Fi24Prime :
    SporadicThreeRankGe .Fi24Prime 4 :=
  sporadicThreeRankGe_of_carrier .Fi24Prime 4 CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
    CFSG.SectionRank.Fi24prime_elementary_three_rank_four

end CFSG.HardMathSupport.Timmesfeld.Coordinator
