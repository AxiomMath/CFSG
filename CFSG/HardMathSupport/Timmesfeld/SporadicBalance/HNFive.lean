module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ConjWitness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.RankThree.PartOne.SPOR.HNPlane
public import CFSG.RankThree.PartOne.HNB.NativeAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Criteria
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.WitnessCore
public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.RankThree.PartOne CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

theorem sporadicOuterHolds_HN_five :
    SporadicOuterHolds .HN 5 := fun _ _ _ _ ⟨e⟩ =>
  noOuterFixesCentralizer_of_conjWitness Nat.prime_five (by norm_num)
    (ConjWitness.of_mulEquiv e CFSG.RankThree.PartOne.SPOR.conjWitness_HN)

theorem gLAPPrimeCoreOf_eq_bot_of_isConj_pow {G : Type*} [Group G] [Finite G] {p : ℕ}
    {f x : G} {k : ℕ} (hx : orderOf x = orderOf f) (hk : IsConj x (f ^ k))
    (hf : CFSG.Open.GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set G)) = ⊥) :
    CFSG.Open.GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) = ⊥ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hk
  rw [← gLAPPrimeCoreOf_centralizer_conj c x, hc]
  have hko : orderOf (f ^ k) = orderOf f := by
    rw [← hx, ← hc]
    have h1 := (MulAut.conj c : G ≃* G).orderOf_eq x
    rw [MulAut.conj_apply] at h1
    exact h1
  have hz : Subgroup.zpowers (f ^ k) = Subgroup.zpowers f :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers _) k))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hko])
  have hmem : f ∈ Subgroup.zpowers (f ^ k) := by
    rw [hz]
    exact Subgroup.mem_zpowers f
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hcent : Subgroup.centralizer ({f ^ k} : Set G) = Subgroup.centralizer ({f} : Set G) := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      rw [← hm]
      exact ((Commute.zpow_left (show Commute (f ^ k) y from hy.symm) m)).eq.symm
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      exact ((Commute.pow_left (show Commute f y from hy.symm) k)).eq.symm
  rw [hcent]
  exact hf

theorem gLAPPrimeCoreOf_CJ_fJ :
    CFSG.Open.GLAPPrimeCoreOf 5 (Subgroup.centralizer ({fJ} : Set JH)) = ⊥ := by
  obtain ⟨hcomm, -, hsup, hord, -, hcard, -, hder, -⟩ := ctuc_hn_five_centralizer_perfect_factor
  have hs : IsSimpleGroup IJ :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity IJ 3 5 1
      CFSG.RankThree.PartOne.HNB.model_IJ).2
  exact gLAPPrimeCoreOf_eq_bot_of_zpowers_sup_simple Nat.prime_five hord hsup.symm
    (fun x hx => (hcomm fJ (Subgroup.mem_zpowers _) x hx).symm) hder hs
    (by rw [hcard]; norm_num)

@[expose] def HNFiveRest : Prop :=
  ∀ x : JH, orderOf x = 5 → (∀ k : ℕ, ¬ IsConj x (fJ ^ k)) →
    CFSG.Open.GLAPPrimeCoreOf 5 (Subgroup.centralizer ({x} : Set JH)) = ⊥

theorem sporadicOPrimeHolds_HN_five_of_rest
    (h : HNFiveRest) : SporadicOPrimeHolds .HN 5 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.HN := e
  have e' : S ≃* JH := e0.trans hnEquivJ
  refine @OPrimeCoreTrivialAt.of_mulEquiv 5 S _ ↥JH inferInstance e' ?_
  intro x hx
  by_cases hf : ∃ k : ℕ, IsConj x (fJ ^ k)
  · obtain ⟨k, hk⟩ := hf
    have hfo : orderOf fJ = 5 := (ctuc_hn_five_centralizer_perfect_factor).2.2.2.1
    exact gLAPPrimeCoreOf_eq_bot_of_isConj_pow (hx.trans hfo.symm) hk gLAPPrimeCoreOf_CJ_fJ
  · push Not at hf
    exact h x hx hf

@[expose] def HNFiveOrders : Prop :=
  ∀ x : JH, orderOf x = 5 → (∀ k : ℕ, ¬ IsConj x (fJ ^ k)) →
    Nat.card (Subgroup.centralizer ({x} : Set JH)) ∣ 2 ^ 14 * 3 * 5 ^ 6

set_option maxRecDepth 20000 in
theorem not_sq_five_dvd_card_CJ_three
    (w : JH) (hw : orderOf w = 3) :
    ¬ 5 ^ 2 ∣ Nat.card (Subgroup.centralizer ({w} : Set JH)) := by
  have h544 : Nat.card (Subgroup.centralizer ({CFSG.Sporadic.HNSchreier.sJ 0} : Set JH)) = 544320 :=
    CFSG.Sporadic.HNSchreier.card_CJ_s1
  have h29160 :
      Nat.card (Subgroup.centralizer ({CFSG.Sporadic.HNSchreier.sJ 2} : Set JH)) = 29160 :=
    CFSG.Sporadic.HNSchreier.card_CJ_s3
  rcases (CFSG.Sporadic.HNSchreier.order_three_classes w).1 hw with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc, card_centralizer_conj, h544]
    norm_num
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc, card_centralizer_conj, h29160]
    norm_num

theorem hnFiveRest_of_orders
    (h : HNFiveOrders) : HNFiveRest := by
  intro x hx hnot
  have hA : 5 ^ 2 ∣ Nat.card JH := by rw [card_JH]; norm_num
  exact gLAPPrimeCoreOf_eq_bot_of_conjWitness_card (a := 14) (b := 6) Nat.prime_five
    Nat.prime_three (by norm_num) (by norm_num) center_JH SPOR.conjWitness_JH hA hx
    (h x hx hnot) not_sq_five_dvd_card_CJ_three

theorem sporadicOPrimeHolds_HN_five_of_orders
    (h : HNFiveOrders) : SporadicOPrimeHolds .HN 5 :=
  sporadicOPrimeHolds_HN_five_of_rest (hnFiveRest_of_orders h)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
