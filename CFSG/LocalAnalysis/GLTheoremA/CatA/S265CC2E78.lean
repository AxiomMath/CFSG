module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CC1
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TNA
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6Weyl
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLiftGood
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.HardMathSupport.Solomon.Proving.KZeroLe
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ClassicalGroups.Orthogonal.RootGroupPair
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6SixAux.Plane
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.Twelve
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4Three
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAbstract
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadEigen
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslSplit
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2ModelDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveQ2Fin
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3T
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisCore
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycFive
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycUnique
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFCenter
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFPerfect
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFRest
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoTheoremZ
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93All
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz9
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQResidueLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NFAxis
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Close
public import CFSG.RankThree.PartOne.TCX.LayerEngineG

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C.C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S265 CFSG.LocalAnalysis.GLTheoremA.S265C
open CFSG.StandardType

section Step1


variable {Ω : Type} [Group Ω] [Finite Ω]

theorem three_pow_seven_le_card {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K)
    (hS : catalogIs (PSimple 3 S) (fun i => isE7TwoIdx i ∨ isE8TwoIdx i)) :
    3 ^ 7 ≤ Nat.card B := by
  have hc := h.cfg
  have hx3 : x ^ 3 = 1 := hc.elem.2 x hc.xB
  have hxz : x ∈ Subgroup.center Ω := Subgroup.mem_center_iff.2 hc.xcen
  have hD : IsElemAbelian 3 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx3
  have hDC : Subgroup.zpowers x ≤ Subgroup.centralizer (S : Set Ω) :=
    (Subgroup.zpowers_le.2 hxz).trans (Subgroup.center_le_centralizer _)
  have hxD : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hc.x1]
  have key : ∀ r : ℕ, GGTorusLift 3 r (↥S ⧸ Subgroup.center ↥S) → 3 ^ (r + 1) ≤ Nat.card B := by
    intro r hlift
    have h1 := SF.pow_mul_card_le_of_torusLift (p := 3) (r := r) (K := S)
      (D := Subgroup.zpowers x) Nat.prime_three hc.quasi.1 (MulEquiv.refl _) hlift hD hDC
    rw [hxD, ← pow_succ] at h1
    exact h1.trans hc.rank
  obtain ⟨i, hi, ⟨eCat⟩⟩ := hS
  cases i with
  | lie d =>
    obtain ⟨idx, hv⟩ := d
    cases idx with
    | E7 q =>
      simp only [isE7TwoIdx, isE8TwoIdx, onLie, or_false, false_or] at hi
      obtain ⟨K, hKf, hKfin, hKcard, -, ⟨eAdj⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
      letI : Field K := hKf
      letI : Finite K := hKfin
      have hK2 : Nat.card K = 2 := hKcard.trans hi
      have hcharK : CharP K 2 :=
        CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by rw [hK2]; norm_num)
      have hlift : GGTorusLift 3 6 (↥S ⧸ Subgroup.center ↥S) :=
        TableBF4.ggTorusLift_of_mulEquiv
          ((S9.nonempty_pSimple_equiv (p := 3) hc.prime hc.comp hc.quasi).some.symm.trans
            (eCat.trans (eAdj.trans (TableBExc.recipeEquiv .E7 K).symm)))
          CFSG.StandardType.TableBExcTwo.ggTorusLift_E7Two
      exact key 6 hlift
    | E8 q =>
      simp only [isE7TwoIdx, isE8TwoIdx, onLie, or_false, false_or] at hi
      obtain ⟨K, hKf, hKfin, hKcard, -, ⟨eAdj⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
      letI : Field K := hKf
      letI : Finite K := hKfin
      have hK2 : Nat.card K = 2 := hKcard.trans hi
      have hcharK : CharP K 2 :=
        CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by rw [hK2]; norm_num)
      have hlift : GGTorusLift 3 7 (↥S ⧸ Subgroup.center ↥S) :=
        TableBF4.ggTorusLift_of_mulEquiv
          ((S9.nonempty_pSimple_equiv (p := 3) hc.prime hc.comp hc.quasi).some.symm.trans
            (eCat.trans (eAdj.trans (TableBExc.recipeEquiv .E8 K).symm)))
          CFSG.StandardType.TableBExcTwo.ggTorusLift_E8Two
      exact (Nat.pow_le_pow_right (by norm_num) (by norm_num : 7 ≤ 8)).trans (key 7 hlift)
    | _ => exact absurd hi (by simp [isE7TwoIdx, isE8TwoIdx, onLie])
  | _ => exact absurd hi (by simp [isE7TwoIdx, isE8TwoIdx, onLie])

theorem five_le_pRank_range {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K)
    (hS : catalogIs (PSimple 3 S) (fun i => isE7TwoIdx i ∨ isE8TwoIdx i))
    (h3K : 3 ∣ Nat.card ↥K) {d : TauCeti.ValidLieTypeIndex}
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    5 ≤ CFSG.Open.pRank 3 (KD264Lie.kd264Rho (h.nlAct h3K).norm eK).range := by
  have hc := h.cfg
  obtain ⟨-, -, hDcard, -, -, hKcomp, hDK⟩ := hc.std
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  set ρ : ↥B →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    KD264Lie.kd264Rho (h.nlAct h3K).norm eK with hρdef
  have hcard := KD264Lie.card_range_kd264Rho_mul (⟨hKq.1⟩ : Group.IsPerfect ↥K)
    (h.nlAct h3K).norm eK
  obtain ⟨e, he⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hc.elem
  have hcard9 : Nat.card ρ.range * 9 = 3 ^ e := by
    have h1 : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Ω)) = 9 := by
      rw [← hDK]
      exact hDcard
    rw [← he, ← hcard, h1]
  have he7 : 7 ≤ e := by
    have h1 := three_pow_seven_le_card h hS
    rw [he] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
  have h35 : 3 ^ 5 ≤ Nat.card ρ.range := by
    have h2 : 3 ^ 5 * 9 ≤ Nat.card ρ.range * 9 := by
      rw [hcard9]
      calc 3 ^ 5 * 9 = 3 ^ 7 := by norm_num
        _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he7
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  have hρab : IsElemAbelian 3 ρ.range := by
    have htop : IsElemAbelian 3 (⊤ : Subgroup ↥B) := by
      have h1 := CFSG.Open.IsElemAbelian.subgroupOf hc.elem B
      rwa [Subgroup.subgroupOf_self] at h1
    have h1 := CFSG.Open.IsElemAbelian.map htop ρ
    rwa [← MonoidHom.range_eq_map] at h1
  obtain ⟨n, hn⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hρab
  have hpr : CFSG.Open.pRank 3 ρ.range = n :=
    KD264Lie.X2E6.pRank_eq_of_card_eq Nat.prime_three hρab hn
  have h5n : 5 ≤ n := by
    rw [hn] at h35
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h35
  rw [hpr]
  exact h5n

end Step1

section Step3


theorem exists_good_of_rank_five {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (hd : d.1 = .twistedE6 q) (hq : q.card = 2)
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)}
    (hA : IsElemAbelian 3 A) (h5 : 5 ≤ CFSG.Open.pRank 3 A) :
    ∃ F ≤ A, IsElemAbelian 3 F ∧ CFSG.Open.pRank 3 F = 2 ∧ KD264Lie.IsGood 3 F := by
  have hns : ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group := by
    intro hchev
    refine CFSG.LocalAnalysis.GLTheoremA.S265C.C1.not_lvData_three_of_f4_te6
      (Or.inr ⟨.lie d, ?_, ⟨MulEquiv.refl _⟩⟩) (Or.inl hchev)
    simpa [S9.isTE6two, onLie, hd] using hq
  have h2 : ¬ k2Lie 3 d.1 := by
    rw [hd]
    simp [k2Lie]
  have h3 : ¬ k3Lie d.1 := by
    rw [hd]
    simp [k3Lie]
  have hrow : KD264Lie.KD264X2E6Row :=
    KD264Lie.X2E6.kd264X2E6Row_of_localP
      (KD264Lie.X2E6.x2e6LocalP_of_torusGoodP _ KD264Lie.X2E6.T.x2e6TorusGood9_holds)
      KD264Lie.X2E6.x2e6WeylCore_of_certificate
  exact hrow d q hns h2 h3 hd hq A hA h5

end Step3

section Step4


variable {Ω : Type} [Group Ω] [Finite Ω]

theorem false_of_te6_data {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K)
    (hK : catalogIs (PSimple 3 K) S9.isTE6two)
    (hS : catalogIs (PSimple 3 S) (fun i => isE7TwoIdx i ∨ isE8TwoIdx i))
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hd : d.1 = .twistedE6 q) (hq : q.card = 2)
    (eCatK : PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  have hc := h.cfg
  obtain ⟨-, -, hDcard, -, -, hKcomp, hDK⟩ := hc.std
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have h3K : 3 ∣ Nat.card ↥K := by
    have h1 := card_pSimple_dvd 3 K
    rw [card_of_isTE6two hK] at h1
    exact (by norm_num : 3 ∣ 76532479683774853939200).trans h1
  have hact := h.nlAct h3K
  have hBN : B ≤ Subgroup.normalizer (K : Set Ω) := hact.norm
  have eK : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group :=
    (S9.nonempty_pSimple_equiv (p := 3) hc.prime hact.comp hKq).some.symm.trans eCatK
  set ρ : ↥B →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    KD264Lie.kd264Rho hBN eK with hρdef
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ eK.toEquiv
  have h5 : 5 ≤ CFSG.Open.pRank 3 ρ.range := five_le_pRank_range h hS h3K eK
  have hρab : IsElemAbelian 3 ρ.range := by
    have htop : IsElemAbelian 3 (⊤ : Subgroup ↥B) := by
      have h1 := CFSG.Open.IsElemAbelian.subgroupOf hc.elem B
      rwa [Subgroup.subgroupOf_self] at h1
    have h1 := CFSG.Open.IsElemAbelian.map htop ρ
    rwa [← MonoidHom.range_eq_map] at h1
  obtain ⟨F, hFA, hFel, hFpr, hFgood⟩ := exists_good_of_rank_five hd hq (A := ρ.range) hρab h5
  have hFcard : Nat.card ↥F = 9 := by
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hFel
    have hk2 : CFSG.Open.pRank 3 F = k :=
      KD264Lie.X2E6.pRank_eq_of_card_eq Nat.prime_three hFel hk
    rw [hk, ← hk2, hFpr]
    norm_num
  have hFne : F ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hFcard
    omega
  obtain ⟨e, heF, heD⟩ : ∃ e ∈ (F.comap ρ).map B.subtype, e ∉ D := by
    by_contra hcon
    push Not at hcon
    refine hFne (le_bot_iff.1 ?_)
    intro f hf
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 (hFA hf)
    have hbF : b ∈ F.comap ρ := by
      rw [Subgroup.mem_comap, hb]
      exact hf
    have hmem : ((b : ↥B) : Ω) ∈ (F.comap ρ).map B.subtype :=
      Subgroup.mem_map.2 ⟨b, hbF, rfl⟩
    have hmemD : ((b : ↥B) : Ω) ∈ D := hcon _ hmem
    have hbker : b ∈ ρ.ker := by
      rw [KD264Lie.ker_kd264Rho (⟨hKq.1⟩ : Group.IsPerfect ↥K) hBN eK]
      exact Subgroup.mem_subgroupOf.2 ⟨b.2, (hDK.le hmemD).2⟩
    have hb1 : ρ b = 1 := MonoidHom.mem_ker.1 hbker
    rw [← hb, hb1]
    exact Subgroup.one_mem ⊥
  have hFB : (F.comap ρ).map B.subtype ≤ B := Subgroup.map_subtype_le _
  have hFel' : IsElemAbelian 3 ((F.comap ρ).map B.subtype) := hc.elem.mono hFB
  have hFp : IsPGroup 3 ↥((F.comap ρ).map B.subtype) := isPGroup_of_isElemAbelian hFel'
  have hFN : (F.comap ρ).map B.subtype ≤ Subgroup.normalizer (K : Set Ω) := hFB.trans hBN
  have hFe : (F.comap ρ).map B.subtype ≤ Subgroup.centralizer ({e} : Set Ω) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (isElemAbelian_commute hFel' hf heF).symm
  have hlayer : GLAPLayer 3 (K ⊓ Subgroup.centralizer
      (((F.comap ρ).map B.subtype : Subgroup Ω) : Set Ω)) ≠ ⊥ :=
    KD264Lie.kd264LiftGood_holds (p := 3) Nat.prime_three (Y := Ω) (K := K) (B := B) hBN
      (S := (TauCeti.CFSGIndex.lie d).Group) eK F hFA hFgood
  have hle := CFSG.HardMathSupport.Solomon.Proving.kZeroOf_le_layer_inf_centralizer
    (CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog)
    (HDesc.isKGroup_of_le hc.kgroup ((K ⊓ Subgroup.centralizer ({e} : Set Ω)) ⊔
      ((F.comap ρ).map B.subtype)))
    hFp heF hFN hFe
  have hbot : GLAPLayer 3 (K ⊓ Subgroup.centralizer ({e} : Set Ω)) = ⊥ :=
    h.nl e (hFB heF) heD
  rw [hbot] at hle
  exact hlayer (le_bot_iff.1 hle)

theorem false_of_qsnl_te6_e78 {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K)
    (hK : catalogIs (PSimple 3 K) S9.isTE6two)
    (hS : catalogIs (PSimple 3 S) (fun i => isE7TwoIdx i ∨ isE8TwoIdx i)) : False := by
  have hKc : catalogIs (PSimple 3 K) S9.isTE6two := hK
  obtain ⟨i, hi, ⟨eCatK⟩⟩ := hK
  cases i with
  | lie d =>
    obtain ⟨idx, hv⟩ := d
    cases idx with
    | twistedE6 q =>
      simp only [S9.isTE6two, onLie, or_false, false_or] at hi
      exact false_of_te6_data h hKc hS rfl hi eCatK
    | _ => exact absurd hi (by simp [S9.isTE6two, onLie])
  | _ => exact absurd hi (by simp [S9.isTE6two, onLie])

end Step4

section Final


theorem qSFamCTE6C2_holds : CFSG.LocalAnalysis.GLTheoremA.S265C.C1.QSFamCTE6C2 := by
  intro Ω _ _ S B T x D K h hK hS _
  exact (false_of_qsnl_te6_e78 h hK hS).elim

theorem qSFamCTE6_holds : CFSG.LocalAnalysis.GLTheoremA.S265C.QSFamCTE6 := by
  intro Ω _ _ S B T x D K h hK hS
  exact (false_of_qsnl_te6_e78 h hK hS).elim

end Final

end CFSG.LocalAnalysis.GLTheoremA.S265C.C2

end
