module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1419b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs255r
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1314
public import CFSG.HardMathSupport.Dickson.BMRows.M13L33
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables3b
public import Certificates.Certificate10136
public import Certificates.Certificate17632Base
public import Certificates.Certificate17700
public import Certificates.Certificate17701

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporK

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Yardstones.Md0ec50421ce4 (PSimple PQuot IsChevSimple)

section Inputs1415K

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415 (SporNoAltDown)

@[expose] def Input14_15K : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K],
    CFSG.LocalAnalysis.GLTheoremA.IsKHat K → CFSG.Open.IsKGroup K → GLAPPrimeCore p K = ⊥ →
    (∃ x : MulAut K, Lemma1314.PumpupVia p ↥(alternatingGroup (Fin (p + 2))) K x) →
      (∃ k : ℕ, 2 ≤ k ∧ IsAltType (k * p + 2) K) ∨ (p = 5 ∧ IsSporType .Fi23 K)

theorem input14_15_of_sporK (hnl : Prop1116Design.InputAltNotLie)
    (hD : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ r, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p r)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hFi23 : ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
      IsSporType .Fi23 (Y ⧸ Subgroup.center Y) → GLAPPrimeCore 5 Y = ⊥ → Subgroup.center Y = ⊥)
    (hS : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ name : TauCeti.SporadicName, ¬ (p = 5 ∧ name = .Fi23) →
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group → SporNoAltDown p (p + 2) name) :
    Input14_15K := by
  intro p hp hp5 K _ _ hKH hKK hO hpump
  obtain ⟨x, hx, J₁, hJ₁, ⟨e⟩⟩ := hpump
  rw [Inputs1415.lemma1314_fixSub_eq] at hJ₁
  have hp2 : p ≠ 2 := by omega
  have hJt : Nonempty (PSimple p J₁ ≃* alternatingGroup (Fin (p + 2))) :=
    Inputs1415.nonempty_center_quot_of_alt (by omega) e
  have hp8 : p + 2 ≠ 8 := fun h => by
    have h6 : p = 6 := by omega
    rw [h6] at hp
    norm_num at hp
  rcases Inputs1415.pumpup_alt_classify hnl (hD p hp hp5) hOut hp hp2 (by omega) hp8 hKH.1 hKH.2 hO hx
    hJ₁ hJt with ⟨k, hk, ⟨f⟩⟩ | ⟨name, ⟨g⟩, hns⟩
  · have hk8 : 8 ≤ p + 2 + k * p := by nlinarith
    obtain ⟨f'⟩ := Inputs1415.alt_of_center_odd hKH.1 hk8 f (Inputs1415.odd_card_center hp hp2 hO)
    have heq : p + 2 + k * p = (k + 1) * p + 2 := by ring
    rw [heq] at f'
    exact Or.inl ⟨k + 1, by omega, ⟨f'⟩⟩
  · by_cases h5 : p = 5 ∧ name = .Fi23
    · obtain ⟨rfl, rfl⟩ := h5
      have hZ := hFi23 K hKH.1 ⟨g⟩ hO
      exact Or.inr ⟨rfl, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
        QuotientGroup.quotientBot).symm.trans g⟩⟩
    · exact (hns (hS p hp hp5 name h5 ((hKK.quotient _).of_surjective g.toMonoidHom g.surjective))).elim

structure Open1314K : Prop where
  fi22_5 : SporNoAltDown 5 7 .Fi22
  fi24_5 : SporNoAltDown 5 7 .Fi24Prime
  b_5 : SporNoAltDown 5 7 .B
  m_5 : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group → SporNoAltDown 5 7 .M
  m_11 : SporNoAltDown 11 13 .M

end Inputs1415K

section Inputs1419K

open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1419b (SporNoOmegaDown)

@[expose] def Input14_19_3K : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (ε : Bool) (n : ℕ), 1 ≤ n →
    ∀ (J : Type) [Group J] (K : Type) [Group K] [Finite K],
      CFSG.LocalAnalysis.GLTheoremA.IsKHat K → CFSG.Open.IsKGroup K → GLAPPrimeCore p K = ⊥ →
      IsOmegaTwo ε (n + 1) J → HasFixedPointFreeOrder ε n p →
      ∀ x : MulAut K, Lemma1314.PumpupVia p J K x →
        IsLieChar (· = 2) K ∨ (p = 5 ∧ IsLieChar (· = 3) K)

@[expose] def InputSporOmegaDownK : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (ε : Bool) (n : ℕ), 1 ≤ n → HasFixedPointFreeOrder ε n p →
    ∀ (J : Type) [Group J] (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      GLAPPrimeCore p K = ⊥ → ∀ s : TauCeti.SporadicName,
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group →
      IsOmegaTwo ε (n + 1) J → ∀ x : MulAut K, ¬ Lemma1314.PumpupVia p J K x

@[expose] def SporOmegaTableK : Prop :=
  ∀ (name : TauCeti.SporadicName) (ε : Bool) (n p : ℕ), (name, ε, n, p) ∈ Inputs1419b.sporOmegaCases →
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group → SporNoOmegaDown p ε n name

@[expose] def SporOmegaTableOpenK : Prop :=
  ∀ (name : TauCeti.SporadicName) (ε : Bool) (n p : ℕ), (name, ε, n, p) ∈ Inputs1419b.sporOmegaCasesOpen →
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group → SporNoOmegaDown p ε n name

open Inputs1419b in
theorem inputSporOmegaDown_of_tableK (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (hFi : SporNoOmegaDown 5 false 2 .Fi22) (hT : SporOmegaTableK) :
    InputSporOmegaDownK := by
  intro p hp hp5 ε n hn hF J _ K _ _ hK hO name hS hKs hJ x hx
  obtain ⟨f⟩ := hS
  obtain ⟨hxo, J1, hJ1, ⟨eJ⟩⟩ := hx
  have hn2 := Inputs1419.two_le_of_fpf hp hp5 hn hF
  haveI : Finite J := Finite.of_equiv _ eJ.toEquiv
  have hJ1' : GLAPComponent p (fixSubgroup x) J1 := by
    rw [show fixSubgroup x = Lemma1314.fixSub x from Subgroup.ext fun _ => Iff.rfl]
    exact hJ1
  obtain ⟨s, hs, I, hI, ⟨eI⟩⟩ := exists_spor_comp hOut hp (by omega) hK f hxo hJ1'
  have hZJ : Subgroup.center J = ⊥ := Inputs1419.center_eq_bot_of_isOmegaTwo hn2 hJ
  have e1 : PSimple p J1 ≃* J :=
    (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).trans
      (Inputs1419.quotCenterEquivOfBot hZJ)
  have hIΩ : IsOmegaTwo ε (n + 1) (PSimple p I) :=
    CFSG.LocalAnalysis.GLTheoremB.Prop95I1920.isOmegaTwo_of_mulEquiv (e1.symm.trans eI) ε (n + 1) hJ
  have hcard : Nat.card (PSimple p I) = OmegaFacts.omegaOrd ε (n + 1) :=
    OmegaFacts2.card_eq_omegaOrd hp (by omega) hn hF hIΩ
  have hdvd : p * OmegaFacts.omegaOrd ε (n + 1) ∣ sporOrd name := by
    rw [← hcard, ← hOrd name, ← Nat.card_congr f.toEquiv]
    exact (mul_card_pSimple_dvd hp hs hI).trans (Subgroup.card_subgroup_dvd_card _)
  have hdT :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.dvd_typeSign_of_hasFixedPointFreeOrder hp
      (by omega) hn hF
  rcases spor_omega_cases hp hp5 hn hdT name hdvd with hmem | ⟨rfl, rfl, rfl, rfl⟩
  · exact hT name ε n p hmem hKs _ ⟨f⟩ s hs I hI hIΩ
  · exact hFi _ ⟨f⟩ s hs I hI hIΩ

end Inputs1419K

section Inputs255K

@[expose] def Input25_5RowsK : Prop :=
  (CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group → Inputs256.SporNoChevTwoDown 5 .B) ∧
    (CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group → Inputs256.SporNoChevTwoDown 5 .M) ∧
    Inputs256.SporNoChevTwoDown 7 .M

end Inputs255K

section Lemma1314K

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut barAut_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

theorem isKGroup_barOf_of_le_cg {G : Type} [Group G] [Finite G] {m p : ℕ} (hS : GLStanding G m p) {d : G}
    (hd : d ≠ 1) {L : Subgroup G} (hL : L ≤ Cg d) : CFSG.Open.IsKGroup (barOf p L) :=
  ((Prop1310a5b.isKGroup_centralizer_of_standing hS hd).of_le hL).quotient _

theorem input23_10_cube_of (h : Lemma1314.Input23_10) :
    ∀ (p q : ℕ), p.Prime → 5 ≤ p → q.Prime → q ≠ p →
      ∀ (Y : Type) [Group Y] [Finite Y], GLAPPrimeCore p Y = ⊥ →
        ∀ (K B : Subgroup Y), IsComponentOf K ⊤ → IsElemAbelian p B → Nat.card B ≤ p ^ 3 →
          IsLieChar (· = q) ↥K → (p = 5 → ¬ Lemma1314.I2310Exc5 K) → Lemma1314.IsGMinusOne p B K := by
  intro p q hp hp5 hq hqp Y _ _ hcore K B hK hB hcard hlie hexc
  exact h p q hp hp5 hq hqp Y hcore K B hK hB hcard hlie hexc

open Lemma1314 in
theorem lemma1314_iv_of_inputsK {G : Type} [Group G] [Finite G] {m p : ℕ}
    {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    (hL1312 : Lemma1312Statement) (hL1313 : Lemma1313Statement) (hP111 : Prop111Statement)
    (hL101ii : Lemma101_iiStatement) (hL104ii : Lemma104_iiStatement)
    (hL104iii : Lemma104_iiiStatement)
    (hI1415 : Input14_15K) (hI1419 : Input14_19_3K) (hI2310 : Lemma1314.Input23_10)
    (hI2324 : Lemma1314.Input23_24Fi23)
    (hPump : Lemma1314.PumpupBlock) (hKHat : Lemma1314.KHatBlock) (hExc : Lemma1314.ExcBlock)
    (hConn : Lemma1314.ConnBlock) :
    CFSG.Open.pRank p A = 3 := by
  have hp : p.Prime := h.standing.beta.1
  have hI2310c := input23_10_cube_of hI2310
  have h139a' := h139a
  obtain ⟨hp3lt, hIst, LI, hLIc, -, -, htypeI⟩ := h139a
  have hp5ge : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    norm_num at hp
  obtain ⟨U, hU, -⟩ := hL1312 h
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU.2.2.2
  have hb1' : b ≠ 1 := fun e => hb1 (Subtype.ext e)
  obtain ⟨-, ⟨hLc, -, hisoL⟩, hLM, hLpi⟩ := hL1313 h hU hb hb1'
  have hEA : IsDDpStar p M E A := h.pair
  have hinDD : inDDp p M E A := hEA.1
  have hD_E : inD p M E := hinDD.1
  have hDp_A : inDp p M A := hinDD.2.1
  have hk2 : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := hinDD.2.2
  have hAel : IsElemAbelian p A := hDp_A.1.1.2.1
  have hdD : d ∈ D ∧ d ≠ 1 := h.hd
  have hdA : d ∈ A := h.hD.1 hdD.1
  have hd1 : d ≠ 1 := hdD.2
  have hAC : A ≤ Subgroup.centralizer ({d} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    have hc : d * a = a * d := congrArg Subtype.val (hAel.1.is_comm.comm ⟨d, hdA⟩ ⟨a, ha⟩)
    exact hc
  have hFel : IsElemAbelian p (E ⊓ A) := isElemAbelian_of_le' hAel inf_le_right
  have hFp : IsPGroup p ↥(E ⊓ A) := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hFel.2 g.1 g.2)⟩
  have hFC : E ⊓ A ≤ Subgroup.centralizer ({d} : Set G) := inf_le_right.trans hAC
  have hFbar : IsElemAbelian p (barX p (Subgroup.centralizer ({d} : Set G)) (E ⊓ A)) :=
    isElemAbelian_barX (C := Subgroup.centralizer ({d} : Set G)) hFel
  have hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) ≤ M :=
    hP111 h.toSec13.toSec11 hdA hd1
  have hnorm : ∀ E' : Subgroup G, E' ≤ E ⊓ A → 2 ≤ CFSG.Open.pRank p E' →
      Subgroup.normalizer (E' : Set G) ≤ M := by
    intro E' hE' hr
    refine le_trans ?_ hD_E.2.clause_d
    unfold GLBCore
    exact le_sSup ⟨E', hE'.trans inf_le_left, hr, rfl⟩
  have hFle : CFSG.Open.pRank p (E ⊓ A) ≤ 2 := by
    by_contra hcon
    have hk3 : 3 ≤ CFSG.Open.pRank p (E ⊓ A) := by omega
    obtain ⟨x, hx⟩ := hPump h hU hb hb1'
    have hKH := hKHat h hU hb hb1'
    have hKK : CFSG.Open.IsKGroup (barOf p (LOf p L0 d b)) := isKGroup_barOf_of_le_cg h.standing hd1 hLc.1
    have hGp : GLAPPrimeCore p (barOf p (LOf p L0 d b)) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
    have hYp : GLAPPrimeCore p (↥(Subgroup.centralizer ({d} : Set G)) ⧸
        GLAPPrimeCore p ↥(Subgroup.centralizer ({d} : Set G))) = ⊥ :=
      glaPPrimeCore_quotient_eq_bot hp
    have hcomp := isComponentOf_barX_of_glaPComponent hLc
    haveI : Fact p.Prime := ⟨hp⟩
    have hdvd3 : p ^ 3 ∣ Nat.card ↥(E ⊓ A) := by
      rw [GL83.PiGen.card_eq_pow_pRank hFel]
      exact pow_dvd_pow p hk3
    obtain ⟨K₃, hK₃⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd3
    set F₃ : Subgroup G := K₃.map (E ⊓ A).subtype with hF₃def
    have hF₃F : F₃ ≤ E ⊓ A := Subgroup.map_subtype_le K₃
    have hF₃el : IsElemAbelian p F₃ := isElemAbelian_of_le' hFel hF₃F
    have hF₃card : Nat.card F₃ = p ^ 3 := by
      rw [hF₃def, Subgroup.card_map_of_injective (E ⊓ A).subtype_injective, hK₃]
    have hk₃ : 3 ≤ CFSG.Open.pRank p F₃ := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hF₃el hF₃card
    have hF₃C : F₃ ≤ Subgroup.centralizer ({d} : Set G) := hF₃F.trans hFC
    have hF₃p : IsPGroup p ↥F₃ := fun g =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hF₃el.2 g.1 g.2)⟩
    have hF₃bar : IsElemAbelian p (barX p (Subgroup.centralizer ({d} : Set G)) F₃) :=
      isElemAbelian_barX (C := Subgroup.centralizer ({d} : Set G)) hF₃el
    have hF₃barc : Nat.card (barX p (Subgroup.centralizer ({d} : Set G)) F₃) ≤ p ^ 3 := by
      rw [Claims1116.card_barX_of_isPGroup hp hF₃p hF₃C, hF₃card]
    have hnorm₃ : ∀ E' : Subgroup G, E' ≤ F₃ → 2 ≤ CFSG.Open.pRank p E' →
        Subgroup.normalizer (E' : Set G) ≤ M := fun E' hE' hr => hnorm E' (hE'.trans hF₃F) hr
    obtain ⟨eI⟩ := hisoL LI (by rw [← hIst]; exact hLIc)
    rcases type_of_iso eI htypeI with hTalt | ⟨ε, n, hn1, hO, hFPF⟩
    · obtain ⟨eA⟩ : Nonempty (barOf p (L0bOf p L0 b) ≃* alternatingGroup (Fin (p + 2))) := hTalt
      have hx' : Lemma1314.PumpupVia p ↥(alternatingGroup (Fin (p + 2))) (barOf p (LOf p L0 d b)) x :=
        pumpupVia_of_equiv eA hx
      rcases hI1415 p hp hp5ge (barOf p (LOf p L0 d b)) hKH hKK hGp ⟨x, hx'⟩ with
        ⟨k, hk2', hkA⟩ | ⟨hp5, hFi⟩
      · exact hLpi (le_piOf_of_alt hp (by omega) hLc (by omega) hkA)
      · have hsp : IsSporType .Fi23
            ↥(barX p (Subgroup.centralizer ({d} : Set G)) (LOf p L0 d b)) :=
          isSporType_of_equiv (quotEquivBarX hp hLc.1 hLc.2.1).symm _ hFi
        subst hp5
        have hG := hI2324 _ hYp _ _ hcomp hFbar hsp
        exact hLM (le_of_gMinusOne hp hLc.1 hFC hFp hnorm hcore hG hk3)
    · have hΩ : ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (barOf p (L0bOf p L0 b)) ∧
          HasFixedPointFreeOrder ε n p := ⟨ε, n, hn1, hO, hFPF⟩
      rcases hI1419 p hp hp5ge ε n hn1 (barOf p (L0bOf p L0 b))
          (barOf p (LOf p L0 d b)) hKH hKK hGp hO hFPF x hx with hC2 | ⟨hp5, hC3⟩
      · have hG := hI2310c p 2 hp hp5ge Nat.prime_two (by omega) _ hYp _ _ hcomp
          hF₃bar hF₃barc (isLieChar_of_equiv (quotEquivBarX hp hLc.1 hLc.2.1).symm _ hC2)
          (fun hp5 => hExc h h139a' hU hb hb1' hp5 hΩ (Or.inl hC2))
        exact hLM (le_of_gMinusOne hp hLc.1 hF₃C hF₃p hnorm₃ hcore hG hk₃)
      · have hG := hI2310c p 3 hp hp5ge Nat.prime_three (by omega) _ hYp _ _
          hcomp hF₃bar hF₃barc (isLieChar_of_equiv (quotEquivBarX hp hLc.1 hLc.2.1).symm _ hC3)
          (fun _ => hExc h h139a' hU hb hb1' hp5 hΩ (Or.inr hC3))
        exact hLM (le_of_gMinusOne hp hLc.1 hF₃C hF₃p hnorm₃ hcore hG hk₃)
  have hFeq : CFSG.Open.pRank p (E ⊓ A) = 2 := le_antisymm hFle hk2
  by_contra hA
  have hA4 : 4 ≤ CFSG.Open.pRank p A := by
    have hA3 : 3 ≤ CFSG.Open.pRank p A := hDp_A.1.2
    omega
  have hconnA : IsKConnectedIn p 3 ⊤ A B := hConn h h139a' hA4
  have hscpA : IsSCp p ⊤ A := (hL104ii h.toSec13.toSec11.toSec10Fails hEA).2
  have hB : inD p M B := hL101ii h.toSec13.toSec11.toSec10Fails
  have hconn' : IsKConnectedIn p (CFSG.Open.pRank p (E ⊓ A) + 1) ⊤ A B := by
    rw [hFeq]
    exact hconnA
  have hAD : inD p M A := hL104iii h.toSec13.toSec11.toSec10Fails hEA hscpA hB hconn'
  exact hDp_A.2 hAD.2

section IIICoreK

variable {G : Type} [Group G] [Finite G]

open Lemma1314c in
theorem iii_coreK {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    (hL1313 : Lemma1313Statement) (hP111 : Prop111Statement) (hP112 : Prop112Statement)
    (hP1116 : Prop1116Statement)
    (hI1415 : Input14_15K) (hI1419 : Input14_19_3K)
    (hPump : Lemma1314.PumpupBlock) (hKHat : Lemma1314.KHatBlock) (hExc : Lemma1314.ExcBlock)
    (hFiLoc : Input23_24Fi23Loc) (hFiFaith : FiFaithBlock) (hChev3 : Chev3Block)
    (hChevGen : ChevGenBlock) (hChevOpM : ChevOpMBlock)
    (hL133 : Lemma133Statement) (hcomp : Sec13g.Lemma133_compStatement)
    (hi : R = (R ⊓ Iof p M D) ⊔ centBar p R (Iof p M D) ∧
      (R ⊓ Iof p M D) ⊓ centBar p R (Iof p M D) = ⊥ ∧ CFSG.Open.pRank p (R ⊓ Iof p M D) = 1)
    (hii : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1) (hA3 : CFSG.Open.pRank p A = 3)
    {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) (hUR : U ≤ centerOf R) :
    ∃ z ∈ U, z ≠ 1 ∧ ∃ H0 : Subgroup G, GLAPComponent p (Cg2 d z) H0 ∧ ¬ H0 ≤ M ∧
      (Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0))) := by
  have hp : p.Prime := h.standing.beta.1
  have h139a' := h139a
  obtain ⟨hp3lt, hIst, LI, hLIc, -, -, htypeI⟩ := h139a
  have hp5ge : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    norm_num at hp
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU.2.2.2
  have hb1' : b ≠ 1 := fun e => hb1 (Subtype.ext e)
  obtain ⟨-, ⟨hLc, -, hisoL⟩, hLM, hLpi⟩ := hL1313 h hU hb hb1'
  have hdD : d ∈ D ∧ d ≠ 1 := h.hd
  have hdA : d ∈ A := h.hD.1 hdD.1
  have hd1 : d ≠ 1 := hdD.2
  have hcore : GLAPPrimeCoreOf p (Cg d) ≤ M := hP111 h.toSec13.toSec11 hdA hd1
  have hLC : Lemma1314.LOf p L0 d b ≤ Cg d := hLc.1
  have hKH := hKHat h hU hb hb1'
  have hKK : CFSG.Open.IsKGroup (barOf p (Lemma1314.LOf p L0 d b)) := isKGroup_barOf_of_le_cg h.standing hd1 hLC
  have hGp : GLAPPrimeCore p (barOf p (Lemma1314.LOf p L0 d b)) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot hp
  obtain ⟨x, hx⟩ := hPump h hU hb hb1'
  obtain ⟨eI⟩ := hisoL LI (by rw [← hIst]; exact hLIc)
  rcases Lemma1314.type_of_iso eI htypeI with hTalt | ⟨ε, n, hn1, hO, hFPF⟩
  ·
    obtain ⟨eA⟩ : Nonempty (barOf p (Lemma1314.L0bOf p L0 b) ≃* alternatingGroup (Fin (p + 2))) :=
      hTalt
    have hx' : Lemma1314.PumpupVia p ↥(alternatingGroup (Fin (p + 2)))
        (barOf p (Lemma1314.LOf p L0 d b)) x := Lemma1314.pumpupVia_of_equiv eA hx
    rcases hI1415 p hp hp5ge (barOf p (Lemma1314.LOf p L0 d b)) hKH hKK hGp ⟨x, hx'⟩ with
      ⟨k, hk2', hkA⟩ | ⟨hp5, hFi⟩
    · exact (hLpi (Lemma1314.le_piOf_of_alt hp (by omega) hLc (by omega) hkA)).elim
    · subst hp5
      have hN := U_le_normalizer_LOf h h139a' hL133 hcomp hU hb hb1'
      have hF := hFiFaith h h139a' hU hUR hb hb1' rfl hFi
      obtain ⟨hgen, hty⟩ := hFiLoc G (Cg d) (Lemma1314.LOf 5 L0 d b) U hLc hFi hU.2.1 hU.1.2.1
        hU.1.2.2 hN hF
      by_contra hcon
      have hXM : (⨆ z ∈ U, ⨆ (_ : z ≠ 1), ⨆ (H : Subgroup G)
          (_ : GLAPComponent 5 (Cg d ⊓ Cg z) H ∧ H ≤ Lemma1314.LOf 5 L0 d b), H) ≤ M := by
        refine iSup₂_le fun z hz => iSup_le fun hz1 => iSup₂_le fun H hH => ?_
        by_contra hHM
        exact hcon ⟨z, hz, hz1, H, by rw [cg2_eq_inf]; exact hH.1, hHM,
          Or.inr ⟨rfl, hty z hz hz1 H hH.1 hH.2⟩⟩
      exact hLM (le_of_barX_le_of_le hLC hcore hXM hgen)
  ·
    have hC2 : IsLieChar (· = 2) (barOf p (Lemma1314.LOf p L0 d b)) := by
      rcases hI1419 p hp hp5ge ε n hn1 (barOf p (Lemma1314.L0bOf p L0 b))
          (barOf p (Lemma1314.LOf p L0 d b)) hKH hKK hGp hO hFPF x hx with hC2 | ⟨hp5, hC3⟩
      · exact hC2
      · exfalso
        have hq : IsLieChar (fun q => q ≠ 2 ∧ q ≠ p) (barOf p (Lemma1314.LOf p L0 d b)) :=
          isLieChar_mono (fun q (hq : q = 3) => ⟨by omega, by omega⟩) hC3
        rcases hP1116 h.toSec13.toSec11 hdA hd1 hLc hq with hLM' | hA1 | hIII | ⟨hp13, -⟩
        · exact hLM hLM'
        · exact hii hA1
        · exact hChev3 h h139a' hU hUR hb hb1' hp5 hC3 hIII.1
        · omega
    obtain ⟨hgen, hty⟩ := hChevGen h h139a' hU hUR hb hb1' hA3 hii hC2
      (fun hp5 => hExc h h139a' hU hb hb1' hp5 ⟨ε, n, hn1, hO, hFPF⟩ (Or.inl hC2))
    have hOM := hChevOpM hP112 h h139a' hi hU hUR hb hb1' hii hC2
    by_contra hcon
    have hXM : (⨆ z ∈ U, ⨆ (_ : z ≠ 1),
        (GLAPPrimeCoreOf p (uConjJoin U (Lemma1314.LOf p L0 d b) ⊓ Cg z) ⊔
          ⨆ (H : Subgroup G) (_ : GLAPComponent p (Cg2 d z) H ∧
            H ≤ uConjJoin U (Lemma1314.LOf p L0 d b)), H)) ≤ M := by
      refine iSup₂_le fun z hz => iSup_le fun hz1 => sup_le (hOM z hz hz1) ?_
      refine iSup₂_le fun H hH => ?_
      by_contra hHM
      exact hcon ⟨z, hz, hz1, H, hH.1, hHM, Or.inl (hty z hz hz1 H hH.1 hH.2)⟩
    exact hLM (le_of_barX_le_of_le hLC hcore hXM hgen)

end IIICoreK

open Claims1314 in
theorem chev3Block_of_inputsK (hL1313 : Lemma1313Statement) (hI1415 : Input14_15K)
    (hI : Input14_19_3c) (hAlt : Prop1116Design.InputAltNotLie) (hFi : InputFi23NotChev3) :
    Lemma1314c.Chev3Block := by
  intro G _ _ m p B M E A D T R L0 d h h139a U hU hUR b hb hb1 hp5 hC3
  have hp : p.Prime := h.standing.prime
  obtain ⟨-, hIst, LI, hLIc, -, -, htypeI⟩ := h139a
  obtain ⟨-, ⟨hLc, -, hisoL⟩, -, -⟩ := hL1313 h hU hb hb1
  obtain ⟨eI⟩ := hisoL LI (by rw [← hIst]; exact hLIc)
  have htype := Lemma1314.type_of_iso eI htypeI
  obtain ⟨x, hx⟩ := pumpupBlock_of_lemma1313 hL1313 h hU hb hb1
  have hKH := kHatBlock_of_lemma1313 hL1313 h hU hb hb1
  have hKK : CFSG.Open.IsKGroup (barOf p (Lemma1314.LOf p L0 d b)) :=
    isKGroup_barOf_of_le_cg h.standing h.hd.2 hLc.1
  have hGp : GLAPPrimeCore p (barOf p (Lemma1314.LOf p L0 d b)) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  rcases htype with hTalt | ⟨ε, n, hn, hO, hF⟩
  · exfalso
    obtain ⟨eA⟩ : Nonempty (barOf p (Lemma1314.L0bOf p L0 b) ≃* alternatingGroup (Fin (p + 2))) := hTalt
    have hx' : Lemma1314.PumpupVia p ↥(alternatingGroup (Fin (p + 2)))
        (barOf p (Lemma1314.LOf p L0 d b)) x := Lemma1314.pumpupVia_of_equiv eA hx
    rcases hI1415 p hp (by omega) (barOf p (Lemma1314.LOf p L0 d b)) hKH hKK hGp ⟨x, hx'⟩ with
      ⟨k, hk2, ⟨f⟩⟩ | ⟨-, hFi23⟩
    · obtain ⟨idx, ⟨g⟩, -⟩ := hC3
      have hn : 5 ≤ k * p + 2 := by nlinarith
      have hZ : Subgroup.center (barOf p (Lemma1314.LOf p L0 d b)) = ⊥ :=
        center_eq_bot_of_mulEquiv f.symm (AltFacts3.center_alt (by omega))
      have eZ : (barOf p (Lemma1314.LOf p L0 d b) ⧸
          Subgroup.center (barOf p (Lemma1314.LOf p L0 d b))) ≃* barOf p (Lemma1314.LOf p L0 d b) :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      exact (hAlt (k * p + 2) idx hn).false (f.symm.trans (eZ.symm.trans g))
    · subst hp5
      exact hFi _ hFi23 hC3
  · subst hp5
    exact hI _ hKH hGp _ ε n hn hO hF ⟨x, hx⟩ hC3

open Claims1314 in
theorem chevOpMBlock_of_inputsK (hL1312 : Lemma1312Statement) (hL1313 : Lemma1313Statement)
    (hI1415 : Input14_15K) (hI1419 : Input14_19_3K) (hI2310 : Lemma1314.Input23_10)
    (hI2324 : Lemma1314.Input23_24Fi23) (hExc : Lemma1314.ExcBlock) (hConn : Lemma1314.ConnBlock)
    (hL133 : Lemma133Statement) (hcomp : Sec13g.Lemma133_compStatement) : Lemma1314c.ChevOpMBlock := by
  intro hP112 G _ _ m p B M E A D T R L0 d h h139a _ U hU hUR b hb hb1 hii _
  have hA3 := lemma1314_iv_of_inputsK h h139a hL1312 hL1313 (prop111_of_prop112 hP112)
    lemma101_ii_holds lemma104_ii_holds lemma104_iii_holds hI1415 hI1419 hI2310 hI2324
    (pumpupBlock_of_lemma1313 hL1313) (kHatBlock_of_lemma1313 hL1313) hExc hConn
  exact chevOpM_of_rank hP112 hL1313 hL133 hcomp h h139a hA3 hU hUR hb hb1 hii

theorem lemma1314_ii_of_inputsK {G : Type} [Group G] [Finite G] {m p : ℕ}
    {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    (hL1312 : Lemma1312Statement) (hL1313 : Lemma1313Statement) (hP111 : Prop111Statement)
    (hL101ii : Lemma101_iiStatement) (hL104ii : Lemma104_iiStatement)
    (hL104iii : Lemma104_iiiStatement)
    (hI1415 : Input14_15K) (hI1419 : Input14_19_3K)
    (hI2310 : Lemma1314.Input23_10) (hI2324 : Lemma1314.Input23_24Fi23)
    (hPump : Lemma1314.PumpupBlock) (hKHat : Lemma1314.KHatBlock) (hExc : Lemma1314.ExcBlock)
    (hConn : Lemma1314.ConnBlock) (hNPC : Lemma1314b.NotPCentralBlock) :
    ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1 :=
  Lemma1314b.ii_of_iv h h139a
    (lemma1314_iv_of_inputsK h h139a hL1312 hL1313 hP111 hL101ii hL104ii hL104iii
      hI1415 hI1419 hI2310 hI2324 hPump hKHat hExc hConn) hL1312 hNPC

theorem lemma1314_iii_of_inputsK {G : Type} [Group G] [Finite G] {m p : ℕ}
    {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    (hI71 : Input7_1Inn) (hL133 : Lemma133Statement) (hcomp : Sec13g.Lemma133_compStatement)
    (hPiI : Lemma1314c.PiTypeClauseBlock)
    (hL1312 : Lemma1312Statement) (hL1313 : Lemma1313Statement) (hP111 : Prop111Statement)
    (hP112 : Prop112Statement) (hP1116 : Prop1116Statement)
    (hL101ii : Lemma101_iiStatement) (hL104ii : Lemma104_iiStatement)
    (hL104iii : Lemma104_iiiStatement)
    (hI1415 : Input14_15K) (hI1419 : Input14_19_3K)
    (hI2310 : Lemma1314.Input23_10) (hI2324 : Lemma1314.Input23_24Fi23)
    (hPump : Lemma1314.PumpupBlock) (hKHat : Lemma1314.KHatBlock) (hExc : Lemma1314.ExcBlock)
    (hConn : Lemma1314.ConnBlock) (hNPC : Lemma1314b.NotPCentralBlock)
    (hFiLoc : Lemma1314c.Input23_24Fi23Loc) (hFiFaith : Lemma1314c.FiFaithBlock)
    (hChev3 : Lemma1314c.Chev3Block) (hChevGen : Lemma1314c.ChevGenBlock)
    (hChevOpM : Lemma1314c.ChevOpMBlock) :
    ∀ U : Subgroup G, IsU1312 p B M D L0 d U → U ≤ centerOf R → ∃ z ∈ U, z ≠ 1 ∧
      ∃ H0 : Subgroup G, GLAPComponent p (Cg2 d z) H0 ∧ ¬ H0 ≤ M ∧
        (Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0))) :=
  fun _ hU hUR => iii_coreK h h139a hL1313 hP111 hP112 hP1116 hI1415 hI1419 hPump hKHat
    hExc hFiLoc hFiFaith hChev3 hChevGen hChevOpM hL133 hcomp
    (Sec13g.lemma1314_i_of_inputs hI71 hL133 hcomp h h139a (hPiI h h139a))
    (lemma1314_ii_of_inputsK h h139a hL1312 hL1313 hP111 hL101ii hL104ii hL104iii hI1415 hI1419
      hI2310 hI2324 hPump hKHat hExc hConn hNPC)
    (lemma1314_iv_of_inputsK h h139a hL1312 hL1313 hP111 hL101ii hL104ii hL104iii hI1415
      hI1419 hI2310 hI2324 hPump hKHat hExc hConn)
    hU hUR

theorem lemma1314_of_inputsK
    (hI71 : Input7_1Inn) (hL133 : Lemma133Statement) (hcomp : Sec13g.Lemma133_compStatement)
    (hPiI : Lemma1314c.PiTypeClauseBlock)
    (hL1312 : Lemma1312Statement) (hL1313 : Lemma1313Statement) (hP111 : Prop111Statement)
    (hP112 : Prop112Statement) (hP1116 : Prop1116Statement)
    (hL101ii : Lemma101_iiStatement) (hL104ii : Lemma104_iiStatement)
    (hL104iii : Lemma104_iiiStatement)
    (hI1415 : Input14_15K) (hI1419 : Input14_19_3K)
    (hI2310 : Lemma1314.Input23_10) (hI2324 : Lemma1314.Input23_24Fi23)
    (hPump : Lemma1314.PumpupBlock) (hKHat : Lemma1314.KHatBlock) (hExc : Lemma1314.ExcBlock)
    (hConn : Lemma1314.ConnBlock) (hNPC : Lemma1314b.NotPCentralBlock)
    (hFiLoc : Lemma1314c.Input23_24Fi23Loc) (hFiFaith : Lemma1314c.FiFaithBlock)
    (hChev3 : Lemma1314c.Chev3Block) (hChevGen : Lemma1314c.ChevGenBlock)
    (hChevOpM : Lemma1314c.ChevOpMBlock) : Lemma1314Statement := by
  intro G _ _ m p B M E A D T R L0 d h h139a
  exact ⟨Sec13g.lemma1314_i_of_inputs hI71 hL133 hcomp h h139a (hPiI h h139a),
    lemma1314_ii_of_inputsK h h139a hL1312 hL1313 hP111 hL101ii hL104ii hL104iii hI1415 hI1419
      hI2310 hI2324 hPump hKHat hExc hConn hNPC,
    lemma1314_iii_of_inputsK h h139a hI71 hL133 hcomp hPiI hL1312 hL1313 hP111 hP112 hP1116 hL101ii
      hL104ii hL104iii hI1415 hI1419 hI2310 hI2324 hPump hKHat hExc hConn hNPC hFiLoc hFiFaith
      hChev3 hChevGen hChevOpM,
    lemma1314_iv_of_inputsK h h139a hL1312 hL1313 hP111 hL101ii hL104ii hL104iii hI1415
      hI1419 hI2310 hI2324 hPump hKHat hExc hConn⟩

open Claims1314 in
theorem lemma1314_of_inputs_redK (hL133 : Lemma133Statement) (hL1312 : Lemma1312Statement)
    (hL1313 : Lemma1313Statement) (hP112 : Prop112Statement) (hP1116 : Prop1116Statement)
    (hI1415 : Input14_15K) (hI1419 : Input14_19_3K)
    (hI2310 : Lemma1314.Input23_10) (hI2324 : Lemma1314.Input23_24Fi23)
    (hFiLoc : Lemma1314c.Input23_24Fi23Loc) (hI1419c : Input14_19_3c)
    (hAlt : Prop1116Design.InputAltNotLie) (hFi : InputFi23NotChev3) (hO : Exc5Orders)
    (hNPC : Lemma1314b.NotPCentralBlock) (hGen : ChevGenGenBlock)
    (hI144 : Lemma1315b.Input14_4_1) : Lemma1314Statement := by
  have hI71 : Input7_1Inn := Inputs71.input7_1Inn_holds
  have hcomp : Sec13g.Lemma133_compStatement := Bridges2.lemma133_comp_holds
  have hChevGen : Lemma1314c.ChevGenBlock := chevGenBlock_of_inputs hGen hI144 hL1313 hL133 hcomp
  have hConn : Lemma1314.ConnBlock :=
    Lemma1314c.connBlock_of_inputs hI71 hL133 hcomp Lemma1314c.piTypeClauseBlock_holds
  have hExc : Lemma1314.ExcBlock := excBlock_of_orders hL1313 hO
  have hP111 : Prop111Statement := prop111_of_prop112 hP112
  have hPump : Lemma1314.PumpupBlock := pumpupBlock_of_lemma1313 hL1313
  have hKHat : Lemma1314.KHatBlock := kHatBlock_of_lemma1313 hL1313
  have hFiFaith : Lemma1314c.FiFaithBlock := fiFaithBlock_of_inputs hL1313 hL133 hcomp
  have hChev3 : Lemma1314c.Chev3Block := chev3Block_of_inputsK hL1313 hI1415 hI1419c hAlt hFi
  have hChevOpM : Lemma1314c.ChevOpMBlock :=
    chevOpMBlock_of_inputsK hL1312 hL1313 hI1415 hI1419 hI2310 hI2324 hExc hConn hL133 hcomp
  have hL101ii : Lemma101_iiStatement := lemma101_ii_holds
  have hL104ii : Lemma104_iiStatement := lemma104_ii_holds
  have hL104iii : Lemma104_iiiStatement := lemma104_iii_holds
  exact @lemma1314_of_inputsK hI71 hL133 hcomp
    Lemma1314c.piTypeClauseBlock_holds hL1312 hL1313 hP111 hP112 hP1116 hL101ii hL104ii hL104iii
    hI1415 hI1419 hI2310 hI2324 hPump hKHat hExc hConn hNPC hFiLoc hFiFaith hChev3 hChevGen hChevOpM

open Claims1314 in
theorem lemma1314_of_inputs_certK
    (hL133 : Lemma133Statement) (hL1312 : Lemma1312Statement)
    (hL1313 : Lemma1313Statement) (hP112 : Prop112Statement) (hP1116 : Prop1116Statement)
    (hI1415 : Input14_15K) (hI1419 : Input14_19_3K)
    (hI2310 : Lemma1314.Input23_10) (hI2324 : Lemma1314.Input23_24Fi23)
    (hFiLoc : Lemma1314c.Input23_24Fi23Loc) (hI1419c : Input14_19_3c)
    (hFi : InputFi23NotChev3) (hNPC : Lemma1314b.NotPCentralBlock) (hGen : ChevGenGenBlock)
    (hI144 : Lemma1315b.Input14_4_1) : Lemma1314Statement :=
  lemma1314_of_inputs_redK hL133 hL1312 hL1313 hP112 hP1116 hI1415 hI1419 hI2310 hI2324
    hFiLoc hI1419c AltFacts4.inputAltNotLie_holds hFi exc5Orders_holds hNPC hGen hI144

end Lemma1314K

section Lemma1315K

open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut)
open CFSG.LocalAnalysis.GLTheoremA (IsKHat)

open Lemma1315b in
structure InputsK : Prop where
  i2319 : Input23_19
  i255 : Input25_5
  i33 : Input3_3
  i144 : Input14_4_1
  i1418 : Input14_18
  i1415 : Input14_15K
  iFi23 : Lemma1314.Input23_24Fi23
  i112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2
  i183 : Prop115.Input18_3Gen
  iDiag : Input18_3DiagZ
  iL2 : InputL2

variable {G : Type} [Group G] [Finite G]

open Lemma1315b in
theorem single_caseK {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z)
    (hI : InputsK) (hstd : GLStanding G m p) (hX : Cg z ≠ ⊤)
    {H H0 : Subgroup G} (hHc : GLAPComponent p (Cg z) H)
    (hdH : d ∈ Subgroup.normalizer (H : Set G)) (hH0H : H0 ≤ H)
    (hH0 : GLAPComponent p (Cg2 d z) H0) (hHM : ¬ H ≤ M)
    (hH0t : Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0)))
    {A : Subgroup G} (hA : IsSCp p (Cg z) A) (hAr : CFSG.Open.pRank p A = 3) (hdA : d ∈ A)
    (hzA : z ∈ A) :
    (p = 5 ∨ p = 7) ∧ IsLpType 2 p (barOf p H0) ∧ IsLpType 2 (p ^ p) (barOf p H) ∧
      ¬ InducesInner p H d := by
  have hp := hb.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hKP : CFSG.Open.IsKProper G := hstd.kProper
  have hdX : d ∈ Cg z := hb.d_mem_Cg
  have hHX : H ≤ Cg z := hHc.1
  have hKX : CFSG.Open.IsKGroup ↥(Cg z) := CFSG.Open.IsKProper.isKGroup hKP (Cg z) hX
  haveI : (GLAPPrimeCore p ↥(Cg z)).Normal := inferInstance
  have hY : CFSG.Open.IsKGroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) :=
    CFSG.Open.IsKGroup.quotient hKX _
  have hcomp := Lemma1314.isComponentOf_barX_of_glaPComponent hHc
  have hKhat := isKHat_barX hp hKX hHc
  have hKK : CFSG.Open.IsKGroup ↥(barX p (Cg z) H) := hY.subgroup _
  have hcoreK := core_barX_eq_bot hp hHc
  have hdK := mk_mem_normalizer_barX (p := p) hdX hdH
  have hdord := orderOf_mk_eq (p := p) hdX hb.dord
  have hdp : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩) ^ p = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩)
    rwa [hdord] at this
  have hH0' : GLAPComponent p (H ⊓ Cg d) H0 :=
    glaPComponent_of_le hp hH0 (le_inf hH0H (hH0.1.trans cg2_le_cg_d)) (inf_le_cg2 hHX)
  have hH0X : H0 ≤ Cg z := hH0H.trans hHX
  have hdz : IsPGroup p ↥(Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb.dord, pow_one])
  have hJ := glaPComponent_barX_inf_centralizer hp hdX hHX hdH hdz hH0'
  have eH : barOf p H ≃* ↥(barX p (Cg z) H) := quotEquivBarX hp hHX hHc.2.1
  have hH0q : CFSG.Open.IsQuasisimple (barOf p H0) := isQuasisimple_barOf_of_comp hp hH0
  have hH0core : GLAPPrimeCore p (barOf p H0) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hp2 : 2 ≠ p := by have := hb.five_le; omega
  have hH0type : (∃ n : ℕ, IsAltType n (barOf p H0 ⧸ Subgroup.center (barOf p H0))) ∨
      IsChevSimple 2 (barOf p H0 ⧸ Subgroup.center (barOf p H0)) := by
    rcases hH0t with hc | ⟨-, hA7⟩
    · exact Or.inr (isChevSimple_two_of_isChevTwo hc.2)
    · exact Or.inl ⟨7, isAltType_center_quot (by norm_num) hA7⟩
  have hclaim : ((∃ n : ℕ, IsAltType n (barOf p H ⧸ Subgroup.center (barOf p H))) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧
        IsChevSimple q (barOf p H ⧸ Subgroup.center (barOf p H)))) → False :=
    fun ht => hHM (le_M_of_type hb hI.i2319 hKP hX hHc ht)
  by_cases hcen : barX p (Cg z) H ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩} : Set (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)))
  ·
    exfalso
    have hinf : barX p (Cg z) H ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩} :
          Set (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))) = barX p (Cg z) H := inf_eq_left.2 hcen
    have hJ' : GLAPComponent p (barX p (Cg z) H) (barX p (Cg z) H0) := by
      rw [hinf] at hJ
      exact hJ
    have hper : ⁅barX p (Cg z) H0, barX p (Cg z) H0⁆ = barX p (Cg z) H0 := glaPComponent_perfect hJ'
    have hJbot : barX p (Cg z) H0 ≠ ⊥ := ne_bot_of_quasisimple_quot (isQuasisimple_barOf_of_comp hp hJ')
    have hJK : barX p (Cg z) H0 = barX p (Cg z) H :=
      eq_of_perfect_subnormal_quasisimple hcomp.2.2 hJbot hper hJ'.2.1
    have e0 : barOf p H0 ≃* ↥(barX p (Cg z) H) :=
      (barOfBarX hp hH0X).trans (iso_of_eq_of_core hJK hcoreK)
    have eHH0 : barOf p H ≃* barOf p H0 := eH.trans e0.symm
    rcases hH0type with ⟨n, hn⟩ | hch
    · exact hclaim (Or.inl ⟨n, isAltType_center_of_equiv eHH0 hn⟩)
    · exact hclaim (Or.inr ⟨2, Nat.prime_two, hp2, isChevSimple_center_of_equiv eHH0 hch⟩)
  · have hpump0 := pumpupVia_of_setting hp hdK hdp hcen hJ
    have hpump : Lemma1314.PumpupVia p (barOf p H0) ↥(barX p (Cg z) H) (conjAutOf _ _ hdK) :=
      Lemma1314.pumpupVia_of_equiv (barOfBarX hp hH0X).symm hpump0
    rcases hH0t with hchev | ⟨hp5, hA7⟩
    · have hch2 : IsChevSimple 2 (barOf p H0 ⧸ Subgroup.center (barOf p H0)) :=
        isChevSimple_two_of_isChevTwo hchev.2
      have hnab := exists_noncomm_quot hKhat.1
      rcases catalog_cases hnab hKhat.2 with ⟨n, hn⟩ | ⟨idx, ⟨e⟩⟩ | ⟨name, hname⟩
      · exact absurd (Or.inl ⟨n, isAltType_center_of_equiv eH hn⟩) hclaim
      · have hr : idx.1.characteristic.Prime := idx.1.characteristic_prime
        have hchev : IsChevSimple idx.1.characteristic
            (↥(barX p (Cg z) H) ⧸ Subgroup.center ↥(barX p (Cg z) H)) := isChevSimple_of_lie e
        by_cases hrp : idx.1.characteristic = p
        · rw [hrp] at hchev
          obtain ⟨hch_p, hnot_inner⟩ := hI.i144 p p hp hb.five_le hp _ hKhat hcoreK hchev
            (barOf p H0) _ hpump
          obtain ⟨h57, hL2p⟩ := hI.i33 p hp hb.five_le (barOf p H0) hH0q hH0core hch2 hch_p
          have hLq := hI.i1418 p hp (by have := hb.five_le; omega) _ hKhat hcoreK hchev
            (barOf p H0) _ hL2p hpump
          refine ⟨h57, hL2p, isLpType_of_equiv eH hLq, ?_⟩
          intro hind
          obtain ⟨k, hk, hkk⟩ := innerOn_of_inducesInner hp hHc.2.1 hdX hind
          exact hnot_inner rfl (mem_innerAut_of_innerOn hdK hk hkk)
        · exact absurd (Or.inr ⟨idx.1.characteristic, hr, hrp,
            isChevSimple_center_of_equiv eH hchev⟩) hclaim
      · exact absurd (le_M_of_spor hb hI.i255 hKP hX hHc hdH hH0' hch2 ⟨name, hname⟩ hA hAr hdA hzA)
          hHM
    · exfalso
      subst hp5
      have hdis := hI.i1415 5 hp (le_refl 5) _ hKhat hKK hcoreK
        ⟨_, Lemma1314.pumpupVia_of_equiv hA7.some hpump⟩
      rcases hdis with ⟨k, hk2, hk⟩ | ⟨-, hFi⟩
      · have : IsAltType (k * 5 + 2) (↥(barX 5 (Cg z) H) ⧸ Subgroup.center ↥(barX 5 (Cg z) H)) :=
          isAltType_center_quot (by omega) hk
        exact hclaim (Or.inl ⟨_, isAltType_center_of_equiv eH this⟩)
      · have hG := hI.iFi23 (↥(Cg z) ⧸ GLAPPrimeCore 5 ↥(Cg z)) (glaPPrimeCore_quotient_eq_bot hp)
          (barX 5 (Cg z) H) (barX 5 (Cg z) B) hcomp (isElemAbelian_barX hb.bel) hFi
        have hk3 : 3 ≤ CFSG.Open.pRank 5 B := by rw [hb.pRank_B]; have := hb.m4; omega
        exact hHM (Lemma1314.le_of_gMinusOne hp hHX hb.B_le_Cg (isPGroup_of_elemAbelian hb.bel)
          hb.normB hb.core hG hk3)

open Lemma1315b in
theorem type_analysisK {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z)
    (hI : InputsK) (hstd : GLStanding G m p) (hX : Cg z ≠ ⊤)
    {H0 : Subgroup G} (hH0 : GLAPComponent p (Cg2 d z) H0) (hH0M : ¬ H0 ≤ M)
    (hH0t : Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0)))
    {A : Subgroup G} (hA : IsSCp p (Cg z) A) (hAr : CFSG.Open.pRank p A = 3) (hdA : d ∈ A)
    (hzA : z ∈ A) {H : Subgroup G} (hHdef : H = ⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0) :
    TypeResult p (Cg z) H0 H d := by
  have hp := hb.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := hb.five_le; omega
  have hH0H : H0 ≤ H := by
    rw [hHdef]
    exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (le_of_eq (gLBConj_one H0).symm)
  rcases hI.i183 p hp hp2 G hstd.simple hstd.nonabelian hstd.kProper d z hb.dord hb.zo hb.dz H0
    hH0 with ⟨L, hL, hHL, hdL⟩ | ⟨L, hL, hinj, hcyc, hHL⟩
  · have hLH : H = L := hHdef.trans hHL
    have hHc : GLAPComponent p (Cg z) H := hLH ▸ hL
    have hdH : d ∈ Subgroup.normalizer (H : Set G) :=
      mem_normalizer_iff_gLBConj_eq.2 (hLH ▸ hdL)
    have hHM : ¬ H ≤ M := fun h => hH0M (hH0H.trans h)
    obtain ⟨h57, hlp, hlq, hni⟩ :=
      single_caseK hb hI hstd hX hHc hdH hH0H hH0 hHM hH0t hA hAr hdA hzA
    exact ⟨h57, hlp, hlq, hHc, hH0H, hdH, hni⟩
  · exfalso
    have hdiag := hI.iDiag p hp hp2 G hstd.simple hstd.nonabelian hstd.kProper d z hb.dord hb.zo
      hb.dz H0 hH0 L hL hinj hcyc hHL
    have hLM : ∀ i, L i ≤ M := fun i => by
      obtain ⟨e⟩ := hdiag i
      rcases h0type hH0t with ⟨n, hn⟩ | hch
      · exact le_M_of_type hb hI.i2319 hstd.kProper hX (hL i)
          (Or.inl ⟨n, Lemma1314.isAltType_of_equiv e.symm hn⟩)
      · exact le_M_of_type hb hI.i2319 hstd.kProper hX (hL i)
          (Or.inr ⟨2, Nat.prime_two, hp2.symm, isChevSimple_of_equiv e.symm hch⟩)
    have hHM : H ≤ M := by
      rw [hHdef, hHL]
      exact iSup_le hLM
    exact hH0M (hH0H.trans hHM)

open Lemma1315b in
theorem exists_sitK {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h1314 : Lemma1314Statement) (hI : InputsK)
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) (hUR : U ≤ centerOf R) {z : G} {H0 : Subgroup G}
    (hz : z ∈ U ∧ z ≠ 1) (hH0 : GLAPComponent p (Cg2 d z) H0) (hH0M : ¬ H0 ≤ M)
    (hH0t : Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0))) :
    ∃ H : Subgroup G, H = (⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0) ∧
      TypeResult p (Cg z) H0 H d ∧ Sit m p B M R d z H := by
  have hb := basic_of_cex h h139a hU hUR hz
  have hstd := h.standing
  haveI : IsSimpleGroup G := hstd.simple
  have hX : Cg z ≠ ⊤ := centralizer_ne_top_of_simple hstd.nonabelian hz.2
  obtain ⟨hAsc, hdA, hzA⟩ := A_data h hb
  have h14 := h1314 h h139a
  have hAr : CFSG.Open.pRank p A = 3 := h14.2.2.2
  have tr := type_analysisK hb hI hstd hX hH0 hH0M hH0t hAsc hAr hdA hzA
    (H := ⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0) rfl
  have hHM : ¬ (⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0) ≤ M := fun hle => hH0M (tr.H0H.trans hle)
  exact ⟨_, rfl, tr, hb, tr.comp, tr.dN, hb.B_le_normalizer hstd hI.i112 tr.comp,
    hb.centBar_B_eq hstd hI.i112 tr.comp hHM, tr.ninner, hI.iL2 p hb.prime hb.five_le _ tr.lq⟩

end Lemma1315K

theorem lemma1315_of_inputsK (h1314 : Lemma1314Statement)
    (hI2319 : Lemma1315b.Input23_19) (hI255 : Lemma1315b.Input25_5) (hI33 : Lemma1315b.Input3_3)
    (hI144 : Lemma1315b.Input14_4_1) (hI1418 : Lemma1315b.Input14_18)
    (hI1415 : Input14_15K) (hFi23 : Lemma1314.Input23_24Fi23)
    (hI112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (hI183 : Prop115.Input18_3Gen) (hDiag : Lemma1315b.Input18_3DiagZ)
    (hL2 : Lemma1315b.InputL2) : Lemma1315Statement := by
  have hI : InputsK :=
    ⟨hI2319, hI255, hI33, hI144, hI1418, hI1415, hFi23, hI112, hI183, hDiag, hL2⟩
  intro G _ _ m p B M E A D T R L0 d h h139a U hU hUR z H0 hz hH0 hH0M hH0t H
  obtain ⟨H', hH', tr, hs⟩ := exists_sitK h1314 hI h h139a hU hUR hz hH0 hH0M hH0t
  subst hH'
  have h14 := h1314 h h139a
  have hIM := Lemma1315b.mem_normalizer_Iof h139a
  have hr : Lemma1315b.RIC p R (Iof p M D) :=
    ⟨fun r hr' => hIM r (hs.hb.rM hr'), h14.1.1, h14.1.2.1, h14.1.2.2⟩
  obtain ⟨P, -, -, -, -, -, -, -, -, -, -, -, hRB⟩ := hs.R_facts
  exact ⟨⟨tr.p57, tr.lp, tr.lq, hs.cyclic_centBar, tr.dN, tr.ninner⟩,
    Lemma1315.sylow_of_central_rank_two h hU.1 hUR, hRB,
    hs.iv hr (Lemma1315b.normalizer_R_le_M h hU.1 hUR) hIM⟩

theorem lemma1315_extras_of_inputsK (h1314 : Lemma1314Statement)
    (hI2319 : Lemma1315b.Input23_19) (hI255 : Lemma1315b.Input25_5) (hI33 : Lemma1315b.Input3_3)
    (hI144 : Lemma1315b.Input14_4_1) (hI1418 : Lemma1315b.Input14_18)
    (hI1415 : Input14_15K) (hFi23 : Lemma1314.Input23_24Fi23)
    (hI112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (hI183 : Prop115.Input18_3Gen) (hDiag : Lemma1315b.Input18_3DiagZ)
    (hL2 : Lemma1315b.InputL2) : Lemma1315b.ExtrasStatement := by
  have hI : InputsK :=
    ⟨hI2319, hI255, hI33, hI144, hI1418, hI1415, hFi23, hI112, hI183, hDiag, hL2⟩
  intro G _ _ m p B M E A D T R L0 d h h139a U hU hUR z H0 hz hH0 hH0M hH0t H
  obtain ⟨H', hH', tr, hs⟩ := exists_sitK h1314 hI h h139a hU hUR hz hH0 hH0M hH0t
  subst hH'
  obtain ⟨P, hPH, hPp, hPmax, -, hPB, hBeq, hdis, hBH, -, hRH, -, -⟩ := hs.R_facts
  have hBH' : B ⊓ H = P := hBH
  refine ⟨?_, ?_, ?_, fun x hx => hs.normalizer_zpowers_le hx, hs.m_eq_and_inner.1⟩
  · rw [hBH']
    exact ⟨hPH, hPp, hPmax⟩
  · rw [hBH']
    exact ⟨hBeq, hdis⟩
  · rw [hBH']
    exact hRH

section Holds

set_option linter.unusedSectionVars false

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs k2Spor)
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)

open Inputs1415b Inputs1415 CFSG.Yardstones.Md0ec50421ce4 in
theorem sporResidual1314_of_openK
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hnl : Prop1116Design.InputAltNotLie)
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) (hR : Inputs1415b.Rows1314)
    (h : Open1314K) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ name : TauCeti.SporadicName, ¬ (p = 5 ∧ name = .Fi23) →
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group → SporNoAltDown p (p + 2) name := by
  intro p hp hp5 name hne hK
  by_cases h17 : 17 ≤ p
  · exact sporNoAltDown_large hOrd hp h17 name
  have hlev5 : 2 < kLevel 5 (alternatingGroup (Fin 7)) :=
    two_lt_kLevel_alt hnl hOrd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (factorial_ne_sporOrd (Or.inl rfl))
  have hlev7 : 2 < kLevel 7 (alternatingGroup (Fin 9)) :=
    two_lt_kLevel_alt hnl hOrd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (factorial_ne_sporOrd (Or.inr rfl))
  have hfin := finite_spor hOrd
  interval_cases p <;> first
    | (exfalso; revert hp; norm_num; done)
    | skip
  ·
    cases name with
    | Fi23 => exact absurd ⟨rfl, rfl⟩ hne
    | J2 => exact sporNoAltDown5_J2 (by norm_num) hBr
    | He => exact sporNoAltDown5_He (by norm_num) hBr
    | Suz => exact sporNoAltDown5_Suz (by norm_num) hBr
    | Co1 => exact sporNoAltDown5_Co1 (by norm_num) (by norm_num) (by norm_num) hnl hOrd hBr hOut
    | Co2 => exact sporNoAltDown5_Co2 (by norm_num) hBr
    | Co3 => exact sporNoAltDown5_Co3 (by norm_num) hBr
    | Fi22 => exact h.fi22_5
    | Fi24Prime => exact h.fi24_5
    | B => exact h.b_5
    | M => exact h.m_5 hK
    | HN => exact sporNoAltDown_of_downLe hp (hR.hn.1 (by simp [k2, k2Spor])) hlev5
    | Ru => exact sporNoAltDown_of_downLe hp (hR.ru.1 (by simp [k2, k2Spor])) hlev5
    | HS => exact sporNoAltDown_of_downLe hp (hR.hs.1 (by simp [k2, k2Spor])) hlev5
    | Ly => exact sporNoAltDown_of_downLe hp (hR.ly.1 (by simp [k2, k2Spor])) hlev5
    | McL => exact sporNoAltDown_of_downLe hp (hR.mcl.1 (by simp [k2, k2Spor])) hlev5
    | Th => exact sporNoAltDown_of_downLe hp (hR.th.1 (by simp [k2, k2Spor])) hlev5
    | _ => exact sporNoAltDown_of_not_dvd hOrd hp (by norm_num) (by decide)
  ·
    cases name with
    | Co1 => exact sporNoAltDown7_Co1 (by norm_num) hBr
    | Fi24Prime => exact sporNoAltDown7_Fi24 (by norm_num) hOrd hBr
    | Th => exact sporNoAltDown7_Th (by norm_num) hBr
    | B => exact sporNoAltDown7_B (by norm_num) hBr
    | M => exact sporNoAltDown7_M (by norm_num) (by norm_num) (by norm_num) hnl hOrd hOut
    | ONan => exact sporNoAltDown_of_downLe hp (hR.on.1 (by simp [k2, k2Spor])) hlev7
    | _ => exact sporNoAltDown_of_not_dvd hOrd hp (by norm_num) (by decide)
  ·
    cases name with
    | M => exact h.m_11
    | _ => exact sporNoAltDown_of_not_dvd hOrd hp (by norm_num) (by decide)
  ·
    cases name with
    | M => exact sporNoAltDown13_M (by norm_num) hBr
    | _ => exact sporNoAltDown_of_not_dvd hOrd hp (by norm_num) (by decide)

theorem input14_15_holdsK
    (h : Open1314K) : Input14_15K :=
  input14_15_of_sporK AltFacts4.inputAltNotLie_holds
    (fun _ hp hp5 _ => CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1315.kdChevDownQ_five_le hp hp5)
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    (Inputs1415b.fi23_center_eq_bot
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    (sporResidual1314_of_openK CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
      AltFacts4.inputAltNotLie_holds CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds Inputs1415b.rows1314_holds h)

theorem open1314K_holds
    (hm11 : SporTables.MElevenNoSeven) : Open1314K where
  fi22_5 := SporTables.sporNoAltDown_Fi22_five_seven
  fi24_5 := SporTables.sporNoAltDown_Fi24_five_seven
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group SporTables3.fi24FiveA9_holds
  b_5 := SporTables.sporNoAltDown_B_five CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds 7 le_rfl
  m_5 := fun hK => SporTables.sporNoAltDown_M_five_of_kGroup
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds 7 (by norm_num) hK
  m_11 := SporTables.sporNoAltDown_M_eleven_of hm11 13 (by norm_num)

theorem input14_15K_holds
    (hm11 : SporTables.MElevenNoSeven) : Input14_15K :=
  input14_15_holdsK (open1314K_holds hm11)

open Inputs1419 in
theorem input14_19_3_of_sporK
    (hS : InputSporOmegaDownK) : Input14_19_3K := by
  intro p hp hp5 ε n hn J _ K _ _ hK hKK hO hJ hF x hx
  obtain ⟨i, ⟨e⟩⟩ := hK.2
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod q)) _ _
  | alternating N hN => exact (Inputs1419.not_pumpup_alt hp hp5 hn hF hK.1 hO hJ hN e x hx).elim
  | sporadic s =>
    exact (hS p hp hp5 ε n hn hF J K hK.1 hO s ⟨e⟩ ((hKK.quotient _).of_surjective e.toMonoidHom e.surjective)
      hJ x hx).elim
  | lie d =>
    by_cases hd2 : d.1.characteristic = 2
    · exact Or.inl ⟨d, ⟨e⟩, hd2⟩
    · obtain ⟨-, -, hp5', hr3⟩ := Inputs1419.lie_case hp hp5 hn hF hK hO hJ hx hd2 e
      exact Or.inr ⟨hp5', d, ⟨e⟩, hr3⟩

theorem sporOmegaTable_of_openK
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hT : SporOmegaTableOpenK) : SporOmegaTableK := by
  intro name ε n p hmem hK
  rcases Inputs1419b.sporOmegaCases_split _ hmem with ho | ⟨hname, hrest⟩
  · exact hT name ε n p ho hK
  · simp only [Prod.mk.injEq] at hrest
    obtain ⟨rfl, rfl, rfl⟩ := hrest
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl | rfl | rfl
    · exact Inputs1419b.sporNoOmegaDown_McL hbr
    · exact Inputs1419b.sporNoOmegaDown_Suz hbr
    · exact Inputs1419b.sporNoOmegaDown_Co3 hbr
    · exact Inputs1419b.sporNoOmegaDown_Co2 hbr

theorem input14_19_3_of_tableK
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (hT : SporOmegaTableK) : Input14_19_3K :=
  input14_19_3_of_sporK (inputSporOmegaDown_of_tableK hOrd hOut Inputs1419b.sporNoOmegaDown_Fi22 hT)

theorem input14_19_3_of_openK
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hT : SporOmegaTableOpenK) : Input14_19_3K :=
  input14_19_3_of_tableK hOrd hOut (sporOmegaTable_of_openK hbr hT)

theorem sporOmegaTableOpenK_holds
    (hm11 : SporTables.MElevenNoSeven) : SporOmegaTableOpenK := by
  have hb := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hOrd := CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hBr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  intro name ε n p hmem hK
  simp only [Inputs1419b.sporOmegaCasesOpen, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · exact SporTables.sporNoOmegaDown_HN_five hb hOrd hOut hBr
  · exact SporTables.sporNoOmegaDown_Ly_five hb hOrd hOut hBr
  · exact SporTables.sporNoOmegaDown_Th_five hb hOrd hOut hBr
  · exact SporTables.sporNoOmegaDown_Fi23_five hBr
  · exact SporTables.sporNoOmegaDown_Co1_five hb hOrd hOut hBr
  · exact SporTables.sporNoOmegaDown_Fi24_five hOrd hBr SporTables3.fi24FiveA9_holds
  · exact SporTables.sporNoOmegaDown_of_card (R := fun N => N = 44352000) (le_refl 2)
      (SporTables.sporTypes_B_five_of_kGroup hBr hOrd hK) (by decide +kernel)
  · exact SporTables.sporNoOmegaDown_of_card (R := fun N => N = 273030912000000) (le_refl 2)
      (SporTables.sporTypes_M_five_of_kGroup hBr hOrd hK) (by decide +kernel)
  · exact SporTables.sporNoOmegaDown_Th_seven hBr
  · exact SporTables.sporNoOmegaDown_Co1_seven hBr
  · exact SporTables.sporNoOmegaDown_Fi24_seven hOrd hBr
  · exact SporTables.sporNoOmegaDown_B_seven
  · exact SporTables.sporNoOmegaDown_M_seven hBr hOrd
  · exact SporTables.sporNoOmegaDown_B_five_ten hBr hOrd
  · exact SporTables.sporNoOmegaDown_of_card (R := fun N => N = 273030912000000) (by norm_num)
      (SporTables.sporTypes_M_five_of_kGroup hBr hOrd hK) (by decide +kernel)
  · exact SporTables.sporNoOmegaDown_M_eleven_of hm11

theorem input14_19_3K_holds
    (hm11 : SporTables.MElevenNoSeven) : Input14_19_3K :=
  input14_19_3_of_openK CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group (sporOmegaTableOpenK_holds hm11)

open Inputs256 CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Dickson.I271 in
theorem input25_5Core_of_factsK
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hOff : ∀ s : TauCeti.SporadicName, OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hNC : ∀ name : TauCeti.SporadicName,
      name ∈ ({.Co1, .HN, .Ly, .B, .M} : Finset TauCeti.SporadicName) →
      ∀ (S : Type) [Group S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
        ¬ IsChevSimple 2 S)
    (hB : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group → SporNoChevTwoDown 5 .B)
    (hM5 : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group → SporNoChevTwoDown 5 .M)
    (hM7 : SporNoChevTwoDown 7 .M) :
    InputsSeitz.Input25_5Core := by
  intro Y _ _ p hp hp5 hKY K d hK hdN hd hspor hJ hA h3 B _
  exfalso
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨name, ⟨e⟩⟩ := hspor
  have hKs : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group :=
    ((hKY.subgroup K).quotient _).of_surjective e.toMonoidHom e.surjective
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hp2 : p ≠ 2 := by omega
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hq
  have hcen := CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout := hOut _ hq.2 hnab name ⟨e⟩
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    intro h
    have h12 := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.card_center_dvd_twelve hSpM hq name e
    have hp12 : p ∣ 2 ^ 2 * 3 := h.trans h12
    rcases (Nat.Prime.dvd_mul hp).1 hp12 with h2 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
      omega
  have hpair := onePair_of_three_le hp hp2 hOut hbr hOff hq e h3
  have hdp : d ^ p = 1 := hd ▸ pow_orderOf_eq_one d
  obtain ⟨J, hJc, hJchev⟩ := hJ
  obtain ⟨s, hsp, hsk, I, hI, ⟨eI⟩⟩ := transfer_comp hp hp2 hcen hout hdN hdp hJc
  have hIchev : IsChevSimple 2 (PSimple p I) := isChevSimple_of_mulEquiv eI hJchev
  have hname : name ∈ ({.Co1, .HN, .Ly, .B, .M} : Finset TauCeti.SporadicName) := by
    unfold SporadicOnePair at hpair
    rcases hpair with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · omega
    · exact h
    · rw [h]; decide
  have hs1 : s ≠ 1 := by
    rintro rfl
    have hc1 : Subgroup.centralizer ({1} : Set (↥K ⧸ Subgroup.center ↥K)) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [hc1] at hI
    have hIt := CFSG.LocalAnalysis.GLTheoremA.KDSpor.eq_top_of_glaPComponent_top hI
    subst hIt
    obtain ⟨eS⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.nonempty_pSimple_top_equiv hp hnab hI
    exact hNC name hname _ ⟨e⟩ (isChevSimple_of_mulEquiv eS hIchev)
  have hso : orderOf s = p := orderOf_eq_prime hsp hs1
  have hrow : name = .Co1 ∨ SporNoChevTwoDown p name := by
    unfold SporadicOnePair at hpair
    rcases hpair with ⟨h, -⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl⟩
    · omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (sporNoChevTwoDown_HN hbr hb)
      · exact Or.inr (sporNoChevTwoDown_Ly hbr)
      · exact Or.inr (hB hKs)
      · exact Or.inr (hM5 hKs)
    · exact Or.inr hM7
  rcases hrow with rfl | hrow
  swap
  · exact hrow _ ⟨e⟩ s hso I hI hIchev
  have hp5' : p = 5 := by
    unfold SporadicOnePair at hpair
    rcases hpair with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact h
    · exact absurd h (by decide)
  subst hp5'
  obtain ⟨A, hAscp, hdA, hArk, hAZ⟩ := hA
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAZ
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hAc : Nat.card A = 5 ^ 3 := by rw [GL83.PiGen.card_eq_pow_pRank hAscp.2.1, hArk]
  obtain ⟨E₀, hE₀el, hE₀c⟩ := exists_sq_of_three_le hp hp2 hq hout h3
  refine false_of_isSCp hp hK hZ
    (fun y hy hyp => exists_inner_of_pow hp hp2 hq.1 hcen hout hZ hy hyp)
    (fun k hk hkp => exists_elemAbelian_of_quot hp hZ ⟨E₀, hE₀el, hE₀c⟩ hk hkp) hdN ?_
    (hplane_of_planeOK hp hZ fun k hk _ hkd => by
      rw [hsk k hk hkd]
      exact planeOK_Co1 hbr hb e hso ⟨I, hI, hIchev⟩)
    hAscp hdA hAc (Subgroup.mem_inf.1 hz).1 (Subgroup.mem_inf.1 hz).2 hz1'
  by_contra hcon
  push Not at hcon
  apply hs1
  have h1 := hsk 1 K.one_mem (fun x hx => by rw [hcon x hx]; group)
  have h2 : (⟨1, K.one_mem⟩ : ↥K) = 1 := rfl
  rw [h2, map_one] at h1
  exact h1.symm

theorem input25_5Core_of_rowsK
    (hB : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group → Inputs256.SporNoChevTwoDown 5 .B)
    (hM5 : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group → Inputs256.SporNoChevTwoDown 5 .M)
    (hM7 : Inputs256.SporNoChevTwoDown 7 .M) : InputsSeitz.Input25_5Core :=
  input25_5Core_of_factsK CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    (CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_carrier
      CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds)
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    Inputs256.notChev2_of_mem hB hM5 hM7

theorem input25_5RowsK_holds
    : Input25_5RowsK := by
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hT : ∀ (q : ℕ) (name : TauCeti.SporadicName), k2Spor q name → ∀ (T : Type) [Group T],
      catalogIs T (· = .sporadic name) → ¬ IsChevSimple 2 T := by
    rintro q name hk T _ ⟨i, rfl, he⟩
    exact CFSG.LocalAnalysis.GLTheoremA.List93.notChev2_holds T _ (Or.inl ⟨name, rfl, q, hk⟩) he
  refine ⟨fun hK => Inputs255r.sporNoChevTwoDown_of_census Nat.prime_five (hbr .B).some
      (CFSG.HardMathSupport.Dickson.BMRows.census_B_five
        (hK.of_surjective (hbr .B).some.symm.toMonoidHom (hbr .B).some.symm.surjective))
      (hT 5 .HS (by simp [k2Spor])),
    fun hK => Inputs255r.sporNoChevTwoDown_of_census Nat.prime_five (hbr .M).some
      (CFSG.HardMathSupport.Dickson.BMRows.census_M_five
        (hK.of_surjective (hbr .M).some.symm.toMonoidHom (hbr .M).some.symm.surjective))
      (hT 5 .HN (by simp [k2Spor])),
    Inputs255r.sporNoChevTwoDown_of_census (by norm_num) (hbr .M).some
      CFSG.HardMathSupport.Dickson.BMRows.census_M_seven (hT 7 .He (by simp [k2Spor]))⟩

end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporK

end
