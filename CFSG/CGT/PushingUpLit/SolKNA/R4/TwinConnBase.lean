module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinReduce
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecConj

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

structure TwinStdR (r n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y)
    (S : Sylow 2 R) (t : Y) : Prop where
  card : Nat.card Y = n
  simple : IsSimpleGroup ↥(genFittingFStar Y)
  nonab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a
  datum : Q8TwinDatum R S t
  quat : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))
  gen : TightSelfGen R
  oddFree : TightOddFree Y
  hyp : HypOmegaGen (CoreAssembly.conjClass (tightCore R))
  aEmpty : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  twin : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R

section Std

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {r n : ℕ}

theorem TwinStdR.conj (h : TwinStdR r n Y R S t) (g : Y) :
    ∃ S' : Sylow 2 ↥(conjSub g R), TwinStdR r n Y (conjSub g R) S' (g * t * g⁻¹) := by
  obtain ⟨S', hd', ⟨e'⟩⟩ := TwinEdge.conjDatum h.datum g
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hΩ := h.hyp.conjInvariant
  refine ⟨S', ⟨h.card, h.simple, h.nonab, hd', ⟨e'.trans h.quat.some⟩, ?_, h.oddFree, ?_, ?_, ?_⟩⟩
  · have hgen : (⨆ x : Y, conjSub x (tightCore R)) = ⊤ := h.gen
    unfold TightSelfGen
    rw [← conjSub_tightCore, eq_top_iff, ← hgen]
    refine iSup_le fun x => ?_
    have : conjSub x (tightCore R) = conjSub (x * g⁻¹) (conjSub g (tightCore R)) := by
      rw [← conjSub_mul]
      simp
    rw [this]
    exact le_iSup (fun y : Y => conjSub y (conjSub g (tightCore R))) (x * g⁻¹)
  · rw [hfam]
    exact h.hyp
  · rw [hfam, ← conjSub_tightCore]
    exact aEmpty_conj h.hyp.conjInvariant h.aEmpty g
  · rw [hfam, ← conjSub_tightCore]
    obtain ⟨K', hK', hne⟩ := h.twin
    refine ⟨conjSub g K', twinSet_conj h.hyp.conjInvariant hK' g, fun heq => hne ?_⟩
    exact Generic.conjSub_injective g heq

theorem TwinStdR.core (h : TwinStdR r n Y R S t) :
    ∃ S₀ : Sylow 2 ↥(tightCore R), TwinStdR r n Y (tightCore R) S₀ t := by
  obtain ⟨S₀, hd₀, ⟨e₀⟩⟩ := TwinEdge.toCore h.datum
  have hid := TwinEdge.tightCore_idem R
  refine ⟨S₀, ⟨h.card, h.simple, h.nonab, hd₀, ⟨e₀.trans h.quat.some⟩, ?_, h.oddFree, ?_, ?_, ?_⟩⟩
  · unfold TightSelfGen
    rw [hid]
    exact h.gen
  · rw [hid]
    exact h.hyp
  · rw [hid]
    exact h.aEmpty
  · rw [hid]
    exact h.twin

theorem exists_datum_atR (h : TwinStdR r n Y R S t) (hRc : tightCore R = R) {M : Subgroup Y}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) {z : Y} (hz : IsUniqueInvolution M z) :
    ∃ S' : Sylow 2 ↥M, TwinStdR r n Y M S' z := by
  obtain ⟨g, rfl⟩ := hM
  have hz' : g * t * g⁻¹ = z :=
    ((Q8Datum.isUniqueInvolution_core h.datum).conj g).eq hz
  rw [hRc]
  rw [hRc] at hz
  obtain ⟨S', hh⟩ := h.conj g
  rw [hz'] at hh
  exact ⟨S', hh⟩

end Std

section Fam

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem quatSylow_quot_odd {k : ℕ} {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N))
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup k)) :
    ∀ L ∈ quotFamily Ω N, ∃ P : Subgroup (G ⧸ N),
      IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup k) := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hq K hK
  have hPN : P ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hP.2.1 hP.1 (odd_natCard_inf hN K)
  exact ⟨P.map (QuotientGroup.mk' N), isSylow2In_map_mk hN hP,
    ⟨(AscQuot.quotRestrictEquiv hPN).symm.trans e⟩⟩

theorem restrictCFam_quat {k : ℕ} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup k))
    (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :
    ∀ L ∈ restrictFamily (cFam Ω c) X, ∃ P : Subgroup ↥X, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup k) := by
  rintro _ ⟨_, ⟨_, ⟨M, hM, rfl⟩, -, rfl⟩, hMX, rfl⟩
  obtain ⟨P, hP, hPc⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hM.2
  have hPs : IsSylow2In P (TwinADescent.coreAt c M) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hM.2).mpr ⟨hP, hPc⟩
  obtain ⟨e⟩ := hq M hM.1 P hP
  have hs1 : IsSylow2In (P.subgroupOf (Subgroup.centralizer ({c} : Set G)))
      ((TwinADescent.coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G))) :=
    hPs.subgroupOf (TwinADescent.coreAt_le_centralizer c M)
  have hs2 := hs1.subgroupOf hMX
  refine ⟨_, hs2, ⟨?_⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe (hs1.1.trans hMX)).trans
    ((Subgroup.subgroupOfEquivOfLe hPc).trans e)

theorem famX_quat {k : ℕ} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup k))
    (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :
    ∀ J ∈ famX Ω c X, ∀ P : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X),
      IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup k) := by
  intro J hJ
  apply forall_sylow_iso_of_exists
  exact quatSylow_quot_odd (CFSG.ComponentClassification.OddCore.odd_card ↥X)
    (restrictCFam_quat hc2 hq X) J hJ

theorem thm4_famX_R {r n : ℕ} (h4 : Thm4RTwinBelow r n) (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G)))
    (hlt : Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) < n) :
    ∀ J ∈ famX Ω c X, ∀ L ∈ famX Ω c X,
      (¬ ∃ g : ↥X ⧸ classicalInvolutionOddCore ↥X, conjSub g J = L) → Commutes J L :=
  h4 _ hlt (famX Ω c X) (famX_hyp hΩ hc2 X) (famX_twoGroup h2 X) (famX_quat hc2 hq X)
    (TwinADescent3.aEmpty_quot_coreFamily hΩ hA hc2 X)
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥X)

end Fam

section InO2

@[expose] def Thm1RTwinInO2 (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) → TightSelfGen R →
      TightOddFree Y → HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → TightInO2 t

theorem thm1RTwinInO2_of_below {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (h : Thm1RTwinBelowR r n) :
    Thm1RTwinInO2 r n := by
  intro Y _ _ hlt R S t hd hq hg hO hΩ hA htw
  rcases h Y hlt R S t hd hq hg hO hΩ hA htw with h1 | h1
  · exact h1
  · exact tightInO2_of_twinE4' hr hNo hd hq h1

end InO2

end CFSG.CGT.PushingUpLit.SolKNA.R4
