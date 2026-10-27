module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporFacts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.McLThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.LyFive
public import CFSG.HardMathSupport.Dickson.KD.CharP

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicOnePair OffPair SporadicBridges)

@[expose] def InputI2711SporPairs : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (L B : Subgroup X),
    CFSG.IsKGroup ↥L → CFSG.Open.IsQuasisimple ↥L → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    (¬ ∃ n : ℕ, IsAltType n (↥L ⧸ Subgroup.center ↥L)) →
    (¬ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥L ⧸ Subgroup.center ↥L)) →
    (∃ A : Subgroup (MulAut ↥L), IsElemAbelian p A ∧ 3 ≤ CFSG.Open.pRank p A) →
    CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1 →
    ∀ name : TauCeti.SporadicName, IsSporType name (↥L ⧸ Subgroup.center ↥L) →
    SporadicOnePair name p → ¬ (name = .McL ∧ p = 3) → ¬ (name = .Ly ∧ p = 5) →
    (∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) →
    ∀ J0 : Subgroup X,
      CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)) →
      ((∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) J0) ∨ (∃ k : ℕ, IsAltType (k * p + 2) J0) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
          Nonempty (↥J0 ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
            (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J0 ∧
          HasFixedPointFreeOrder ε n p)) →
      ¬ (p = 3 ∧ IsAltType 5 J0) →
    ∀ E : Subgroup X, E ≤ B → B ⊓ Subgroup.centralizer (L : Set X) ≤ E →
      Nat.card B ≤ p ^ 2 * Nat.card E →
      GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      2 ≤ CFSG.Open.pRank p E →
      GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      (∀ e ∈ E, GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥) →
      L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)

section Pairs

theorem sporadicOnePair_of_autRank {L : Type} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hBr : SporadicBridges) (hOff : ∀ s, OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hLq : CFSG.Open.IsQuasisimple L) {name : TauCeti.SporadicName}
    (hname : IsSporType name (L ⧸ Subgroup.center L))
    (hA : ∃ A : Subgroup (MulAut L), IsElemAbelian p A ∧ 3 ≤ CFSG.Open.pRank p A) :
    SporadicOnePair name p := by
  by_contra hnot
  obtain ⟨f⟩ := hname
  obtain ⟨g⟩ := hBr name
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hLq.2
  have hnab := CFSG.HardMathSupport.Solomon.Coordinator.exists_noncomm_of_isQuasisimple hLq
  have hout := hOut (L ⧸ Subgroup.center L) inferInstance hnab name ⟨f⟩
  have h2 := SporFacts.pRank_aut_le_two_of_offPair hp hp2 hLq hnot (hOff name) (f.trans g.symm) hout
  obtain ⟨A, -, hA3⟩ := hA
  have h3 := CFSG.SectionRank.pRank_mono hp.one_lt (le_top : A ≤ ⊤)
  omega

end Pairs

section Transfer

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem inf_centralizer_eq_of_inner {L : Subgroup X} {e k : X}
    (hc : k⁻¹ * e ∈ Subgroup.centralizer (L : Set X)) :
    L ⊓ Subgroup.centralizer ({e} : Set X) = L ⊓ Subgroup.centralizer ({k} : Set X) := by
  have key : ∀ y ∈ L, (e * y = y * e ↔ k * y = y * k) := by
    intro y hy
    have hcy : Commute (k⁻¹ * e) y := (Subgroup.mem_centralizer_iff.1 hc y hy).symm
    have hcy' : (k⁻¹ * e)⁻¹ * y = y * (k⁻¹ * e)⁻¹ := hcy.inv_left.eq
    constructor
    · intro h
      calc k * y = e * ((k⁻¹ * e)⁻¹ * y) := by group
        _ = e * (y * (k⁻¹ * e)⁻¹) := by rw [hcy']
        _ = (e * y) * (k⁻¹ * e)⁻¹ := by group
        _ = (y * e) * (k⁻¹ * e)⁻¹ := by rw [h]
        _ = y * k := by group
    · intro h
      calc e * y = k * ((k⁻¹ * e) * y) := by group
        _ = k * (y * (k⁻¹ * e)) := by rw [hcy.eq]
        _ = (k * y) * (k⁻¹ * e) := by group
        _ = (y * k) * (k⁻¹ * e) := by rw [h]
        _ = y * e := by group
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun ⟨hy, h⟩ => ⟨hy, ((key y hy).1 h.symm).symm⟩,
    fun ⟨hy, h⟩ => ⟨hy, ((key y hy).2 h.symm).symm⟩⟩

theorem exists_glaPComponent_quot_of_inner (hp : p.Prime) {L : Subgroup X} {e k : X} (hk : k ∈ L)
    (hc : k⁻¹ * e ∈ Subgroup.centralizer (L : Set X))
    (hl : GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥) :
    ∃ I : Subgroup (↥L ⧸ Subgroup.center ↥L), GLAPComponent p
      (Subgroup.centralizer ({(QuotientGroup.mk (⟨k, hk⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)} :
        Set (↥L ⧸ Subgroup.center ↥L))) I := by
  obtain ⟨J, hJ⟩ := Inputs2711.exists_glaPComponent_of_ne_bot hl
  rw [inf_centralizer_eq_of_inner hc] at hJ
  have hJ' := Lemma1315b.glaPComponent_subgroupOf hp
    (inf_le_left : L ⊓ Subgroup.centralizer ({k} : Set X) ≤ L) hJ
  have hfix : (L ⊓ Subgroup.centralizer ({k} : Set X)).subgroupOf L =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj (⟨k, hk⟩ : ↥L)) := by
    rw [Inputs1415.fixSubgroup_conj]
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨y.2, congrArg Subtype.val h⟩
  rw [hfix] at hJ'
  obtain ⟨hI, -⟩ := Inputs1415.center_transfer hp _ hJ'
  have hcq : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L
      (MulAut.conj (⟨k, hk⟩ : ↥L)) =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) := by
    ext z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) z
    have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
      (MulAut.conj (⟨k, hk⟩ : ↥L)) y
    refine h1.trans ?_
    simp [MulAut.conj_apply]
  rw [hcq, Inputs1415.fixSubgroup_conj] at hI
  exact ⟨_, hI⟩

theorem false_of_constrainedShape (hp : p.Prime) (hBr : SporadicBridges) {name : TauCeti.SporadicName}
    (hsh : CFSG.HardMathSupport.Dickson.I271.ConstrainedShape name p) {L : Subgroup X}
    (hname : IsSporType name (↥L ⧸ Subgroup.center ↥L)) {e k : X} (hep : e ^ p = 1) (hk : k ∈ L)
    (hc : k⁻¹ * e ∈ Subgroup.centralizer (L : Set X)) (he : e ∉ Subgroup.centralizer (L : Set X))
    (hl : GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥) : False := by
  obtain ⟨I, hI⟩ := exists_glaPComponent_quot_of_inner hp hk hc hl
  obtain ⟨f⟩ := hname
  obtain ⟨g⟩ := hBr name
  let σ : (↥L ⧸ Subgroup.center ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier name := f.trans g.symm
  set s : ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk (⟨k, hk⟩ : ↥L) with hs
  have hs1 : s ≠ 1 := fun h =>
    Inputs2711.not_mem_center_of_inner hk hc he ((QuotientGroup.eq_one_iff _).1 h)
  have hsp : s ^ p = 1 := by
    rw [hs, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Inputs2711.pow_mem_center_of_inner hep hk hc
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ hI
  have hmap : (Subgroup.centralizer ({s} : Set (↥L ⧸ Subgroup.center ↥L))).map σ.toMonoidHom =
      Subgroup.centralizer ({σ s} : Set (CFSG.Blueprint.NativeSporadic.Carrier name)) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
      apply σ.injective
      rw [map_mul, map_mul, σ.apply_symm_apply, hy]
  rw [hmap] at hI'
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier name) := Finite.of_equiv _ σ.toEquiv
  have hσ1 : σ s ≠ 1 := fun h => hs1 (σ.injective (h.trans (map_one σ).symm))
  have hσp : σ s ^ p = 1 := by rw [← map_pow, hsp, map_one]
  exact CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape hp
    (hsh (σ s) hσ1 hσp) hI'

theorem exists_not_mem_centralizer (hp : p.Prime) {B E L : Subgroup X} (hEB : E ≤ B)
    (hE2 : 2 ≤ CFSG.Open.pRank p E) (hC1 : CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1) :
    ∃ e ∈ E, e ∉ Subgroup.centralizer (L : Set X) := by
  by_contra h
  push Not at h
  have hle : E ≤ B ⊓ Subgroup.centralizer (L : Set X) := fun e he => ⟨hEB he, h e he⟩
  have := CFSG.SectionRank.pRank_mono hp.one_lt hle
  omega

end Transfer

section Reduction

theorem inputI2711SporInner_of_pairs
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hOff : ∀ s, OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hMcL : CFSG.HardMathSupport.Dickson.I271.ConstrainedShape .McL 3)
    (hLy : CFSG.HardMathSupport.Dickson.I271.ConstrainedShape .Ly 5) (h : InputI2711SporPairs) :
    Inputs2711.InputI2711SporInner := by
  intro X _ _ p hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA hC1 hS hin J0 hJ0 hJt hJ5 E hEB hEC hEi hEl
    hE2 hlE hle
  obtain ⟨name, hname⟩ := hS
  obtain ⟨e, he, heC⟩ := exists_not_mem_centralizer hp hEB hE2 hC1
  obtain ⟨k, hk, hc⟩ := hin e (hEB he)
  have hep : e ^ p = 1 := hB.2 e (hEB he)
  have hex : ∀ (n : TauCeti.SporadicName) (r : ℕ),
      CFSG.HardMathSupport.Dickson.I271.ConstrainedShape n r → ¬ (name = n ∧ p = r) := by
    rintro n r hsh ⟨rfl, rfl⟩
    exact false_of_constrainedShape hp hBr hsh hname hep hk hc heC (hle e he)
  exact h X p hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA hC1 name hname
    (sporadicOnePair_of_autRank hp hp2 hOut hBr hOff hLq hname hA) (hex _ _ hMcL) (hex _ _ hLy) hin J0
    hJ0 hJt hJ5 E hEB hEC hEi hEl hE2 hlE hle

end Reduction

section Certified

theorem inputI2711ChevPSpor_of_outer_pairs (hC : Inputs2711.InputI2711ChevPOuter)
    (hS : InputI2711SporPairs) : Inputs27.InputI2711ChevPSpor :=
  Inputs2711.inputI2711ChevPSpor_of_residuals
    (fun G _ _ p hp => CFSG.LocalAnalysis.GLTheoremA.lBalanceAt_holds G p hp)
    (fun p hp hp2 => CFSG.LocalAnalysis.GLTheoremA.kdChevInner_of hp hp2
      (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds hp hp2)
      (CFSG.LocalAnalysis.GLTheoremA.kdAmbSolv_holds hp hp2
        CFSG.LocalAnalysis.GLTheoremA.u42_fixSubgroup_solvable))
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.HardMathSupport.Timmesfeld.DefChar.lieOuterRank_proved hC
    (inputI2711SporInner_of_pairs CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      (CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_carrier
        CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds)
      (CFSG.HardMathSupport.Dickson.I271.mcl_constrainedShape_three
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL)
      (fun k hk1 hk5 => CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_Ly_five _
        ⟨MulEquiv.refl _⟩ (orderOf_eq_prime hk5 hk1)) hS)

end Certified

@[expose] def InputI2711Rest : Prop := Inputs2711.InputI2711ChevPOuter ∧ InputI2711SporPairs

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711b
