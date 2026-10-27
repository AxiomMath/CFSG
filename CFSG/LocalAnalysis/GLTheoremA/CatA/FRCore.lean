module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRDisp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def CoreSub {S : Type} [Group S] (C : Subgroup S) : Prop :=
  ∃ E : Subgroup S, E ≤ C ∧ IsSimpleGroup ↥E ∧ (∃ x y : ↥E, x * y ≠ y * x) ∧
    (∀ T : Subgroup S, T ≤ C → ⁅T, T⁆ = T → T ≤ E) ∧
    twoPart (Nat.card ↥C) ≤ 2 * twoPart (Nat.card ↥E) ∧ (IsChevSimple 2 ↥E ∨ Nat.card ↥E = 168)

theorem eq_core_of_glaPComponent {p : ℕ} {S : Type} [Group S] [Finite S] {C E : Subgroup S}
    (hE : IsSimpleGroup ↥E) (hEC : E ≤ C)
    (hperf : ∀ T : Subgroup S, T ≤ C → ⁅T, T⁆ = T → T ≤ E) {I : Subgroup S}
    (hI : GLAPComponent p C I) : I = E := by
  have hIE : I ≤ E := hperf I hI.1 (glaPComponent_perfect hI)
  have hsn : CFSG.Open.IsSubnormal I E := isSubnormal_of_le_of_le hI.2.1 hIE hEC
  exact (CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn hE).resolve_left
    (glaPComponent_ne_bot' hI)

theorem fixSub_indAut {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    FP.fixSub (indAut p L b hb) = fixSubgroup (chevAut p L ⟨b, hb⟩) := by
  have : indAut p L b hb = (chevAut p L ⟨b, hb⟩)⁻¹ := by
    rw [indAut, ← map_inv]
    rfl
  ext x
  rw [FP.mem_fixSub, mem_fixSubgroup, this]
  constructor
  · intro h
    simpa using (congrArg (chevAut p L ⟨b, hb⟩) h).symm
  · intro h
    exact (MulEquiv.symm_apply_eq _).2 h.symm

variable {G : Type} [Group G] [Finite G]

theorem ipart_eq_sSup {p : ℕ} (X : Subgroup G) :
    GLAPLayer p X = sSup {J | GLAPComponent p X J} := rfl

theorem exists_component_of_ne_bot {p : ℕ} (X : Subgroup G) (h : GLAPLayer p X ≠ ⊥) :
    ∃ J, GLAPComponent p X J := by
  by_contra hc
  push Not at hc
  apply h
  rw [ipart_eq_sSup]
  have : {J | GLAPComponent p X J} = ∅ := Set.eq_empty_iff_forall_notMem.2 fun J hJ => hc J hJ
  rw [this, sSup_empty]

theorem ipart_single {p : ℕ} (hp : p.Prime) {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hbp : b ^ p = 1) {E : Subgroup (PSimple p L)}
    (hE : IsSimpleGroup ↥E) (hEC : E ≤ fixSubgroup (chevAut p L ⟨b, hb⟩))
    (hperf : ∀ T : Subgroup (PSimple p L), T ≤ fixSubgroup (chevAut p L ⟨b, hb⟩) →
      ⁅T, T⁆ = T → T ≤ E)
    (hI : Ipart p L b ≠ ⊥) :
    ∃ J₀ : Subgroup G, GLAPComponent p (L ⊓ cx b) J₀ ∧ Ipart p L b = J₀ ∧
      chevTransfer p L J₀ = E := by
  have hap : IsPGroup p (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hbp
  obtain ⟨J₀, hJ₀⟩ := exists_component_of_ne_bot (L ⊓ cx b) hI
  have hT : ∀ J, GLAPComponent p (L ⊓ cx b) J → chevTransfer p L J = E := fun J hJ =>
    eq_core_of_glaPComponent hE hEC hperf (glaPComponent_chevTransfer hp hb hap hJ)
  refine ⟨J₀, hJ₀, ?_, hT J₀ hJ₀⟩
  rw [Ipart, ipart_eq_sSup]
  have : {J | GLAPComponent p (L ⊓ cx b) J} = {J₀} := Set.ext fun J =>
    ⟨fun hJ => Set.mem_singleton_iff.2 (eq_of_chevTransfer_eq hp hb hap hJ hJ₀
      ((hT J hJ).trans (hT J₀ hJ₀).symm)), fun hJ => (Set.mem_singleton_iff.1 hJ) ▸ hJ₀⟩
  rw [this, sSup_singleton]

theorem center_eq_bot_of_simple_nonab {K : Type*} [Group K] [IsSimpleGroup K] {x y : K}
    (h : x * y ≠ y * x) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h0 | h0
  · exact h0
  · exact absurd (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top x) y).symm h

theorem nonempty_pSimple_equiv_of_simple {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    {C E : Subgroup S} (hE : IsSimpleGroup ↥E) (hna : ∃ x y : ↥E, x * y ≠ y * x)
    (hC : GLAPComponent p C E) : Nonempty (PSimple p E ≃* ↥E) := by
  haveI := hE
  obtain ⟨x, y, hxy⟩ := hna
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hC
  have hN : GLAPPrimeCore p ↥E = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥E) with h0 | h0
    · exact h0
    · exfalso
      haveI : Subsingleton (↥E ⧸ (⊤ : Subgroup ↥E)) := QuotientGroup.subsingleton_quotient_top
      haveI : Subsingleton (PQuot p E) :=
        (QuotientGroup.quotientMulEquivOfEq h0).toEquiv.subsingleton
      haveI : Subsingleton (PQuot p E ⧸ Subgroup.center (PQuot p E)) :=
        QuotientGroup.mk_surjective.subsingleton
      haveI := hq.2
      exact not_subsingleton (PQuot p E ⧸ Subgroup.center (PQuot p E)) inferInstance
  have e₁ : PQuot p E ≃* ↥E :=
    (QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (PQuot p E) := (MulEquiv.isSimpleGroup_congr e₁).mpr inferInstance
  have hZ : Subgroup.center (PQuot p E) = ⊥ :=
    center_eq_bot_of_simple_nonab (x := e₁.symm x) (y := e₁.symm y)
      fun h => hxy (e₁.symm.injective (by simpa using h))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e₁⟩

theorem ipart_of_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hbp : b ^ p = 1)
    (hcore : CoreSub (FP.fixSub (indAut p L b hb))) (hI : Ipart p L b ≠ ⊥) :
    GLAPComponent p (L ⊓ cx b) (Ipart p L b) ∧
      (IsChevSimple 2 (PSimple p (Ipart p L b)) ∨ Nat.card (PSimple p (Ipart p L b)) = 168) ∧
      centCard2 p L b ≤ 2 * card2 p (Ipart p L b) := by
  rw [fixSub_indAut hb] at hcore
  obtain ⟨E, hEC, hE, hna, hperf, h2, hchev⟩ := hcore
  obtain ⟨J₀, hJ₀, hIeq, hTE⟩ := ipart_single hp hb hbp hE hEC hperf hI
  have hap : IsPGroup p (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hbp
  have hEcomp : GLAPComponent p (fixSubgroup (chevAut p L ⟨b, hb⟩)) E :=
    hTE ▸ glaPComponent_chevTransfer hp hb hap hJ₀
  obtain ⟨e₁⟩ := nonempty_pSimple_equiv_of_simple hp hE hna hEcomp
  obtain ⟨e₂⟩ := nonempty_pSimple_equiv_chevTransfer hp hb hap hJ₀
  rw [hTE] at e₂
  have e : PSimple p J₀ ≃* ↥E := e₂.trans e₁
  rw [hIeq]
  refine ⟨hJ₀, ?_, ?_⟩
  · rcases hchev with hchev | hc
    · exact Or.inl (chev_isChevSimple_of_mulEquiv e hchev)
    · exact Or.inr (by rw [Nat.card_congr e.toEquiv]; exact hc)
  rw [FP.card2_eq_twoPart_card_pSimple hp hp2, Nat.card_congr e.toEquiv,
    FP.centCard2_eq_twoPart_fixNum hb (FP.odd_card_center_pQuot hp hp2 L),
    FP.fixNum_eq_card_fixSub, fixSub_indAut hb]
  exact h2

theorem exists_perfect_of_ipart {p : ℕ} (hp : p.Prime) {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hbp : b ^ p = 1) (hI : Ipart p L b ≠ ⊥) :
    ∃ T : Subgroup (PSimple p L), T ≤ FP.fixSub (indAut p L b hb) ∧ ⁅T, T⁆ = T ∧ T ≠ ⊥ := by
  obtain ⟨J, hJ⟩ := exists_component_of_ne_bot (L ⊓ cx b) hI
  have h := glaPComponent_chevTransfer hp hb (isPGroup_zpowers_of_pow_eq_one hbp) hJ
  exact ⟨chevTransfer p L J, by rw [fixSub_indAut hb]; exact h.1, glaPComponent_perfect h,
    glaPComponent_ne_bot' h⟩

end FR

end CFSG.LocalAnalysis.GLTheoremA
