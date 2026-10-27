module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrderDvd443520
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporThreeSmall

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

section General

variable {Q : Type} [Group Q] [Finite Q] {X : Subgroup Q}

theorem subnormal_eq_or_le_center (hX : CFSG.Open.IsQuasisimple ↥X) {H : Subgroup Q}
    (hH : CFSG.Open.IsSubnormal H X) :
    H = X ∨ H ≤ (Subgroup.center ↥X).map X.subtype := by
  induction hH with
  | refl => exact Or.inl rfl
  | @step H M K hHM hn hMK ih =>
    rcases ih hX with rfl | hM
    · rcases CFSG.ASVolI.A129Aux.normal_eq_top_or_le_center hX hn with h | h
      · left
        apply le_antisymm hHM
        intro x hx
        have : (⟨x, hx⟩ : ↥M) ∈ H.subgroupOf M := h ▸ Subgroup.mem_top _
        exact this
      · right
        intro x hx
        exact ⟨⟨x, hHM hx⟩, h hx, rfl⟩
    · exact Or.inr (hHM.trans hM)

theorem glaPComponent_eq_of_quasisimple (hX : CFSG.Open.IsQuasisimple ↥X) {p : ℕ}
    {I : Subgroup Q} (hI : GLAPComponent p X I) : I = X := by
  rcases subnormal_eq_or_le_center hX hI.2.1 with h | h
  · exact h
  · exfalso
    apply CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hI
    have hperf := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_perfect hI
    have hcomm : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := h ha
      obtain ⟨b', -, rfl⟩ := h hb
      have := Subgroup.mem_center_iff.1 ha' b'
      simp only [Subgroup.coe_subtype]
      exact congrArg Subtype.val this.symm
    rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def, hcomm a ha b hb, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _

noncomputable def pSimple_equiv_center_quot (hX : CFSG.Open.IsQuasisimple ↥X) {p : ℕ}
    (hs : IsSimpleGroup (PSimple p X)) : (↥X ⧸ Subgroup.center ↥X) ≃* PSimple p X := by
  haveI := hX.2
  let π : ↥X →* PSimple p X :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p X))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥X))
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hZ : Subgroup.center ↥X ≤ π.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' (Subgroup.center (PQuot p X)))
      ((QuotientGroup.mk' (GLAPPrimeCore p ↥X)) z) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥X) g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
  let φ : (↥X ⧸ Subgroup.center ↥X) →* PSimple p X := QuotientGroup.lift _ π hZ
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (PSimple p X)).exists_pair_ne
      obtain ⟨a, rfl⟩ := hφs a
      obtain ⟨b, rfl⟩ := hφs b
      apply hab
      have ha : a ∈ φ.ker := h ▸ Subgroup.mem_top a
      have hb : b ∈ φ.ker := h ▸ Subgroup.mem_top b
      rw [MonoidHom.mem_ker] at ha hb
      rw [ha, hb]
  exact MulEquiv.ofBijective φ ⟨hφi, hφs⟩

end General

open CFSG.Open in
theorem not_isChevSimple_M22 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] (hT : Nat.card T = 443520) (q : ℕ) : ¬ IsChevSimple q T :=
  CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_not_lieOrder hb hT
    (fun d hd => OrderDvd443520.lieOrderFormula_ne_443520 hd) (by decide) (by decide) (by decide) q

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows

namespace CFSG.Sporadic.J4

open CFSG.Sporadic.J4Schreier

set_option maxRecDepth 100000 in
theorem not_prime_card_J : ¬ (Nat.card ↥J).Prime := by
  have h2 : 2 ∣ Nat.card ↥J := by
    rw [card_J_eq]
    exact Dvd.intro (2 ^ 20 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43) (by ring)
  intro hpr
  rcases hpr.eq_one_or_self_of_dvd 2 h2 with h | h
  · norm_num at h
  · rw [card_J_eq] at h
    norm_num at h

set_option maxRecDepth 100000 in
theorem j4_model
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    Finite ↥J ∧ IsSimpleGroup ↥J ∧ (∃ a c : ↥J, a * c ≠ c * a) ∧
      Nonempty (↥J ≃* (TauCeti.CFSGIndex.sporadic .J4).Group) := by
  haveI hJs : IsSimpleGroup ↥J := isSimpleGroup_J j4Facts
  exact ⟨inferInstance, hJs,
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥J _ inferInstance hJs
      not_prime_card_J,
    ⟨(seedEquiv j4Facts.mat).symm.trans (hbr .J4).some⟩⟩

end CFSG.Sporadic.J4

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2
  CFSG.Quasithin.J4Loc CFSG.AGLEmbeddingD2.Wilson.Coordinator CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77 CFSG.Sporadic.J4.Native
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.GLQ Subgroup
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem centralizer_cE_open :
    CFSG.Open.IsQuasisimple ↥(centralizer ({cE} : Set J)) ∧
      Nonempty (↥(centralizer ({cE} : Set J)) ⧸ center ↥(centralizer ({cE} : Set J)) ≃*
        CFSG.Blueprint.NativeSporadic.M22) := by
  obtain ⟨hq, -, he⟩ := centralizer_cE_quasisimple j4Facts
  exact ⟨⟨hq.1.commutator_eq_top, hq.2.1⟩, he⟩

theorem pSimple_of_glaPComponent_cE {p : ℕ} (hp : p.Prime) {I : Subgroup J}
    (hI : GLAPComponent p (centralizer ({cE} : Set J)) I) :
    Nonempty (PSimple p I ≃* CFSG.Blueprint.NativeSporadic.M22) := by
  obtain ⟨hq, ⟨e⟩⟩ := centralizer_cE_open
  have hIC := glaPComponent_eq_of_quasisimple hq hI
  subst hIC
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J_eq]; norm_num)
  obtain ⟨hs, -⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab hp hI
  exact ⟨(pSimple_equiv_center_quot hq hs).symm.trans e⟩

theorem pSimple_of_glaPComponent_three {p : ℕ} (hp : p.Prime) {x : J} (hx : orderOf x = 3)
    {I : Subgroup J} (hI : GLAPComponent p (centralizer ({x} : Set J)) I) :
    Nonempty (PSimple p I ≃* CFSG.Blueprint.NativeSporadic.M22) := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J_eq]; norm_num)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx; norm_num at hx
  obtain ⟨g, hg⟩ := exists_conj_cE_of_orderThree x hx3 hx1
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp (MulAut.conj g) hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv, MulAut.conj_apply, hg] at hI'
  obtain ⟨e⟩ := pSimple_of_glaPComponent_cE hp hI'
  exact ⟨(CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).trans e⟩

theorem row_J4_three (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : I1416SporRow .J4 3 := by
  obtain ⟨hfin, hJs, hnc, ⟨b⟩⟩ := CFSG.Sporadic.J4.j4_model hbr
  have hM : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  haveI : Finite CFSG.Blueprint.NativeSporadic.M22 :=
    Nat.finite_of_card_ne_zero (by rw [hM]; norm_num)
  refine @row_of_model .J4 3 J _ hfin hJs hOut b hnc fun x hx I hI => ?_
  obtain ⟨e⟩ := pSimple_of_glaPComponent_three Nat.prime_three hx hI
  exact TypeOK.of_mulEquiv e.symm (typeOK_of_not_chev (not_isChevSimple_M22 hb hM 2))

theorem qrow_J4_three (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.I1416QRow .J4 3 := by
  obtain ⟨hfin, hJs, hnc, ⟨b⟩⟩ := CFSG.Sporadic.J4.j4_model hbr
  have hM : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  haveI : Finite CFSG.Blueprint.NativeSporadic.M22 :=
    Nat.finite_of_card_ne_zero (by rw [hM]; norm_num)
  refine @CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qrow_of_model .J4 3 J _ hfin hJs hOut b hnc
    fun x hx I hI => ?_
  obtain ⟨e⟩ := pSimple_of_glaPComponent_three Nat.prime_three hx hI
  exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.QTypeOK.of_mulEquiv e.symm
    (CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qtypeOK_of_not_chev fun q _ _ _ =>
      not_isChevSimple_M22 hb hM q)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
