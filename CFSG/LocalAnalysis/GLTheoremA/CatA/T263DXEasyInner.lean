module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXFam
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalOuter
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerOrder
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOut
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6Out
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutE6Untw
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms
  (Outer congr_mem_inner_iff inner innAutDerived mem_innAutDerived_congr)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (t6outtrid4_commutator_le_range)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (exists_catEquiv_trialityD4
  twistedE6Inndiag_eq_inn_of_mod_three)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (untwistedChevalleyModel_of_bridge)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (inner_of_pow_three_adjointE6
  mem_inndiag_of_mem_innAutDerived_twistedE6 mem_inner_of_mem_innAutDerived_of_outPNice
  mem_inner_of_mem_innAutDerived_of_pow_eq_one_twistedE6)
open CFSG.LieType.SeitzGeneration (exists_catEquiv_adjointGroup exists_catEquiv_twistedE6)
open CFSG.RankThree.PartOne.OutStructure (OutPNice outPNice_E6_gen outPNice_E7_gen outPNice_E8_gen
  outPNice_of_isCyclic_outer)
open CFSG.TauCetiBridge.Even (chevalleyBridgesAll)


@[expose] def t263GExcInner (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E7 q | .E8 q | .F4 q | .G2 q => q.p = 2
    | _ => False

@[expose] def t263GE6Inner (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q => q.p = 2 ∧ ¬ (p = 3 ∧ 3 ∣ q.card - 1)
    | .twistedE6 q => q.p = 2 ∧ ¬ (p = 3 ∧ 3 ∣ q.card + 1)
    | _ => False

@[expose] def t263GTD4Inner (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .trialityD4 q => q.p = 2
    | _ => False

theorem mem_inner_of_pow_of_isPGroup_two_outer {R : Type} [Group R]
    (h : IsPGroup 2 (Outer R)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut R}
    (hα : α ^ p = 1) : α ∈ inner R := by
  obtain ⟨k, hk⟩ := h (QuotientGroup.mk α)
  have h1 : (QuotientGroup.mk α : Outer R) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hord := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one hk)
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 hord)

private theorem inducesInnerMod_of_model {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type}
    [Group Ω] [Finite Ω] {S : Subgroup Ω} {x : Ω} (hSn : S.Normal)
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) {M : Type} [Group M]
    (e : ↥S ⧸ Subgroup.center ↥S ≃* M)
    (hM : ∀ a : MulAut M, a ∈ innAutDerived M → a ^ p = 1 → a ∈ inner M) :
    InducesInnerMod p S x := by
  have hx : x ∈ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top x
  have hL : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  have hqS : CFSG.Open.IsQuasisimple (PQuot p S) := isQuasisimple_pQuot_of_glaPComponent hp hL
  obtain ⟨labL, hLabQuot, hinDiag⟩ := I141F.innDiagKind_chevAut hx hqS hInn
  have hcen : Subgroup.center (PSimple p S) = ⊥ := Y10F.center_centerQuot_eq_bot hqS
  haveI : Group.IsPerfect (PQuot p S) := ⟨hqS.1⟩
  have hperf : commutator (PSimple p S) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot p S)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  have hLabPS : Y10F.HasLabel (PSimple p S) (· = labL) :=
    Y10F.hasLabel_of_equiv_centerQuot hperf
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm hLabQuot
  have hαp : chevAut p S ⟨x, hx⟩ ^ p = 1 := chevAut_pow_eq_one p S hx hxp
  have hinner : chevAut p S ⟨x, hx⟩ ∈ inner (PSimple p S) := by
    by_cases hder : labL.tag = .B2der ∨ labL.tag = .G2der ∨ labL.tag = .twF4der
    · have hMq : CFSG.StandardType.MarkedModel labL
          (PSimple p S ⧸ Subgroup.center (PSimple p S)) :=
        CanonSubcomp.markedModel_of_hasLabel hLabPS
      let eZ : PSimple p S ⧸ Subgroup.center (PSimple p S) ≃* PSimple p S :=
        (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
      exact mem_inner_of_pow_of_isPGroup_two_outer
        (T2021.t2021Layer_isPGroup_outer hder (hMq.of_mulEquiv eZ)) hp hp2 hαp
    · rw [not_or, not_or] at hder
      have hα : chevAut p S ⟨x, hx⟩ ∈ innAutDerived (PSimple p S) :=
        I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived hcen hder hinDiag
      let eP : PSimple p S ≃* M := (pSimpleEquiv hSp).trans e
      have h1 : MulAut.congr eP (chevAut p S ⟨x, hx⟩) ∈ innAutDerived M :=
        (mem_innAutDerived_congr eP).2 hα
      have h2 : (MulAut.congr eP (chevAut p S ⟨x, hx⟩)) ^ p = 1 := by
        rw [← map_pow, hαp, map_one]
      exact (congr_mem_inner_iff eP _).1 (hM _ h1 h2)
  exact (chevAut_mem_inner_iff hp hL hx).1 hinner

private theorem inducesInnerMod_of_outPNice {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type}
    [Group Ω] [Finite Ω] {S : Subgroup Ω} {x : Ω} (hSn : S.Normal)
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (h : OutPNice p (↥S ⧸ Subgroup.center ↥S)) :
    InducesInnerMod p S x := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact inducesInnerMod_of_model hp hp2 hSn hSq hSp hxp hInn (MulEquiv.refl _) fun a ha hap =>
    mem_inner_of_mem_innAutDerived_of_outPNice h ha hap

theorem inducesInnerMod_excInner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hcat : catalogIs (↥S ⧸ Subgroup.center ↥S) (t263GExcInner p)) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) : InducesInnerMod p S x := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | E7 q =>
      have hm : ChevalleyExceptionalModel (↥S ⧸ Subgroup.center ↥S) .E7 q.p q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          untwistedChevalleyModel_of_bridge chevalleyBridgesAll.e7 e⟩
      exact inducesInnerMod_of_outPNice hp hp2 hSn hSq hSp hxp hInn (outPNice_E7_gen hp hp2 hm)
    | E8 q =>
      have hm : ChevalleyExceptionalModel (↥S ⧸ Subgroup.center ↥S) .E8 q.p q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          untwistedChevalleyModel_of_bridge chevalleyBridgesAll.e8 e⟩
      exact inducesInnerMod_of_outPNice hp hp2 hSn hSq hSp hxp hInn (outPNice_E8_gen hp hm)
    | F4 q =>
      have hm : UntwistedChevalleyModel (↥S ⧸ Subgroup.center ↥S) .F4 (q.p ^ q.exponent) :=
        untwistedChevalleyModel_of_bridge chevalleyBridgesAll.f4 e
      exact inducesInnerMod_of_outPNice hp hp2 hSn hSq hSp hxp hInn
        (outPNice_of_isCyclic_outer hp
          (GL83.I713.isCyclic_outer_of_untwistedModel_F4 q.prime_p q.exponent_pos hm))
    | G2 q =>
      have hq3 : 3 ≤ q.p ^ q.exponent := by
        rw [← TauCeti.PrimePower.card_def]
        exact (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
          ((TauCeti.LieTypeIndex.valid_iff (.G2 q)).1 hv).1
      have hm : UntwistedChevalleyModel (↥S ⧸ Subgroup.center ↥S) .G2 (q.p ^ q.exponent) :=
        untwistedChevalleyModel_of_bridge chevalleyBridgesAll.g2 e
      exact inducesInnerMod_of_outPNice hp hp2 hSn hSq hSp hxp hInn
        (outPNice_of_isCyclic_outer hp
          (GL83.I713.isCyclic_outer_of_untwistedModel_G2 q.prime_p q.exponent_pos hq3 hm))
    | _ => exact absurd hi (by simp only [t263GExcInner, onLie, not_false_eq_true])
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

theorem inducesInnerMod_e6Inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hcat : catalogIs (↥S ⧸ Subgroup.center ↥S) (t263GE6Inner p)) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) : InducesInnerMod p S x := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | E6 q =>
      simp only [t263GE6Inner, onLie] at hi
      by_cases hp3 : p = 3
      · subst hp3
        have h3 : ¬ 3 ∣ q.card - 1 := fun h => hi.2 ⟨rfl, h⟩
        refine inducesInnerMod_of_model hp hp2 hSn hSq hSp hxp hInn e fun a ha ha3 => ?_
        obtain ⟨K, hfield, hfin, hK, -, ⟨eA⟩⟩ :=
          exists_catEquiv_adjointGroup chevalleyBridgesAll.e6 q hv
        letI := hfield
        letI := hfin
        have hK' : Nat.card K = q.p ^ q.exponent := hK.trans q.card_def
        have h3K : ¬ 3 ∣ Nat.card K - 1 := by
          rw [hK]
          exact h3
        have ha' : MulAut.congr eA a ∈ innAutDerived (adjointGroup Tag.E6 K) :=
          (mem_innAutDerived_congr eA).2 ha
        have ha3' : (MulAut.congr eA a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
        exact (congr_mem_inner_iff eA a).1
          (inner_of_pow_three_adjointE6 q.prime_p hK' h3K ha' ha3')
      · have hm : ChevalleyExceptionalModel (↥S ⧸ Subgroup.center ↥S) .E6 q.p q.exponent :=
          ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
            untwistedChevalleyModel_of_bridge chevalleyBridgesAll.e6 e⟩
        exact inducesInnerMod_of_outPNice hp hp2 hSn hSq hSp hxp hInn
          (outPNice_E6_gen hp hp3 hp2 hm)
    | twistedE6 q =>
      simp only [t263GE6Inner, onLie] at hi
      obtain ⟨K, hfield, σ, hK, hσ, ⟨eC⟩⟩ := exists_catEquiv_twistedE6 q hv
      letI := hfield
      haveI : Finite K := Nat.finite_of_card_ne_zero (by
        rw [hK]
        exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
      by_cases hp3 : p = 3
      · subst hp3
        have h3 : ¬ 3 ∣ q.card + 1 := fun h => hi.2 ⟨rfl, h⟩
        have h3' : ¬ 3 ∣ q.card := by
          rw [TauCeti.PrimePower.card_def, hi.1]
          exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
        have hq1 : q.p ^ q.exponent % 3 = 1 := by
          rw [← TauCeti.PrimePower.card_def]
          omega
        have hKf : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
        refine inducesInnerMod_of_model hp hp2 hSn hSq hSp hxp hInn (e.trans eC) fun a ha _ => ?_
        have hx := mem_inndiag_of_mem_innAutDerived_twistedE6 q.prime_p q.exponent_pos hK σ hσ ha
        rw [twistedE6Inndiag_eq_inn_of_mod_three K hKf σ hσ hq1] at hx
        exact hx
      · exact inducesInnerMod_of_model hp hp2 hSn hSq hSp hxp hInn (e.trans eC) fun a ha hap =>
          mem_inner_of_mem_innAutDerived_of_pow_eq_one_twistedE6 q.prime_p q.exponent_pos hK σ
            hσ hp hp3 ha hap
    | _ => exact absurd hi (by simp only [t263GE6Inner, onLie, not_false_eq_true])
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

theorem inducesInnerMod_td4Inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hcat : catalogIs (↥S ⧸ Subgroup.center ↥S) (t263GTD4Inner p)) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) : InducesInnerMod p S x := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | trialityD4 q =>
      obtain ⟨K, hfield, hfin, σ, hK, hσ, -, ⟨eC⟩⟩ := exists_catEquiv_trialityD4 q hv
      letI := hfield
      letI := hfin
      exact inducesInnerMod_of_model hp hp2 hSn hSq hSp hxp hInn (e.trans eC) fun a ha _ =>
        sup_le le_rfl (t6outtrid4_commutator_le_range q.prime_p q.exponent_pos hK σ hσ) ha
    | _ => exact absurd hi (by simp only [t263GTD4Inner, onLie, not_false_eq_true])
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

private theorem t263GExcInner_of_easy {p : ℕ} {i : TauCeti.CFSGIndex} (h : t263GExcEasy p i) :
    t263GExcInner p i := by
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;> simp only [t263GExcEasy, t263GExcInner, onLie] at h ⊢ <;>
      first | exact h.elim | exact h.1
  | cyclic r hr => exact h.elim
  | alternating n hn => exact h.elim
  | sporadic s => exact h.elim

private theorem t263GE6Inner_of_easy {p : ℕ} {i : TauCeti.CFSGIndex} (h : t263GE6Easy p i) :
    t263GE6Inner p i := by
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;> simp only [t263GE6Easy, t263GE6Inner, onLie] at h ⊢ <;>
      first | exact h.elim | exact ⟨h.1, h.2.2.2⟩
  | cyclic r hr => exact h.elim
  | alternating n hn => exact h.elim
  | sporadic s => exact h.elim

private theorem t263GTD4Inner_of_easy {p : ℕ} {i : TauCeti.CFSGIndex} (h : t263GTD4Easy p i) :
    t263GTD4Inner p i := by
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;> simp only [t263GTD4Easy, t263GTD4Inner, onLie] at h ⊢ <;>
      first | exact h.elim | exact h.1
  | cyclic r hr => exact h.elim
  | alternating n hn => exact h.elim
  | sporadic s => exact h.elim

theorem inducesInnerMod_excEasy {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hcat : catalogIs (↥S ⧸ Subgroup.center ↥S) (t263GExcEasy p)) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) : InducesInnerMod p S x :=
  inducesInnerMod_excInner hp hp2 hSn hSq hSp
    (catalogIs_imp (fun _ h => t263GExcInner_of_easy h) hcat) hxp hInn

theorem inducesInnerMod_e6Easy {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hcat : catalogIs (↥S ⧸ Subgroup.center ↥S) (t263GE6Easy p)) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) : InducesInnerMod p S x :=
  inducesInnerMod_e6Inner hp hp2 hSn hSq hSp
    (catalogIs_imp (fun _ h => t263GE6Inner_of_easy h) hcat) hxp hInn

theorem inducesInnerMod_td4Easy {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hcat : catalogIs (↥S ⧸ Subgroup.center ↥S) (t263GTD4Easy p)) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) : InducesInnerMod p S x :=
  inducesInnerMod_td4Inner hp hp2 hSn hSq hSp
    (catalogIs_imp (fun _ h => t263GTD4Inner_of_easy h) hcat) hxp hInn

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
