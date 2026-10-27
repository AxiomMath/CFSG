module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts4
public import CFSG.LocalAnalysis.GLTheoremA.S3.KD65Holds
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Tags
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Unitary
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthOrth
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcUntwisted
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTwistedE6
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts5
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs183eqv
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1315
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityGe5Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.PumpDefChar

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf innerAut)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie ambiguousChev PSimple PQuot)
open CFSG.LocalAnalysis.GLTheoremA (KDChevInner KD65 KDAmbSolv)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieSylowExponent)
open CFSG.LocalAnalysis.ComponentInitial

@[expose] def Input9_1FieldAt (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n p f : ℕ), p.Prime → 5 ≤ p →
    CFSG.Blueprint.LieModel S t n p f → ∀ x : MulAut S, orderOf x = p → x ∉ innerAut S →
      ∀ I : Subgroup S, GLAPComponent p (Lemma1314.fixSub x) I →
        p ∣ f ∧ CFSG.Blueprint.LieModel (barOf p I) t n p (f / p)

@[expose] def Input9_1Field : Prop := ∀ t : StatedLieTag, Input9_1FieldAt t

theorem fixSub_eq_fixSubgroup {K : Type} [Group K] (x : MulAut K) :
    Lemma1314.fixSub x = fixSubgroup x := by
  ext y
  exact Iff.rfl

theorem autCenterQuot_conj {K : Type} [Group K] (k : K) :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot K (MulAut.conj k) =
      MulAut.conj (k : K ⧸ Subgroup.center K) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H z =>
    rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_mk, MulAut.conj_apply,
      MulAut.conj_apply]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem false_of_inner {p : ℕ} (hp : p.Prime) (hKD : KDChevInner p) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hchev : IsChevSimple p (K ⧸ Subgroup.center K))
    {x : MulAut K} (hxo : orderOf x = p) (hin : x ∈ innerAut K) {J1 : Subgroup K}
    (hJ1 : GLAPComponent p (Lemma1314.fixSub x) J1) : False := by
  obtain ⟨k, rfl⟩ := hin
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnc := Lemma1315b.exists_noncomm_quot hq
  have hSz : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    Lemma1315b.center_eq_bot_of_simple hnc
  set π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hπ
  set β : MulAut (K ⧸ Subgroup.center K) := MulAut.conj (π k) with hβ
  have hker : π.ker ≤ Subgroup.center K := by rw [hπ, QuotientGroup.ker_mk']
  have hαβ : ∀ y, π (MulAut.conj k y) = β (π y) := by
    intro y
    simp only [hβ, MulAut.conj_apply, map_mul, map_inv]
  have hJ1' : GLAPComponent p (fixSubgroup (MulAut.conj k)) J1 := by
    rw [← fixSub_eq_fixSubgroup]
    exact hJ1
  have hmap := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup π hker
    (MulAut.conj k) β hαβ (QuotientGroup.mk'_surjective _) hp hJ1'
  have hkp : k ^ p ∈ Subgroup.center K := by
    have h1 : MulAut.conj (k ^ p) = 1 := by
      rw [map_pow, ← hxo, pow_orderOf_eq_one]
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg (fun φ : MulAut K => φ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc g * k ^ p = k ^ p * g * (k ^ p)⁻¹ * k ^ p := by rw [h2]
      _ = k ^ p * g := by group
  have hβp : β ^ p = 1 := by
    rw [hβ, ← map_pow, ← map_pow]
    have : π (k ^ p) = 1 := (QuotientGroup.eq_one_iff _).2 hkp
    rw [this, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    have hc : π k ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun φ : MulAut (K ⧸ Subgroup.center K) => φ g) h
      simp only [hβ, MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * π k = π k * g * (π k)⁻¹ * π k := by rw [h3]
        _ = π k * g := by group
    rw [hSz, Subgroup.mem_bot] at hc
    have hkZ : k ∈ Subgroup.center K := (QuotientGroup.eq_one_iff _).1 hc
    have hc1 : MulAut.conj k = 1 := by
      ext g
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [← Subgroup.mem_center_iff.1 hkZ g]
      group
    rw [hc1, orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  have hlay := hKD (K ⧸ Subgroup.center K) hq.2 hnc hchev β hβp hβ1 ⟨π k, rfl⟩
  have hle : J1.map π ≤ GLAPLayer p (fixSubgroup β) := le_sSup hmap
  rw [hlay, le_bot_iff] at hle
  exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hmap hle

theorem center_eq_bot_of_outer {p : ℕ} (hp : p.Prime) (hK65 : KD65 p) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore p K = ⊥)
    (hchev : IsChevSimple p (K ⧸ Subgroup.center K)) {x : MulAut K} (hxp : x ^ p = 1)
    (hout : x ∉ innerAut K) : Subgroup.center K = ⊥ := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnc := Lemma1315b.exists_noncomm_quot hq
  refine hK65 (K ⧸ Subgroup.center K) hq.2 hnc hchev
    ⟨CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot K x, ?_, ?_⟩ K hq
    (CFSG.HardMathSupport.Solomon.Coordinator.i271h_center_isPGroup hp hO) ⟨MulEquiv.refl _⟩
  · rw [← map_pow, hxp, map_one]
  · rintro ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective s
    apply hout
    refine ⟨k, ?_⟩
    apply CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hq.1
    rw [autCenterQuot_conj]
    exact hs

theorem psl_two_of_lieModel (hO : LieOrderFormulasInput) {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (h1 : CFSG.Blueprint.LieModel X t n p f)
    (h2 : CFSG.Blueprint.LieModel X .PSL 2 p 1) : t = .PSL ∧ n = 2 ∧ f = 1 := by
  have hadm1 := CFSG.Blueprint.LieModel.admissible h1
  obtain ⟨-, -, hf1⟩ := hO X t n p f hadm1 h1
  obtain ⟨-, -, hf2⟩ := hO X .PSL 2 p 1 (CFSG.Blueprint.LieModel.admissible h2) h2
  refine CFSG.ComponentClassification.CatFC.e16_sylowExp_mul_eq_one hadm1 ?_
  rw [← hf1, hf2]
  rfl

theorem lieModel_of_isLpType {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X J : Type} [Group X]
    [Group J] (e : X ≃* J) (hJ : IsLpType 2 p J) : CFSG.Blueprint.LieModel X .PSL 2 p 1 := by
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := hJ
  refine Or.inl ⟨by decide, ⟨hp, le_rfl, le_rfl, ?_, ?_⟩, F, hF, hFin, by rw [hcard, pow_one],
    ⟨e.trans φ⟩⟩
  · simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]
    omega
  · simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]
    omega

theorem nontrivial_barOf {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X J1 : Subgroup G} (hJ1 : GLAPComponent p X J1) : Nontrivial (barOf p J1) := by
  have hqJ := Lemma1315b.isQuasisimple_barOf_of_comp hp hJ1
  haveI : IsSimpleGroup (barOf p J1 ⧸ Subgroup.center (barOf p J1)) := hqJ.2
  exact (QuotientGroup.mk_surjective (s := Subgroup.center (barOf p J1))).nontrivial

theorem primeCore_eq_bot_of_simple {G : Type} [Group G] {p : ℕ} {I : Subgroup G}
    [IsSimpleGroup ↥I] (hnt : Nontrivial (barOf p I)) : GLAPPrimeCore p ↥I = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥I) with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨a, b, hab⟩ := hnt
    apply hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => exact QuotientGroup.eq.2 (by rw [h0]; exact Subgroup.mem_top _)

noncomputable def barOfEquivSelf {G : Type} [Group G] {p : ℕ} {I : Subgroup G}
    [IsSimpleGroup ↥I] (hnt : Nontrivial (barOf p I)) : barOf p I ≃* ↥I :=
  (QuotientGroup.quotientMulEquivOfEq (primeCore_eq_bot_of_simple hnt)).trans
    QuotientGroup.quotientBot

theorem nonempty_barOf_equiv {G T : Type} [Group G] [Group T] [Finite G] {p : ℕ} (hp : p.Prime)
    (e : G ≃* T) {β : MulAut G} {a : MulAut T} (hβa : MulAut.congr e β = a)
    {J : Subgroup T} (hJC : J ≤ fixSubgroup a) [(J.subgroupOf (fixSubgroup a)).Normal]
    (hJs : IsSimpleGroup ↥J)
    (hsol : Group.IsSolvable (↥(fixSubgroup a) ⧸ J.subgroupOf (fixSubgroup a)))
    {I : Subgroup G} (hI : GLAPComponent p (Lemma1314.fixSub β) I) :
    Nonempty (barOf p I ≃* ↥J) := by
  haveI : Finite T := Finite.of_equiv G e.toEquiv
  have hI' : GLAPComponent p (fixSubgroup β) I := by
    rw [← fixSub_eq_fixSubgroup]
    exact hI
  have hmap : GLAPComponent p (fixSubgroup a) (I.map e.toMonoidHom) := by
    rw [← hβa, CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr]
    exact CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp e.toMonoidHom
      (CFSG.HardMathSupport.Dickson.I271.coprime_ker_mulEquiv e _) hI'
  have hperf : ⁅I.map e.toMonoidHom, I.map e.toMonoidHom⁆ = I.map e.toMonoidHom :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hmap
  have hle : I.map e.toMonoidHom ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hJC hsol
      hmap.1 hperf
  have hsn : IsSubnormal (I.map e.toMonoidHom) J :=
    CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_le_of_le hmap.2.1 hle hJC
  have hIJ : I.map e.toMonoidHom = J := by
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn hJs with h0 | h0
    · exact absurd h0 (CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hmap)
    · exact h0
  let E : ↥I ≃* ↥J := (I.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hIJ)
  haveI : IsSimpleGroup ↥I := E.isSimpleGroup
  exact ⟨(barOfEquivSelf (nontrivial_barOf hp hI)).trans E⟩

theorem nonempty_barOf_equiv_of_eq {G T : Type} [Group G] [Group T] [Finite G] {p : ℕ}
    (hp : p.Prime) (e : G ≃* T) {β : MulAut G} {a : MulAut T} (hβa : MulAut.congr e β = a)
    {N J : Subgroup T} (hN : fixSubgroup a = N) (hJN : J ≤ N) [(J.subgroupOf N).Normal]
    (hJs : IsSimpleGroup ↥J) (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N))
    {I : Subgroup G} (hI : GLAPComponent p (Lemma1314.fixSub β) I) :
    Nonempty (barOf p I ≃* ↥J) := by
  subst hN
  exact nonempty_barOf_equiv hp e hβa hJN hJs hsol hI

theorem congr_trans_inv {G T : Type} [Group G] [Group T] (e : G ≃* T) (x : MulAut G)
    (g a : MulAut T) (h : MulAut.congr e x = g * a * g⁻¹) :
    MulAut.congr (e.trans (g⁻¹ : T ≃* T)) x = a := by
  have h1 : MulAut.congr (e.trans (g⁻¹ : T ≃* T)) x = g⁻¹ * MulAut.congr e x * g := by
    ext y
    rfl
  rw [h1, h]
  group

theorem congr_not_mem_innerAut {G T : Type} [Group G] [Group T] (e : G ≃* T) {x : MulAut G}
    (hout : x ∉ innerAut G) : MulAut.congr e x ∉ innerAut T := by
  rintro ⟨g, hg⟩
  apply hout
  refine ⟨e.symm g, ?_⟩
  apply (MulAut.congr e).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply]
  exact hg

section Linear

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export (exists_conj_fieldAut_of_outer
  exists_conj_fieldAut_of_outer_two fixSubgroup_fieldAut_eq_range not_dvd_card_units_of_card_eq
  exists_finset_card_four)

noncomputable def projSLEquivStated (n : ℕ) (k : Type) [Field k] :
    projectiveSL n k ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL n k) :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n k)

theorem isSimpleGroup_projectiveSL {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k]
    (hk : 4 ≤ Nat.card k) : IsSimpleGroup (projectiveSL n k) := by
  obtain ⟨hnt, hsimp, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := k) (n := n) hn
    (Or.inr (exists_finset_card_four hk))
  haveI := hnt
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).symm.isSimpleGroup

theorem input9_1FieldAt_PSL : Input9_1FieldAt .PSL := by
  intro S _ _ n p f hp hp5 hS x hxo hout J1 hJ1
  have hadm := CFSG.Blueprint.LieModel.admissible hS
  obtain ⟨-, hf, hn, -, -⟩ := hadm
  obtain ⟨F, hF, hFin, hFcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hS
  haveI := hFin
  have hp2 : p ≠ 2 := by omega
  set β : MulAut (projectiveSL n F) := MulAut.congr e x with hβdef
  have hβo : orderOf β = p := by rw [hβdef, MulEquiv.orderOf_eq]; exact hxo
  have hβout : β ∉ innerAut (projectiveSL n F) := congr_not_mem_innerAut e hout
  obtain ⟨τ, h, hτ, hβeq⟩ : ∃ (τ : F ≃+* F) (h : MulAut (projectiveSL n F)), orderOf τ = p ∧
      β = h * fieldAut n F τ * h⁻¹ := by
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact exists_conj_fieldAut_of_outer_two hp hf hFcard hβo hβout
    · exact exists_conj_fieldAut_of_outer hn3 hp hp2 hf hFcard (hβo ▸ pow_orderOf_eq_one β) hβout
  set k : Subfield F := semilinearFixedSubfield τ with hk
  obtain ⟨hpf, hkcard⟩ := card_semilinearFixedSubfield hp hf hFcard hτ
  have hτp : τ ^ p = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hC : fixSubgroup (fieldAut n F τ) = (linearSubfieldInclusion n k).range :=
    fixSubgroup_fieldAut_eq_range (by omega) hp hτp (not_dvd_card_units_of_card_eq hp hf hFcard)
  have hcongr := congr_trans_inv e x h (fieldAut n F τ) hβeq
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  have hpk : p ≤ p ^ (f / p) := Nat.le_self_pow (Nat.div_pos (Nat.le_of_dvd (by omega) hpf)
    hp.pos).ne' p
  have hk4 : 4 ≤ Nat.card k := by rw [hkcard]; omega
  haveI : IsSimpleGroup (projectiveSL n k) := isSimpleGroup_projectiveSL (by omega) hk4
  let eR : ↥(fixSubgroup (fieldAut n F τ)) ≃* projectiveSL n k :=
    (MulEquiv.subgroupCongr hC).trans (MonoidHom.ofInjective hinj).symm
  haveI := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.normal_subgroupOf_self
    (fixSubgroup (fieldAut n F τ))
  obtain ⟨E0⟩ := nonempty_barOf_equiv hp _ hcongr le_rfl eR.isSimpleGroup
    (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.isSolvable_quotient_self _) hJ1
  have hdiv : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  refine ⟨hpf, Or.inl ⟨by decide, ⟨hp, hdiv, hn, ?_, ?_⟩, ↥k, inferInstance, inferInstance,
    hkcard, ⟨(E0.trans eR).trans (projSLEquivStated n k)⟩⟩⟩
  · simp only [ne_eq, Prod.mk.injEq, not_and]
    intro _
    omega
  · simp only [ne_eq, Prod.mk.injEq, not_and]
    intro _
    omega

end Linear

section Unitary

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical

theorem input9_1FieldAt_PSU : Input9_1FieldAt .PSU := by
  intro S _ _ n p f hp hp5 hS x hxo hout J1 hJ1
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, hf, hn, hq⟩, K, hKf, hKfin, hK, ⟨eT⟩⟩ := hS.statedClassicalModel (by decide)
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h hC
  let e' : S ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  set β := MulAut.congr e' x with hβdef
  have hβo : orderOf β = p := by rw [hβdef, MulEquiv.orderOf_eq]; exact hxo
  have hβout := congr_not_mem_innerAut e' hout
  obtain ⟨σ, g, hσ, hβeq⟩ :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_conj_primeFormFieldHom_of_outer h hn hp2
      hβo hβout
  have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    intro hd
    have h2 : p ∣ p ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h3 : p ∣ p ^ f := dvd_pow_self p (by omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h3).1 h2))
  obtain ⟨hpf, hcardK0, -, -, -, hinj, hrange, -, -, hsimple, -⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσ n hn hq' hZ
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hpk : p ≤ p ^ (f / p) := Nat.le_self_pow (by omega) p
  have hq₀ : ¬(n = 3 ∧ p ^ (f / p) = 2) := fun h3 => by omega
  obtain ⟨hsC, -, -, -, -⟩ := hsimple hq₀
  set a := primeFormFieldHom h
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (n := n)) σ with ha
  have hCeq : fixSubgroup a = fieldFixedPSU h n σ := Subgroup.ext fun y => Iff.rfl
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) ≃* fieldFixedPSU h n σ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let eM : primeFormP h₀ ((1 : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU n (p ^ (f / p))
        (CFSG.LieType.Chevalley.fixSubfield σ)) :=
    (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h₀ n).symm.trans
      (unitaryPSUEquiv h₀ (by omega))
  have hcongr := congr_trans_inv e' x g a hβeq
  haveI := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.normal_subgroupOf_self (fixSubgroup a)
  have hsa : IsSimpleGroup ↥(fixSubgroup a) := by
    rw [hCeq]
    exact hsC
  obtain ⟨E0⟩ := nonempty_barOf_equiv hp _ hcongr le_rfl hsa
    (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.isSolvable_quotient_self _) hJ1
  refine ⟨hpf, Or.inl ⟨by decide, ⟨hp, hfp, hn, fun heq => hq₀ ⟨congrArg Prod.fst heq,
    congrArg Prod.snd heq⟩⟩, ↥(CFSG.LieType.Chevalley.fixSubfield σ), inferInstance, inferInstance,
    hcardK0, ⟨((E0.trans (MulEquiv.subgroupCongr hCeq)).trans eJ.symm).trans eM⟩⟩⟩

end Unitary

section Symplectic

open CFSG.RankThree.CASymplecticSubfield CFSG.RankThree.PartOne.KCSpComm
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation

theorem input9_1FieldAt_PSp : Input9_1FieldAt .PSp := by
  intro S _ _ r p f hp hp5 hS x hxo hout J1 hJ1
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hadm, K, hfield, hfin, hK, ⟨θ⟩⟩ := hS.statedClassicalModel (by decide)
  have hf : 1 ≤ f := hadm.2.1
  have hr : 2 ≤ r := hadm.2.2.1
  have hr1 : 1 ≤ r := by omega
  set β' : MulAut (StatedProj (StatedSp r K)) := MulAut.congr θ x with hβ'def
  have hβ'ord : orderOf β' = p := by rw [hβ'def, MulEquiv.orderOf_eq]; exact hxo
  have hβ'out : β' ∉ innerAut (StatedProj (StatedSp r K)) := congr_not_mem_innerAut θ hout
  have hβ'p : β' ^ p = 1 := hβ'ord ▸ pow_orderOf_eq_one β'
  have hO := spOuter hp hf hr hK
  have hodd : Odd (orderOf β') := hβ'ord ▸ hp.odd_of_ne_two hp2
  have hE : β' ∈ spSemilinearAutGroup r K :=
    mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hD : β' ∉ spLinearAutGroup r K := by
    intro hD
    have := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal
      (StatedProj (StatedSp r K))
    have hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    exact hβ'out (mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp hp2 hD hβ'p)
  obtain ⟨-, σ, hσ, h', -, hβeq⟩ := hO.descent p hp β' hE hD hβ'ord
  haveI : CharP K p := finite_field_prime_power_characteristic hp hf hK
  set k : Subfield K := descentField σ with hkdef
  obtain ⟨hpf, hkcard⟩ := CFSG.RankThree.PartOne.card_semilinearFixedSubfield hp hf hK hσ
  have hk : Nat.card k = p ^ (f / p) := hkcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hpk : p ≤ p ^ (f / p) := Nat.le_self_pow (by omega) p
  have hoddσ : Odd (orderOf σ) := hσ ▸ hp.odd_of_ne_two hp2
  set a : MulAut (StatedProj (StatedSp r K)) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut r K σ with ha
  have hfixSub : fixSubgroup a = subfieldFixedGroup K r σ :=
    Subgroup.ext fun y => mem_fixSubgroup.trans (fieldAut_apply_eq_self_iff hr1 hoddσ y)
  have hinj : Function.Injective (subfieldSpProj r k) := subfieldSpProj_injective hr1 k
  let eH : StatedProj (StatedSp r k) ≃* subfieldFixedGroup K r σ := MonoidHom.ofInjective hinj
  let eC : ↥(fixSubgroup a) ≃* StatedProj (StatedSp r k) :=
    (MulEquiv.subgroupCongr hfixSub).trans eH.symm
  have hadm' : StatedLieAdmissible .PSp r p (f / p) := ⟨hp, hfp, hr, fun h => by
    have := (Prod.mk.inj h).2
    omega⟩
  have hmodel : StatedClassicalModel ↥(fixSubgroup a) .PSp r p (f / p) :=
    ⟨hadm', ↥k, inferInstance, inferInstance, hk, ⟨eC⟩⟩
  obtain ⟨-, hsimpC, -⟩ :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth.finite_simple_nonab_of_model hmodel
      (Or.inl ⟨rfl, hr⟩)
  have hcongr := congr_trans_inv θ x h' a hβeq
  haveI := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.normal_subgroupOf_self (fixSubgroup a)
  obtain ⟨E0⟩ := nonempty_barOf_equiv hp _ hcongr le_rfl hsimpC
    (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.isSolvable_quotient_self _) hJ1
  exact ⟨hpf, Or.inl ⟨by decide, ⟨hadm', ↥k, inferInstance, inferInstance, hk, ⟨E0.trans eC⟩⟩⟩⟩

end Symplectic

section Orthogonal

open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth (outer_order_prime
  mem_E_of_pow_eq_one_of_three_lt)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)

theorem orth_barOf_equiv {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
    {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
    {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ} (S : SubfieldSetup k Q₀ Q σ p)
    (E : G ≃* matrixProjectiveDerived Q) {β : MulAut G}
    (hβ : MulAut.congr E β = fieldAutT Q σ S.hQσ) {I : Subgroup G}
    (hI : GLAPComponent p (Lemma1314.fixSub β) I) :
    Nonempty (barOf p I ≃* matrixProjectiveDerived Q₀) := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hsimple, -⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  have hfix : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => fieldAutT_apply_iff S t
  haveI hJnorm := subfieldDerivedImage_normal k S.hext
  have hquot := fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent hquot
  haveI := hsimple
  obtain ⟨E0⟩ := nonempty_barOf_equiv_of_eq S.hp E hβ hfix (subfieldDerivedImage_le k S.hext)
    (inclEquiv k S.hext hd).symm.isSimpleGroup inferInstance hI
  exact ⟨E0.trans (inclEquiv k S.hext hd).symm⟩

theorem congr_eq_fieldAutT {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    {k : Subfield K} {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {Q' : QuadraticForm K (Fin d → K)}
    {Q₀' : QuadraticForm k (Fin d → k)} {σ : K ≃+* K} {p : ℕ} (S : SubfieldSetup k Q₀' Q' σ p)
    (e : G ≃* matrixProjectiveDerived Q) (β : MulAut G) (U : similarityPairs Q)
    (hUβ : matrixProjectiveConjugationHom Q U = MulAut.congr e β)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x)) :
    MulAut.congr (e.trans Θ) β = fieldAutT Q' σ S.hQσ := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr (e.trans Θ) β) x = Θ ((MulAut.congr e β) (Θ.symm x)) := rfl
  rw [h1, ← hUβ, hΘ, MulEquiv.apply_symm_apply, hg']
  rfl

theorem input9_1FieldAt_POmegaOdd : Input9_1FieldAt .POmegaOdd := by
  intro G _ _ n p f hp hp5 hS β hβo hout I hI
  have hp2 : p ≠ 2 := by omega
  have hG : StatedClassicalModel G .POmegaOdd n p f := hS.statedClassicalModel (by decide)
  have hβ : β ^ p = 1 := hβo ▸ pow_orderOf_eq_one β
  obtain ⟨-, hf, hn3, -⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n p f hG K hK e
  obtain ⟨hchar, -⟩ := coordinate_model_witness_odd hG K hK e
  have h2K : ringChar K ≠ 2 := by rw [hchar]; exact hp2
  have htop : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn3 h2K
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinateOddWitnessEquiv K e) hgates hp hp2 hβ hout
  have hE : MulAut.congr (coordinateOddWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadOdd n K) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd (Or.inl rfl)
    n p f p hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = p ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd hf hpf) hp.pos
  have S := subfieldSetup_odd (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn3
    (Ring.two_ne_zero h2K)
  obtain ⟨E0⟩ := orth_barOf_equiv S _
    (congr_eq_fieldAutT S (coordinateOddWitnessEquiv K e) β U hUκ Θ g' hg'l hg'r hΘ) hI
  refine ⟨hpf, Or.inl ⟨by decide, ⟨hp, hfp, hn3, hp2⟩, _, inferInstance, inferInstance, hcard',
    ⟨E0.trans (statedProjectiveReindexEquiv (oddIndexEquiv n)
      (CFSG.LieType.Universal.Spin.quadOdd n _)
      (CFSG.LieType.Universal.Spin.coe_quadOdd n _)).symm⟩⟩⟩

theorem input9_1FieldAt_POmegaMinus : Input9_1FieldAt .POmegaMinus := by
  intro G _ _ n p f hp hp5 hS β hβo hout I hI
  have hp2 : p ≠ 2 := by omega
  have hG : StatedClassicalModel G .POmegaMinus n p f := hS.statedClassicalModel (by decide)
  have hβ : β ^ p = 1 := hβo ▸ pow_orderOf_eq_one β
  obtain ⟨-, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n p f hG hn1 K hK b c hirr e
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinateMinusWitnessEquiv K hn1 b c e) hgates hp hp2
    hβ hout
  have htop : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
  have hE : MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β ∈
      matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n p f p hG hp hp2 hn1 K hK b c hirr e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = p ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd hf hpf) hp.pos
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / p = m := by rw [hm]; exact Nat.mul_div_cancel_left m hp.pos
  have hcardm : Nat.card (semilinearFixedSubfield U.val.right) = p ^ m := by
    rw [hcard', hdiv]
  have hm1 : 1 ≤ m := by
    rw [hdiv] at hfp
    exact hfp
  have hK' : Nat.card K = p ^ (m * p) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hp hm1 hcardm hK'
  have S := subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn4 hdeg b'
    c' hirr'
  obtain ⟨E0⟩ := orth_barOf_equiv S _
    (congr_eq_fieldAutT S (coordinateMinusWitnessEquiv K hn1 b c e) β U hUκ Θ g' hg'l hg'r hΘ) hI
  refine ⟨⟨m, hm⟩, Or.inl ⟨by decide, ⟨hp, hfp, hn4⟩, _, inferInstance, inferInstance, hcard',
    b', c', hirr', ⟨E0.trans (statedProjectiveReindexEquiv (minusIndexEquiv n hn1)
      (CFSG.LieType.Universal.Spin.quadMinus n _ b' c')
      (CFSG.LieType.Universal.Spin.coe_quadMinus n _ b' c')).symm⟩⟩⟩

theorem input9_1FieldAt_POmegaPlus : Input9_1FieldAt .POmegaPlus := by
  intro G _ _ n p f hp hp5 hS β hβo hout I hI
  have hp2 : p ≠ 2 := by omega
  have hG : StatedClassicalModel G .POmegaPlus n p f := hS.statedClassicalModel (by decide)
  have hβ : β ^ p = 1 := hβo ▸ pow_orderOf_eq_one β
  obtain ⟨-, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n p f hG K hK e
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinatePlusWitnessEquiv K e) hgates hp hp2 hβ hout
  have hE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus n K) := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · exact mem_E_of_pow_eq_one_of_three_lt hgates hp (by omega) (by rw [← map_pow, hβ, map_one])
    · rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n h5]
      exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n p f p hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = p ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd hf hpf) hp.pos
  have S := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord''
    (by omega : 3 ≤ n)
  obtain ⟨E0⟩ := orth_barOf_equiv S _
    (congr_eq_fieldAutT S (coordinatePlusWitnessEquiv K e) β U hUκ Θ g' hg'l hg'r hΘ) hI
  refine ⟨hpf, Or.inl ⟨by decide, ⟨hp, hfp, hn4⟩, _, inferInstance, inferInstance, hcard',
    ⟨E0.trans (statedProjectiveReindexEquiv (plusIndexEquiv n)
      (CFSG.LieType.Universal.Spin.quadPlus n _)
      (CFSG.LieType.Universal.Spin.coe_quadPlus n _)).symm⟩⟩⟩

end Orthogonal

theorem admissible_div {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hp5 : 5 ≤ p) (hpf : p ∣ f) : StatedLieAdmissible t n p (f / p) := by
  obtain ⟨hp, hf, h⟩ := hadm
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hq : p ≤ p ^ (f / p) := Nat.le_self_pow (by omega) p
  refine ⟨hp, hfp, ?_⟩
  cases t
  case PSL =>
    exact ⟨h.1, fun he => by simp only [Prod.mk.injEq] at he; omega,
      fun he => by simp only [Prod.mk.injEq] at he; omega⟩
  case PSU => exact ⟨h.1, fun he => by simp only [Prod.mk.injEq] at he; omega⟩
  case PSp => exact ⟨h.1, fun he => by simp only [Prod.mk.injEq] at he; omega⟩
  case G2 => exact ⟨h.1, by omega⟩
  case twistedB2 => exact absurd h.2.1 (by omega)
  case twistedF4 => exact absurd h.2.1 (by omega)
  case twistedG2 => exact absurd h.2.1 (by omega)
  case Tits => exact absurd h.2.1 (by omega)
  all_goals exact h

section ExcUntwisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement


theorem entrywise_barOf_equiv (τ : Tag) {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (σ : K ≃+* K) {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (E : G ≃* ↥(adjointGroup τ K)) {β : MulAut G}
    (hβ : MulAut.congr E β = entrywiseAdjointAut τ σ) {I : Subgroup G}
    (hI : GLAPComponent p (Lemma1314.fixSub β) I) :
    Nonempty (barOf p I ≃* ↥(adjointGroup τ (fixSubfield σ))) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  set a := entrywiseAdjointAut τ σ with ha
  have hk2 : ringChar (fixSubfield σ) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : fixSubfield σ) = 0 := by
      rw [← h]
      exact ringChar.Nat.cast_ringChar
    apply Ring.two_ne_zero hK2
    have := congrArg (fixSubfield σ).subtype h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  obtain ⟨hs, -, -⟩ := odd_pinned_Chevalley_p_components τ (fixSubfield σ) hk2
  obtain ⟨-, -, -, hJΓ, -, hnormal, -, hder⟩ :=
    Chevalley_coordinate_field_fixed_structure τ K hK2 σ
  have hJA : fixedFieldImage τ σ ≤ adjointGroup τ K := hJΓ.trans inf_le_left
  have hΓ : ∀ n : ↥(fixSubgroup a), ((n : ↥(adjointGroup τ K)) : ModGL τ K) ∈
      entrywiseFixedGroup τ σ := fun n =>
    ⟨(n : ↥(adjointGroup τ K)).2, by
      have h1 : a n = n := n.2
      have := congrArg Subtype.val h1
      rwa [coe_entrywiseAdjointAut] at this⟩
  set J : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
    with hJ
  have hmemJ : ∀ x : ↥(adjointGroup τ K), x ∈ J ↔ (x : ModGL τ K) ∈ fixedFieldImage τ σ :=
    fun x => Iff.rfl
  have hJC : J ≤ fixSubgroup a := fun x hx => by
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  haveI hJn : (J.subgroupOf (fixSubgroup a)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, hmemJ] at hn ⊢
    have h1 := hnormal.conj_mem ⟨((n : ↥(adjointGroup τ K)) : ModGL τ K), hΓ n⟩
      (Subgroup.mem_subgroupOf.2 hn) ⟨((g : ↥(adjointGroup τ K)) : ModGL τ K), hΓ g⟩
    simpa using Subgroup.mem_subgroupOf.1 h1
  let eJ : ↥J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv σ).symm
  haveI := hs
  have hsJ : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hsol : Group.IsSolvable (↥(fixSubgroup a) ⧸ J.subgroupOf (fixSubgroup a)) := by
    refine Group.isSolvable_of_comm fun u v => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, Subgroup.mem_subgroupOf, hmemJ]
    have h2 : (((⁅y⁻¹, x⁻¹⁆ : ↥(fixSubgroup a)) : ↥(adjointGroup τ K)) : ModGL τ K) =
        ⁅(((y⁻¹ : ↥(fixSubgroup a)) : ↥(adjointGroup τ K)) : ModGL τ K),
          (((x⁻¹ : ↥(fixSubgroup a)) : ↥(adjointGroup τ K)) : ModGL τ K)⁆ := by
      simp [commutatorElement_def]
    rw [h2, ← hder]
    exact Subgroup.commutator_mem_commutator (hΓ _) (hΓ _)
  obtain ⟨E0⟩ := nonempty_barOf_equiv hp E hβ hJC hsJ hsol hI
  exact ⟨E0.trans eJ⟩

theorem exc_untwisted_descent (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup τ K)) (hα : orderOf α = ℓ)
    (hout : α ∉ innerAut (adjointGroup τ K)) :
    ∃ (r j : ℕ) (δ : MulAut (adjointGroup τ K)) (σ : K ≃+* K),
      orderOf σ = ℓ ∧ (α ^ r) ^ j = α ∧ δ * α ^ r * δ⁻¹ = entrywiseAdjointAut τ σ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have hαp : α ^ ℓ = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  rcases hτ with rfl | rfl | hE
  · obtain ⟨x, σ, hσp, hασ⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.G2_form_odd hℓ hℓ2 hℓ3 hf K hK hℓ α hα hout
    obtain ⟨δ, hδ⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.exists_conj_eq_entrywiseAdjointAut_of_form
        Tag.G2 hℓ hf K hK hℓ α hα x σ hσp hασ
    exact ⟨1, 1, δ, σ, hσp, by rw [pow_one, pow_one], by rw [pow_one]; exact hδ⟩
  · obtain ⟨x, σ, δ, hσp, -, hδ, -, -⟩ :=
      odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hℓ α hα hout
    exact ⟨1, 1, δ, σ, hσp, by rw [pow_one, pow_one], by rw [pow_one]; exact hδ⟩
  · have hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
        α ≠ MulAut.conj g * rootDiagAut τ K a := by
      intro g a h
      have hdvd :=
        (CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner τ hE K hℓ g a α h hαp
          hout).2
      rw [hK] at hdvd
      have h1 : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
      have h2 : ℓ ∣ ℓ ^ f - (ℓ ^ f - 1) := Nat.dvd_sub h1 hdvd
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
      exact hℓ.one_lt.ne' (Nat.dvd_one.1 h2)
    obtain ⟨d, T, r, j, ψ, -, hTord, -, -, -, hαβ, hψ⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_not_innerDiag τ hE hf K hK
        hℓ hℓ2 α hαp hnd
    exact ⟨r, j, ψ, T, hTord, hαβ, hψ⟩

theorem input9_1FieldAt_untwisted {t : StatedLieTag} (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hmodel : ∀ (G : Type) [Group G] (p f : ℕ), ChevalleyExceptionalModel G t p f ↔
      (StatedLieAdmissible t 0 p f ∧ UntwistedChevalleyModel G τ (p ^ f)))
    (hct : t ∈ chevalleyExceptionalTags) (hcl : t ∉ classicalTags) (hrt : t ∉ reeTitsTags)
    (hsz : t ≠ .twistedB2) : Input9_1FieldAt t := by
  intro S _ _ n p f hp hp5 hS x hxo hout I hI
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hS with ⟨ht, -⟩ | ⟨hn, -, hce⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht hcl
  · subst hn
    obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := (hmodel S p f).1 hce
    have hf : 1 ≤ f := hadm.2.1
    haveI : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    let θ : S ≃* ↥(adjointGroup τ K) := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    set α := MulAut.congr θ x with hαdef
    have hα : orderOf α = p := by rw [hαdef, MulEquiv.orderOf_eq]; exact hxo
    have hαout : α ∉ innerAut (adjointGroup τ K) := congr_not_mem_innerAut θ hout
    obtain ⟨r, j, δ, σ, hσ, hrj, hδ⟩ := exc_untwisted_descent τ hτ hp hp2 hp3 hf K hK α hα hαout
    have hxrj : (x ^ r) ^ j = x := by
      apply (MulAut.congr θ).injective
      rw [map_pow, map_pow]
      exact hrj
    have hfixeq : Lemma1314.fixSub (x ^ r) = Lemma1314.fixSub x := by
      rw [fixSub_eq_fixSubgroup, fixSub_eq_fixSubgroup]
      exact CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcUntwisted.fixSubgroup_pow_eq hxrj
    have hI' : GLAPComponent p (Lemma1314.fixSub (x ^ r)) I := by
      rw [hfixeq]
      exact hI
    have hcongr : MulAut.congr (θ.trans (δ : ↥(adjointGroup τ K) ≃* ↥(adjointGroup τ K))) (x ^ r) =
        entrywiseAdjointAut τ σ := by
      have h1 : MulAut.congr (θ.trans (δ : ↥(adjointGroup τ K) ≃* ↥(adjointGroup τ K))) (x ^ r) =
          δ * α ^ r * δ⁻¹ := by
        rw [hαdef, ← map_pow]
        ext y
        rfl
      rw [h1, hδ]
    obtain ⟨E0⟩ := entrywise_barOf_equiv τ hK2 σ hp _ hcongr hI'
    obtain ⟨hdvdf, hkcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hp hf hK σ
    rw [hσ] at hdvdf hkcard
    have hZk : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
    let eQ : ↥(adjointGroup τ (fixSubfield σ)) ≃* AdjointQuotient τ (fixSubfield σ) :=
      ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm
    exact ⟨hdvdf, Or.inr (Or.inl ⟨rfl, hct, (hmodel _ p (f / p)).2
      ⟨admissible_div hadm hp5 hdvdf, ↥(fixSubfield σ), inferInstance, inferInstance, hkcard,
        ⟨E0.trans eQ⟩⟩⟩)⟩
  · exact absurd ht hrt
  · exact absurd ht hsz

theorem input9_1FieldAt_G2 : Input9_1FieldAt .G2 :=
  input9_1FieldAt_untwisted .G2 (Or.inl rfl) (fun _ _ _ _ => Iff.rfl) (by decide) (by decide)
    (by decide) (by decide)

theorem input9_1FieldAt_F4 : Input9_1FieldAt .F4 :=
  input9_1FieldAt_untwisted .F4 (Or.inr (Or.inl rfl)) (fun _ _ _ _ => Iff.rfl) (by decide)
    (by decide) (by decide) (by decide)

theorem input9_1FieldAt_E6 : Input9_1FieldAt .E6 :=
  input9_1FieldAt_untwisted .E6 (Or.inr (Or.inr (Or.inl rfl))) (fun _ _ _ _ => Iff.rfl)
    (by decide) (by decide) (by decide) (by decide)

theorem input9_1FieldAt_E7 : Input9_1FieldAt .E7 :=
  input9_1FieldAt_untwisted .E7 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun _ _ _ _ => Iff.rfl)
    (by decide) (by decide) (by decide) (by decide)

theorem input9_1FieldAt_E8 : Input9_1FieldAt .E8 :=
  input9_1FieldAt_untwisted .E8 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (fun _ _ _ _ => Iff.rfl)
    (by decide) (by decide) (by decide) (by decide)

end ExcUntwisted

section ExcTwisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement
open CFSG.RankThree.Chevalley (subfieldRootGroupImage
  twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer)
open CFSG.HardMathSupport.Lang.Coordinator (mem_inner_of_mem_inn_sup_diag
  twisted_E6_field_descent_data_of_prime_order)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export (excTwistedModel_graphFixedRootGroup
  exists_mulEquiv_graphFixedRootGroup_inv_D4 ExcTwistedE6.inv_mul_mul_eq_commutatorElement
  ExcTwistedE6.coe_commutatorElement_subgroup)


theorem input9_1FieldAt_twistedE6 : Input9_1FieldAt .twistedE6 := by
  classical
  intro S _ _ n p f hp hp5 hS x hxo hout I hI
  have hp2 : p ≠ 2 := by omega
  rcases hS with ⟨ht, -⟩ | ⟨hn, -, hchev⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    have hf : 1 ≤ f := hchev.1.2.1
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e'⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
    set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
    set α := MulAut.congr e' x with hαdef
    have hα : orderOf α = p := by rw [hαdef, MulEquiv.orderOf_eq]; exact hxo
    have hout' : α ∉ innerAut C := congr_not_mem_innerAut e' hout
    have hαp : α ^ p = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    have hK2f : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
    obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
    have hpg : ¬ p ∣ Nat.gcd 3 (p ^ f + 1) := fun h => by
      have h1 : p ∣ p ^ f + 1 := h.trans (Nat.gcd_dvd_right 3 _)
      have h2 : p ∣ p ^ f := dvd_pow_self _ (by omega)
      exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
    have hη1 : Θ α ≠ 1 := by
      intro h1
      have hmem : α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
        rw [← hker, MonoidHom.mem_ker]
        exact h1
      exact hout' (mem_inner_of_mem_inn_sup_diag hp hK hσ hpg hcube hαp hmem)
    obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
      twisted_E6_field_descent_data_of_prime_order hp hf K hK2f σ hσ Θ hΘ hp hp2 α hαp hη1
    have hdp : d * p = f := by rw [hd, mul_comm]
    obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality hp
      (by omega : 1 ≤ 2 * f) hK2f
    obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ p ^ (2 * d) :=
      ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
    have hKdp : Nat.card K = p ^ (2 * d * p) := by rw [hK2f, mul_assoc, hdp]
    have hσdp : ∀ c, σ c = c ^ p ^ (d * p) := fun c => by rw [hσ, hdp]
    have hm3 : 3 ≤ p := by omega
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    have : Finite (fixSubfield κ) := Subtype.finite
    have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ p ^ d :=
      fun c => by rw [coe_fixSubfieldRestrict, hT]
    obtain ⟨-, hK0, hJC, -, hder, hsimpleJ, -, -⟩ :=
      twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hp hd1 hm3
        (hp.odd_of_ne_two hp2) K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
    set δ := fieldActor (t := TwistTag.E6) σ ε with hδ
    set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ)
      with hJdef
    have hder' : ⁅fixSubgroup δ, fixSubgroup δ⁆ = J.subgroupOf C := hder
    have hJΓ : J.subgroupOf C ≤ fixSubgroup δ := by
      rw [← hder']
      exact Subgroup.commutator_le.2 fun a ha b hb => by
        rw [commutatorElement_def]
        exact (fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ha hb)
          ((fixSubgroup δ).inv_mem ha)) ((fixSubgroup δ).inv_mem hb)
    haveI hJnorm : ((J.subgroupOf C).subgroupOf (fixSubgroup δ)).Normal := by
      rw [← hder']
      have h := Subgroup.normal_subgroupOf_commutator_sup (fixSubgroup δ) (fixSubgroup δ)
      rwa [sup_idem] at h
    have hsol : Group.IsSolvable
        (↥(fixSubgroup δ) ⧸ (J.subgroupOf C).subgroupOf (fixSubgroup δ)) := by
      refine Group.isSolvable_of_comm fun a b => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [ExcTwistedE6.inv_mul_mul_eq_commutatorElement, Subgroup.mem_subgroupOf, ← hder',
        ExcTwistedE6.coe_commutatorElement_subgroup]
      exact Subgroup.commutator_mem_commutator (v⁻¹).2 (u⁻¹).2
    let eJC : ↥(J.subgroupOf C) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
    haveI := hsimpleJ
    have hJs : IsSimpleGroup ↥(J.subgroupOf C) := eJC.isSimpleGroup
    have hσ₀' : ∀ c : fixSubfield κ, fixSubfieldRestrict T κ c = c ^ (p ^ d) := fun c =>
      Subtype.ext (by rw [hσ₀]; rfl)
    have hK0' : Nat.card (fixSubfield κ) = (p ^ d) ^ TwistTag.E6.order := by
      rw [hK0, ← pow_mul, mul_comm]
      rfl
    have hmodel : ChevalleyExceptionalModel
        (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom)
        .twistedE6 p d :=
      ⟨⟨hp, hd1, rfl⟩, excTwistedModel_graphFixedRootGroup TwistTag.E6 hp hd1 (fixSubfield κ) hK0'
        (fixSubfieldRestrict T κ) hσ₀'⟩
    let eM : ↥(J.subgroupOf C) ≃*
        graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom :=
      eJC.trans ((Subgroup.equivMapOfInjective _ _
        (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield κ).subtype)).symm)
    have hxrs : (x ^ r) ^ s = x := by
      apply (MulAut.congr e').injective
      rw [map_pow, map_pow]
      exact hrs
    have hfixeq : Lemma1314.fixSub (x ^ r) = Lemma1314.fixSub x := by
      rw [fixSub_eq_fixSubgroup, fixSub_eq_fixSubgroup]
      exact CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTwistedE6.fixSubgroup_pow_eq hxrs
    have hI' : GLAPComponent p (Lemma1314.fixSub (x ^ r)) I := by
      rw [hfixeq]
      exact hI
    have hcongr : MulAut.congr (e'.trans (ψ : C ≃* C)) (x ^ r) = δ := by
      have h1 : MulAut.congr (e'.trans (ψ : C ≃* C)) (x ^ r) = ψ * α ^ r * ψ⁻¹ := by
        rw [hαdef, ← map_pow]
        ext y
        rfl
      rw [h1, hψ]
    obtain ⟨E0⟩ := nonempty_barOf_equiv hp _ hcongr hJΓ hJs hsol hI'
    have hdf : f / p = d := by rw [← hdp, Nat.mul_div_cancel _ hp.pos]
    have hL : CFSG.Blueprint.LieModel
        (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom)
        .twistedE6 0 p d := Or.inr (Or.inl ⟨rfl, by decide, hmodel⟩)
    refine ⟨⟨d, by rw [← hdp, mul_comm]⟩, ?_⟩
    rw [hdf]
    exact CFSG.Blueprint.LieModel.of_mulEquiv (E0.trans eM).symm hL
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem input9_1FieldAt_trialityD4 : Input9_1FieldAt .trialityD4 := by
  classical
  intro S _ _ n p f hp hp5 hS x hxo hout I hI
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hp4 : 3 < p := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hS with ⟨ht, -⟩ | ⟨hn, -, hchev⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    have hf : 1 ≤ f := hchev.1.2.1
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hchev.2
    set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
    set β := MulAut.congr e₁ x with hβdef
    have hβ : orderOf β = p := by rw [hβdef, MulEquiv.orderOf_eq]; exact hxo
    have hβin : β ∉ innerAut C := congr_not_mem_innerAut e₁ hout
    have hK₃ : Nat.card K = (p ^ f) ^ 3 := hK
    have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK₃, ← pow_mul, mul_comm]
    obtain ⟨-, hcyc, Θ, hΘ, -⟩ :=
      CFSG.RankThree.Chevalley.triality_normal_form_data hp hf K hK₃ σ hσ
    haveI := hcyc
    obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
      CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
        hp hf K hK₃ σ hσ Θ hΘ hp hp4 ⊤ le_top ⟨β, Subgroup.mem_top _⟩ hβin
        (by rw [Subgroup.orderOf_mk]; exact hβ)
    have hh₀' : MulAut.conj h₀ * β * (MulAut.conj h₀)⁻¹ =
        fieldActor (t := TwistTag.D4) σ (Θ β) := hh₀
    obtain ⟨f', hff'⟩ := hpf
    have hd : 1 ≤ f' := by
      rcases Nat.eq_zero_or_pos f' with h | h
      · rw [h, mul_zero] at hff'
        omega
      · exact h
    obtain ⟨φ, hφ, hφord, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
        (by omega : 1 ≤ 3 * f) hK3
    obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
    have hδc : ∀ c, δc c = c ^ p ^ (3 * f') := fun c => by
      rw [← hδcdef]
      exact ringAut_pow_apply_of_frobenius hφ _ c
    have hδcord : orderOf δc = p := by
      rw [← hδcdef, orderOf_pow_of_dvd (by omega)
        (by rw [hφord, hff']; exact ⟨p, by ring⟩), hφord, hff',
        show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
    have hzp : Subgroup.zpowers (Θ β) = Subgroup.zpowers δc := by
      have h1 : Nat.card (Subgroup.zpowers (Θ β)) = p := by
        rw [Nat.card_zpowers]; exact hηord
      have h2 : Nat.card (Subgroup.zpowers δc) = p := by rw [Nat.card_zpowers, hδcord]
      have : Finite (Subgroup.zpowers (Θ β)) :=
        Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
      have : Finite (Subgroup.zpowers δc) :=
        Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
      exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)
    have hfix_eq :
        fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ β)) =
          fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
      have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
        (fieldActorHom (t := TwistTag.D4) σ) hzp
      ext y
      exact SetLike.ext_iff.1 h y
    have hK' : Nat.card K = p ^ (3 * f' * p) := by
      rw [hK3, hff']; congr 1; ring
    have hσ' : ∀ c, σ c = c ^ p ^ (f' * p) := fun c => by
      rw [hσ c, hff', mul_comm p f']
    have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
    obtain ⟨-, -, hk, -, -, -, hmap, hsimple, -, -, -, -, -, -, -⟩ :=
      CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hp
        hd hp.two_le hm3 K hK' σ hσ' δc hδc
    set δ₀ := fieldActor (t := TwistTag.D4) σ δc with hδ₀
    haveI := hsimple
    let e3 : ↥(fixSubgroup δ₀) ≃* ↥(trialityFieldImage σ δc) :=
      (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).trans
        (MulEquiv.subgroupCongr hmap)
    have hsimE : IsSimpleGroup ↥(fixSubgroup δ₀) := e3.isSimpleGroup
    have hk3 : Nat.card (fixSubfield δc) = (p ^ f') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
    haveI : Finite (fixSubfield δc) := Subtype.finite
    obtain ⟨r, hr, hσr⟩ := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_cubic_exponent hp
      hp3 (fixSubfield δc) hk σ hσ'
    have hσ₀ : ∀ c, fixSubfieldRestrict σ δc c = c ^ ((p ^ f') ^ r) := fun c =>
      Subtype.ext (hσr c)
    let eJ : graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
        (fixSubfieldRestrict σ δc).toRingHom ≃* ↥(trialityFieldImage σ δc) :=
      Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δc).subtype)
        (baseChangeGL_injective _)
    obtain ⟨σ₁, hσ₁, ⟨eo⟩⟩ : ∃ σ₁ : fixSubfield δc ≃+* fixSubfield δc,
        (∀ c, σ₁ c = c ^ (p ^ f')) ∧
        Nonempty (graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
            (fixSubfieldRestrict σ δc).toRingHom ≃*
          graphFixedRootGroup TwistTag.D4 (fixSubfield δc) σ₁.toRingHom) := by
      rcases hr with rfl | rfl
      · exact ⟨fixSubfieldRestrict σ δc, fun c => by rw [hσ₀, pow_one], ⟨MulEquiv.refl _⟩⟩
      · have h₁ : ∀ c, (fixSubfieldRestrict σ δc).symm c = c ^ (p ^ f') := fun c => by
          rw [RingEquiv.symm_apply_eq, hσ₀, ← pow_mul,
            show p ^ f' * (p ^ f') ^ 2 = (p ^ f') ^ 3 by ring]
          have : Fintype (fixSubfield δc) := Fintype.ofFinite _
          have hq : Fintype.card (fixSubfield δc) = (p ^ f') ^ 3 := by
            rw [← Nat.card_eq_fintype_card, hk3]
          rw [← hq]
          exact (FiniteField.pow_card c).symm
        exact ⟨(fixSubfieldRestrict σ δc).symm, h₁,
          exists_mulEquiv_graphFixedRootGroup_inv_D4 (fixSubfield δc) (fixSubfieldRestrict σ δc)
            (fixSubfieldRestrict σ δc).symm
            (fun c => (fixSubfieldRestrict σ δc).apply_symm_apply c)⟩
    have hmodel :=
      CFSG.HardMathSupport.Dickson.DefCharOuter.Export.excTwistedModel_graphFixedRootGroup
        TwistTag.D4 hp hd (fixSubfield δc) hk3 σ₁ hσ₁
    have hL : CFSG.Blueprint.LieModel (graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
        σ₁.toRingHom) .trialityD4 0 p f' :=
      Or.inr (Or.inl ⟨rfl, by decide, ⟨⟨hp, hd, rfl⟩, hmodel⟩⟩)
    have hcongr : MulAut.congr (e₁.trans (MulAut.conj h₀ : C ≃* C)) x =
        fieldActor (t := TwistTag.D4) σ (Θ β) := by
      have h1 : MulAut.congr (e₁.trans (MulAut.conj h₀ : C ≃* C)) x =
          MulAut.conj h₀ * β * (MulAut.conj h₀)⁻¹ := by
        ext y
        rfl
      rw [h1, hh₀']
    haveI := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.normal_subgroupOf_self
      (fixSubgroup δ₀)
    obtain ⟨E0⟩ := nonempty_barOf_equiv_of_eq hp _ hcongr hfix_eq le_rfl hsimE
      (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.isSolvable_quotient_self _) hI
    have hdf : f / p = f' := by rw [hff', Nat.mul_div_cancel_left _ hp.pos]
    refine ⟨⟨f', hff'⟩, ?_⟩
    rw [hdf]
    exact CFSG.Blueprint.LieModel.of_mulEquiv ((E0.trans e3).trans (eJ.symm.trans eo)).symm hL
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end ExcTwisted

theorem input9_1FieldAt_of_small {t : StatedLieTag}
    (ht : ∀ n p f, StatedLieAdmissible t n p f → p = 2 ∨ p = 3) : Input9_1FieldAt t := by
  intro S _ _ n p f hp hp5 hS
  rcases ht n p f (CFSG.Blueprint.LieModel.admissible hS) with h | h <;> omega

section Main


theorem input14_18_of_inputs (h91 : Input9_1Field) : Lemma1315b.Input14_18 := by
  intro p hp hp3 K _ _ hKhat hO hchev J _ x hJ hpump
  obtain ⟨hxo, J1, hJ1, ⟨eJ⟩⟩ := hpump
  have hp5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have hp2 : p ≠ 2 := by omega
  have hq : CFSG.Open.IsQuasisimple K := hKhat.1
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hKD : KDChevInner p :=
    CFSG.LocalAnalysis.GLTheoremA.kdChevInner_of hp hp2
      (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds hp hp2)
      (CFSG.LocalAnalysis.GLTheoremA.kdAmbSolv_holds hp hp2
        CFSG.LocalAnalysis.GLTheoremA.u42_fixSubgroup_solvable)
  by_cases hin : x ∈ innerAut K
  · exact (false_of_inner hp hKD hq hchev hxo hin hJ1).elim
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_outer hp (CFSG.LocalAnalysis.GLTheoremA.kd65_holds hp hp2) hq hO hchev hxp hin
  let eSK : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hchevK : IsChevSimple p K :=
    CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv eSK hchev
  have hL2 : CFSG.Blueprint.LieModel (barOf p J1) .PSL 2 p 1 := lieModel_of_isLpType hp hp5 eJ hJ
  have hO' : LieOrderFormulasInput :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  rcases hchevK with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie d =>
      have hdp : d.1.characteristic = p := hi
      obtain ⟨t, n, p', f, hX, hpp', -⟩ := AltFacts4.exists_blueprint_tagged d e
      have hp' : p' = p := hpp'.trans hdp
      subst hp'
      have key : p' ∣ f ∧ CFSG.Blueprint.LieModel (barOf p' J1) t n p' (f / p') :=
        h91 t K n p' f hp hp5 hX x hxo hin J1 hJ1
      obtain ⟨hpf, hLie⟩ := key
      obtain ⟨rfl, rfl, hf1⟩ := psl_two_of_lieModel hO' hLie hL2
      have hfp : f = p' := by
        obtain ⟨c, rfl⟩ := hpf
        rw [Nat.mul_div_cancel_left c hp.pos] at hf1
        rw [hf1, mul_one]
      subst hfp
      obtain ⟨-, F, hF, hFin, hFc, ⟨φ⟩⟩ := hX.statedClassicalModel (by decide)
      exact ⟨F, hF, hFin, hFc, ⟨φ⟩⟩
  ·
    exfalso
    have hamb := CFSG.LocalAnalysis.GLTheoremA.kdAmbSolv_holds hp hp2
      CFSG.LocalAnalysis.GLTheoremA.u42_fixSubgroup_solvable
    have hα1 : MulAut.congr e x ≠ 1 := by
      intro h1
      have : orderOf (MulAut.congr e x) = 1 := by rw [h1, orderOf_one]
      rw [MulEquiv.orderOf_eq, hxo] at this
      exact hp.one_lt.ne' this
    have hαp : MulAut.congr e x ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hsolv := hamb i hi (MulAut.congr e x) hαp hα1
    rw [CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr] at hsolv
    haveI : Group.IsSolvable ↥((fixSubgroup x).map e.toMonoidHom) := hsolv
    have hsolvx : Group.IsSolvable ↥(fixSubgroup x) :=
      Group.isSolvable_of_isSolvable_injective
        (f := ((fixSubgroup x).equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        ((fixSubgroup x).equivMapOfInjective e.toMonoidHom e.injective).injective
    have hJ1' : GLAPComponent p (fixSubgroup x) J1 := by
      rw [← fixSub_eq_fixSubgroup]
      exact hJ1
    exact CFSG.HardMathSupport.Dickson.DefCharOuter.Export.not_glaPComponent_of_solvable hsolvx hJ1'

theorem input9_1Field_holds : Input9_1Field := by
  intro t
  cases t
  case PSL => exact input9_1FieldAt_PSL
  case PSU => exact input9_1FieldAt_PSU
  case PSp => exact input9_1FieldAt_PSp
  case POmegaOdd => exact input9_1FieldAt_POmegaOdd
  case POmegaPlus => exact input9_1FieldAt_POmegaPlus
  case POmegaMinus => exact input9_1FieldAt_POmegaMinus
  case G2 => exact input9_1FieldAt_G2
  case F4 => exact input9_1FieldAt_F4
  case E6 => exact input9_1FieldAt_E6
  case E7 => exact input9_1FieldAt_E7
  case E8 => exact input9_1FieldAt_E8
  case twistedE6 => exact input9_1FieldAt_twistedE6
  case trialityD4 => exact input9_1FieldAt_trialityD4
  case twistedB2 => exact input9_1FieldAt_of_small fun _ _ _ h => Or.inl h.2.2.2.1
  case twistedF4 => exact input9_1FieldAt_of_small fun _ _ _ h => Or.inl h.2.2.2.1
  case twistedG2 => exact input9_1FieldAt_of_small fun _ _ _ h => Or.inr h.2.2.2.1
  case Tits => exact input9_1FieldAt_of_small fun _ _ _ h => Or.inl h.2.2.2.1

theorem input14_18_holds : Lemma1315b.Input14_18 :=
  input14_18_of_inputs input9_1Field_holds

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.PumpDefChar

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.PumpDefChar

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

section ChevDown


theorem kdChevDownQ_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (r : ℕ) :
    CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p r := by
  by_cases hp3 : p = 3
  · subst hp3
    exact CFSG.LocalAnalysis.GLTheoremA.kdChevDownQ_three_of_lieComp
      CFSG.LocalAnalysis.GLTheoremA.lieComp_holds r
  · have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    exact Inputs1315.kdChevDownQ_five_le hp (by have := hp.two_le; omega)

theorem chevDown_of_kd {G : Type} [Group G] [Finite G] {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p r) {e a : G} {J0 J1 : Subgroup G}
    (hae : a * e = e * a) (hap : a ^ p = 1) (hJ1 : GLAPComponent p (Cg e) J1)
    (hJ0 : GLAPComponent p (GLAPLayer p (Kx p J0 e ⊓ Cg a)) J0)
    (hKx : Kx p J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1)
    (hr : IsChevSimple r (barOf p J1 ⧸ Subgroup.center (barOf p J1))) :
    IsChevSimple r (barOf p J0 ⧸ Subgroup.center (barOf p J0)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Js : Subgroup G := ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1 with hJs
  rw [hKx] at hJ0
  have hcomp : ∀ g ∈ Subgroup.zpowers a, GLAPComponent p (Cg e) (GLBConj g J1) := by
    intro g hg
    have hge : g * e = e * g := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact (Commute.zpow_left hae k).eq
    have := glaPComponent_gLBConj hJ1 g
    rwa [Prop1116Design.gLBConj_cg_eq hge] at this
  have hJsn : IsSubnormal Js (Cg e) := by
    have hJs' : Js = sSup ((fun g => GLBConj g J1) '' (Subgroup.zpowers a : Set G)) := by
      rw [hJs, sSup_image]
      rfl
    rw [hJs']
    exact CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp _
      (by rintro L ⟨g, hg, rfl⟩; exact hcomp g hg)
  have hlayer : IsSubnormal (GLAPLayer p (Js ⊓ Cg a)) (Js ⊓ Cg a) :=
    CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp
      {L | GLAPComponent p (Js ⊓ Cg a) L} fun _ h => h
  have hJ0a : GLAPComponent p (Js ⊓ Cg a) J0 := l119_glaPComponent_of_isSubnormal hp hlayer hJ0
  have hJ0' : GLAPComponent p (Cg e ⊓ Subgroup.centralizer ({a} : Set G)) J0 :=
    l119_glaPComponent_of_isSubnormal hp (isSubnormal_inf hJsn (Cg a)) hJ0a
  have hq1 : CFSG.Open.IsQuasisimple (barOf p J1) :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_barX_iff hp hJ1.2.1).1
      hJ1.2.2.1.2.2
  by_cases haN : a ∈ Subgroup.normalizer (J1 : Set G)
  ·
    have hJsJ : Js = J1 := by
      refine le_antisymm (iSup₂_le fun g hg => ?_) (le_iSup₂_of_le 1 (Subgroup.one_mem _) (by
        rw [gLBConj_one]))
      have hgN : g ∈ Subgroup.normalizer (J1 : Set G) :=
        (Subgroup.zpowers_le.2 haN) hg
      exact (mem_normalizer_iff_gLBConj_eq.1 hgN).le
    have hJ0'' : GLAPComponent p (J1 ⊓ Subgroup.centralizer ({a} : Set G)) J0 := by
      rw [← hJsJ]
      exact hJ0a
    exact CFSG.LocalAnalysis.GLTheoremA.chevQ_step hp hD hJ1 hr haN hap hJ0''
  ·
    have ha1 : a ≠ 1 := fun h => haN (h ▸ (Subgroup.normalizer (J1 : Set G)).one_mem)
    have haC : a ∈ Cg e := Subgroup.mem_centralizer_singleton_iff.2 hae
    have hle : barX p (Cg e) J0 ≤ barX p (Cg e) Js := barX_mono (hJ0a.1.trans inf_le_left)
    obtain ⟨π, hπs, hπk, -⟩ := Inputs183eqv.input18_3_eqv_holds G p hp hp2 (Cg e) J1
      (Subgroup.zpowers a) hJ1 (AltFacts5.isElemAbelian_zpowers hap) (Subgroup.zpowers_le.2 haC)
      a (Subgroup.mem_zpowers a) ha1 haC (Or.inl haN) J0 hJ0' hle
    obtain ⟨e1⟩ := Claims126.nonempty_quot_center_quot hq1.1 π.ker hπk
    have e2 : (barOf p J0 ⧸ Subgroup.center (barOf p J0)) ≃*
        (barOf p J1 ⧸ Subgroup.center (barOf p J1)) :=
      (Lemma1315b.centerQuotEquiv (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm).trans e1
    exact CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv e2.symm hr

theorem input14_4_ChevDown_holds : Claims1116.Input14_4_ChevDown := by
  intro G _ _ p hp hp2 e a J0 J1 hae hap hJ1 hJ0 hKx r hr
  exact chevDown_of_kd hp hp2 (kdChevDownQ_odd hp hp2 r) hae hap hJ1 hJ0 hKx hr

end ChevDown

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.PumpDefChar
