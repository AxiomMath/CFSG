module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma105

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

abbrev layerC (p : ℕ) (X : Subgroup G) (y : G) : Subgroup G := GLAPLayer p (X ⊓ cx y)

theorem odd_core_of_caseU (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hU : CaseU G p B x L b) {a : G} (haB : a ∈ B) :
    Odd (Nat.card (GLAPPrimeCoreOf p (cx a))) := by
  have hS := sstar_triple h.star
  have hp := hc.ctx.prime
  have hp3 := hU.p3
  have hrk := hU.rank
  subst hp3
  obtain ⟨A, hAel, hAB, hAcard⟩ := hU.centRank
  have hAa : A ≤ cx a := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hAB hg) a haB).symm
  have hBcard : Nat.card B = 3 ^ 4 := by
    rw [hS.1.2.1, hrk]
  refine S8.odd_core_of_big_rank hp hS.1 hAa hAel ?_
  rw [hBcard]
  calc 3 ^ 4 < 3 ^ 5 := by norm_num
    _ ≤ Nat.card A := hAcard

theorem hasTL_of_caseU (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : CaseU G p B x L b) : HasTL p B L := by
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hodd := odd_core_of_caseU hc h hU ((dgrp_facts hc h).1 hxD)
  refine exists_T_in_L hc hin h ?_
  intro T hTO hT2 _
  rw [eq_bot_of_le_odd hT2 hodd hTO]
  simp

private theorem caseU_isSimple_of_isU4eight {S : Type} [Group S] (h : catalogIs S S9.isU4eight) :
    IsSimpleGroup S :=
  isSimple_of_isU4eight h

private theorem caseU_subsingleton_quot {Q : Type} [Group Q] [Subsingleton Q] (N : Subgroup Q) :
    Subsingleton (Q ⧸ N) :=
  ⟨fun a b => by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim u v]⟩

theorem psimple_L_isU48 (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hU : CaseU G p B x L b) : catalogIs (PSimple p L) S9.isU4eight := by
  have hp3 := hU.p3
  subst hp3
  have hL : GLAPComponent 3 (cx x) L := (sstar_triple h.star).2.2
  have hsimple : IsSimpleGroup ↥L := caseU_isSimple_of_isU4eight hU.L_iso
  have hPS : IsSimpleGroup (PSimple 3 L) := (isQuasisimple_pQuot_of_glaPComponent hc.ctx.prime hL).2
  haveI := hPS.toNontrivial
  have hne_top : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PQuot 3 L) := by
      unfold PQuot
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (PSimple 3 L) (caseU_subsingleton_quot _)
  have hO : GLAPPrimeCore 3 ↥L = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥L)).resolve_right hne_top
  have eQ : PQuot 3 L ≃* ↥L := (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hsQ : IsSimpleGroup (PQuot 3 L) := eQ.isSimpleGroup
  have hZ : Subgroup.center (PQuot 3 L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PQuot 3 L)) with h1 | h1
    · exact h1
    · exfalso
      have hsub : Subsingleton (PSimple 3 L) := by
        unfold PSimple
        rw [h1]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton (PSimple 3 L) hsub
  have ePS : PSimple 3 L ≃* ↥L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eQ
  exact (catalogIs_congr ePS).2 hU.L_iso

theorem exists_z_L (hc : S10Ctx G p) (hin : Lemma105Inputs G p) (hu : U48CentInvAt G) {B : Subgroup G}
    {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : CaseU G p B x L b) :
    ∃ z : G, z ^ 2 = 1 ∧ z ≠ 1 ∧ IsCentralIn 2 z L ∧ B ≤ Subgroup.centralizer ({z} : Set G) := by
  have hp3 := hU.p3
  subst hp3
  obtain ⟨T, hTL, hT2, hTB, hTO⟩ := hasTL_of_caseU hc hin.l103 h hU
  obtain ⟨E₂, hE₂I, hE₂el, hE₂card, hBE, -⟩ := hU.decomp
  have hE₂B : E₂ ≤ B := by
    rw [hBE]
    exact le_sup_right
  exact hu (cx x) L B E₂ T (sstar_triple h.star).2.2 hU.L_iso (sstar_norm h.star) (B_el h)
    hE₂B (hE₂I.trans (layer_le _ _ |>.trans inf_le_left)) hE₂card hTL hT2 hTO hTB

private theorem caseU_mem_Ipart {B : Subgroup G} {L : Subgroup G} {b z : G} (hb : b ∈ B)
    (hzL : IsCentralIn 2 z L) (hBz : B ≤ Subgroup.centralizer ({z} : Set G))
    (hI : Ipart p L b = L ⊓ cx b) : z ∈ Ipart p L b := by
  rw [hI]
  exact ⟨hzL.1, Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 (hBz hb)).symm⟩

theorem z_mem_I (hz : U48CentInvFieldAt G) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hU : CaseU G p B x L b) {z : G} (hz2 : z ^ 2 = 1) (hzL : IsCentralIn 2 z L)
    (hBz : B ≤ Subgroup.centralizer ({z} : Set G)) : z ∈ Ipart p L b ∧ IsCentralIn 2 z (Ipart p L b) := by
  refine ⟨caseU_mem_Ipart h.mem hzL hBz hU.I_eq, ?_⟩
  have hp3 := hU.p3
  subst hp3
  rw [hU.I_eq]
  exact hz (cx x) L b z (sstar_triple h.star).2.2 hU.L_iso hU.field hz2 hzL
    (Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 (hBz h.mem)).symm)

theorem exists_z (hc : S10Ctx G p) (hin : Lemma105Inputs G p) (hu : U48CentInvAt G) (hz : U48CentInvFieldAt G)
    {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hU : CaseU G p B x L b) :
    ∃ z : G, z ∈ Ipart p L b ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧ IsCentralIn 2 z (Ipart p L b) ∧
      B ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨z, hz2, hz1, hzL, hBz⟩ := exists_z_L hc hin hu h hU
  obtain ⟨hzI, hzIc⟩ := z_mem_I hz h hU hz2 hzL hBz
  exact ⟨z, hzI, hz2, hz1, hzIc, hBz⟩

theorem Icomp_of_cfg (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) :
    GLAPComponent p (L ⊓ cx b) (Ipart p L b) ∧ IsChevSimple 2 (PSimple p (Ipart p L b)) :=
  hin.i91comp (cx x) L b (sstar_triple h.star).2.2 (sstar_chev2 hc h.star) ((B_el h).2 b h.mem) h.prop h.I_ne

theorem odd_core_I (hc : S10Ctx G p) (hin : Lemma103Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) (hU : CaseU G p B x L b) : Odd (Nat.card (GLAPPrimeCoreOf p (Ipart p L b))) := by
  rw [hU.I_core, Subgroup.card_bot]
  exact odd_one

private theorem caseU_decomp_of_mem_D {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) {a d e : G} (ha : a ∈ D) (ha1 : a ≠ 1) (hd : d ∈ D) (he : e ∈ D)
    (hda : d ∉ Subgroup.zpowers a) (hea : e ∉ Subgroup.zpowers a) :
    ∃ i j : ℕ, e = a ^ i * d ^ j ∧ ¬ p ∣ j := by
  haveI := Fact.mk hp
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, y * x = x * y := fun x hx y hy =>
    congrArg Subtype.val (hD.1.is_comm.comm (⟨y, hy⟩ : D) ⟨x, hx⟩)
  have hd1 : d ≠ 1 := fun h => hda (h ▸ Subgroup.one_mem _)
  have hA : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hD.2 a ha) ha1]
  have hB : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hD.2 d hd) hd1]
  have hnorm : ∀ x ∈ D, ∀ y ∈ D, y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro x hx y hy
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_right (show Commute y x from hcomm x hx y hy) k)).eq.symm
  have hBN : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    Subgroup.zpowers_le.2 (hnorm a ha d hd)
  have hAN : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    Subgroup.zpowers_le.2 (hnorm d hd a ha)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hBN
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers d = ⊥ := by
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers a ⊓ Subgroup.zpowers d ≤
      Subgroup.zpowers a)
    rw [hA] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers d = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [h1, hA]))
      have hle : Subgroup.zpowers a ≤ Subgroup.zpowers d := inf_eq_left.1 heq
      have heq2 : Subgroup.zpowers a = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hA, hB]))
      exact hda (by rw [heq2]; exact Subgroup.mem_zpowers d)
  have hsup : Subgroup.zpowers a ⊔ Subgroup.zpowers d = D := by
    have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤ D :=
      sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hd)
    refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
    rw [hinf, Subgroup.card_bot, hA, hB, mul_one] at hprod
    rw [hDc, sq, hprod]
  have hmem : e ∈ (↑(Subgroup.zpowers a ⊔ Subgroup.zpowers d) : Set G) := by
    rw [hsup]
    exact he
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hmem
  obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hx)
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hy)
  refine ⟨i, j, hxy.symm, ?_⟩
  rintro ⟨k, rfl⟩
  apply hea
  rw [← hxy, pow_mul, hD.2 d hd, one_pow, mul_one]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i

private theorem caseU_conjQ_mul {p : ℕ} {M : Subgroup G} {x y : G} (hx : x ∈ Subgroup.normalizer (M : Set G))
    (hy : y ∈ Subgroup.normalizer (M : Set G)) (q : PQuot p M) :
    lemma102_conjQ p (Subgroup.mul_mem _ hx hy) q = lemma102_conjQ p hy (lemma102_conjQ p hx q) := by
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [lemma102_conjQ_mk, lemma102_conjQ_mk, lemma102_conjQ_mk]
    congr 1
    apply Subtype.ext
    show (x * y)⁻¹ * (l : G) * (x * y) = y⁻¹ * (x⁻¹ * (l : G) * x) * y
    group

private theorem caseU_conjQ_congr {p : ℕ} {M : Subgroup G} {g g' : G} (h : g = g')
    (hg : g ∈ Subgroup.normalizer (M : Set G)) (hg' : g' ∈ Subgroup.normalizer (M : Set G))
    (q : PQuot p M) : lemma102_conjQ p hg q = lemma102_conjQ p hg' q := by
  subst h
  rfl

private theorem caseU_conjQ_one {p : ℕ} {M : Subgroup G} (q : PQuot p M) :
    lemma102_conjQ p (Subgroup.one_mem _ : (1 : G) ∈ Subgroup.normalizer (M : Set G)) q = q := by
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [lemma102_conjQ_mk]
    congr 1
    apply Subtype.ext
    simp [lemma102_conjHomL_val]

private theorem caseU_conjQ_cent {p : ℕ} {M : Subgroup G} {a : G} (hc : CentMod p M a)
    (ha : a ∈ Subgroup.normalizer (M : Set G)) (q : PQuot p M) : lemma102_conjQ p ha q = q := by
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [lemma102_conjQ_mk, QuotientGroup.eq]
    have hO := lemma102_mem_glaPPrimeCoreOf_comm hc l.2
    have hO' : ((lemma102_conjHomL ha l : ↥M) : G)⁻¹ * (l : G) ∈ GLAPPrimeCoreOf p M := by
      have e1 : ((lemma102_conjHomL ha l : ↥M) : G)⁻¹ * (l : G) =
          ((l : G)⁻¹ * (a⁻¹ * (l : G) * a))⁻¹ := by
        rw [lemma102_conjHomL_val]
        group
      rw [e1]
      exact Subgroup.inv_mem _ hO
    exact (lemma102_mem_glaPPrimeCore_iff (M.mul_mem (M.inv_mem (lemma102_conjHomL ha l).2) l.2)).2 hO'

private theorem caseU_conjQ_pow_cent {p : ℕ} {M : Subgroup G} {a : G} (hc : CentMod p M a)
    (ha : a ∈ Subgroup.normalizer (M : Set G)) (i : ℕ) (q : PQuot p M) :
    lemma102_conjQ p (Subgroup.pow_mem _ ha i) q = q := by
  induction i generalizing q with
  | zero =>
    rw [caseU_conjQ_congr (pow_zero a) (Subgroup.pow_mem _ ha 0) (Subgroup.one_mem _)]
    exact caseU_conjQ_one q
  | succ n ih =>
    rw [caseU_conjQ_congr (pow_succ a n) (Subgroup.pow_mem _ ha (n + 1))
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ ha n) ha)]
    rw [caseU_conjQ_mul (Subgroup.pow_mem _ ha n) ha q, ih q, caseU_conjQ_cent hc ha q]

private theorem caseU_conjQ_pow_iter {p : ℕ} {M : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (M : Set G)) (j : ℕ) (q : PQuot p M) :
    lemma102_conjQ p (Subgroup.pow_mem _ hd j) q = (⇑(lemma102_conjQ p hd))^[j] q := by
  induction j generalizing q with
  | zero =>
    rw [caseU_conjQ_congr (pow_zero d) (Subgroup.pow_mem _ hd 0) (Subgroup.one_mem _)]
    rw [Function.iterate_zero_apply]
    exact caseU_conjQ_one q
  | succ n ih =>
    rw [caseU_conjQ_congr (pow_succ d n) (Subgroup.pow_mem _ hd (n + 1))
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hd n) hd)]
    rw [caseU_conjQ_mul (Subgroup.pow_mem _ hd n) hd q, ih q, Function.iterate_succ_apply']

private theorem caseU_iter_induced {p : ℕ} {M : Subgroup G} {d : G} (hd : d ∈ Subgroup.normalizer (M : Set G))
    {R : Type} [Group R] {φ : MulAut R}
    {θ : PQuot p M ⧸ Subgroup.center (PQuot p M) ≃* R}
    (hφ : CFSG.Assembly.LargeEvenInduces θ (indRel p M d) φ) (n : ℕ) (q : PQuot p M) :
    (φ ^ n) (θ (QuotientGroup.mk q)) =
      θ (QuotientGroup.mk ((⇑(lemma102_conjQ p hd))^[n] q)) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, Function.iterate_succ_apply]
    rw [hφ q (lemma102_conjQ p hd q) ((lemma102_indRel_iff_conjQ hd q _).2 rfl)]
    exact ih _

private theorem caseU_primeField_pow {p : ℕ} (hp : p.Prime) {M : Subgroup G} {d e : G}
    (hd : d ∈ Subgroup.normalizer (M : Set G)) (he : e ∈ Subgroup.normalizer (M : Set G))
    {j : ℕ} (hpj : ¬ p ∣ j)
    (hce : ∀ q, lemma102_conjQ p he q = (⇑(lemma102_conjQ p hd))^[j] q)
    {lab : CFSG.Assembly.LargeEvenLabel} {R : Type} [Group R] {I F : Set (MulAut R)}
    {θ : PQuot p M ⧸ Subgroup.center (PQuot p M) ≃* R}
    (hF : ∀ f ∈ F, ∀ n : ℕ, 0 < n → f ^ n ∈ F)
    (hP : CFSG.Assembly.LargeEvenPrimeField p lab I F
      (CFSG.Assembly.LargeEvenInduces θ (indRel p M d))) :
    CFSG.Assembly.LargeEvenPrimeField p lab I F (CFSG.Assembly.LargeEvenInduces θ (indRel p M e)) := by
  obtain ⟨htag, f, hf, u, hu, hord, hα⟩ := hP
  have hj0 : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; exact hpj (dvd_zero p))
  refine ⟨htag, f ^ j, hF f hf j hj0, u, hu, ?_, ?_⟩
  · rw [orderOf_pow' f hj0.ne', hord, Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).2 hpj),
      Nat.div_one]
  · rw [← conj_pow]
    intro l l' hll
    rw [lemma102_indRel_iff_conjQ he l l'] at hll
    rw [← hll, hce l]
    exact caseU_iter_induced hd hα j l

private theorem caseU_fieldOn_of_closed
    (hcl : ∀ (lab : CFSG.Assembly.LargeEvenLabel), CFSG.Assembly.LargeEvenInLambda2 lab →
      ∀ Q : CFSG.Assembly.LargeEvenRawCont, CFSG.Assembly.LargeEvenRawDatum lab Q →
        CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F =>
          Q R I F ∧ ∀ f ∈ F, ∀ n : ℕ, 0 < n → f ^ n ∈ F)
    {p : ℕ} (hp : p.Prime) {M D : Subgroup G} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) {a d e : G} (ha : a ∈ D) (ha1 : a ≠ 1) (hd : d ∈ D) (he : e ∈ D)
    (hda : d ∉ Subgroup.zpowers a) (hea : e ∉ Subgroup.zpowers a) (hacm : CentMod p M a)
    (hfd : FieldOn p d M) : FieldOn p e M := by
  obtain ⟨i, j, rfl, hpj⟩ := caseU_decomp_of_mem_D hp hD hDc ha ha1 hd he hda hea
  obtain ⟨hdN, hmark⟩ := hfd
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark
  have haN : a ∈ Subgroup.normalizer (M : Set G) := (centMod_iff.1 hacm).1
  have heN : a ^ i * d ^ j ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ haN i) (Subgroup.pow_mem _ hdN j)
  have hce : ∀ q, lemma102_conjQ p heN q = (⇑(lemma102_conjQ p hdN))^[j] q := by
    intro q
    rw [caseU_conjQ_mul (Subgroup.pow_mem _ haN i) (Subgroup.pow_mem _ hdN j) q,
      caseU_conjQ_pow_cent hacm haN i q, caseU_conjQ_pow_iter hdN j q]
  unfold FieldOn
  refine ⟨heN, hcomm, lab, hlab, ?_⟩
  refine lemma103_rawDatum_mono (fun R _ I F h => ?_) (hcl lab hlab _ hraw)
  obtain ⟨⟨hsimp, hnc, θ, hP⟩, hF⟩ := h
  exact ⟨hsimp, hnc, θ, caseU_primeField_pow hp hdN heN hpj hce hF hP⟩

theorem fieldOn_of_mem_D (hcl : FieldAutPowClosedAt) {p : ℕ} (hp : p.Prime) {M D : Subgroup G}
    (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) {a d e : G} (ha : a ∈ D) (ha1 : a ≠ 1) (hd : d ∈ D) (he : e ∈ D)
    (hda : d ∉ Subgroup.zpowers a) (hea : e ∉ Subgroup.zpowers a) (hacm : CentMod p M a)
    (hfd : FieldOn p d M) : FieldOn p e M :=
  caseU_fieldOn_of_closed hcl hp hD hDc ha ha1 hd he hda hea hacm hfd

theorem nonInner_of_mem_D {p : ℕ} (hp : p.Prime) {M D : Subgroup G} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) {a d e : G} (ha : a ∈ D) (ha1 : a ≠ 1) (hd : d ∈ D) (he : e ∈ D)
    (hda : d ∉ Subgroup.zpowers a) (hea : e ∉ Subgroup.zpowers a) (hacm : CentMod p M a)
    (hnd : NonInner p d M) : NonInner p e M := by
  obtain ⟨i, j, rfl, hpj⟩ := caseU_decomp_of_mem_D hp hD hDc ha ha1 hd he hda hea
  obtain ⟨hdN, hnd'⟩ := hnd
  have haN : a ∈ Subgroup.normalizer (M : Set G) := (centMod_iff.1 hacm).1
  have hdjN : d ^ j ∈ Subgroup.normalizer (M : Set G) := Subgroup.pow_mem _ hdN j
  have haiC : CentMod p M (a ^ i) := centMod_iff.2 (Subgroup.pow_mem _ (centMod_iff.1 hacm) i)
  have heN : a ^ i * d ^ j ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ haN i) hdjN
  refine ⟨heN, fun hinn => hnd' ?_⟩
  have hcomm : a ^ i * d ^ j = d ^ j * a ^ i :=
    ((show Commute a d from isElemAbelian_commute hD ha hd).pow_pow i j).eq
  have h1 : InducesInnerMod p M (d ^ j * a ^ i) := by
    rw [← hcomm]
    exact hinn
  have h2 : InducesInnerMod p M (d ^ j) := (lemma102_inducesInnerMod_mul_cent hdjN haiC).1 h1
  have hpj' : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpj).symm
  have hdp : d ^ p = 1 := hD.2 d hd
  have hbez : (1 : ℤ) = (j : ℤ) * Nat.gcdA j p + (p : ℤ) * Nat.gcdB j p := by
    have := Nat.gcd_eq_gcd_ab j p
    rw [Nat.Coprime.gcd_eq_one hpj'] at this
    simpa using this
  have hdz : d = (d ^ j) ^ (Nat.gcdA j p) := by
    calc d = d ^ (1 : ℤ) := (zpow_one d).symm
      _ = d ^ ((j : ℤ) * Nat.gcdA j p + (p : ℤ) * Nat.gcdB j p) := by rw [← hbez]
      _ = (d ^ (j : ℤ)) ^ (Nat.gcdA j p) * (d ^ (p : ℤ)) ^ (Nat.gcdB j p) := by
        rw [zpow_add, zpow_mul, zpow_mul]
      _ = (d ^ j) ^ (Nat.gcdA j p) := by
        rw [zpow_natCast, zpow_natCast, hdp]
        simp
  have h3 := S3.inducesInnerMod_zpow h2 (Nat.gcdA j p)
  rw [← hdz] at h3
  exact h3

private theorem caseU_prime_eq_two_of_card_eight (q : TauCeti.PrimePower) (h : q.card = 8) :
    q.p = 2 := by
  have hdvd : q.p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  rw [h] at hdvd
  have h2 : q.p ∣ 2 := q.prime_p.dvd_of_dvd_pow (n := 3) (by norm_num; exact hdvd)
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h2

theorem isChevTwo_of_isU3eight {S : Type} [Group S] (h : catalogIs S S9.isU3eight) : IsChevSimple 2 S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  refine Or.inl ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | cyclic p hp => simp [S9.isU3eight, onLie] at hi
  | alternating n hn => simp [S9.isU3eight, onLie] at hi
  | sporadic s => simp [S9.isU3eight, onLie] at hi
  | lie j =>
    obtain ⟨d, hv⟩ := j
    simp only [S9.isU3eight, onLie] at hi
    simp only [onLie]
    change d.characteristic = 2
    split at hi
    · rename_i q
      rw [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact caseU_prime_eq_two_of_card_eight q hi
    · exact absurd hi id

end S10

end CFSG.LocalAnalysis.GLTheoremA
