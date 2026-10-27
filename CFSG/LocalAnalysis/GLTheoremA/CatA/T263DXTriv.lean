module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXHardExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOut
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinctShapes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

private theorem exists_card_eq_two_pow {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcard⟩ := FiniteField.card K (ringChar K)
  exact ⟨f, f.pos, by rw [Nat.card_eq_fintype_card, hcard, hK2]⟩

theorem not_dvd_card_and_five_le_of_not_dvd_sq_sub_one {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1) :
    ¬ p ∣ Nat.card K ∧ 5 ≤ p := by
  obtain ⟨f, -, hcard⟩ := exists_card_eq_two_pow hK2
  have h3 : 3 ∣ Nat.card K ^ 2 - 1 := by
    have h4 : (2 : ℕ) ^ f * 2 ^ f = 4 ^ f := by rw [← mul_pow]; norm_num
    rw [hcard, sq, h4]
    exact Nat.sub_one_dvd_pow_sub_one 4 f
  refine ⟨fun h => hp2 ?_, ?_⟩
  · rw [hcard] at h
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
  · have hp3 : p ≠ 3 := by
      rintro rfl
      exact hpq h3
    have h2 := hp.two_le
    by_contra hlt
    have : p = 4 := by omega
    subst this
    exact absurd hp (by decide)

theorem conj_mem_subgroupStabAut_of_mem_normalizer {G : Type} [Group G] {J : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (J : Set G)) :
    MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut J := by
  show J.map (MulAut.conj w).toMonoidHom = J
  ext x
  rw [Subgroup.mem_map_equiv]
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hw)) x
  simpa [MulAut.conj_symm_apply] using this.symm

theorem mem_centralizer_of_restrict_eq_one {G : Type} [Group G] {J : Subgroup G}
    [Group.IsPerfect ↥J] {w : G} (hw : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut J)
    (h : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥J
      (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj w, hw⟩) = 1) :
    w ∈ Subgroup.centralizer (J : Set G) := by
  have h1 : CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj w, hw⟩ = 1 :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥J
      (h.trans (map_one _).symm)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h2 := congrArg (fun φ : MulAut ↥J => ((φ ⟨x, hx⟩ : ↥J) : G)) h1
  have h3 : w * x * w⁻¹ = x := by
    simpa [CFSG.GroupActions.subgroupStabRestrict_apply] using h2
  calc x * w = (w * x * w⁻¹) * w := by rw [h3]
    _ = w * x := by group

private theorem markDeg_ge_two {labS lab : GLALabel} (hnS : 2 ≤ labS.n)
    (hlam : CFSG.Assembly.LargeEvenInLambda2 lab)
    (hdvd : labS.n ∣ lab.n ∨ (lab.tag = .twD ∧ lab.rank = 2 ∧ labS.n ∣ 2 * lab.n)) :
    2 ≤ CFSG.StandardType.markDeg lab ∧ CFSG.StandardType.markChar lab = 2 := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn1, hrest⟩ := hlam
  simp only at hn1 hdvd
  rcases hdvd with h | ⟨htag, hrank, h⟩
  · have hle : labS.n ≤ n := Nat.le_of_dvd (by omega) h
    cases tag <;>
      simp only [CFSG.StandardType.markDeg, CFSG.StandardType.markChar, and_true] at hrest ⊢ <;>
      (try split_ifs) <;> omega
  · subst htag hrank
    simp [CFSG.StandardType.markDeg, CFSG.StandardType.markChar]
    omega

private theorem pRank_le_one_of_not_dvd {X : Type} [Group X] [Finite X] {p : ℕ}
    (hpX : ¬ p ∣ Nat.card X) : CFSG.pRank p X ≤ 1 := by
  unfold CFSG.pRank
  refine csSup_le' ?_
  rintro r ⟨A, -, hcard⟩
  by_contra hr
  apply hpX
  have h1 : p ∣ p ^ r := dvd_pow_self p (by omega)
  rw [← hcard] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card A)

private theorem label_of_exc {lab : GLALabel} {t : StatedLieTag} {f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (htag : CFSG.StandardType.markTag lab = t)
    (hdeg : CFSG.StandardType.markDeg lab = f) :
    lab.n = f ∧ ¬ MI.DerivedLab lab := by
  obtain ⟨tag, rank, n⟩ := lab
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases tag <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markDeg] at htag hdeg <;>
    (try split_ifs at htag hdeg) <;>
    simp_all [MI.DerivedLab]

theorem conj_ne_one_of_center_eq_bot {G : Type} [Group G] (hZ : Subgroup.center G = ⊥)
    {r : G} (hr1 : r ≠ 1) : MulAut.conj r ≠ 1 := by
  intro h
  refine hr1 (Subgroup.mem_bot.1 ?_)
  rw [← hZ, Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun f : MulAut G => f g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  rwa [mul_inv_eq_iff_eq_mul, eq_comm] at h1

theorem exists_chevModel_adjointGroup {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hG2 : τ = .G2 → 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    ∃ t : StatedLieTag, t ∈ chevalleyExceptionalTags ∧
      ChevalleyExceptionalModel ↥(adjointGroup τ K) t 2 f := by
  have hU := CFSG.HardMathSupport.Dickson.Sec6.I923.untwisted_adjointGroup (τ := τ) (k := K)
    (q := 2 ^ f) hK
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · have h3 : 3 ≤ 2 ^ f :=
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (hG2 rfl)
    exact ⟨.G2, by simp [chevalleyExceptionalTags], ⟨Nat.prime_two, by omega, rfl, h3⟩, hU⟩
  · exact ⟨.F4, by simp [chevalleyExceptionalTags], ⟨Nat.prime_two, by omega, rfl⟩, hU⟩
  · exact ⟨.E6, by simp [chevalleyExceptionalTags], ⟨Nat.prime_two, by omega, rfl⟩, hU⟩
  · exact ⟨.E7, by simp [chevalleyExceptionalTags], ⟨Nat.prime_two, by omega, rfl⟩, hU⟩
  · exact ⟨.E8, by simp [chevalleyExceptionalTags], ⟨Nat.prime_two, by omega, rfl⟩, hU⟩

theorem adjointGroup_facts_exc {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hG2 : τ = .G2 → 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    IsSimpleGroup ↥(adjointGroup τ K) ∧ (∃ a b : ↥(adjointGroup τ K), a * b ≠ b * a) ∧
      IsChevSimple 2 ↥(adjointGroup τ K) ∧
      ∃ t : StatedLieTag, t ∈ chevalleyExceptionalTags ∧
        ChevalleyExceptionalModel ↥(adjointGroup τ K) t 2 f := by
  obtain ⟨t, ht, hmod⟩ := exists_chevModel_adjointGroup hτ hf hG2 hK
  have hLM : LieModel ↥(adjointGroup τ K) t 0 2 f := Or.inr (Or.inl ⟨rfl, ht, hmod⟩)
  obtain ⟨-, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple _ t 0 2 f hLM
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  refine ⟨hs, ?_, ?_, t, ht, hmod⟩
  · by_contra hcon
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(adjointGroup τ K))
    have hxc : x ∈ Subgroup.center ↥(adjointGroup τ K) :=
      Subgroup.mem_center_iff.2 fun g => by_contra fun h => hcon ⟨g, x, h⟩
    rw [hZ, Subgroup.mem_bot] at hxc
    exact hx hxc
  · obtain ⟨d, hd, e⟩ := CFSG.LocalAnalysis.GLTheoremA.index_of_chevalleyExceptional ht hmod
    exact Or.inl ⟨TauCeti.CFSGIndex.lie d, hd, e⟩

private theorem exists_markedInnDiag_top {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (r : ↥(adjointGroup τ K)) :
    ∃ lab : GLALabel, 2 ≤ lab.n ∧ MarkedInnDiag (⊤ : Subgroup ↥(adjointGroup τ K)) r lab := by
  obtain ⟨hs, hnc, -, t, ht, hmod⟩ := adjointGroup_facts_exc hτ (by omega) (fun _ => hf) hK
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hZtop : Subgroup.center ↥(⊤ : Subgroup ↥(adjointGroup τ K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxG : (x : ↥(adjointGroup τ K)) ∈ Subgroup.center ↥(adjointGroup τ K) :=
      Subgroup.mem_center_iff.2 fun g => by
        have := Subgroup.mem_center_iff.1 hx ⟨g, Subgroup.mem_top g⟩
        exact congrArg Subtype.val this
    rw [hZ, Subgroup.mem_bot] at hxG
    exact Subgroup.mem_bot.2 (Subtype.ext hxG)
  let eT : ↥(⊤ : Subgroup ↥(adjointGroup τ K)) ⧸
      Subgroup.center ↥(⊤ : Subgroup ↥(adjointGroup τ K)) ≃* ↥(adjointGroup τ K) :=
    (QuotientGroup.quotientMulEquivOfEq hZtop).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have hLM : LieModel (↥(⊤ : Subgroup ↥(adjointGroup τ K)) ⧸
      Subgroup.center ↥(⊤ : Subgroup ↥(adjointGroup τ K))) t 0 2 f :=
    LieModel.of_mulEquiv eT.symm (Or.inr (Or.inl ⟨rfl, ht, hmod⟩))
  haveI := hs
  haveI : Group.IsPerfect ↥(adjointGroup τ K) :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun h => by
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (h.is_comm.comm a b)
  have hperf : commutator ↥(⊤ : Subgroup ↥(adjointGroup τ K)) = ⊤ :=
    (Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv (G := ↥(adjointGroup τ K))).symm.toMonoidHom)
      (Subgroup.topEquiv (G := ↥(adjointGroup τ K))).symm.surjective).commutator_eq_top
  obtain ⟨hX, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hLM
  obtain ⟨R₀, _, I₀, F₀, -, -, -, htag, -, -, hdeg⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨hn, hnd⟩ := label_of_exc ht htag hdeg
  have hsub : MI.CAll lab (CFSG.StandardType.LargeEvenSimpleGuard
      CFSG.StandardType.GGRawInnSubgroup) :=
    (MI.canonAll_iff_legacyAll hlab hnd _).2 (T171Sh.largeEvenLabelAll_innSubgroup hlab)
  refine ⟨lab, by omega, hX, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ (hsub _ hraw)
  rintro R _ I F ⟨⟨hs', hna', θ, -⟩, hsubfun⟩
  obtain ⟨-, -, hinn⟩ := hsubfun hs' hna'
  refine ⟨hs', hna', θ, rfl, MulAut.conj (θ (QuotientGroup.mk ⟨r⁻¹, Subgroup.mem_top _⟩)),
    hinn _, ?_⟩
  intro l l' hl
  have hl' : (⟨r⁻¹, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(adjointGroup τ K))) * l *
      (⟨r⁻¹, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(adjointGroup τ K)))⁻¹ = l' := by
    apply Subtype.ext
    simp [hl]
  rw [MulAut.conj_apply, ← hl']
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]

private theorem component_lieModel {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {r : ↥(adjointGroup τ K)} (hrp : r ^ p = 1) (hr1 : r ≠ 1) {J : Subgroup ↥(adjointGroup τ K)}
    (hJ : IsComponentOf J (Subgroup.centralizer ({r} : Set ↥(adjointGroup τ K)))) :
    ∃ (t : StatedLieTag) (n m : ℕ), 2 ≤ m ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 m := by
  obtain ⟨f, -, hK⟩ := exists_card_eq_two_pow hK2
  have hf : 2 ≤ f := by
    by_contra hlt
    have h1 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hs, hnc, hchev, -⟩ := adjointGroup_facts_exc hτ (by omega) (fun _ => hf) hK
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj r
  have hβp : (MulAut.conj r) ^ p = 1 := by rw [← map_pow, hrp, map_one]
  have hβ1 : MulAut.conj r ≠ 1 := conj_ne_one_of_center_eq_bot hZ hr1
  have hJcomp : IsComponentOf J (CFSG.LocalAnalysis.GLTheoremA.I142.centFix
      (Subgroup.zpowers (MulAut.conj r))) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.I142C.centFix_zpowers', hfix]
    exact hJ
  have hJchev : IsChevSimple 2 (↥J ⧸ Subgroup.center ↥J) :=
    CFSG.LocalAnalysis.GLTheoremA.I142M.Three.chevCompTypes_holds _ hs hnc hchev p hp hp2
      (MulAut.conj r) hβp hβ1 J hJcomp
  obtain ⟨hperf, lab, hlam, hraw⟩ := CFSG.StandardType.ChevTwo.ys08_holds ↥J hJ.2.2 hJchev
  have hlab : LabelOf J lab :=
    ⟨hperf, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨labS, hnS, hM⟩ := exists_markedInnDiag_top hτ hf hK r
  have hxC : r ∉ Subgroup.centralizer (((⊤ : Subgroup ↥(adjointGroup τ K)) :
      Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
    intro h
    refine hr1 (Subgroup.mem_bot.1 ?_)
    rw [← hZ, Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.1 h g (Subgroup.mem_top g))
  have hJ' : IsComponentOf J ((⊤ : Subgroup ↥(adjointGroup τ K)) ⊓
      Subgroup.centralizer ({r} : Set ↥(adjointGroup τ K))) := by
    rwa [top_inf_eq]
  have hdvd := labS_dvd_of_labelOf hp hp2 Subgroup.normal_top hrp hxC hM hJ' hlam hlab
  have hmm : CFSG.StandardType.MarkedModel lab (↥J ⧸ Subgroup.center ↥J) :=
    CanonSubcomp.markedModel_of_hasLabel hlab
  have hkey := markDeg_ge_two hnS hlam hdvd
  refine ⟨CFSG.StandardType.markTag lab, CFSG.StandardType.markRank lab,
    CFSG.StandardType.markDeg lab, hkey.1, ?_⟩
  unfold CFSG.StandardType.MarkedModel at hmm
  rwa [hkey.2] at hmm

private theorem eq_one_of_mem_innAutDerived {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n m : ℕ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 2 ≤ m) (h : LieModel X t n 2 m)
    (hpX : ¬ p ∣ Nat.card X) (hZ : Subgroup.center X = ⊥) {α : MulAut X}
    (hα : α ∈ innAutDerived X) (hαp : α ^ p = 1) : α = 1 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hrk := pRank_le_one_of_not_dvd hpX
  let heq : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hinn : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    rcases CFSG.RankThree.PartOne.OutStructure.outPNice_or_D4 hp hp5 hm h
      (fun hmod => CFSG.RankThree.PartOne.OutStructure.not_dvd_gcd_psl_of_pRank hp hp5 hrk
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv heq.symm hmod))
      (fun hmod => CFSG.RankThree.PartOne.OutStructure.not_dvd_gcd_psu_of_pRank hp hp5 hrk
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv heq.symm hmod)) with hN | ⟨m', hm'⟩
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.mem_inner_of_mem_innAutDerived_of_outPNice
        hN hα hαp
    · obtain ⟨-, K', _, _, -, ⟨e⟩⟩ := hm'
      obtain ⟨e'⟩ :=
        CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K'
      let e'' := e.trans e'
      have hβ : MulAut.congr e'' α ∈ innAutDerived ↥(adjointGroup Tag.D4 K') :=
        (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e'').2 hα
      have hβp : MulAut.congr e'' α ^ p = 1 := by rw [← map_pow, hαp, map_one]
      obtain ⟨g, hg⟩ :=
        CFSG.ComponentClassification.OuterAutomorphisms.exists_conj_eq_of_mem_innAutDerived_D4
          hp hp2 hp3 hβ hβp
      refine ⟨e''.symm g, MulEquiv.ext fun x => ?_⟩
      have h1 := congrArg (fun φ : MulAut _ => φ (e'' x)) hg
      simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.symm_apply_apply] at h1
      apply e''.injective
      simpa [MulAut.conj_apply, map_mul, map_inv] using h1.symm
  obtain ⟨j, rfl⟩ := hinn
  have hjp : j ^ p = 1 := by
    have hc : j ^ p ∈ Subgroup.center X := Subgroup.mem_center_iff.2 fun x => by
      have hx := congrArg (fun φ : MulAut X => φ x)
        (show MulAut.conj (j ^ p) = 1 by rw [map_pow]; exact hαp)
      simp only [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * j ^ p = (j ^ p * x * (j ^ p)⁻¹) * j ^ p := by rw [hx]
        _ = j ^ p * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hj1 : j = 1 := by
    by_contra hj
    have hord : orderOf j = p := orderOf_eq_prime hjp hj
    apply hpX
    rw [← hord]
    exact orderOf_dvd_natCard j
  rw [hj1, map_one]

theorem adjCompTriv_of (hA : CFSG.LocalAnalysis.GLTheoremA.T171Sh.ExcAdjCompInnAut) :
    AdjCompTriv := by
  intro τ hτ K _ _ hK2 hK4 p hp hp2 hpq r hrp hr1 w hw hwp J hJ hJp
  haveI : CharP K 2 := ringChar.of_eq hK2
  obtain ⟨hpK, hp5⟩ := not_dvd_card_and_five_le_of_not_dvd_sq_sub_one hK2 hp hp2 hpq
  have hp3 : p ≠ 3 := by omega
  obtain ⟨t, n, m, hm, hLM⟩ := component_lieModel hτ hK2 hK4 hp hp2 hrp hr1 hJ
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj r
  have hβp : (MulAut.conj r) ^ p = 1 := by rw [← map_pow, hrp, map_one]
  have hβ1 : MulAut.conj r ≠ 1 := conj_ne_one_of_center_eq_bot hZ hr1
  have hβmem : MulAut.conj r ∈ innAutDerived ↥(adjointGroup τ K) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ ⟨r, rfl⟩
  have hCN := CFSG.LocalAnalysis.GLTheoremA.S267.Gen.compNormal_adjointGroup hτ
    (fun _ => by omega) hp hp2 hpK (fun _ => hp3) (MulAut.conj r) hβmem hβp hβ1
  have hJfix : IsComponentOf J (fixSubgroup (MulAut.conj r)) := by rw [hfix]; exact hJ
  have hwfix : w ∈ fixSubgroup (MulAut.conj r) := by rw [hfix]; exact hw
  have hwN : w ∈ Subgroup.normalizer (J : Set ↥(adjointGroup τ K)) := hCN J hJfix hwfix
  have hstab := conj_mem_subgroupStabAut_of_mem_normalizer hwN
  have hcomm : r * w = w * r := (Subgroup.mem_centralizer_singleton_iff.1 hw).symm
  have hJA : CFSG.Assembly.IsComponentOf J
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj r)) :=
    CFSG.Assembly.isComponentOf_iff_open.2 hJfix
  have h360 : Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 360 :=
    CFSG.Quasithin.H13.EvenOrd.card_ne_of_evenLieType CFSG.Quasithin.H13.EvenOrd.excl_360
      ⟨t, n, m, hLM.admissible, hLM⟩
  have hα := hA hτ K p hp hp2 (fun _ => hK4) (fun _ h3 => absurd h3 hp3) r w hr1 hrp hwp hcomm J
    hJA h360 hstab
  haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  refine mem_centralizer_of_restrict_eq_one hstab ?_
  have hZJ : Subgroup.center (↥J ⧸ Subgroup.center ↥J) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hJ.2.2
  refine eq_one_of_mem_innAutDerived hp hp5 hm hLM hJp hZJ hα ?_
  rw [← map_pow, ← map_pow]
  have h1 : (⟨MulAut.conj w, hstab⟩ : CFSG.GroupActions.subgroupStabAut J) ^ p = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hwp, map_one]
  rw [h1, map_one, map_one]

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
