module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.IsCyclicOfPRankLeOne
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeFactsOrth
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycMain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10K101

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_isElemAbelian_le_inner {X : Type} [Group X] [Finite X] {d : ℕ}
    (hd : d.Prime) (hZ : ¬ d ∣ Nat.card (Subgroup.center X))
    (hX : CFSG.Open.pRank d (⊤ : Subgroup X) ≤ 1) {A : Subgroup (MulAut X)}
    (hA : CFSG.Open.IsElemAbelian d A) (hAI : A ≤ inner X) : Nat.card A ≤ d := by
  have hker : (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have h1 : x * y * x⁻¹ = y := by
        simpa using congrArg (fun f : MulAut X => f y) h
      calc y * x = (x * y * x⁻¹) * x := by rw [h1]
        _ = x * y := by group
    · intro h
      ext y
      rw [MulAut.conj_apply]
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [← h y]
        _ = y := by group
  let e : inner X ≃* (X ⧸ Subgroup.center X) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : X →* MulAut X))).symm
  let A' : Subgroup (X ⧸ Subgroup.center X) := (A.subgroupOf (inner X)).map e.toMonoidHom
  have hA' : CFSG.Open.IsElemAbelian d A' :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hA (inner X)) e.toMonoidHom
  have hcardA' : Nat.card A' = Nat.card A := by
    change Nat.card ((A.subgroupOf (inner X)).map e.toMonoidHom) = Nat.card A
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hA').exists_card_dvd_pow
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hd).mp hn
  have hk1 : k ≤ 1 := by
    have hle : k ≤ CFSG.Open.pRank d (⊤ : Subgroup (X ⧸ Subgroup.center X)) :=
      CFSG.SectionRank.le_pRank hd.one_lt le_top hA' hk
    rw [CFSG.SectionRank.pRank_quotient_eq (p := d) (hp := ⟨hd⟩) (Subgroup.center X) hZ] at hle
    exact hle.trans hX
  calc Nat.card A = Nat.card A' := hcardA'.symm
    _ = d ^ k := hk
    _ ≤ d ^ 1 := Nat.pow_le_pow_right hd.pos hk1
    _ = d := pow_one d

theorem pRank_outer_quot_center_le_one
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X)
    (hcat : CFSG.Open.IsCatalogGroup (X ⧸ Subgroup.center X)) {d : ℕ} (hd : d.Prime)
    (hd2 : d ≠ 2) (hZ : ¬ d ∣ Nat.card (Subgroup.center X))
    (hX : CFSG.Open.pRank d (⊤ : Subgroup X) ≤ 1) :
    CFSG.Open.pRank d (⊤ : Subgroup (Outer (X ⧸ Subgroup.center X))) ≤ 1 := by
  have : Fact d.Prime := ⟨hd⟩
  have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  have hperf : Group.IsPerfect (X ⧸ Subgroup.center X) := by
    have : Group.IsPerfect X := ⟨hq.1⟩
    infer_instance
  have hnab : ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative (X ⧸ Subgroup.center X)
      (IsMulCommutative.of_comm h)
  have hrank : CFSG.Open.pRank d (⊤ : Subgroup (X ⧸ Subgroup.center X)) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center X) hZ]
    exact hX
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow d (X ⧸ Subgroup.center X)))
  refine hOut (X ⧸ Subgroup.center X) hq.2 hnab hcat d hd hd2 T ?_
  refine CFSG.isCyclic_of_pRank_le_one hd hd2 T.isPGroup' ?_
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (T : Subgroup (X ⧸ Subgroup.center X))]
  exact (CFSG.SectionRank.pRank_mono hd.one_lt le_top).trans hrank

private theorem mem_inner_of_centerQuotientHom_mem {X : Type} [Group X]
    (hperf : Group.IsPerfect X) {α : MulAut X}
    (h : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X α ∈
      inner (X ⧸ Subgroup.center X)) : α ∈ inner X := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj] at hq
  have hinj : Function.Injective
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X) :=
    @CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X _ hperf
  exact ⟨x, hinj hq⟩

private theorem ker_centerQuotientOuterHom_restrict {X : Type} [Group X]
    (hperf : Group.IsPerfect X) {A : Subgroup (MulAut X)} :
    (((CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom X).comp
        (QuotientGroup.mk' (inner X))).domRestrict A).ker =
      (A ⊓ inner X).subgroupOf A := by
  let f : MulAut X →* Outer (X ⧸ Subgroup.center X) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom X).comp
      (QuotientGroup.mk' (inner X))
  have hfker : f.ker = inner X := by
    ext a
    rw [MonoidHom.mem_ker]
    have hmap : f a = (QuotientGroup.mk' (inner (X ⧸ Subgroup.center X)))
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X a) := rfl
    rw [hmap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨mem_inner_of_centerQuotientHom_mem hperf, fun h => ?_⟩
    obtain ⟨g, rfl⟩ := h
    exact ⟨QuotientGroup.mk' (Subgroup.center X) g,
      (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj g).symm⟩
  show (f.domRestrict A).ker = (A ⊓ inner X).subgroupOf A
  rw [MonoidHom.ker_domRestrict, hfker]
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem card_le_mul_card_inf_inner {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {d : ℕ} (hd : d.Prime)
    (hO : CFSG.Open.pRank d (⊤ : Subgroup (Outer (X ⧸ Subgroup.center X))) ≤ 1)
    {A : Subgroup (MulAut X)} (hA : CFSG.Open.IsElemAbelian d A) :
    Nat.card A ≤ d * Nat.card (A ⊓ inner X : Subgroup (MulAut X)) := by
  let φ : A →* Outer (X ⧸ Subgroup.center X) :=
    ((CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom X).comp
      (QuotientGroup.mk' (inner X))).domRestrict A
  have hker : φ.ker = (A ⊓ inner X).subgroupOf A :=
    ker_centerQuotientOuterHom_restrict ⟨hq.1⟩
  have hφea : CFSG.Open.IsElemAbelian d φ.range := by
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro u v
      obtain ⟨a, ha⟩ := u.2
      obtain ⟨b, hb⟩ := v.2
      apply Subtype.ext
      show (u : Outer (X ⧸ Subgroup.center X)) * v = v * u
      rw [← ha, ← hb, ← map_mul, ← map_mul, hA.1.is_comm.comm a b]
    · intro u hu
      obtain ⟨a, ha⟩ := hu
      show u ^ d = 1
      rw [← ha, ← map_pow]
      have ha' : a ^ d = 1 := by
        apply Subtype.ext
        simpa using hA.2 (a : MulAut X) a.2
      rw [ha', map_one]
  have hquot : Nat.card (A ⧸ φ.ker) ≤ d := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hφea).exists_card_dvd_pow
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hd).mp hn
    rw [hk]
    have hk1 : k ≤ 1 :=
      (CFSG.SectionRank.le_pRank hd.one_lt le_top hφea hk).trans hO
    calc d ^ k ≤ d ^ 1 := Nat.pow_le_pow_right hd.pos hk1
      _ = d := pow_one d
  have hkercard : Nat.card φ.ker = Nat.card (A ⊓ inner X : Subgroup (MulAut X)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card A = Nat.card (A ⧸ φ.ker) * Nat.card φ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    _ = Nat.card (A ⧸ φ.ker) * Nat.card (A ⊓ inner X : Subgroup (MulAut X)) := by
        rw [hkercard]
    _ ≤ d * Nat.card (A ⊓ inner X : Subgroup (MulAut X)) :=
        Nat.mul_le_mul_right _ hquot

theorem pow_two_le_card_ker_or_exists_not_mem {E Y : Type} [Group E] [Finite E] [Group Y]
    [Finite Y] {d : ℕ} (hd : d.Prime) (hE : Nat.card E = d ^ 3) (ψ : E →* Y) (I : Subgroup Y)
    (h1 : Nat.card (ψ.range ⊓ I : Subgroup Y) ≤ d)
    (h2 : Nat.card ψ.range ≤ d * Nat.card (ψ.range ⊓ I : Subgroup Y)) :
    d ^ 2 ≤ Nat.card ψ.ker ∨ ((∃ c : E, c ∈ ψ.ker ∧ c ≠ 1) ∧ ∃ e : E, ψ e ∉ I) := by
  by_cases hbig : d ^ 2 ≤ Nat.card ψ.ker
  · exact Or.inl hbig
  · right
    have hklt : Nat.card ψ.ker < d ^ 2 := Nat.lt_of_not_le hbig
    have hcard : Nat.card ψ.ker * Nat.card ψ.range = d ^ 3 := by
      rw [Subgroup.card_ker_mul_card_range, hE]
    have hkne : Nat.card ψ.ker ≠ 1 := by
      intro hk1
      rw [hk1, one_mul] at hcard
      have hle : d ^ 3 ≤ d ^ 2 := by
        calc d ^ 3 = Nat.card ψ.range := hcard.symm
          _ ≤ d * Nat.card (ψ.range ⊓ I : Subgroup Y) := h2
          _ ≤ d * d := Nat.mul_le_mul_left d h1
          _ = d ^ 2 := by ring
      have hlt : d ^ 2 < d ^ 3 := Nat.pow_lt_pow_right hd.one_lt (by norm_num)
      omega
    have hne : ψ.ker ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hkne
      exact hkne rfl
    refine ⟨?_, ?_⟩
    · obtain ⟨c, hc⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := ψ.ker)).mp hne
      exact ⟨c, c.2, by simpa using hc⟩
    · by_contra hno
      push Not at hno
      have hle : ψ.range ≤ I := by
        rintro y ⟨e, rfl⟩
        exact hno e
      have hI : (ψ.range ⊓ I : Subgroup Y) = ψ.range := inf_eq_left.mpr hle
      rw [hI] at h1
      have hstep : Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card ψ.ker * d :=
        Nat.mul_le_mul_left _ h1
      have hstep' : Nat.card ψ.ker * d < d ^ 2 * d :=
        Nat.mul_lt_mul_of_pos_right hklt hd.pos
      have hlt : Nat.card ψ.ker * Nat.card ψ.range < d ^ 2 * d := hstep.trans_lt hstep'
      rw [hcard, show d ^ 2 * d = d ^ 3 by ring] at hlt
      exact (lt_irrefl _) hlt

theorem exists_ker_or_outer (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (hcat : CFSG.Open.IsCatalogGroup (X ⧸ Subgroup.center X)) {d : ℕ} (hd : d.Prime)
    (hd5 : 5 ≤ d) (hX : CFSG.Open.pRank d (⊤ : Subgroup X) ≤ 1)
    (hZ : ¬ d ∣ Nat.card (Subgroup.center X)) {E : Type} [Group E] [Finite E]
    (hEd : ∀ e : E, e ^ d = 1) (hEc : ∀ a b : E, a * b = b * a) (hcard : Nat.card E = d ^ 3)
    (ψ : E →* MulAut X) :
    d ^ 2 ≤ Nat.card ψ.ker ∨ ((∃ c : E, c ∈ ψ.ker ∧ c ≠ 1) ∧ ∃ e : E, ψ e ∉ inner X) := by
  have hd2 : d ≠ 2 := by omega
  have hEea : CFSG.Open.IsElemAbelian d (⊤ : Subgroup E) := by
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro a b
      apply Subtype.ext
      simpa using hEc a b
    · intro x _
      simpa using hEd x
  have hrange : CFSG.Open.IsElemAbelian d ψ.range := by
    simpa only [Subgroup.map_top] using CFSG.Open.IsElemAbelian.map hEea ψ
  have h1 : Nat.card (ψ.range ⊓ inner X : Subgroup (MulAut X)) ≤ d :=
    card_le_of_isElemAbelian_le_inner hd hZ hX
      (CFSG.Open.IsElemAbelian.mono hrange inf_le_left) inf_le_right
  have hO : CFSG.Open.pRank d (⊤ : Subgroup (Outer (X ⧸ Subgroup.center X))) ≤ 1 :=
    pRank_outer_quot_center_le_one hOut hq hcat hd hd2 hZ hX
  have h2 : Nat.card ψ.range ≤
      d * Nat.card (ψ.range ⊓ inner X : Subgroup (MulAut X)) :=
    card_le_mul_card_inf_inner hq hd hO hrange
  exact pow_two_le_card_ker_or_exists_not_mem hd hcard ψ (inner X) h1 h2

omit [Finite G] in
private theorem exists_barM_action {M L E : Subgroup G} (hEM : E ≤ M)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) :
    ∃ ψ : ↥E →* MulAut ↥(barM M L),
      (∀ e : ↥E, ψ e = 1 →
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hEM e) ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
      (∀ e : ↥E, ∃ (he : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hEM e) ∈
            Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))),
          ψ e = (barM M L).normalizerMonoidHom ⟨_, he⟩) := by
  let q : ↥E →* (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hEM)
  have hq_apply : ∀ e : ↥E,
      q e = QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(e : G), hEM e.2⟩ := fun _ => rfl
  have hqN : ∀ e : ↥E, q e ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro e
    refine barM_le_normalizer_barM (M := M) (L := E) (S := L) hEL ?_
    rw [barM, Subgroup.mem_map]
    exact ⟨Subgroup.inclusion hEM e, Subgroup.mem_subgroupOf.mpr e.2, rfl⟩
  let f : ↥E →* ↥(Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
    q.codRestrict _ hqN
  refine ⟨(barM M L).normalizerMonoidHom.comp f, ?_, ?_⟩
  · intro e he
    have hfe : f e ∈ (barM M L).normalizerMonoidHom.ker := (MonoidHom.mem_ker).mpr he
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hfe
    exact hfe
  · intro e
    exact ⟨hqN e, congrArg (barM M L).normalizerMonoidHom (Subtype.ext (hq_apply e))⟩

omit [Finite G] in
private theorem barM_map_ker_le_centralizer {M L E : Subgroup G} (hEM : E ≤ M)
    {ψ : ↥E →* MulAut ↥(barM M L)}
    (hψ : ∀ e : ↥E, ψ e = 1 →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hEM e) ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    barM M (ψ.ker.map E.subtype) ≤
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro x hx
  rw [barM, Subgroup.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hg)
  have hg_eq : g = Subgroup.inclusion hEM y := Subtype.ext hyval.symm
  rw [hg_eq]
  exact hψ y (MonoidHom.mem_ker.mp hy)

omit [Finite G] in
private theorem barM_zpowers_le_centralizer_of_mem {M L : Subgroup G} {c : G} (hc : c ∈ M)
    (hker : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hc⟩ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    barM M (Subgroup.zpowers c) ≤
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro x hx
  rw [barM, Subgroup.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hg)
  have hg_eq : g = (⟨c, hc⟩ : ↥M) ^ n := Subtype.ext (by simpa using hn.symm)
  rw [hg_eq, map_zpow]
  exact Subgroup.zpow_mem _ hker n

theorem exists_le_centralizer_or_not_mem_inner
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) {M L E : Subgroup G}
    (hL : IsTwoPrimeComponent M L)
    (hcat : CFSG.Open.IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hLd : CFSG.Open.pRank d (barM M L) ≤ 1)
    (hZ : ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)))
    (hE : CFSG.Open.IsElemAbelian d E) (hcard : Nat.card E = d ^ 3) (hEM : E ≤ M)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) :
    (∃ E₀ : Subgroup G, E₀ ≤ E ∧ 2 ≤ CFSG.Open.pRank d E₀ ∧
        barM M E₀ ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∨
      ((∃ c ∈ E, c ≠ 1 ∧ barM M (Subgroup.zpowers c) ≤
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
        ∃ e : ↥M, (e : G) ∈ E ∧ ∃ he : QuotientGroup.mk' (CFSG.pCore 2 ↥M) e ∈
            Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
          (barM M L).normalizerMonoidHom ⟨_, he⟩ ∉ inner ↥(barM M L)) := by
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have hLd' : CFSG.Open.pRank d (⊤ : Subgroup ↥(barM M L)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barM M L)]
    exact hLd
  obtain ⟨ψ, hker, houter⟩ := exists_barM_action (M := M) (L := L) hEM hEL
  rcases exists_ker_or_outer hOut hq hcat hd hd5 hLd' hZ
      (fun e => Subtype.ext (by simpa using hE.2 (e : G) e.2))
      (fun a b => hE.1.is_comm.comm a b) hcard ψ with h2 | ⟨⟨c, hc, hc1⟩, ⟨e, he⟩⟩
  · left
    refine ⟨ψ.ker.map E.subtype, ?_, ?_, barM_map_ker_le_centralizer hEM hker⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · have hcardE₀ : Nat.card (ψ.ker.map E.subtype) = Nat.card ψ.ker :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective E)
      have hE₀ : CFSG.Open.IsElemAbelian d (ψ.ker.map E.subtype) :=
        CFSG.Open.IsElemAbelian.mono hE (by rintro _ ⟨y, -, rfl⟩; exact y.2)
      rw [← hcardE₀] at h2
      rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hd hE₀] at h2
      exact (Nat.pow_le_pow_iff_right hd.one_lt).mp h2
  · right
    refine ⟨⟨(c : G), c.2, ?_,
      barM_zpowers_le_centralizer_of_mem (hEM c.2) (hker c (MonoidHom.mem_ker.mp hc))⟩, ?_⟩
    · intro hcG
      exact hc1 (Subtype.ext hcG)
    · obtain ⟨he', hψe⟩ := houter e
      refine ⟨Subgroup.inclusion hEM e, by simp, he', ?_⟩
      rwa [← hψe]

theorem mem_inner_of_quot_center_alternating {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hn : 5 ≤ n)
    (hA : Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin n)))
    {α : MulAut X} (hα : Odd (orderOf α)) : α ∈ inner X := by
  have : Group.IsPerfect X := Group.IsPerfect.mk hq.1
  obtain ⟨e⟩ := hA
  let β : MulAut (X ⧸ Subgroup.center X) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X α
  have hβ : Odd (orderOf β) :=
    Odd.of_dvd_nat hα (orderOf_map_dvd
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X) α)
  obtain ⟨y, hy⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F10.exists_conj_of_odd_orderOf_alt hn e β hβ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) y
  refine ⟨g, ?_⟩
  apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X
  rw [CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj]
  exact hy.symm

open CFSG.LocalAnalysis.RankThreeUC.S15 in
private theorem four_le_rkOmPlus_three {m : ℕ} (hm : 4 ≤ m) : 4 ≤ rkOmPlus m 2 3 := by
  have heP : eP 2 3 = 2 := by simpa using eP_two_pow_three 1
  have heS : eS 2 3 = 1 := by simpa using eS_two_pow_three 1
  unfold rkOmPlus
  rw [heP, heS, Nat.div_one]
  split_ifs with h
  · have hodd : Odd m := Nat.not_even_iff_odd.mp fun he => h.2 he.two_dvd
    obtain ⟨k, hk⟩ := hodd
    have hdiv : 2 * m / 2 = m := Nat.mul_div_cancel_left m (by norm_num)
    omega
  · omega

open CFSG.LocalAnalysis.RankThreeUC.S15 in
private theorem three_le_rkOmMinus_three {m : ℕ} (hm : 4 ≤ m) : 3 ≤ rkOmMinus m 2 3 := by
  have heP : eP 2 3 = 2 := by simpa using eP_two_pow_three 1
  have heS : eS 2 3 = 1 := by simpa using eS_two_pow_three 1
  unfold rkOmMinus
  rw [heP, heS, Nat.div_one]
  split_ifs <;> omega

open CFSG.LocalAnalysis.RankThreeUC.S15 in
private theorem eq_three_rkLin_twistedA_three_two : rkLin 4 false 2 3 1 = 3 := by
  norm_num [rkLin, eM_2_3]

open CFSG.HardMathSupport.Curtis.Coordinator.PLType in
private theorem isSimpleGroup_lie_orthogonal_two
    {dL : TauCeti.ValidLieTypeIndex} {m : ℕ} {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hdL : dL.1 = .D m q ∨ dL.1 = .twistedD m q ∨ (m = 3 ∧ dL.1 = .twistedA 3 q)) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie dL).Group := by
  rcases hdL with h | h | ⟨-, h⟩
  · exact isSimpleGroup_lie_typeD_two m dL q hq h
  · exact isSimpleGroup_lie_twistedD_two m dL q hq h
  · exact isSimpleGroup_lie_twistedA_three_two dL q hq h

open CFSG.HardMathSupport.Curtis.Coordinator.PLType in
private theorem not_prime_card_of_lie_orthogonal_two {Y : Type} [Group Y] [Finite Y]
    {dL : TauCeti.ValidLieTypeIndex} {m : ℕ} {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hdL : dL.1 = .D m q ∨ dL.1 = .twistedD m q ∨ (m = 3 ∧ dL.1 = .twistedA 3 q))
    (e : Y ≃* (TauCeti.CFSGIndex.lie dL).Group) : ¬ (Nat.card Y).Prime := by
  have hcard : Nat.card Y = Nat.card (TauCeti.CFSGIndex.lie dL).Group :=
    Nat.card_congr e.toEquiv
  rw [hcard]
  rcases hdL with h | h | ⟨-, h⟩
  · have hm : 4 ≤ m := four_le_of_valid_D (h ▸ dL.2)
    rw [card_lie_typeD_two m dL q hq h, mul_assoc]
    refine not_prime_of_two_le_factorization ?_
    rw [factorization_two_pow_mul_of_odd
      ((odd_two_pow_sub_one (by omega)).mul (odd_prod_four_pow_sub_one m))]
    exact two_le_mul_pred hm
  · have hm : 4 ≤ m := four_le_of_valid_twistedD (h ▸ dL.2)
    rw [card_lie_twistedD_two m dL q hq h, mul_assoc]
    refine not_prime_of_two_le_factorization ?_
    rw [factorization_two_pow_mul_of_odd
      ((odd_two_pow_add_one (by omega)).mul (odd_prod_four_pow_sub_one m))]
    exact two_le_mul_pred hm
  · rw [card_lie_twistedA_three_two dL q hq h]
    norm_num

open CFSG.HardMathSupport.Curtis.Coordinator.PLType in
private theorem isClassicalOrG2Index_of_lie_orthogonal_two
    {dL : TauCeti.ValidLieTypeIndex} {m : ℕ} {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hdL : dL.1 = .D m q ∨ dL.1 = .twistedD m q ∨ (m = 3 ∧ dL.1 = .twistedA 3 q)) :
    CFSG.AGLEmbedding.IsClassicalOrG2Index dL.1 := by
  rcases hdL with h | h | ⟨-, h⟩
  · simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index, h] using (primePower_card_two hq).1
  · simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index, h] using (primePower_card_two hq).1
  · simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index, h] using (primePower_card_two hq).1

open CFSG.LocalAnalysis.RankThreeUC.S15 CFSG.HardMathSupport.Curtis.Coordinator.PLType in
private theorem three_le_mRankChev_three_of_lie_orthogonal_two
    {dL : TauCeti.ValidLieTypeIndex} {m : ℕ} {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hdL : dL.1 = .D m q ∨ dL.1 = .twistedD m q ∨ (m = 3 ∧ dL.1 = .twistedA 3 q)) :
    3 ≤ mRankChev dL.1 3 1 := by
  rcases hdL with h | h | ⟨-, h⟩
  · have hm : 4 ≤ m := four_le_of_valid_D (h ▸ dL.2)
    have h4 := four_le_rkOmPlus_three hm
    simp only [h, mRankChev, hq]
    omega
  · have hm : 4 ≤ m := four_le_of_valid_twistedD (h ▸ dL.2)
    have h3 := three_le_rkOmMinus_three hm
    simp only [h, mRankChev, hq]
    omega
  · simp only [h, mRankChev, hq]
    rw [eq_three_rkLin_twistedA_three_two]

theorem three_le_pRank_three_of_orthogonal_lie
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) {Y : Type} [Group Y] [Finite Y]
    {dL : TauCeti.ValidLieTypeIndex} {m : ℕ} {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hdL : dL.1 = .D m q ∨ dL.1 = .twistedD m q ∨ (m = 3 ∧ dL.1 = .twistedA 3 q))
    (e : Y ≃* (TauCeti.CFSGIndex.lie dL).Group) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : IsSimpleGroup (TauCeti.CFSGIndex.lie dL).Group :=
    isSimpleGroup_lie_orthogonal_two hq hdL
  have : IsSimpleGroup Y := MulEquiv.isSimpleGroup e
  have hnp := not_prime_card_of_lie_orthogonal_two hq hdL e
  have hnab : ∃ a b : Y, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcon }
    exact hnp (IsSimpleGroup.prime_card (α := Y))
  obtain ⟨hqLC, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  have hqY : CFSG.Open.IsQuasisimple Y := ⟨hqLC.1.commutator_eq_top, hqLC.2.1⟩
  have hquot : Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie dL).Group) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have hrank := hT Y hqY dL (isClassicalOrG2Index_of_lie_orthogonal_two hq hdL) hquot 3
    Nat.prime_three (by norm_num)
  rw [hrank, hZ, Subgroup.card_bot]
  exact three_le_mRankChev_three_of_lie_orthogonal_two hq hdL

theorem exists_mulEquiv_alternating_of_isOrthogonalTwo
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) {Y : Type} [Group Y] [Finite Y]
    (hY : IsOrthogonalTwo Y) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2) :
    ∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n)) := by
  rcases hY with ⟨dL, ⟨m, q, hq, hdL⟩, ⟨e⟩⟩ | h
  · exfalso
    exact absurd (three_le_pRank_three_of_orthogonal_lie hT hq hdL e) (by omega)
  · exact h

theorem nineThreeTwo_of_not_mem_inner
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) {M S L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (h93 : NineThreeConclusion M S L) (hn1 : ¬ NineThreeOne L)
    (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    {α : MulAut ↥(barM M L)} (hα : α ^ d = 1) (hαi : α ∉ inner ↥(barM M L)) :
    NineThreeTwo M S L := by
  have hq := hL.component.2.2
  have : Group.IsPerfect ↥(barM M L) := Group.IsPerfect.mk hq.1
  have hodd : Odd (orderOf α) :=
    Odd.of_dvd_nat (hd.odd_of_ne_two hd2) (orderOf_dvd_of_pow_eq_one hα)
  have hnot : ∀ {n : ℕ}, 5 ≤ n → Nonempty ((↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ≃*
      alternatingGroup (Fin n)) → False := fun hn hA =>
    hαi (mem_inner_of_quot_center_alternating hq hn hA hodd)
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact (hn1 h1).elim
  · exact h2
  · obtain ⟨-, hY, -⟩ := h3
    have h3' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact hm3L
    obtain ⟨n, hn, ⟨e⟩⟩ := exists_mulEquiv_alternating_of_isOrthogonalTwo hT hY h3'
    obtain ⟨hn5, -, hA⟩ := quot_center_alternating_of_mulEquiv hq e
    exact (hnot hn5 hA).elim
  · obtain ⟨-, -, hA, -⟩ := h4
    exact (hnot (by norm_num) hA).elim
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    obtain ⟨hn5, -, hA⟩ := quot_center_alternating_of_mulEquiv hq e
    exact (hnot hn5 hA).elim
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h6
    have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hq.2.toNontrivial
    have hn5 : 5 ≤ 2 * n :=
      CFSG.AGLEmbedding.BlockCyc.five_le_of_perfect_mulEquiv_alternatingGroup e
    exact (hnot hn5 ⟨e⟩).elim
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h7
    obtain ⟨hn5, -, hA⟩ := quot_center_alternating_of_mulEquiv hq e
    exact (hnot hn5 hA).elim
  · obtain ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩ := h8
    obtain ⟨hN5, -, hA⟩ := quot_center_alternating_of_mulEquiv hq e
    exact (hnot hN5 hA).elim

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
