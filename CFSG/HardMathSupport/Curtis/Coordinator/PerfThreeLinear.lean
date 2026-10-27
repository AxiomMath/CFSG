module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixPrimeBar
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVOut
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section CentralQuotient

variable {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]

omit [Finite X] in
theorem exists_sylow_normalizer_map_of_central_quotient (ψ : G →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card ψ.ker)) {J : Subgroup G}
    (hpar : ∃ T : Subgroup G, IsSylowTwoOf T ⊤ ∧ Subgroup.normalizer (T : Set G) ≤ J ∧
      J ≠ Subgroup.normalizer (T : Set G))
    (hperf : ∀ U : Subgroup G, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    (∃ T : Sylow 2 X, Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ J.map ψ ∧
      J.map ψ ≠ Subgroup.normalizer ((T : Subgroup X) : Set X)) ∧
    ∀ V : Subgroup X, V ≤ J.map ψ → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hNJ, hneB⟩ := hpar
  have hkJ : ψ.ker ≤ J :=
    hker.trans ((Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)).trans hNJ)
  have hcomap : (J.map ψ).comap ψ = J := Subgroup.comap_map_eq_self hkJ
  have hidx : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
  let T' : Sylow 2 G := hT.2.1.toSylow hidx
  refine ⟨⟨T'.mapSurjective hψ, ?_, ?_⟩, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    exact ToralCensus.normalizer_map_le_map ψ hψ hker hodd hT.2.1 hNJ
  · rw [Sylow.coe_mapSurjective]
    intro hJe
    have hJe : J.map ψ = Subgroup.normalizer ((T.map ψ : Subgroup X) : Set X) := hJe
    apply hneB
    refine le_antisymm (fun x hx => ?_) hNJ
    have hmem : ψ x ∈ Subgroup.normalizer ((T.map ψ : Subgroup X) : Set X) := by
      rw [← hJe]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hyN, hyx⟩ := ToralCensus.normalizer_map_le_map ψ hψ hker hodd hT.2.1
      (le_refl (Subgroup.normalizer (T : Set G))) hmem
    have hxy : y⁻¹ * x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hzN : y⁻¹ * x ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)) (hker hxy)
    simpa using Subgroup.mul_mem _ hyN hzN
  · intro V hVJ hV
    obtain ⟨W, hW, hWle, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker hV
      (by rw [MonoidHom.range_eq_top.2 hψ]; exact le_top)
    have hWJ : W ≤ J := by
      refine hWle.trans ?_
      rw [← hcomap]
      exact Subgroup.comap_mono hVJ
    have hdvd : Nat.card V ∣ Nat.card W := by
      rw [← hWmap]
      exact Subgroup.card_dvd_of_surjective (ψ.subgroupMap_surjective W)
    exact (hperf W hWJ hW).coprime_dvd_right hdvd

omit [Finite G] [Finite X] in
theorem exists_perfect_centralizer_dvd_of_central_quotient (ψ : G →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G) {l : G} {P : Subgroup X}
    (hP : ⁅P, P⁆ = P) (hPc : P ≤ Subgroup.centralizer ({ψ l} : Set X)) :
    ∃ W : Subgroup G, ⁅W, W⁆ = W ∧ W ≤ Subgroup.centralizer ({l} : Set G) ∧
      Nat.card P ∣ Nat.card W := by
  obtain ⟨W, hW, -, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker hP
    (by rw [MonoidHom.range_eq_top.2 hψ]; exact le_top)
  have hcentral : ∀ w ∈ W, ⁅w, l⁆ ∈ Subgroup.center G := by
    intro w hw
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    have hwP : ψ w ∈ P := by rw [← hWmap]; exact ⟨w, hw, rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 (hPc hwP) (ψ l) (Set.mem_singleton _)).symm
  refine ⟨W, hW, ?_, ?_⟩
  · rw [← hW]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 := commutator_commutator_eq_one_of_central (hcentral a ha) (hcentral b hb)
    rw [commutatorElement_eq_one_iff_commute] at h1
    exact h1.symm
  · rw [← hWmap]
    exact Subgroup.card_dvd_of_surjective (ψ.subgroupMap_surjective W)

end CentralQuotient

section Component

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}

theorem exists_sylow_normalizer_subgroupOf_of_compParab (h : CompParab L J) :
    ∃ T : Subgroup ↥L, IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set ↥L) ≤ J.subgroupOf L ∧
      J.subgroupOf L ≠ Subgroup.normalizer (T : Set ↥L) := by
  have hJL : J ≤ L := h.parab.1
  obtain ⟨-, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := h.parab
  refine ⟨T.subgroupOf L, ⟨le_top, hT2.comap_subtype (K := L), ?_⟩, ?_, ?_⟩
  · have e : ((T.subgroupOf L).subgroupOf ⊤).index = (T.subgroupOf L).index :=
      Subgroup.relIndex_top_right _
    rw [e]
    exact hTi
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hNJ ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
    have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := Subgroup.mem_subgroupOf.2 ht
    have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 h1
    simpa [Subgroup.mem_subgroupOf] using h2
  · intro hJe
    apply h.ne_borel T ⟨hTL, hT2, hTi⟩
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hyL : y ∈ L := hJL hy
      refine ⟨hyL, ?_⟩
      have hyG : (⟨y, hyL⟩ : ↥L) ∈ J.subgroupOf L := Subgroup.mem_subgroupOf.2 hy
      rw [hJe] at hyG
      refine Subgroup.mem_normalizer_fintype fun t ht => ?_
      have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := Subgroup.mem_subgroupOf.2 ht
      have h2 := (Subgroup.mem_normalizer_iff.1 hyG ⟨t, hTL ht⟩).1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
    · obtain ⟨hyL, hyN⟩ := hy
      have : (⟨y, hyL⟩ : ↥L) ∈ J.subgroupOf L := by
        rw [hJe, Subgroup.mem_normalizer_iff]
        intro g
        have := Subgroup.mem_normalizer_iff.1 hyN g.1
        simp only [Subgroup.mem_subgroupOf]
        exact this
      exact Subgroup.mem_subgroupOf.1 this

omit [Finite Y] in
theorem coprime_card_of_perf_subgroupOf
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∀ U : Subgroup ↥L, U ≤ J.subgroupOf L → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U) := by
  intro U hUJ hU
  have hU' : ⁅U.map L.subtype, U.map L.subtype⁆ = U.map L.subtype := by
    rw [← Subgroup.map_commutator, hU]
  have hUJ' : U.map L.subtype ≤ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hUJ hx)
  have hcard : Nat.card (U.map L.subtype) = Nat.card U :=
    Nat.card_congr (Subgroup.equivMapOfInjective U L.subtype L.subtype_injective).toEquiv.symm
  rw [← hcard]
  exact hperf _ hUJ' hU'

omit [Finite Y] in
theorem exists_decomp_of_mem_sup_centralizer {u : Y} (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y))
    (hpow : u ^ 3 = 1) (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    ∃ l : ↥L, l ^ 3 ∈ Subgroup.center ↥L ∧ ∀ g : ↥L, g * l = l * g → g ∈ J.subgroupOf L := by
  obtain ⟨a, ha, c, hc, huac⟩ := exists_mul_of_mem_sup_of_commute (A := L)
    (C := Subgroup.centralizer (L : Set Y))
    (fun a ha c hc => (Subgroup.mem_centralizer_iff.1 hc) a ha) hu
  have hcomm : ∀ g : Y, g ∈ L → g * c = c * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.1 hc) g hg
  refine ⟨⟨a, ha⟩, ?_, ?_⟩
  · have hu3 := hpow
    rw [huac] at hu3
    have hac : a * c = c * a := hcomm a ha
    rw [Commute.mul_pow (hac : Commute a c) 3] at hu3
    have hcp : c ^ 3 ∈ Subgroup.centralizer (L : Set Y) := Subgroup.pow_mem _ hc 3
    have hap : a ^ 3 = (c ^ 3)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hu3
    have hapc : a ^ 3 ∈ Subgroup.centralizer (L : Set Y) := by
      rw [hap]
      exact Subgroup.inv_mem _ hcp
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Y) * a ^ 3 = a ^ 3 * (g : Y)
    exact (Subgroup.mem_centralizer_iff.1 hapc) (g : Y) g.2
  · intro g hg
    rw [Subgroup.mem_subgroupOf]
    apply hfix g.1 g.2
    have h1 : (g : Y) * a = a * (g : Y) := congrArg Subtype.val hg
    have h2 : (g : Y) * c = c * (g : Y) := hcomm g g.2
    rw [huac]
    calc (a * c) * (g : Y) * (a * c)⁻¹ = a * (c * g) * (c⁻¹ * a⁻¹) := by group
      _ = a * (g * c) * (c⁻¹ * a⁻¹) := by rw [h2]
      _ = (a * g) * (c * c⁻¹) * a⁻¹ := by group
      _ = (g * a) * a⁻¹ := by rw [h1]; group
      _ = g := by group

end Component

section Model

open CFSG.LocalAnalysis.ComponentInitial

theorem exists_perfect_three_dvd_centralizer_of_model_psl_two {X : Type} [Group X] {n : ℕ}
    (hn : 5 ≤ n) (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1) (v : X)
    (hv : v ^ 3 = 1) :
    ∃ P : Subgroup X, P ≤ Subgroup.centralizer ({v} : Set X) ∧ ⁅P, P⁆ = P ∧
      3 ∣ Nat.card P := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  let e1 : X ≃* LinearFlag.projectiveSL n K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have hbot : LinearFlag.scalars n K = ⊥ := by
    rw [LinearFlag.scalars_eq_center]
    exact Setup.Family.center_specialLinear_eq_bot_of_card_two n K hK2
  have hinj : Function.Injective (LinearFlag.proj n K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have := LinearFlag.proj_eq_one_iff.mp hg
    rwa [hbot, Subgroup.mem_bot] at this
  let e2 : Matrix.SpecialLinearGroup (Fin n) K ≃* LinearFlag.projectiveSL n K :=
    MulEquiv.ofBijective (LinearFlag.proj n K) ⟨hinj, LinearFlag.proj_surjective n K⟩
  have hbij : Function.Bijective
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K) := by
    refine ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => ?_⟩
    have hmem : g ∈ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
      apply Units.ext
      have hne : ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) ≠ 0 := Units.ne_zero _
      rcases eq_zero_or_eq_one_of_card_eq_two hK2 ((Matrix.GeneralLinearGroup.det g : Kˣ) : K)
        with h0 | h1
      · exact absurd h0 hne
      · simpa using h1
    exact hmem
  let e3 : Matrix.SpecialLinearGroup (Fin n) K ≃* GL (Fin n) K :=
    MulEquiv.ofBijective _ hbij
  let φ : X ≃* GL (Fin n) K := e1.trans (e2.symm.trans e3)
  have h3 : φ v ^ 3 = 1 := by rw [← map_pow, hv, map_one]
  obtain ⟨P, hPc, hPp, hP3⟩ := exists_perfect_three_dvd_centralizer_gl_two hK2 hn (φ v) h3
  refine ⟨P.map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have := Subgroup.mem_centralizer_iff.1 (hPc hp) (φ w) (Set.mem_singleton _)
    apply φ.injective
    simpa using this
  · rw [← Subgroup.map_commutator, hPp]
  · rw [← Nat.card_congr
      (Subgroup.equivMapOfInjective P φ.symm.toMonoidHom φ.symm.injective).toEquiv]
    exact hP3

end Model

theorem isClassicalOrG2Index_of_idxA {i : TauCeti.LieTypeIndex} (h : IdxA i) :
    IsClassicalOrG2Index i := by
  cases i <;> first | exact h | exact h.elim

theorem isClassicalOrG2Index_of_idxG2 {i : TauCeti.LieTypeIndex} (h : IdxG2 i) :
    IsClassicalOrG2Index i := by
  cases i <;> first | exact h | exact h.elim

section Void


theorem isClassicalOrG2IndexTwo_of_fixPerfThreeHyp {Y : Type} [Group Y] [Finite Y]
    {L J : Subgroup Y} {u : Y} (h : FixPerfThreeHyp L J u) (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    IsClassicalOrG2IndexTwo d.1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ Subgroup.center ↥L :=
    (QuotientGroup.ker_mk' _).le
  have hodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center ↥L)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact h.parab.odd
  obtain ⟨⟨T, hNT, hneT⟩, hperf⟩ := exists_sylow_normalizer_map_of_central_quotient
    (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _) hker hodd
    (exists_sylow_normalizer_subgroupOf_of_compParab h.parab)
    (coprime_card_of_perf_subgroupOf h.perf)
  exact isClassicalOrG2IndexTwo_of_perfect_coprime d hd e T _ hNT hneT hperf

theorem fixPerfThreeVoid_g2 : FixPerfThreeVoid (IsLieOf IdxG2) := by
  intro Y _ _ L J u hyp hX
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  have hidx2 := isClassicalOrG2IndexTwo_of_fixPerfThreeHyp hyp ⟨d, hv⟩
    (isClassicalOrG2Index_of_idxG2 hd) e
  cases d
  case G2 q =>
    have h3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have h2 : q.card = 2 := hidx2
    omega
  all_goals exact hd.elim

theorem fixPerfThreeVoid_A : FixPerfThreeVoid (IsLieOf IdxA) := by
  intro Y _ _ L J u hyp hX
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  have hidx2 := isClassicalOrG2IndexTwo_of_fixPerfThreeHyp hyp ⟨d, hv⟩
    (isClassicalOrG2Index_of_idxA hd) e
  cases d
  case A r q =>
    have hp2 : q.p = 2 := hd
    have hcard : q.card = 2 := hidx2
    have hexp : q.exponent = 1 := by
      have hpos := q.exponent_pos
      by_contra hne
      have h2 : 2 ≤ q.exponent := by omega
      have : 2 ^ 2 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
      rw [TauCeti.PrimePower.card_def, hp2] at hcard
      omega
    have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hv
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1
    have hdup := hvalid.2
    simp only [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, not_or, not_and] at hdup
    have hr : 4 ≤ r := by
      by_contra hlt
      have h1 := hrange.1
      have h4 := hrange.2
      have hd2 := hdup.2.1
      have hd3 := hdup.2.2
      interval_cases r
      · exact absurd (h4 rfl) (by omega)
      · exact hd2 rfl hcard
      · exact hd3 rfl hcard
    have hmodel := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hp2, hexp] at hmodel
    have hq : CFSG.Open.IsQuasisimple ↥L := hyp.parab.comp.2.2
    have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
    have hout : ¬ 3 ∣ Nat.card (Outer ↥L) := fun h3 =>
      not_three_dvd_card_outer_of_psl_two hmodel
        (h3.trans (card_outer_dvd_card_outer_centerQuotient ↥L))
    have hu := mem_sup_centralizer_of_not_dvd_card_outer (p := 3) (k := 1) Nat.prime_three hout
      hyp.norm (by simpa using hyp.pow)
    obtain ⟨l, hl3, hlfix⟩ := exists_decomp_of_mem_sup_centralizer hu hyp.pow hyp.fix
    have hv3 : (QuotientGroup.mk' (Subgroup.center ↥L) l) ^ 3 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hl3
    obtain ⟨P, hPc, hPp, hP3⟩ := exists_perfect_three_dvd_centralizer_of_model_psl_two
      (by omega) hmodel _ hv3
    obtain ⟨W, hW, hWc, hPW⟩ := exists_perfect_centralizer_dvd_of_central_quotient
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _).le hPp hPc
    have hWJ : W ≤ J.subgroupOf L := fun w hw =>
      hlfix w ((Subgroup.mem_centralizer_iff.1 (hWc hw) l (Set.mem_singleton _)).symm)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (coprime_card_of_perf_subgroupOf hyp.perf W hWJ hW) (hP3.trans hPW)
  all_goals exact hd.elim

end Void

end CFSG.HardMathSupport.Curtis.Coordinator
