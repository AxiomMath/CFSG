module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma91Proof
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Basic

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem centralizer_singleton_ne_top (hS : GLStanding G m p) {b : G} (hb1 : b ≠ 1) :
    Subgroup.centralizer ({b} : Set G) ≠ ⊤ := by
  have := hS.simple
  intro htop
  have hcenter : b ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({b} : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_singleton_iff.1 this)
  have hcbot : Subgroup.center G = ⊥ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨a, c, hac⟩ := hS.nonabelian
      exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top c : c ∈ Subgroup.center G) a)
        hac
  rw [hcbot, Subgroup.mem_bot] at hcenter
  exact hb1 hcenter

end Basic

section BarX

variable {G : Type*} [Group G]

theorem barX_le_gLBConj (p : ℕ) {C : Subgroup G} {j : G} (hj : j ∈ C) (T : Subgroup G) :
    barX p C (GLBConj j T) ≤
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨j, hj⟩) (barX p C T) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' : (c : G) ∈ GLBConj j T := (Subgroup.mem_subgroupOf).1 hc
  rw [mem_gLBConj, ← map_inv, ← map_mul, ← map_mul]
  refine ⟨⟨j, hj⟩ * c * ⟨j, hj⟩⁻¹, ?_, rfl⟩
  show (⟨j, hj⟩ * c * ⟨j, hj⟩⁻¹ : ↥C) ∈ T.subgroupOf C
  rw [Subgroup.mem_subgroupOf]
  simpa using mem_gLBConj.1 hc'

theorem barX_iSup_conj_le (p : ℕ) {C Js S : Subgroup G} (hJs : Js ≤ C) (hS : S ≤ C) :
    barX p C (⨆ j ∈ Js, GLBConj j S) ≤
      ⨆ y ∈ barX p C Js, GLBConj y (barX p C S) := by
  set W : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) := ⨆ y ∈ barX p C Js, GLBConj y (barX p C S) with hW
  have hC : (⨆ j ∈ Js, GLBConj j S) ≤ C := by
    refine iSup₂_le fun j hj => ?_
    intro x hx
    rw [mem_gLBConj] at hx
    have h1 : j * x * j⁻¹ ∈ C := hS hx
    have := C.mul_mem (C.mul_mem (C.inv_mem (hJs hj)) h1) (hJs hj)
    simpa [mul_assoc] using this
  have hone : ∃ hx : (1 : G) ∈ C, QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨1, hx⟩ ∈ W :=
    ⟨C.one_mem, by rw [show (⟨1, C.one_mem⟩ : ↥C) = 1 from rfl, map_one]; exact W.one_mem⟩
  have hmul : ∀ x y : G, (∃ hx : x ∈ C, QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩ ∈ W) →
      (∃ hy : y ∈ C, QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨y, hy⟩ ∈ W) →
      ∃ hxy : x * y ∈ C, QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x * y, hxy⟩ ∈ W := by
    rintro x y ⟨hxC, hx⟩ ⟨hyC, hy⟩
    refine ⟨C.mul_mem hxC hyC, ?_⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨x, hxC⟩ * ⟨y, hyC⟩) ∈ W
    rw [map_mul]
    exact W.mul_mem hx hy
  have key : ∀ x ∈ ⨆ j ∈ Js, GLBConj j S, ∃ hx : x ∈ C,
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩ ∈ W := by
    intro x hx
    refine Subgroup.iSup_induction (fun j => ⨆ (_ : j ∈ Js), GLBConj j S)
      (C := fun x => ∃ hx : x ∈ C, QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩ ∈ W)
      hx ?_ hone hmul
    intro j x hx
    refine Subgroup.iSup_induction (fun _ : j ∈ Js => GLBConj j S)
      (C := fun x => ∃ hx : x ∈ C, QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩ ∈ W)
      hx ?_ hone hmul
    intro hj x hxS
    have hxJ : x ∈ ⨆ j ∈ Js, GLBConj j S :=
      (le_iSup₂_of_le j hj le_rfl : GLBConj j S ≤ ⨆ j ∈ Js, GLBConj j S) hxS
    have hxC : x ∈ C := hC hxJ
    refine ⟨hxC, ?_⟩
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hxC⟩ ∈ barX p C (GLBConj j S) :=
      ⟨⟨x, hxC⟩, (Subgroup.mem_subgroupOf).2 hxS, rfl⟩
    have h2 := barX_le_gLBConj p (hJs hj) S h1
    exact (le_iSup₂_of_le (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨j, hJs hj⟩)
      ⟨⟨j, hJs hj⟩, (Subgroup.mem_subgroupOf).2 hj, rfl⟩ le_rfl :
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨j, hJs hj⟩) (barX p C S) ≤ W) h2
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨hcC, hcW⟩ := key (c : G) ((Subgroup.mem_subgroupOf).1 hc)
  exact hcW

theorem barX_perfect (p : ℕ) {C T : Subgroup G} (hT : T ≤ C) (hperf : ⁅T, T⁆ = T) :
    ⁅barX p C T, barX p C T⁆ = barX p C T := by
  have h1 : ⁅T.subgroupOf C, T.subgroupOf C⁆ = T.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hT, hperf]
  unfold barX
  rw [← Subgroup.map_commutator, h1]

theorem isSubnormal_barX (p : ℕ) {C A B : Subgroup G} (h : IsSubnormal A B) :
    IsSubnormal (barX p C A) (barX p C B) :=
  isSubnormal_map' _ (isSubnormal_comap' C.subtype h)

theorem isSubnormal_preimage_barX (p : ℕ) {C : Subgroup G}
    {A : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)} (h : IsSubnormal A ⊤) :
    IsSubnormal ((A.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥C))).map C.subtype) C := by
  have h1 := isSubnormal_map' C.subtype
    (isSubnormal_comap' (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) h)
  rwa [Subgroup.comap_top, Subgroup.map_top, Subgroup.range_subtype] at h1

end BarX

section PCore

variable {G : Type*} [Group G] [Finite G]

theorem pCoreOf_le_of_normal (r : ℕ) [Fact r.Prime] {H M : Subgroup G} (hHM : H ≤ M)
    (hn : (H.subgroupOf M).Normal) : pCoreOf r H ≤ pCoreOf r M := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer r
    ((CFSG.LieType.BorelTits.pCoreOf_le r H).trans hHM) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup r H)
  intro g hg
  have hgH : g ∈ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn hg
  rw [mem_normalizer_iff_gLBConj_eq] at hgH ⊢
  rw [← pCoreOf_gLBConj, hgH]

theorem pCoreOf_le_of_isSubnormal (r : ℕ) [Fact r.Prime] {L T : Subgroup G}
    (h : IsSubnormal L T) : pCoreOf r L ≤ pCoreOf r T := by
  induction h with
  | refl => exact le_rfl
  | step hHM hn _ ih => exact (pCoreOf_le_of_normal r hHM hn).trans ih

theorem inf_pCoreOf_eq_of_isSubnormal (r : ℕ) [Fact r.Prime] {L T : Subgroup G}
    (h : IsSubnormal L T) (hLT : L ≤ T) : L ⊓ pCoreOf r T = pCoreOf r L := by
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le r L)
    (pCoreOf_le_of_isSubnormal r h))
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer r inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup r T).to_le inf_le_right)
  intro x hx
  have hxT : x ∈ T := hLT hx
  have h1 := Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf r T hxT)
  have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hx)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 y, h2 y]

end PCore

section TwoPrime

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def imageHom (J T : Subgroup G) (hJT : J ≤ T) :
    ↥J →* ↥((J.subgroupOf T).map (QuotientGroup.mk' (CFSG.pCore 2 ↥T))) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥T)).comp (Subgroup.inclusion hJT)).codRestrict _ fun j =>
    ⟨Subgroup.inclusion hJT j, (Subgroup.mem_subgroupOf).2 j.2, rfl⟩

omit [Finite G] in
theorem imageHom_surjective (J T : Subgroup G) (hJT : J ≤ T) :
    Function.Surjective (imageHom J T hJT) := by
  rintro ⟨_, c, hc, rfl⟩
  exact ⟨⟨(c : G), (Subgroup.mem_subgroupOf).1 hc⟩, Subtype.ext rfl⟩

omit [Finite G] in
theorem mem_ker_imageHom (J T : Subgroup G) (hJT : J ≤ T) (j : ↥J) :
    j ∈ (imageHom J T hJT).ker ↔ (j : G) ∈ pCoreOf 2 T := by
  have key : QuotientGroup.mk' (CFSG.pCore 2 ↥T) (Subgroup.inclusion hJT j) = 1 ↔
      (j : G) ∈ pCoreOf 2 T := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨t, ht, htj⟩
      have : t = Subgroup.inclusion hJT j := Subtype.ext htj
      rwa [this] at ht
  rw [← key, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem isTwoPrimeComp_of_le {X T J : Subgroup G} (hJX : IsTwoPrimeComp X J) (hXT : X ≤ T)
    (hJT : IsSubnormal J T) : IsTwoPrimeComp T J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJX', hsnX, hperf, hcomp⟩ := hJX
  have hJT' : J ≤ T := hJX'.trans hXT
  refine ⟨hJT', hJT, hperf, le_top, ?_, ?_⟩
  · have h1 := isSubnormal_map' (QuotientGroup.mk' (CFSG.pCore 2 ↥T))
      (isSubnormal_comap' T.subtype hJT)
    rw [show T.comap T.subtype = ⊤ from Subgroup.subgroupOf_self T,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
    exact h1
  · have hkX : ∀ j : ↥J, j ∈ (imageHom J X hJX').ker ↔ (j : G) ∈ pCoreOf 2 J := fun j => by
      rw [mem_ker_imageHom, ← inf_pCoreOf_eq_of_isSubnormal 2 hsnX hJX', Subgroup.mem_inf]
      exact ⟨fun h => ⟨j.2, h⟩, fun h => h.2⟩
    have hkT : ∀ j : ↥J, j ∈ (imageHom J T hJT').ker ↔ (j : G) ∈ pCoreOf 2 J := fun j => by
      rw [mem_ker_imageHom, ← inf_pCoreOf_eq_of_isSubnormal 2 hJT hJT', Subgroup.mem_inf]
      exact ⟨fun h => ⟨j.2, h⟩, fun h => h.2⟩
    have hker : (imageHom J X hJX').ker = (imageHom J T hJT').ker :=
      Subgroup.ext fun j => (hkX j).trans (hkT j).symm
    have : (imageHom J X hJX').ker.Normal := MonoidHom.normal_ker _
    have : (imageHom J T hJT').ker.Normal := MonoidHom.normal_ker _
    let e : ↥((J.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ≃*
        ↥((J.subgroupOf T).map (QuotientGroup.mk' (CFSG.pCore 2 ↥T))) :=
      (QuotientGroup.quotientKerEquivOfSurjective _ (imageHom_surjective J X hJX')).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans
          (QuotientGroup.quotientKerEquivOfSurjective _ (imageHom_surjective J T hJT')))
    exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hcomp.2.2

end TwoPrime

section TwoSubgroup

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem barX_two_subgroup_props (i20 : Input20_1) (i11 : Input11_6) (l23 : Lemma23)
    (hS : GLStanding G m p) {B : Subgroup G} (hB : IsBOneMax p B) {C S : Subgroup G}
    (hCtop : C ≠ ⊤) (hBC : B ≤ C) (hSC : S ≤ C) (hS2 : IsPGroup 2 S)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) :
    barX p C S ≤ Subgroup.centralizer
        ((CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C) : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :
          Set (↥C ⧸ GLAPPrimeCore p ↥C)) ∧
      ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
        barX p C S ≤ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hB' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf (l23 G m p hS B hB) hBC
  have hBbar : IsSCp p ⊤ (barX p C B) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥C)
      ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card) hB'
  have hXb2 : IsPGroup 2 (barX p C S) :=
    IsPGroup.map (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm)
      (QuotientGroup.mk' (GLAPPrimeCore p ↥C))
  have hBXb : barX p C B ≤ Subgroup.normalizer (barX p C S : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    barX_le_normalizer hBS
  have h1 := centralizes_pCore_of_isSCp i20 hp hp2 hBbar hXb2 hBXb
  have hrank : GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p (B.subgroupOf C) := by
    refine (glaTwoLocalRank_subgroup_le hp.one_lt C).trans ?_
    rw [hS.rank_eq]
    refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB'.2.1 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hS.card_eq hB]
  refine ⟨h1, fun K hK => ?_⟩
  obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq C hK
  exact barX_le_normalizer (le_normalizer_of_input11_6 i11 hS.kProper hp hp2 hCtop hBC hSC
    (l23 G m p hS B hB) hrank hS2 hBS hL)

end TwoSubgroup

end CFSG.LocalAnalysis.GLTheoremB
