module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneBranch
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOddCoreReduction
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem pRank_subgroup_mono {H K : Subgroup G} (h : H ≤ K) :
    CFSG.pRank 2 ↥H ≤ CFSG.pRank 2 ↥K := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
    ← SectionRank.pRank_eq_pRank_top_subgroup, ← SectionRank.pRank_eq_pRank_top_subgroup]
  exact SectionRank.pRank_mono one_lt_two h

theorem pRank_le_one_of_card_le_two {Y : Type*} [Group Y] [Finite Y] (h : Nat.card Y ≤ 2) :
    CFSG.pRank 2 Y ≤ 1 := by
  apply csSup_le'
  rintro r ⟨E, -, hcard⟩
  have h1 : 2 ^ r ≤ 2 ^ 1 := by
    rw [← hcard, pow_one]
    exact (Subgroup.card_le_card_group E).trans h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

theorem pRank_le_one_of_sylow_eq_zpowers {Y : Subgroup G} {u : G} (hu : orderOf u = 2)
    (huY : u ∈ Y) (P : Sylow 2 ↥Y) (hP : (P : Subgroup Y) = (zpowers u).subgroupOf Y) :
    CFSG.pRank 2 ↥Y ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← (SectionRank.pRank_sylow P).2]
  refine pRank_le_one_of_card_le_two ?_
  rw [hP, Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).mpr huY)).toEquiv, Nat.card_zpowers,
    hu]

theorem pRank_conjugate (K : Subgroup G) (g : G) :
    CFSG.pRank 2 ↥(conjugate K g) = CFSG.pRank 2 ↥K :=
  (pRank_eq_of_mulEquiv one_lt_two
    (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)).symm

theorem pRank_coreActionKernel_subgroupOf {H K : Subgroup G} (hKH : K ≤ H) :
    CFSG.pRank 2 ↥(coreActionKernel (K.subgroupOf H)) =
      CFSG.pRank 2 ↥(coreActionKernel K ⊓ H) := by
  have hCmap : (coreActionKernel (K.subgroupOf H)).map H.subtype = coreActionKernel K ⊓ H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_inf.mpr ⟨(mem_coreActionKernel_subgroupOf_iff hKH y).mp hy, y.2⟩
    · intro hx
      exact ⟨⟨x, (mem_inf.mp hx).2⟩,
        (mem_coreActionKernel_subgroupOf_iff hKH _).mpr (mem_inf.mp hx).1, rfl⟩
  exact pRank_eq_of_mulEquiv one_lt_two
    (((coreActionKernel (K.subgroupOf H)).equivMapOfInjective H.subtype
      H.subtype_injective).trans (MulEquiv.subgroupCongr hCmap))

theorem pRank_map_sylow_inf_normal {X N : Subgroup G} [N.Normal] (P : Sylow 2 ↥X) :
    CFSG.pRank 2 ↥((P : Subgroup X).map X.subtype ⊓ N) = CFSG.pRank 2 ↥(N ⊓ X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Glauberman.sylow_inf_normal P (N := N.subgroupOf X)
  have hmap : ((P : Subgroup X) ⊓ N.subgroupOf X).map X.subtype =
      (P : Subgroup X).map X.subtype ⊓ N := by
    rw [map_inf_eq _ _ _ X.subtype_injective, subgroupOf_map_subtype, inf_comm N X, ← inf_assoc,
      inf_eq_left.mpr (map_subtype_le _)]
  rw [← pRank_eq_of_mulEquiv one_lt_two ((((P : Subgroup X) ⊓ N.subgroupOf X).equivMapOfInjective
      X.subtype X.subtype_injective).trans (MulEquiv.subgroupCongr hmap)),
    ← pRank_eq_of_mulEquiv one_lt_two (subgroupOfEquivOfLe (inf_le_right :
      (P : Subgroup X) ⊓ N.subgroupOf X ≤ N.subgroupOf X)),
    ← hQ, (SectionRank.pRank_sylow Q).2,
    pRank_eq_of_mulEquiv one_lt_two (((N.subgroupOf X).equivMapOfInjective X.subtype
      X.subtype_injective).trans (MulEquiv.subgroupCongr (subgroupOf_map_subtype N X)))]

theorem exists_involution_central_of_normal {S N : Subgroup G} (hS : IsPGroup 2 S) [N.Normal]
    (hSN : S ⊓ N ≠ ⊥) : ∃ u : G, u ∈ S ∧ u ∈ N ∧ orderOf u = 2 ∧ ∀ s ∈ S, s * u = u * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hM : N.subgroupOf S ≠ ⊥ := by
    intro h
    apply hSN
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, (mem_inf.mp hx).1⟩ : S) ∈ N.subgroupOf S :=
      mem_subgroupOf.mpr (mem_inf.mp hx).2
    rw [h, mem_bot] at hmem
    rw [mem_bot]
    exact congrArg Subtype.val hmem
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hM
  have hZp : IsPGroup 2 ↥(N.subgroupOf S ⊓ center S) := hS.to_subgroup _
  rcases hZp.card_eq_or_dvd with h1 | h2
  · exact absurd (Subgroup.card_eq_one.mp h1) h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨((y : S) : G), (y : S).2, mem_subgroupOf.mp (mem_inf.mp y.2).1, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  · exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.mp y.2).2 ⟨s, hs⟩)

theorem componentsLift_of_normal {H : Subgroup G} (hH : H.Normal) : ComponentsLift H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x _ K hKC hK
  have hn : ((centralizer ({x} : Set G) ⊓ H).subgroupOf (centralizer ({x} : Set G))).Normal := by
    rw [inf_subgroupOf_left]
    infer_instance
  obtain ⟨hs, h2, h3⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K _ hKC).mp hK
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K _ (hKC.trans inf_le_left)).mpr
    ⟨isSubnormal_subgroupOf_trans_of_le hKC inf_le_left hs hn.isSubnormal, h2, h3⟩

theorem isPComponent_top_of_isPComponent {G₀ : Subgroup G} (hG₀ : IsPComponent 2 G₀) :
    IsPComponent 2 (⊤ : Subgroup ↥G₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h2, h3⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 G₀ ⊤ le_top).mp
    (isPComponent_subgroupOf_top_iff'.mpr hG₀)
  have h := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 G₀ G₀ le_rfl).mpr
    ⟨by rw [subgroupOf_self]; exact IsSubnormal.top, h2, h3⟩
  rwa [subgroupOf_self] at h

theorem nonempty_quotient_equiv_fusionZStar (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) {B : Subgroup G}
    (hB : ∃ b : G, IsTwoComponentAt b B) (hfam : FooteFamilyType B)
    (hrank : 2 ≤ CFSG.pRank 2 ↥B) :
    Nonempty (B ⧸ pPrimeCore 2 B ≃* B ⧸ Open.fusionZStar B) := by
  obtain ⟨b, hb⟩ := hB
  have hBq := isQuasisimple_quotient_of_isPComponent hb.2.1 hb.2.2
  have hZ2 := card_center_le_two_of_footeFamilyType hGA hGC hSA G B ⟨b, hb⟩ hfam
  have hZ : center (B ⧸ pPrimeCore 2 B) = ⊥ := by
    by_contra hZ
    have := pRank_le_one_of_center_ne_bot hBq hfam hZ2 hZ
    omega
  obtain ⟨e⟩ := nonempty_fusionZStar_quotient_equiv ↥B
  exact ⟨(e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)).symm⟩

end CFSG.ComponentClassification.FooteLit
