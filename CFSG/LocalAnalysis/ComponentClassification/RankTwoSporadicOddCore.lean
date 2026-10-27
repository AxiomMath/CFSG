module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCoreBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperOver
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupMap
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open

variable {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal]

local notation "π" => QuotientGroup.mk' N

theorem comap_map_mk'_of_le {H : Subgroup G} (hNH : N ≤ H) : (H.map π).comap π = H := by
  rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNH]

omit hN in
theorem mem_centralizer_of_displacement {A : Subgroup G} (hAp : commutator ↥A = ⊤) {g : G}
    (hg : g ∈ normalizer (A : Set G))
    (hdisp : ∀ a ∈ A, a⁻¹ * (g * a * g⁻¹) ∈ centralizer (A : Set G)) :
    g ∈ centralizer (A : Set G) := by
  have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hAp
  let σ : ↥A →* ↥A :=
    { toFun := fun a => ⟨g * a * g⁻¹, (mem_normalizer_iff.mp hg a).mp a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hσ := PerfectAutomorphisms.hom_eq_id_of_central_displacement σ (fun a => by
    rw [mem_center_iff]
    intro b
    apply Subtype.ext
    have hmem : (a : G)⁻¹ * (g * a * g⁻¹) ∈ A :=
      A.mul_mem (A.inv_mem a.2) ((mem_normalizer_iff.mp hg a).mp a.2)
    have := mem_centralizer_iff.mp (hdisp a a.2) b b.2
    simpa [σ] using this)
  rw [mem_centralizer_iff]
  intro a ha
  have := congrArg Subtype.val (DFunLike.congr_fun hσ ⟨a, ha⟩)
  simp only [σ, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.id_apply] at this
  calc a * g = g * a * g⁻¹ * g := by rw [this]
    _ = g * a := by group

section Image

variable [Finite G] {A : Subgroup G}

theorem centralizer_map_eq (hodd : Odd (Nat.card N)) (hNA : N ≤ centralizer (A : Set G))
    (hAp : commutator ↥A = ⊤) :
    centralizer ((A.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) = (centralizer (A : Set G)).map π := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hgAN : g ∈ normalizer ((A ⊔ N : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      rw [← comap_map_mk'_of_le (N := N) (le_sup_right : N ≤ A ⊔ N), mem_comap, mem_comap,
        Subgroup.map_sup, (Subgroup.map_eq_bot_iff N).mpr (QuotientGroup.ker_mk' N).symm.le,
        sup_bot_eq]
      have hc : ∀ z ∈ A.map π, π g * z * (π g)⁻¹ = z := fun z hz => by
        rw [← mem_centralizer_iff.mp hx z hz, mul_inv_cancel_right]
      constructor
      · intro hy
        rw [map_mul, map_mul, map_inv, hc _ hy]
        exact hy
      · intro hy
        rw [map_mul, map_mul, map_inv] at hy
        have h2 := hc _ hy
        have h3 : π y = π g * π y * (π g)⁻¹ := by
          have : π g * π y * (π g)⁻¹ = π g * (π g * π y * (π g)⁻¹) * (π g)⁻¹ := by
            rw [h2]
          calc π y = (π g)⁻¹ * (π g * π y * (π g)⁻¹) * π g := by group
            _ = (π g)⁻¹ * (π g * (π g * π y * (π g)⁻¹) * (π g)⁻¹) * π g := by rw [← this]
            _ = π g * π y * (π g)⁻¹ := by group
        rw [h3]
        exact hy
    have hg : g ∈ normalizer (A : Set G) := by
      rwa [normalizer_sup_eq hodd hNA hAp] at hgAN
    refine ⟨g, mem_centralizer_of_displacement hAp hg fun a ha => ?_, rfl⟩
    apply hNA
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul,
      map_inv]
    have hc := mem_centralizer_iff.mp hx (π a) ⟨a, ha, rfl⟩
    rw [← hc]
    group
  · rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc a ha]

omit [Finite G] in
theorem ker_quotCenter_map (hNA : N ≤ centralizer (A : Set G)) (hAp : commutator ↥A = ⊤) :
    ((QuotientGroup.mk' (center ↥(A.map π))).comp ((QuotientGroup.mk' N).subgroupMap A)).ker =
      center ↥A := by
  ext a
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_center_iff]
  constructor
  · intro h b
    have hcent : (a : G) ∈ centralizer (A : Set G) := by
      refine mem_centralizer_of_displacement hAp (le_normalizer a.2) fun c hc => hNA ?_
      have := h ⟨π c, c, hc, rfl⟩
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      have h' : π c * π a = π a * π c := congrArg Subtype.val this
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, ← h']
      group
    exact Subtype.ext (by simpa using mem_centralizer_iff.mp hcent b b.2)
  · intro h b
    obtain ⟨_, ⟨c, hc, rfl⟩⟩ := b
    apply Subtype.ext
    change π c * π a = π a * π c
    have hca : c * a = a * c := congrArg Subtype.val (h ⟨c, hc⟩)
    rw [← map_mul, ← map_mul, hca]

omit [Finite G] in
noncomputable def quotCenterEquivMap (hNA : N ≤ centralizer (A : Set G))
    (hAp : commutator ↥A = ⊤) : ↥A ⧸ center ↥A ≃* ↥(A.map π) ⧸ center ↥(A.map π) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_quotCenter_map hNA hAp).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp ((QuotientGroup.mk' N).subgroupMap_surjective A)))

theorem standard_map (hA : standardComponentIsStandard A) (hodd : Odd (Nat.card N))
    (hNA : N ≤ centralizer (A : Set G)) : standardComponentIsStandard (A.map π) :=
  (GSThmB.isStandardSubgroup_map_mk' hA.isStandardSubgroup hodd hNA).standardComponentIsStandard

theorem two_le_pRank_map (hodd : Odd (Nat.card N)) (hNA : N ≤ centralizer (A : Set G))
    (hAp : commutator ↥A = ⊤) (hrank : 2 ≤ Open.pRank 2 (centralizer (A : Set G))) :
    2 ≤ Open.pRank 2 (centralizer ((A.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [centralizer_map_eq hodd hNA hAp]
  obtain ⟨U, hUK, hU, hU4⟩ := exists_four_le_of_two_le_pRank hrank
  have hinj : Nat.card (U.map π) = Nat.card U := by
    refine (Nat.card_congr (Equiv.ofBijective _ ⟨fun x y hxy => ?_,
      (QuotientGroup.mk' N).subgroupMap_surjective U⟩)).symm
    have h1 : π ((x : G)⁻¹ * y) = 1 := by
      have := congrArg Subtype.val hxy
      change π x = π y at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hU2 : IsPGroup 2 U := fun u => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa using hU.2 u u.2)⟩
    have hbot : U ⊓ N = ⊥ := by
      refine AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ N
        (hU2.to_inf_left) hodd inf_le_right
    have : (x : G)⁻¹ * y ∈ U ⊓ N := ⟨U.mul_mem (U.inv_mem x.2) y.2, h1⟩
    rw [hbot, mem_bot, inv_mul_eq_one] at this
    exact Subtype.ext this
  refine le_csSup ⟨Nat.card (G ⧸ N), ?_⟩ ⟨U.map π, map_mono hUK, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro k ⟨E, -, -, hE⟩
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ = Nat.card E := hE.symm
      _ ≤ Nat.card (G ⧸ N) := card_le_card_group E
  · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    simp only [coe_mul]
    have hxy : x * y = y * x := congrArg Subtype.val (hU.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hU.2 x hx, map_one]
  · rw [hinj, hU4]
    norm_num

end Image

theorem exists_rankTwoHyp_quotient {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hH : RankTwoStandard.RankTwoHyp G A) :
    ∃ B : Subgroup (G ⧸ standardComponentOddCore G),
      RankTwoStandard.RankTwoHyp (G ⧸ standardComponentOddCore G) B ∧
      standardComponentOddCore (G ⧸ standardComponentOddCore G) = ⊥ ∧
      Nonempty (RankTwoStandard.rankTwoQuot A ≃* RankTwoStandard.rankTwoQuot B) := by
  have hodd := odd_card_standardComponentOddCore (G := G)
  have hNA := standardComponentOddCore_le_centralizer hH.standard hH.rank
  refine ⟨A.map (QuotientGroup.mk' (standardComponentOddCore G)), ⟨?_, ?_, ?_, ?_⟩,
    standardComponentOddCore_quotient_eq_bot, ⟨quotCenterEquivMap hNA hH.standard.1.1⟩⟩
  · exact CatalogueKProperOver.kProper_quotient (fun e h => SectionRank.catalog_of_mulEquiv e h)
      hH.kProper _
  · exact standard_map hH.standard hodd hNA
  · intro hn
    apply hH.not_normal
    have h1 : (A ⊔ standardComponentOddCore G).Normal := by
      have := hn.comap (QuotientGroup.mk' (standardComponentOddCore G))
      rwa [comap_map_eq, QuotientGroup.ker_mk'] at this
    rw [← normalizer_eq_top_iff, ← normalizer_sup_eq hodd hNA hH.standard.1.1]
    exact normalizer_eq_top_iff.mpr h1
  · exact two_le_pRank_map hodd hNA hH.standard.1.1 hH.rank

theorem not_isSporadic_of_sporadicCaseOdd {s : TauCeti.SporadicName} (h : SporadicCaseOdd s)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (hH : RankTwoStandard.RankTwoHyp G A) :
    ¬ Blueprint.NativeSporadic.IsSporadic (RankTwoStandard.rankTwoQuot A) s := by
  rintro ⟨e⟩
  obtain ⟨B, hB, hodd, ⟨f⟩⟩ := exists_rankTwoHyp_quotient hH
  exact h _ B hB hodd ⟨f.symm.trans e⟩

theorem rankTwoSporadicStandard_of_odd (h : ∀ s, SporadicCaseOdd s) :
    RankTwoStandard.RankTwoSporadicStandard := by
  intro G _ _ A hH ⟨s, ⟨e⟩⟩
  obtain ⟨B, hB, hodd, ⟨f⟩⟩ := exists_rankTwoHyp_quotient hH
  exact h s _ B hB hodd ⟨f.symm.trans e⟩

end CFSG.ComponentClassification.RankTwoSporadic
