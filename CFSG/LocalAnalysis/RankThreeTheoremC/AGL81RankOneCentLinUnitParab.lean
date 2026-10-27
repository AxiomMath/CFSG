module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepSix
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabLin
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabUni
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCovers
import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab

open CFSG.AGLEmbedding CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.QuasithinUnique.Setup.X7b (centralQuotientEquiv odd_card_center_quotient_twoPart)
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (twoPart twoPart_le_center isPGroup_twoPart)

theorem isQuasisimple_of_open {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

theorem isQuasisimple_to_open {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem exists_mulEquiv_projectiveSL_three {X : Type} [Group X] {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.p = 2) (hd : d.1 = .A 2 q)
    (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ f : ℕ, 1 ≤ f ∧ Nonempty (X ≃* LinearFlag.projectiveSL 3 (GaloisField 2 f)) := by
  obtain ⟨d, hv⟩ := d
  change d = .A 2 q at hd
  subst hd
  obtain ⟨p, k, hp, hk⟩ := q
  change p = 2 at hq
  subst hq
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  exact ⟨k, hk, ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 ⟨2, k, hp, hk⟩
    hv)).trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL _ _)⟩⟩

theorem three_dvd_card_center_quotient {Q : Type} [Group Q] [Finite Q] {A : Subgroup Q}
    [A.Normal] (hA2 : IsPGroup 2 ↥A)
    (hmap : Subgroup.center (Q ⧸ A) = (Subgroup.center Q).map (QuotientGroup.mk' A))
    (h3 : 3 ∣ Nat.card ↥(Subgroup.center Q)) : 3 ∣ Nat.card ↥(Subgroup.center (Q ⧸ A)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ζ : ↥(Subgroup.center Q) →* ↥(Subgroup.center (Q ⧸ A)) :=
    ((QuotientGroup.mk' A).comp (Subgroup.center Q).subtype).codRestrict
      (Subgroup.center (Q ⧸ A)) (fun z => hmap ▸ ⟨z.1, z.2, rfl⟩) with hζ
  have hζs : Function.Surjective ζ := by
    intro y
    have hy : (y : Q ⧸ A) ∈ (Subgroup.center Q).map (QuotientGroup.mk' A) := hmap ▸ y.2
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hkerp : IsPGroup 2 ↥ζ.ker := by
    refine IsPGroup.of_injective hA2
      (((Subgroup.center Q).subtype.comp ζ.ker.subtype).codRestrict A fun k => ?_) ?_
    · have hk : ζ k.1 = 1 := k.2
      have := congrArg Subtype.val hk
      exact (QuotientGroup.eq_one_iff _).mp this
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hkerp
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ζ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ζ hζs).toEquiv, hn] at hcard
  rw [hcard] at h3
  exact (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right h3

theorem not_two_dvd_index_map_of_surjective' {G P : Type*} [Group G] [Group P] {φ : G →* P}
    (hφ : Function.Surjective φ) {T : Subgroup G} (hT : ¬ 2 ∣ T.index) :
    ¬ 2 ∣ (T.map φ).index := by
  rw [← Subgroup.index_comap_of_surjective _ hφ, Subgroup.comap_map_eq]
  exact fun h => hT (h.trans (Subgroup.index_dvd_of_le le_sup_left))

@[expose] noncomputable def topCenterEquiv (G : Type) [Group G] :
    ↥(⊤ : Subgroup G) ⧸ Subgroup.center ↥(⊤ : Subgroup G) ≃* G ⧸ Subgroup.center G :=
  QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)

theorem card_center_top (G : Type) [Group G] :
    Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup G)) = Nat.card ↥(Subgroup.center G) :=
  Nat.card_congr (Subgroup.centerCongr Subgroup.topEquiv).toEquiv

section OddCentre


theorem solvNormalCentral_parabolic_of_odd_centre (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {L J : Subgroup G} (hL : IsComponentOf L ⊤)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) (h3 : 3 ∣ Nat.card ↥(Subgroup.center ↥L))
    (hLU : IsLinUnitThreeEven (↥L ⧸ Subgroup.center ↥L)) (hJ : IsParabolicTwo L J) :
    SolvNormalCentral (↥J ⧸ CFSG.pCore 2 ↥J) := by
  by_cases hJL : J = L
  · subst hJL
    have hq : CFSG.Open.IsQuasisimple ↥J := hL.2.2
    refine solvNormalCentral_quotPCore (MonoidHom.id ↥J) Function.surjective_id ?_
      (MonoidHom.id ↥J) Function.surjective_id ?_ (solvNormalCentral_of_isQuasisimple hq)
    · rw [MonoidHom.ker_id]
      infer_instance
    · rw [MonoidHom.ker_id]
      exact IsPGroup.of_bot
  · obtain ⟨d, q, hq2, hd, ⟨e⟩⟩ := hLU
    rcases hd with hd | hd
    · obtain ⟨f, hf, ⟨e'⟩⟩ := exists_mulEquiv_projectiveSL_three hq2 hd e
      exact solvNormalCentral_parabolic_linear hGA hL hodd h3 hf e' hJ
    · exact solvNormalCentral_parabolic_unitary hL hodd d q hq2 hd e hJ hJL

theorem solvNormalCentral_parabolic_of_quasisimple (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {Y P : Subgroup X} (hY : CFSG.Open.IsQuasisimple ↥Y)
    (hLU : IsLinUnitThreeEven (↥Y ⧸ Subgroup.center ↥Y))
    (h3 : 3 ∣ Nat.card ↥(Subgroup.center ↥Y)) (hPar : IsParabolicTwo Y P) :
    SolvNormalCentral (↥P ⧸ CFSG.pCore 2 ↥P) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYc : CFSG.IsQuasisimple ↥Y := isQuasisimple_of_open hY
  set Z2 : Subgroup ↥Y := twoPart (Subgroup.center ↥Y) le_rfl with hZ2
  haveI hZ2n : Z2.Normal := Subgroup.normal_of_le_center twoPart_le_center
  obtain ⟨hqq, hcomap, hmap⟩ := quasisimple_central_quotient hYc (A := Z2) twoPart_le_center
  have hq₁ : CFSG.Open.IsQuasisimple (↥Y ⧸ Z2) := isQuasisimple_to_open hqq
  have hodd₁ : Odd (Nat.card ↥(Subgroup.center (↥Y ⧸ Z2))) :=
    odd_card_center_quotient_twoPart hZ2 hYc
  have e₁ : ↥Y ⧸ Subgroup.center ↥Y ≃* (↥Y ⧸ Z2) ⧸ Subgroup.center (↥Y ⧸ Z2) :=
    centralQuotientEquiv hYc twoPart_le_center
  have hLU₁ : IsLinUnitThreeEven ((↥Y ⧸ Z2) ⧸ Subgroup.center (↥Y ⧸ Z2)) := by
    obtain ⟨d, q, hq, hd, ⟨e⟩⟩ := hLU
    exact ⟨d, q, hq, hd, ⟨e₁.symm.trans e⟩⟩
  have h3₁ : 3 ∣ Nat.card ↥(Subgroup.center (↥Y ⧸ Z2)) :=
    three_dvd_card_center_quotient isPGroup_twoPart hmap h3
  obtain ⟨hPY, T, ⟨hTY, hT2, hTi⟩, hTP⟩ := hPar
  set ĝ : ↥P →* (↥Y ⧸ Z2) := (QuotientGroup.mk' Z2).comp (Subgroup.inclusion hPY) with hĝ
  set J₁ : Subgroup (↥Y ⧸ Z2) := ĝ.range with hJ₁
  set T₀ : Subgroup ↥Y := T.subgroupOf Y with hT₀
  have hT₀2 : IsPGroup 2 ↥T₀ := hT2.comap_of_injective Y.subtype Y.subtype_injective
  have hZ2T : Z2 ≤ T₀ := by
    have h := (isPGroup_twoPart (N := Subgroup.center ↥Y) (hN := le_rfl)).le_sylow_of_normal
      (hT₀2.toSylow hTi)
    rwa [IsPGroup.toSylow_coe] at h
  have hmemT : ∀ u : ↥Y, QuotientGroup.mk' Z2 u ∈ T₀.map (QuotientGroup.mk' Z2) ↔ u ∈ T₀ := by
    intro u
    constructor
    · rintro ⟨t, ht, htu⟩
      have hz : t⁻¹ * u ∈ Z2 := (QuotientGroup.eq).mp htu
      have := T₀.mul_mem ht (hZ2T hz)
      simpa using this
    · exact fun hu => ⟨u, hu, rfl⟩
  have hJ₁par : IsParabolicTwo (⊤ : Subgroup (↥Y ⧸ Z2)) J₁ := by
    refine ⟨le_top, T₀.map (QuotientGroup.mk' Z2), ⟨le_top, hT₀2.map _, ?_⟩, ?_⟩
    · have h := not_two_dvd_index_map_of_surjective' (QuotientGroup.mk'_surjective Z2) hTi
      change ¬ 2 ∣ (T₀.map (QuotientGroup.mk' Z2)).relIndex ⊤
      rwa [Subgroup.relIndex_top_right]
    · intro y₁ hy₁
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z2 y₁
      have hyN : y ∈ Subgroup.normalizer (T₀ : Set ↥Y) := by
        refine Subgroup.mem_normalizer_iff.mpr fun t => ?_
        have h := Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hy₁).2
          (QuotientGroup.mk' Z2 t)
        rw [← hmemT, ← hmemT]
        simpa using h
      have hNT : Subgroup.normalizer (T₀ : Set ↥Y) =
          (Subgroup.normalizer (T : Set X)).comap Y.subtype :=
        (Subgroup.comap_normalizer_eq_of_le_range (by rwa [Subgroup.range_subtype])).symm
      rw [hNT] at hyN
      have hyP : (y : X) ∈ P := hTP ⟨y.2, hyN⟩
      exact ⟨⟨y, hyP⟩, rfl⟩
  have hL₁ : IsComponentOf (⊤ : Subgroup (↥Y ⧸ Z2)) ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.isComponentOf_top_of_isQuasisimple hq₁
  have hodd₁' : Odd (Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup (↥Y ⧸ Z2)))) := by
    rw [card_center_top]
    exact hodd₁
  have h3₁' : 3 ∣ Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup (↥Y ⧸ Z2))) := by
    rw [card_center_top]
    exact h3₁
  have hLU₁' : IsLinUnitThreeEven (↥(⊤ : Subgroup (↥Y ⧸ Z2)) ⧸
      Subgroup.center ↥(⊤ : Subgroup (↥Y ⧸ Z2))) := by
    obtain ⟨d, q, hq, hd, ⟨e⟩⟩ := hLU₁
    exact ⟨d, q, hq, hd, ⟨(topCenterEquiv _).trans e⟩⟩
  have hsol := solvNormalCentral_parabolic_of_odd_centre hGA hL₁ hodd₁' h3₁' hLU₁' hJ₁par
  set f : ↥P →* ↥J₁ := ĝ.rangeRestrict with hf
  have hfs : Function.Surjective f := ĝ.rangeRestrict_surjective
  have hfk : IsPGroup 2 ↥f.ker := by
    refine IsPGroup.of_injective (isPGroup_twoPart (N := Subgroup.center ↥Y) (hN := le_rfl))
      (((Subgroup.inclusion hPY).comp f.ker.subtype).codRestrict Z2 fun k => ?_) ?_
    · have hk : f k.1 = 1 := k.2
      have hk' : ĝ k.1 = 1 := congrArg Subtype.val hk
      exact (QuotientGroup.eq_one_iff _).mp hk'
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subgroup.inclusion_injective hPY h1)
  obtain ⟨e₂⟩ := nonempty_quotPCore_mulEquiv f hfs hfk
  exact solvNormalCentral_of_mulEquiv e₂.symm hsol

end OddCentre

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open LinUnitParab

theorem kFactLinUnitThreeParabolic_holds
    : KFactLinUnitThreeParabolic := by
  intro X _ _ Y P R hY hLU h3 hPar hRP hRs
  exact isEmpty_quotPCore_perm_three
    (solvNormalCentral_parabolic_of_quasisimple
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hY hLU h3 hPar) hRP hRs

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
