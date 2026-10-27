module

public import CFSG.LieType.OutStructureSevenOneSeven
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section7.SevenOneFourSplitOfI713
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K4143NoExtraLie
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStated
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieHolds

public section

namespace CFSG.LieType.OutStructure

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem isPSLType_two_galoisField_of_lieModel {Y : Type} [Group Y]
    (h : CFSG.Blueprint.LieModel Y .PSL 2 3 3) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPSLType 2 (GaloisField 3 3) Y := by
  have hm : CFSG.Open.StatedClassicalModel Y .PSL 2 3 3 :=
    h.statedClassicalModel (by decide)
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := hm
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 3 3) := Fintype.ofFinite _
  have hcard' : Nat.card K = Nat.card (GaloisField 3 3) := by
    rw [hcard, GaloisField.card 3 3 (by norm_num)]
  have hcard'' : Fintype.card K = Fintype.card (GaloisField 3 3) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact hcard'
  let θ := FiniteField.ringEquivOfCardEq hcard''
  exact ⟨e.trans (CFSG.ComponentClassification.AutL2Facts.statedEquiv θ)⟩

theorem pSingular_not_mem_inner_of_outer {Y : Type} [Group Y] [Finite Y]
    (I : Subgroup (MulAut Y)) [I.Normal] {φ : MulAut Y}
    (hφI : φ ∉ I) (hφ3I : φ ^ 3 ∈ I) :
    Group.pSingular 3 φ ∉ I := by
  intro hyI
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set y : MulAut Y := Group.pSingular 3 φ with hy
  set r : MulAut Y := Group.pRegular 3 φ with hr
  have hdecomp : r * y = φ := Group.pDecomp' 3 (isOfFinOrder_of_finite φ)
  have hcomm : Commute y r := Group.pDecomp_commute 3 φ
  have hφeq : φ = y * r := hdecomp.symm.trans hcomm.eq.symm
  have hrreg : CFSG.IsPRegular 3 r := Group.isPRegular_pRegular 3 (isOfFinOrder_of_finite φ)
  have hcop : Nat.Coprime (orderOf r) 3 := hrreg
  have hπ3 : orderOf (QuotientGroup.mk' I φ) = 3 := by
    apply orderOf_eq_prime
    · exact (QuotientGroup.eq_one_iff (φ ^ 3)).mpr hφ3I
    · intro h
      exact hφI ((QuotientGroup.eq_one_iff φ).mp h)
  have hy1 : QuotientGroup.mk' I y = 1 := (QuotientGroup.eq_one_iff y).mpr hyI
  have hπeq : QuotientGroup.mk' I φ = QuotientGroup.mk' I r := by
    rw [hφeq, map_mul, hy1, one_mul]
  have hdvd : orderOf (QuotientGroup.mk' I r) ∣ orderOf r := orderOf_map_dvd _ _
  rw [← hπeq, hπ3] at hdvd
  have h1 : 3 ∣ orderOf r := hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop.symm h1

end CFSG.LieType.OutStructure

namespace CFSG.LieType.OutStructure

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_three_dvd_card_centralizer_of_pRank_three {X : Type} [Group X] [Finite X]
    {L : Subgroup X} [L.Normal] (h3L : CFSG.Open.pRank 3 L = 3)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) :
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (L : Set X)) := by
  intro hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer (L : Set X))) 3 hdvd
  let c : X := (z : X)
  have hcC : c ∈ Subgroup.centralizer (L : Set X) := z.2
  have hc3 : c ^ 3 = 1 := by
    have hco : orderOf z = 3 := hz
    have hc_eq : orderOf (z : X) = 3 := (Subgroup.orderOf_coe z).trans hco
    rw [← hc_eq]
    exact pow_orderOf_eq_one (z : X)
  have hcL : c ∉ L := by
    intro hcL
    have hcZ : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcC (l : X) l.2
    have hc_eq : orderOf c = 3 := (Subgroup.orderOf_coe z).trans hz
    have h1 : orderOf (⟨c, hcL⟩ : ↥L) = orderOf c := by
      simpa using (Subgroup.orderOf_coe (⟨c, hcL⟩ : ↥L))
    have h2 : orderOf (⟨(⟨c, hcL⟩ : ↥L), hcZ⟩ : ↥(Subgroup.center ↥L)) =
        orderOf (⟨c, hcL⟩ : ↥L) := by
      simpa using (Subgroup.orderOf_coe
        (⟨(⟨c, hcL⟩ : ↥L), hcZ⟩ : ↥(Subgroup.center ↥L)))
    have hord : orderOf (⟨(⟨c, hcL⟩ : ↥L), hcZ⟩ : ↥(Subgroup.center ↥L)) = 3 :=
      h2.trans (h1.trans hc_eq)
    have h3dvd : 3 ∣ Nat.card (Subgroup.center ↥L) := by
      have h := orderOf_dvd_natCard
        (⟨(⟨c, hcL⟩ : ↥L), hcZ⟩ : ↥(Subgroup.center ↥L))
      rwa [hord] at h
    exact h3Z h3dvd
  obtain ⟨E, hEL, hE, h27⟩ :=
    CFSG.AGLEmbedding.KFactProofs.G28.exists_elemAbelian_27 h3L.ge
  have hcE : c ∉ E := fun hcE => hcL (hEL hcE)
  have hcomm : ∀ e ∈ E, e * c = c * e := by
    intro e he
    exact Subgroup.mem_centralizer_iff.mp hcC e (hEL he)
  have h4 := CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2.four_le_pRank_of_commute
    hE h27 hc3 hcE hcomm
  omega

end CFSG.LieType.OutStructure

namespace CFSG.LieType.OutStructure

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem lieModel_psl2_27_of_outer_three {X : Type} [Group X] [Finite X]
    (hK : CFSG.Open.IsKGroup X) {L : Subgroup X} [L.Normal] (hL : CFSG.IsComponent L)
    (h3L : CFSG.Open.pRank 3 L = 3) (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center ↥L))
    (hK2 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2)
    {x : X} (hxU : x ∉ L ⊔ Subgroup.centralizer (L : Set X))
    (hx3U : x ^ 3 ∈ L ⊔ Subgroup.centralizer (L : Set X)) :
    CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 3 := by
  classical
  by_contra hnot227
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect ↥L := hL.1.1
  let Y := ↥L ⧸ Subgroup.center ↥L
  let ρ : X →* MulAut Y := CFSG.LocalAnalysis.RankThreeUC.AGL81C.centerQuotientAction L
  let φ : MulAut Y := ρ x
  let I : Subgroup (MulAut Y) := CFSG.ComponentClassification.OuterAutomorphisms.inner Y
  let B : Subgroup (MulAut Y) := ρ.range
  have hqc := CFSG.LocalCores.quasisimple_central_quotient hL.1
    (Subgroup.center ↥L) le_rfl
  have hYqF : CFSG.IsQuasisimple Y := hqc.1
  have hZY : Subgroup.center Y = ⊥ := by
    rw [hqc.2.2, Subgroup.eq_bot_iff_forall]
    rintro y ⟨z, hz, rfl⟩
    exact (QuotientGroup.eq_one_iff z).mpr hz
  haveI : IsSimpleGroup Y := hL.1.2.1
  have hYcat : CFSG.Open.IsCatalogGroup Y :=
    CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hK L hL.1.2.2
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
  have h3Ytop : CFSG.Open.pRank 3 (⊤ : Subgroup Y) = 3 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center ↥L) h3Z]
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L]
    exact h3L
  have hI_eq : I = L.map ρ := CFSG.LocalAnalysis.RankThreeUC.AGL81C.inner_eq_map_centerQuotientAction L
  have hI_le_B : I ≤ B := by
    rw [hI_eq]
    exact Subgroup.map_le_range ρ L
  have hφ_notin : φ ∉ I := by
    intro hφ
    rw [hI_eq] at hφ
    obtain ⟨l, hl, hlφ⟩ := Subgroup.mem_map.mp hφ
    have hker : l⁻¹ * x ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      calc ρ (l⁻¹ * x) = (ρ l)⁻¹ * ρ x := by rw [map_mul, map_inv]
        _ = φ⁻¹ * φ := by rw [hlφ]
        _ = 1 := inv_mul_cancel φ
    have hC : l⁻¹ * x ∈ Subgroup.centralizer (L : Set X) := by
      rwa [CFSG.LocalAnalysis.RankThreeUC.AGL81C.centerQuotientAction_ker L] at hker
    apply hxU
    have hx_eq : x = l * (l⁻¹ * x) := by group
    rw [hx_eq]
    exact Subgroup.mul_mem_sup hl hC
  have hφ3in : φ ^ 3 ∈ I := by
    obtain ⟨l, hl, c, hc, hxc⟩ := Subgroup.mem_sup_of_normal_left.1 hx3U
    rw [hI_eq]
    refine Subgroup.mem_map.mpr ⟨l, hl, ?_⟩
    have hc1 : ρ c = 1 := by
      rw [← MonoidHom.mem_ker, CFSG.LocalAnalysis.RankThreeUC.AGL81C.centerQuotientAction_ker L]
      exact hc
    have hφpow : φ ^ 3 = ρ (x ^ 3) := by
      change (ρ x) ^ 3 = ρ (x ^ 3)
      rw [map_pow]
    rw [hφpow, ← hxc, map_mul, hc1, mul_one]
  have hC3 : ¬ 3 ∣ Nat.card (Subgroup.centralizer (L : Set X)) :=
    not_three_dvd_card_centralizer_of_pRank_three h3L h3X h3Z
  have hker3 : ¬ 3 ∣ Nat.card ρ.ker := by
    rwa [CFSG.LocalAnalysis.RankThreeUC.AGL81C.centerQuotientAction_ker L]
  have hquot : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ ρ.ker)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_quotient_eq ρ.ker hker3
  have hB3 : CFSG.Open.pRank 3 (⊤ : Subgroup B) = 3 := by
    have e : X ⧸ ρ.ker ≃* B := QuotientGroup.quotientKerEquivRange ρ
    have h := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
    rw [hquot, h3X] at h
    exact h.symm
  have hZYbot : Subgroup.center Y = ⊥ := hZY
  let eY : Y ≃* I := CFSG.Fischer.innerAutEquiv hZYbot
  have hI3 : CFSG.Open.pRank 3 (⊤ : Subgroup I) = 3 := by
    have h := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eY
    rw [h3Ytop] at h
    exact h.symm
  have hB3ge : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup B) := by
    have := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hI_le_B
    omega
  have hB3eq : CFSG.Open.pRank 3 (⊤ : Subgroup B) = 3 := le_antisymm hB3.le hB3ge
  let eB : Y ≃* ↥(I.subgroupOf B) :=
    eY.trans (Subgroup.subgroupOfEquivOfLe hI_le_B).symm
  let Lb : Subgroup B := I.subgroupOf B
  have eLb : ↥Lb ≃* I := Subgroup.subgroupOfEquivOfLe hI_le_B
  have hZI : Subgroup.center I = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eY.symm hZY
  have hcenterLb : Subgroup.center ↥Lb = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eLb hZI
  have hLb3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Lb) = 3 := by
    have h := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eB
    rw [h3Ytop] at h
    exact h.symm
  haveI : Lb.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hI_le_B]
    have htop : Subgroup.normalizer (I : Set (MulAut Y)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [htop]
    exact le_top
  have hK2amb : ∀ R : Subgroup (MulAut ↥Lb), IsPGroup 3 R →
      CFSG.ABGLocalTools.IsSylowOf 3
        (R ⊓ (MulAut.conj : ↥Lb →* MulAut ↥Lb).range)
        ((MulAut.conj : ↥Lb →* MulAut ↥Lb).range) →
      ¬ R ≤ (MulAut.conj : ↥Lb →* MulAut ↥Lb).range → 4 ≤ CFSG.Open.pRank 3 R := by
    intro R hR hSyl hnle
    have hLbqF : CFSG.IsQuasisimple ↥Lb :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hYqF
    have hLb3p : CFSG.pRank 3 (⊤ : Subgroup ↥Lb) = 3 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank 3 (⊤ : Subgroup ↥Lb)]
      exact hLb3
    have h := hK2 ↥Lb hLbqF ?_ ?_ hLb3p ?_ ?_ R hR hSyl hnle
    · rw [CFSG.SectionRank.pRank_coe_eq_openPRank 3 R] at h
      exact h
    · have hcatLb : CFSG.Open.IsCatalogGroup ↥Lb :=
        CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv eB.symm hYcat
      let e : (↥Lb ⧸ Subgroup.center ↥Lb) ≃* ↥Lb :=
        (QuotientGroup.quotientMulEquivOfEq (G := ↥Lb) hcenterLb).trans
          (QuotientGroup.quotientBot : (↥Lb ⧸ (⊥ : Subgroup ↥Lb)) ≃* ↥Lb)
      exact CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv e hcatLb
    · rw [hcenterLb, Subgroup.card_bot]
      exact odd_one
    · intro h
      obtain ⟨-, hcard, -⟩ := h
      rw [hcenterLb, Subgroup.card_bot] at hcard
      norm_num at hcard
    · intro hLie
      have hLieLb : CFSG.Blueprint.LieModel ↥Lb .PSL 2 3 3 :=
        CFSG.Blueprint.LieModel.of_quotient_center hcenterLb hLie
      exact hnot227 (hLieLb.of_mulEquiv eB.symm)
  have hLb3' : CFSG.Open.pRank 3 Lb = 3 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) Lb]
    exact hLb3
  have hple := CFSG.LocalAnalysis.AGL81TheoremCD.Section14.pElementSubgroup_le_of_k2
    (L := Lb) hcenterLb hLb3' hB3eq hK2amb
  let y : MulAut Y := Group.pSingular 3 φ
  have hy_order : ∃ k : ℕ, orderOf y = 3 ^ k := Group.isPSingular_pSingular (p := 3) φ
  have hφB : φ ∈ B := ⟨x, rfl⟩
  have hyB : y ∈ B := Subgroup.zpow_mem B hφB _
  let yB : B := ⟨y, hyB⟩
  have hy_orderB : ∃ k : ℕ, orderOf yB = 3 ^ k := by
    obtain ⟨k, hk⟩ := hy_order
    exact ⟨k, (Subgroup.orderOf_coe yB).symm.trans hk⟩
  have hyB_mem : yB ∈ CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup
      3 (⊤ : Subgroup B) :=
    Subgroup.subset_closure ⟨Subgroup.mem_top yB, hy_orderB⟩
  have hyLb : yB ∈ Lb := hple hyB_mem
  have hyI : y ∈ I := Subgroup.mem_subgroupOf.mp hyLb
  exact (pSingular_not_mem_inner_of_outer (I := I) hφ_notin hφ3in) hyI

end CFSG.LieType.OutStructure

namespace CFSG.LieType.OutStructure

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem sevenOneSeven_of_K2_cover_ON
    (hK2 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2)
    (hcover : ∀ (M : Type) [Group M] [Finite M], CFSG.Open.IsQuasisimple M →
      CFSG.Open.IsCatalogGroup (M ⧸ Subgroup.center M) →
      3 ∣ Nat.card (Subgroup.center M) →
      CFSG.Open.pRank 3 (⊤ : Subgroup M) = 3 →
      CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
        (fun Y _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Y .ONan) M)
    (hON : ∀ (S : Type) [Group S] [Finite S],
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor S .ONan →
      ¬ 3 ∣ Nat.card (Outer S)) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneSeven := by
  intro X _ _ hK L hL hLn h3L h3X
  haveI := hLn
  by_cases hdiv : 3 ∣ (L ⊔ Subgroup.centralizer (L : Set X)).index
  · right
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let U : Subgroup X := L ⊔ Subgroup.centralizer (L : Set X)
    have hUidx : U.index = Nat.card (X ⧸ U) := Subgroup.index_eq_card (H := U)
    have h3q : 3 ∣ Nat.card (X ⧸ U) := by rw [← hUidx]; exact hdiv
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X ⧸ U) 3 h3q
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective U g
    have hg1 : g ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hg
      norm_num at hg
    have hxU : x ∉ U := by
      intro hxU
      apply hg1
      rw [← hx]
      exact (QuotientGroup.eq_one_iff x).mpr hxU
    have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hx3U : x ^ 3 ∈ U := by
      have h1 : (QuotientGroup.mk' U) (x ^ 3) = 1 := by
        rw [map_pow, hx, hg3]
      exact (QuotientGroup.eq_one_iff (x ^ 3)).mp h1
    by_cases h3Z : 3 ∣ Nat.card (Subgroup.center ↥L)
    ·
      have hqO : CFSG.Open.IsQuasisimple ↥L :=
        ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
      haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
      have hcat : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
        CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hK L hL.1.2.2
          (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
      have hrankL : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 3 := by
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L]
        exact h3L
      obtain ⟨-, -, hSpor⟩ := hcover ↥L hqO hcat h3Z hrankL
      exact ((hON _ hSpor) (three_dvd_outer_centerQuotient_of_three_dvd_index hL hdiv)).elim
    ·
      have hqO : CFSG.Open.IsQuasisimple ↥L :=
        ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
      exact isPSLType_two_galoisField_of_lieModel
        (lieModel_psl2_27_of_outer_three hK hL h3L h3X h3Z hK2 hxU hx3U)
  · exact Or.inl hdiv

end CFSG.LieType.OutStructure

namespace CFSG.LieType.OutStructure

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

section Certificates

theorem sevenOneSeven_holds
    :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneSeven := by
  refine sevenOneSeven_of_K2_cover_ON ?_ ?_ ?_
  · exact k2_of_k1 k1_holds k2Lie_holds
  · intro M _ _ hq hcat h3 hrank
    exact k34odd_threeCover_of_three_dvd
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
      M hq hcat h3 hrank
  · intro S _ _ hSpor h3
    obtain ⟨e⟩ := hSpor
    have hout : Nat.card (Outer S) = Nat.card (Outer Blueprint.NativeSporadic.ON) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
    rw [hout] at h3
    exact (by norm_num : ¬ 3 ∣ 4)
      (h3.trans CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1)

end Certificates

end CFSG.LieType.OutStructure
