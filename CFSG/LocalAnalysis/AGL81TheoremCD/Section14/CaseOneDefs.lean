module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeStar
import CFSG.GroupTheory.WielandtProductAux
import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.CosetFixedPoint
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.RankThree.PartOne.S9.Sylow.GlobalLemmas

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (gnV gnC gnImg)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_coset_translate_centralizer {J B D : Subgroup G}
    (hB : IsPGroup 3 B) (hDJ : D ≤ J) (hJN : J ≤ Subgroup.normalizer (D : Set G))
    (hBN : B ≤ Subgroup.normalizer (D : Set G))
    (hDnot : ¬ 3 ∣ Nat.card D) (hcomm : ⁅B, J⁆ ≤ D) {x : ↥J} :
    ∃ d ∈ D, (x : G) * d ∈ J ∧
      (x : G) * d ∈ Subgroup.centralizer (B : Set G) := by
  have hl : ∀ b ∈ B, (x : G)⁻¹ * (b * (x : G) * b⁻¹) ∈ D := by
    intro b hb
    have hmem : ⁅b, (x : G)⁆ ∈ D := hcomm (Subgroup.commutator_mem_commutator hb x.2)
    have hconj : (x : G)⁻¹ * ⁅b, (x : G)⁆ * (x : G) ∈ D := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp (hJN (J.inv_mem x.2)) ⁅b, (x : G)⁆).mp hmem
    have heq : (x : G)⁻¹ * (b * (x : G) * b⁻¹) =
        (x : G)⁻¹ * ⁅b, (x : G)⁆ * (x : G) := by
      rw [commutatorElement_def]
      group
    rwa [heq]
  obtain ⟨d, hdD, hfix⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.CosetFixedPoint.exists_fixed_point_in_coset
      B D hB hDnot hBN (x : G) hl
  refine ⟨d, hdD, J.mul_mem x.2 (hDJ hdD), Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro b hb
  exact mul_inv_eq_iff_eq_mul.mp (hfix b hb)

structure CaseOneCtx (G : Type) [Group G] [Finite G] (M H E Q J R T : Subgroup G) : Prop where
  choice : S14Choice G M H E Q J
  typeA : TypeA M H
  pre : PreambleTypes M
  nine : NineNineOneAt M
  player : PLayerNotLeAt M
  R_max : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.IsMaxInvariantTwoIn Q R H
  core_le_R : CFSG.Open.pCoreOf 2 H ≤ R
  T_sylow : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)
  R_le_T : R ≤ T

structure FourteenSevenData (M H Q R T : Subgroup G) : Prop where
  normalizer_T_not_le : ¬ Subgroup.normalizer (T : Set G) ≤ M
  sylow_D : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M)
    (CFSG.inSubgroup (CFSG.pPrimeCore 3) M)
  normalizer_R_le : Subgroup.normalizer (R : Set G) ≤ H
  maxInv : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.IsMaxInvariantTwoIn Q R ⊤

@[expose] noncomputable def threeStarImg (M X : Subgroup G) : Subgroup (threeStar M) :=
  (X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))

structure FourteenEightCore (M L : Subgroup G) : Prop where
  L_le : L ≤ M
  L_normal : (L.subgroupOf M).Normal
  residual : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥L = ⊤
  core_eq : (CFSG.pPrimeCore 3 ↥L).map L.subtype = L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  simple : IsSimpleGroup (threeStar L)
  nonabelian : ∃ a b : threeStar L, a * b ≠ b * a
  dichotomy : ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
    N ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M ∨ N = L
  centralizing : ∀ U : Subgroup G, U ≤ M → U ≤ Subgroup.normalizer (L : Set G) →
    ⁅U, L⁆ ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M → U ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  centralizer_img : Subgroup.centralizer (threeStarImg M L : Set (threeStar M)) = ⊥
  img_equiv : Nonempty (↥(threeStarImg M L) ≃* threeStar L)

structure FourteenEightData (M L : Subgroup G) : Prop extends FourteenEightCore M L where
  rank_L : ∀ p ∈ sigmaSet G M, 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (threeStar L))

structure FourteenNineData (M L T : Subgroup G) : Prop where
  charTwo : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥(L ⊔ T))
  core_le : CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥(L ⊔ T)) ≤ T.subgroupOf (L ⊔ T)
  pCore_two : CFSG.pCore 2 (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))) = ⊥
  gnC_le : (gnC (T.subgroupOf (L ⊔ T))).map (L ⊔ T).subtype ≤
    CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  thompson : ⁅CFSG.Quasithin.thompsonJ T, L⁆ = L
  not_le_gnC : ¬ L.subgroupOf (L ⊔ T) ≤ gnC (T.subgroupOf (L ⊔ T))

@[expose] def FourteenTwoCaseOneAt (M : Subgroup G) : Prop :=
  ∀ H E Q J : Subgroup G, S14Choice G M H E Q J → TypeA M H →
    (Nat.card Q = 3 ^ 5 ∧ (∀ x ∈ Q, x ^ 3 = 1) ∧
      ⁅Q, Q⁆ = (Subgroup.center ↥Q).map Q.subtype ∧
      Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3) ∧
    ∃ Q₀ : Subgroup G, Q₀ ≤ Q ∧ Nat.card Q₀ = 27 ∧ ⁅Q₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J ∧
      (Subgroup.center ↥Q).map Q.subtype ≤ Q₀

@[expose] def FourteenThreeCaseOneAt (M : Subgroup G) : Prop :=
  ∀ H E Q J : Subgroup G, S14Choice G M H E Q J → TypeA M H →
    ∀ N : Subgroup G, CFSG.Open.rankThreeIsMaxTwoLocal N → J ≤ N → Q ≤ N → N = H

@[expose] def FourteenFiveCaseOneAt (M : Subgroup G) : Prop :=
  ∀ H E Q J : Subgroup G, S14Choice G M H E Q J → TypeA M H →
    ∀ p ∈ sigmaSet G M, ∀ A₀ : Subgroup G, A₀ ≤ Q → Nat.card A₀ = 3 →
      2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A₀ : Set G)) →
      ⁅A₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J →
      (⁅A₀, E⁆ = ⊥ ∨ ∃ P : Subgroup G,
          P ≤ M ⊓ Subgroup.centralizer (A₀ : Set G) ∧ IsPGroup p P ∧
          (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.normalizer (P : Set G) ∧
          ⁅(Subgroup.center ↥Q).map Q.subtype, P⁆ ≠ ⊥) →
      CFSG.HallHigman.IsPSolvable 3 ↥(kSub 3 M H ⊓ Subgroup.centralizer (A₀ : Set G))

@[expose] def FourteenTwoCaseOneGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G), FourteenTwoCaseOneAt M

@[expose] def FourteenThreeCaseOneGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G), FourteenThreeCaseOneAt M

@[expose] def FourteenFiveCaseOneGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G), FourteenFiveCaseOneAt M

@[expose] def oTwoZStar (J : Subgroup G) : Subgroup G :=
  ((Subgroup.center (threeStar J)).comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))).map J.subtype

@[expose] noncomputable def jStarAct (J : Subgroup G) :
    ↥(Subgroup.normalizer (J : Set G)) →* MulAut (threeStar J) :=
  (CFSG.SectionRank.Ccomm.autQuotient (CFSG.pPrimeCore 3 ↥J)).comp
    (Subgroup.normalizerMonoidHom J)

@[expose] noncomputable def jBarAct (J : Subgroup G) :
    ↥(Subgroup.normalizer (J : Set G)) →* MulAut (threeStar J ⧸ Subgroup.center (threeStar J)) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (threeStar J)).comp
    (jStarAct J)

theorem jStarAct_apply_mk (J : Subgroup G) (n : ↥(Subgroup.normalizer (J : Set G))) (x : ↥J) :
    jStarAct J n (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨(n : G) * (x : G) * (n : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp n.2 (x : G)).mp x.2⟩ := by
  simp only [jStarAct, MonoidHom.comp_apply, CFSG.SectionRank.Ccomm.autQuotient_mk,
    Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

theorem jBarAct_apply_mk (J : Subgroup G) (n : ↥(Subgroup.normalizer (J : Set G))) (x : ↥J) :
    jBarAct J n (QuotientGroup.mk' (Subgroup.center (threeStar J))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x)) =
      QuotientGroup.mk' (Subgroup.center (threeStar J))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨(n : G) * (x : G) * (n : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp n.2 (x : G)).mp x.2⟩) := by
  rw [jBarAct, MonoidHom.comp_apply]
  change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (jStarAct J n)
      ((QuotientGroup.mk' (Subgroup.center (threeStar J)))
        ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)) x)) = _
  rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk,
    jStarAct_apply_mk]

theorem inf_le_normalizer_kSub (p : ℕ) (M H : Subgroup G) :
    H ⊓ M ≤ Subgroup.normalizer (kSub p M H : Set G) := by
  rintro y ⟨hyH, hyM⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_kSub hyH hyM hx
  · intro hx
    have h := conj_mem_kSub (p := p) (M := M) (H := H) (H.inv_mem hyH) (M.inv_mem hyM) hx
    have h' : y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ = x := by group
    rwa [h'] at h

namespace HypCGen

variable {M E H : Subgroup G}

theorem invariant_coprime_le_M (h : HypCGen G M 3 E H) {Y : Subgroup G}
    (hY : ¬ 3 ∣ Nat.card Y) (hEY : E ≤ Subgroup.normalizer (Y : Set G)) : Y ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ^ (1 + 1) ≤ Nat.card E := by
    rw [h.card]
  exact (CFSG.LocalAnalysis.AGL81TheoremC.le_glbCore_of_coprime h.elem hcard hY hEY).trans
    h.gamma

end HypCGen

theorem exists_sylow_gamma_one_le_of_cstar (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ sigmaSet G M) (hp3 : p ≠ 3)
    (hns : ¬ Group.IsSolvable ↥M) :
    ∃ P : Sylow p G, (P : Subgroup G) ≤ M ∧ rankThreeGamma 1 p (P : Subgroup G) ≤ M := by
  obtain ⟨P, hPM, -, hΓ | hclause | ⟨hp3', -⟩⟩ := hC.almost M hM p hp
  · exact ⟨P, hPM, hΓ⟩
  · exact absurd hclause.2.1 hns
  · exact absurd hp3' hp3

theorem mem_centralizer_sup_core_of_commute_mod {M B : Subgroup G} {x : G} (hxM : x ∈ M)
    (hBM : B ≤ M) (hB : IsPGroup 3 B)
    (hx : ∀ b ∈ B, x⁻¹ * (b * x * b⁻¹) ∈ CFSG.inSubgroup (CFSG.pPrimeCore 3) M) :
    x ∈ (M ⊓ Subgroup.centralizer (B : Set G)) ⊔ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  have hD : ¬ 3 ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.RankThree.PartOne.Sec9B.coprime_card_inSubgroup_pPrimeCore (r := 3) M)
  have hAD : B ≤ Subgroup.normalizer (D : Set G) :=
    hBM.trans (Subgroup.le_normalizer.trans
      (CFSG.RankThree.PartOne.Sec9B.normalizer_le_normalizer_inSubgroup_pPrimeCore 3 M))
  obtain ⟨d, hdD, hfix⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.CosetFixedPoint.exists_fixed_point_in_coset
      B D hB hD hAD x hx
  have hdM : d ∈ M := CFSG.RankThree.PartOne.Sec9B.inSubgroup_pPrimeCore_le 3 M hdD
  have hxdM : x * d ∈ M := M.mul_mem hxM hdM
  have hxdC : x * d ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h := hfix b hb
    have h' : b * (x * d) = (x * d) * b := by
      calc b * (x * d) = b * (x * d) * b⁻¹ * b := by group
        _ = (x * d) * b := by rw [h]
    exact h'
  have hmem : (x * d) * d⁻¹ ∈ (M ⊓ Subgroup.centralizer (B : Set G)) ⊔ D :=
    Subgroup.mul_mem_sup ⟨hxdM, hxdC⟩ (D.inv_mem hdD)
  have hxeq : (x * d) * d⁻¹ = x := by group
  rw [hxeq] at hmem
  simpa [D] using hmem

namespace IsKComp

variable {M H J : Subgroup G}

theorem le_oTwoZStar_of_normal {N : Subgroup G} (hJ : IsKComp M H J) (hNJ : N ≤ J)
    (hN : (N.subgroupOf J).Normal) (hne : N ≠ J) : N ≤ oTwoZStar J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  let C : Subgroup (threeStar J) := (N.subgroupOf J).map π
  have hCnorm : C.Normal := hN.map π (QuotientGroup.mk'_surjective _)
  have hC := CFSG.LocalCores.quasisimple_normal_subgroups hJ.isQuasisimple hCnorm
  rcases hC with hCtop | hCcenter
  · exfalso
    have hsup : N.subgroupOf J ⊔ CFSG.pPrimeCore 3 ↥J = ⊤ := by
      have h := Subgroup.comap_map_eq (f := π) (H := N.subgroupOf J)
      rw [show (N.subgroupOf J).map π = ⊤ by simpa [C] using hCtop,
        Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    letI : (N.subgroupOf J).Normal := hN
    have hdvd := CFSG.GroupTheory.WielandtProduct.index_dvd_card_of_sup_eq_top hsup
    have hcop : Nat.Coprime 3 (N.subgroupOf J).index :=
      CFSG.pPrimeCore_coprime_card.of_dvd_right hdvd
    have htop : (⊤ : Subgroup ↥J) ≤ N.subgroupOf J := by
      rw [← hJ.primeResidual_eq_top]
      exact
        CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index
          3 (N.subgroupOf J) hcop
    have hJleN : J ≤ N := Subgroup.subgroupOf_eq_top.mp (top_le_iff.mp htop)
    exact hne (le_antisymm hNJ hJleN)
  · intro x hx
    have hxJ : x ∈ J := hNJ hx
    have hxsub : (⟨x, hxJ⟩ : ↥J) ∈ N.subgroupOf J := hx
    have hxcenter : π ⟨x, hxJ⟩ ∈ Subgroup.center (threeStar J) :=
      hCcenter (Subgroup.mem_map_of_mem π hxsub)
    exact Subgroup.mem_map_of_mem J.subtype (Subgroup.mem_comap.mpr hxcenter)

end IsKComp

private theorem normalizes_and_commutator_of_isPComponentIn {H Y J : Subgroup G}
    (hY : IsPComponentIn 3 Y H) (hJ : IsPComponentIn 3 J H) (hne : Y ≠ J) :
    Y ≤ Subgroup.normalizer (J : Set G) ∧
      ⁅Y, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYne : Y.subgroupOf H ≠ J.subgroupOf H := by
    intro heq
    apply hne
    have hmap := congrArg (Subgroup.map H.subtype) heq
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hY.1,
      inf_eq_left.mpr hJ.1] using hmap
  obtain ⟨-, hYnormJ, hcomm⟩ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.mutual_normalization_core_commutation
      3 (Y.subgroupOf H) (J.subgroupOf H) hY.2 hJ.2 hYne
  have hconj : ∀ z ∈ Y, ∀ w ∈ J, z * w * z⁻¹ ∈ J := by
    intro z hz w hw
    have hzsub : (⟨z, hY.1 hz⟩ : ↥H) ∈ Y.subgroupOf H := hz
    have hwsub : (⟨w, hJ.1 hw⟩ : ↥H) ∈ J.subgroupOf H := hw
    have hmem := (Subgroup.mem_normalizer_iff.mp (hYnormJ hzsub)
      (⟨w, hJ.1 hw⟩ : ↥H)).mp hwsub
    exact Subgroup.mem_subgroupOf.mp hmem
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro w
    exact ⟨hconj z hz w, fun hw => by
      have h := hconj z⁻¹ (Y.inv_mem hz) (z * w * z⁻¹) hw
      simpa [mul_assoc] using h⟩
  · apply Subgroup.commutator_le.mpr
    intro z hz w hw
    have hzsub : (⟨z, hY.1 hz⟩ : ↥H) ∈ Y.subgroupOf H := hz
    have hwsub : (⟨w, hJ.1 hw⟩ : ↥H) ∈ J.subgroupOf H := hw
    have hmemH := hcomm (Subgroup.commutator_mem_commutator hzsub hwsub)
    have hmemJ := (Subgroup.mem_inf.mp hmemH).2
    obtain ⟨c, hc, hcEq⟩ := Subgroup.mem_map.mp hmemJ
    let e := Subgroup.subgroupOfEquivOfLe hJ.1
    refine Subgroup.mem_map.mpr ⟨e c, ?_, ?_⟩
    · rw [← CFSG.pPrimeCore_map_iso 3 e]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hc
    · have h1 : J.subtype (e c) = H.subtype ((J.subgroupOf H).subtype c) := rfl
      rw [h1, hcEq]
      rfl

private theorem jStarAct_eq_one_of_le_M {M H J : Subgroup G}
    (hJ : IsKComp M H J) (hJleM : J ≤ M) (hL : ¬ pLayerIn 3 H ≤ M) :
    ∀ x : ↥J, jStarAct J ⟨x, Subgroup.le_normalizer x.2⟩ = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJp : IsPComponentIn 3 J H := hJ.isPComponentIn
  let S : Set (Subgroup G) := {Y | IsPComponentIn 3 Y H ∧ ¬ Y ≤ M}
  have hKdef : kSub 3 M H = sSup S := by
    unfold kSub
    rw [if_neg hL]
  have hYdata : ∀ Y ∈ S, Y ≤ Subgroup.normalizer (J : Set G) ∧
      ⁅Y, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
    intro Y hY
    exact normalizes_and_commutator_of_isPComponentIn hY.1 hJp
      (fun heq => hY.2 (heq ▸ hJleM))
  let L : Subgroup G := ((jStarAct J).ker).map (Subgroup.normalizer (J : Set G)).subtype
  have hSleL : sSup S ≤ L := by
    refine sSup_le fun Y hY => ?_
    intro z hz
    have hYnorm : Y ≤ Subgroup.normalizer (J : Set G) := (hYdata Y hY).1
    have hYcomm : ⁅Y, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype := (hYdata Y hY).2
    have hstar : jStarAct J ⟨z, hYnorm hz⟩ = 1 := by
      apply MulEquiv.ext
      intro a
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) a
      rw [jStarAct_apply_mk, MulAut.one_apply]
      apply (QuotientGroup.eq).mpr
      obtain ⟨c, hc, hcEq⟩ := hYcomm (Subgroup.commutator_mem_commutator hz (J.inv_mem w.2))
      have heq : (⟨z * (w : G) * z⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hYnorm hz) (w : G)).mp w.2⟩ : ↥J)⁻¹ * w = c := by
        apply Subtype.ext
        simpa [commutatorElement_def, mul_assoc] using hcEq.symm
      rwa [heq]
    refine Subgroup.mem_map.mpr ⟨⟨z, hYnorm hz⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    exact hstar
  have hJleL : J ≤ L := (hJ.1.trans_eq hKdef).trans hSleL
  intro x
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp (hJleL x.2)
  rw [MonoidHom.mem_ker] at hn
  have hsub : (⟨x, Subgroup.le_normalizer x.2⟩ : ↥(Subgroup.normalizer (J : Set G))) = n :=
    Subtype.ext hnx.symm
  rwa [hsub]

private theorem isMulCommutative_threeStar_of_le_M {M H J : Subgroup G}
    (hJ : IsKComp M H J) (hJleM : J ≤ M) (hL : ¬ pLayerIn 3 H ≤ M) :
    IsMulCommutative (threeStar J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJact := jStarAct_eq_one_of_le_M hJ hJleM hL
  have hcommStar : ∀ a b : threeStar J, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) b
    have h := congrArg (fun f : MulAut (threeStar J) =>
      f (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) y)) (hJact x)
    rw [jStarAct_apply_mk, MulAut.one_apply] at h
    have h' : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) y *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x)⁻¹ =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) y := by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact h
    calc QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x *
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) y
        = (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x *
            QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) y *
            (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x)⁻¹) *
            QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x := by group
      _ = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) y *
            QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x := by rw [h']
  exact ⟨⟨hcommStar⟩⟩

namespace IsKComp

variable {M H J : Subgroup G}

theorem not_le_M (hJ : IsKComp M H J) (hL : ¬ pLayerIn 3 H ≤ M) : ¬ J ≤ M := by
  intro hJM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsMulCommutative (threeStar J) :=
    isMulCommutative_threeStar_of_le_M hJ hJM hL
  haveI : Group.IsPerfect (threeStar J) := hJ.isQuasisimple.1
  haveI : Nontrivial (threeStar J) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hJ.isQuasisimple
  exact (Group.IsPerfect.not_isMulCommutative (G := threeStar J)) inferInstance

end IsKComp

namespace S14Choice

variable {M H E Q J : Subgroup G}

theorem not_le_M (h : S14Choice G M H E Q J) (hL : PLayerNotLeAt M) : ¬ J ≤ M := by
  have hJ : IsKComp M H J := by
    obtain ⟨H', -, hK', -⟩ := h.J_star.1
    have hintr := (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff
      3 J (kSub 3 M H') hK'.1).mp hK'.2
    exact ⟨h.J_comp.1,
      (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff
        3 J (kSub 3 M H) h.J_comp.1).mpr ⟨h.J_comp.2.1, hintr.2.1, hintr.2.2⟩⟩
  exact IsKComp.not_le_M hJ (hL 3 E H h.hypCGen)

end S14Choice

namespace IsKComp

variable {M H J : Subgroup G}

theorem ker_jBarAct (hJ : IsKComp M H J) : (jBarAct J).ker = (jStarAct J).ker := by
  haveI : Group.IsPerfect (threeStar J) := hJ.isQuasisimple.1
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, jBarAct, MonoidHom.comp_apply]
  constructor
  · intro h
    exact CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective
      (threeStar J) (by simpa using h)
  · intro h
    rw [h, map_one]

end IsKComp

theorem jBarAct_surjective_inner (J : Subgroup G)
    (b : threeStar J ⧸ Subgroup.center (threeStar J)) :
    ∃ g : G, ∃ hg : g ∈ J, jBarAct J ⟨g, Subgroup.le_normalizer hg⟩ = MulAut.conj b := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (threeStar J)) b
  obtain ⟨g, hg, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) y
  refine ⟨(g : G), g.2, ?_⟩
  ext w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (threeStar J)) w
  obtain ⟨u, hu, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) x
  rw [jBarAct_apply_mk, MulAut.conj_apply]
  change QuotientGroup.mk' (Subgroup.center (threeStar J))
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) (⟨g, g.2⟩ * u * ⟨g, g.2⟩⁻¹)) =
    QuotientGroup.mk' (Subgroup.center (threeStar J))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨g, g.2⟩) *
      QuotientGroup.mk' (Subgroup.center (threeStar J))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) u) *
      (QuotientGroup.mk' (Subgroup.center (threeStar J))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨g, g.2⟩))⁻¹
  simp only [map_mul, map_inv]

theorem mem_ker_jBarAct_of_commutator_le {J : Subgroup G}
    {x : ↥(Subgroup.normalizer (J : Set G))}
    (hx : ∀ g ∈ J, (x : G) * g * (x : G)⁻¹ * g⁻¹ ∈ oTwoZStar J) : x ∈ (jBarAct J).ker := by
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (threeStar J)) a
  obtain ⟨g, hg, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) y
  rw [jBarAct_apply_mk, MulAut.one_apply]
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp (hx (g : G) g.2)
  have hc' : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) c ∈
      Subgroup.center (threeStar J) := hc
  have heq : (⟨(x : G) * (g : G) * (x : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp x.2 (g : G)).mp g.2⟩ : ↥J) = c * g := by
    apply Subtype.ext
    simpa [mul_assoc] using congrArg (fun t => t * (g : G)) hcg.symm
  rw [heq]
  change QuotientGroup.mk' (Subgroup.center (threeStar J))
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) c *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) g) =
    QuotientGroup.mk' (Subgroup.center (threeStar J))
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) g)
  rw [map_mul]
  have hc1 : QuotientGroup.mk' (Subgroup.center (threeStar J))
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) c) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hc'
  rw [hc1, one_mul]

theorem jStarAct_eq_one_of_commutator_le {J : Subgroup G}
    {x : ↥(Subgroup.normalizer (J : Set G))}
    (hx : ∀ g ∈ J, (x : G) * g * (x : G)⁻¹ * g⁻¹ ∈
      (CFSG.pPrimeCore 3 ↥J).map J.subtype) : jStarAct J x = 1 := by
  apply MulEquiv.ext
  intro a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) a
  rw [jStarAct_apply_mk, MulAut.one_apply]
  apply (QuotientGroup.eq).mpr
  obtain ⟨c, hc, hcEq⟩ := hx (g : G)⁻¹ (J.inv_mem g.2)
  have heq : (⟨(x : G) * (g : G) * (x : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp x.2 (g : G)).mp g.2⟩ : ↥J)⁻¹ * g = c := by
    apply Subtype.ext
    simpa [commutatorElement_def, mul_assoc] using hcEq.symm
  rwa [heq]

theorem jBarAct_of_mem {J : Subgroup G} {g : G} (hg : g ∈ J) :
    jBarAct J ⟨g, Subgroup.le_normalizer hg⟩ = MulAut.conj
      (QuotientGroup.mk' (Subgroup.center (threeStar J))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨g, hg⟩)) := by
  ext w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (threeStar J)) w
  obtain ⟨u, hu, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) x
  rw [jBarAct_apply_mk, MulAut.conj_apply]
  change QuotientGroup.mk' (Subgroup.center (threeStar J))
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) (⟨g, hg⟩ * u * ⟨g, hg⟩⁻¹)) =
    QuotientGroup.mk' (Subgroup.center (threeStar J))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨g, hg⟩) *
      QuotientGroup.mk' (Subgroup.center (threeStar J))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) u) *
      (QuotientGroup.mk' (Subgroup.center (threeStar J))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨g, hg⟩))⁻¹
  simp only [map_mul, map_inv]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
