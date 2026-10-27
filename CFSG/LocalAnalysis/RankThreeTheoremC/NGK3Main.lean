module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Core
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.LocalAnalysis.RankThreeTheoremC.NormalPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListE2
import CFSG.RankThree.OddKernel.FailureReduction
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftGrp
public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3LayerCaseA
public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3LayerStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Onan
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Small
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3SmallAut
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def CentralizerGenerationKFact3W : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    CFSG.twoLocalOddRank X ≤ 3 → primeComplementCore (G := X) 3 = ⊥ →
    ∀ (P : Sylow 3 X) (z : X) (D : Subgroup X),
      CFSG.Open.pRank 3 (P : Subgroup X) = 3 → orderOf z = 3 → z ∈ center X →
      z ∈ rankThreeLayer (⊤ : Subgroup X) →
      IsNonabelianPlane 3 (P : Subgroup X) D → (P : Subgroup X) ≤ normalizer (D : Set X) →
      z ∈ D → Nat.card D = 3 ^ 3 → ⊤ ≤ rankThreeAschCore 2 3 (P : Subgroup X)

private theorem le_zpowers_of_cyclic_of_exponent_three {K : Type} [Group K] [Finite K]
    (hc : IsCyclic K) (hexp : ∀ w : K, w ^ 3 = 1) {z : K} (hz3 : orderOf z = 3) :
    ∀ w : K, w ∈ zpowers z := by
  have := hc
  have hdvd : Nat.card K ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  have hle : Nat.card K ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  have hz : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  have hz' : Nat.card (zpowers z) ≤ Nat.card K := Subgroup.card_le_card_group _
  intro w
  rw [Subgroup.eq_top_of_card_eq (zpowers z) (by omega)]
  exact Subgroup.mem_top w

variable {Y : Type} [Group Y] [Finite Y]

private theorem onan_hypotheses' (R : Sylow 3 Y) (K : Subgroup Y) [K.Normal] {z : Y} (hzK : z ∈ K)
    (hzc : ∀ k ∈ K, z * k = k * z) (hz3 : orderOf z = 3) (hZp : IsPGroup 3 (center K))
    (hZc : IsCyclic (center K))
    (hexp : ∀ T : Sylow 3 K, ∀ t ∈ (T : Subgroup K), t ^ 3 = 1)
    (hcomm : ∀ T : Sylow 3 K, ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K),
      x * y * x⁻¹ * y⁻¹ ∈ center K) :
    (∀ t ∈ (R : Subgroup Y) ⊓ K, t ^ 3 = 1) ∧
      ∀ x ∈ (R : Subgroup Y) ⊓ K, ∀ y ∈ (R : Subgroup Y) ⊓ K,
        x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal R (N := K)
  have hmemT : ∀ (t : Y) (ht : t ∈ (R : Subgroup Y) ⊓ K), (⟨t, ht.2⟩ : K) ∈ (T : Subgroup K) := by
    intro t ht
    rw [hT, Subgroup.mem_subgroupOf]
    exact ht
  have hzc' : (⟨z, hzK⟩ : K) ∈ center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2).symm
  have hZle : ∀ w : center K, w ∈ zpowers (⟨⟨z, hzK⟩, hzc'⟩ : center K) := by
    refine le_zpowers_of_cyclic_of_exponent_three hZc (fun w => ?_) ?_
    · have hw : (w : K) ∈ (T : Subgroup K) := hZp.le_sylow_of_normal T w.2
      exact Subtype.ext (hexp T _ hw)
    · rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz3]
  have hcenter : ∀ c : K, c ∈ center K → (c : Y) ∈ zpowers z := by
    intro c hc
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hZle ⟨c, hc⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    simpa using congrArg (fun u : center K => ((u : K) : Y)) hn
  refine ⟨fun t ht => ?_, fun x hx y hy => ?_⟩
  · simpa using congrArg Subtype.val (hexp T _ (hmemT t ht))
  · exact hcenter _ (hcomm T _ (hmemT x hx) _ (hmemT y hy))

theorem exists_generation_and_out_of_beta_data (R : Sylow 3 Y) (K : Subgroup Y) [K.Normal] {z : Y}
    (hq : CFSG.Open.IsQuasisimple K) (hkg : CFSG.IsKGroup K) (he : CFSG.twoLocalOddRank K ≤ 3)
    (hcat : IsCatalogGroup (K ⧸ center K)) (hZ : center K ≠ ⊥)
    (hZp : IsPGroup 3 (center K)) (hZc : IsCyclic (center K))
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    (hzK : z ∈ K) (hzc : ∀ k ∈ K, z * k = k * z) (hzY : z ∈ center Y) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup Y) ⊓ centralizer (K : Set Y), orderOf c = 3 → c ∈ zpowers z)
    (hR3 : CFSG.Open.pRank 3 (R : Subgroup Y) = 3)
    {D : Subgroup Y} (hDR : D ≤ R) (hD3 : ∀ x ∈ D, x ^ 3 = 1) (hzD : z ∈ D)
    (hDn : ¬ (R : Subgroup Y) ≤ normalizer (D : Set Y))
    (hList : KFactAlphaListM3) (hSmall : KFactAlphaSmallAut3Card)
    (hOn : KFactAlphaOnan3Comm) (hLift : KFactSL3LiftGen) (hOut : KFactSL3OutNormalSylow) :
    (∃ A : Subgroup Y, A ≤ (R : Subgroup Y) ∧ CFSG.Open.IsElemAbelian 3 A ∧
      3 ≤ CFSG.Open.pRank 3 A ∧
      closure {k : K | ∃ f ∈ A, f ∉ centralizer (K : Set Y) ∧ f * (k : Y) * f⁻¹ = k} = ⊤) ∧
      CFSG.AGLEmbedding.KOutNormalSylow 3 K := by
  rcases hList K hq hkg he hcat hZ hZp hZc hrk with e | e | e | e | ⟨d, hd, e⟩
  · exact (false_of_small_automorphism_group R K hq hzK hzc hz3
      (hSmall K hq hZ hZp hZc (Or.inl e)) hΩ (by omega)).elim
  · exact (false_of_small_automorphism_group R K hq hzK hzc hz3
      (hSmall K hq hZ hZp hZc (Or.inr (Or.inl e))) hΩ (by omega)).elim
  · exact (false_of_small_automorphism_group R K hq hzK hzc hz3
      (hSmall K hq hZ hZp hZc (Or.inr (Or.inr e))) hΩ (by omega)).elim
  · exfalso
    obtain ⟨hout, hexp, hcomm⟩ := hOn K hq hZ hZp hZc e
    obtain ⟨hexp', hcomm'⟩ := onan_hypotheses' R K hzK hzc hz3 hZp hZc hexp hcomm
    exact hDn (normalizer_of_exponent_three_onan_type R K hout hzK (hDR hzD) hexp' hcomm' hΩ hDR
      hD3 hzD)
  · exact ⟨hLift Y R K z d hd hq e hzY hzK hz3 hΩ (by omega), hOut K hq d hd e⟩

theorem le_rankThreeAschCore_of_generation_top {X : Type} [Group X] [Finite X] {P : Sylow 3 X}
    {K : Subgroup X} {z : X} (hz3 : orderOf z = 3) (hzP : z ∈ (P : Subgroup X))
    (hzc : ∀ g ∈ (P : Subgroup X), z * g = g * z) (hzK : ∀ k ∈ K, z * k = k * z)
    {A : Subgroup X} (hAP : A ≤ (P : Subgroup X)) (hA : CFSG.Open.IsElemAbelian 3 A)
    (hA3 : 3 ≤ CFSG.Open.pRank 3 A)
    (hgen : closure {k : K | ∃ f ∈ A, f ∉ centralizer (K : Set X) ∧ f * (k : X) * f⁻¹ = k} = ⊤) :
    K ≤ rankThreeAschCore 2 3 (P : Subgroup X) := by
  have htop : (⊤ : Subgroup K) ≤ (rankThreeAschCore 2 3 (P : Subgroup X)).comap K.subtype := by
    refine hgen.symm.le.trans ((closure_le _).2 ?_)
    rintro k ⟨f, hfA, hfc, hfk⟩
    have hfz : f ∉ zpowers z := by
      intro hf
      refine hfc (mem_centralizer_iff.2 fun h hh => ?_)
      have hcomm : Commute f h := by
        obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hf
        rw [← hn]
        exact Commute.zpow_left (show Commute z h from hzK _ hh) n
      exact hcomm.symm.eq
    have hfk' : f * (k : X) = (k : X) * f :=
      calc f * (k : X) = f * (k : X) * f⁻¹ * f := (inv_mul_cancel_right _ _).symm
        _ = (k : X) * f := by rw [hfk]
    exact mem_rankThreeAschCore_of_commute hAP hA hA3 hzP hzc hz3 hfA hfz (hzK _ k.2) hfk'
  intro k hk
  exact htop (Subgroup.mem_top (⟨k, hk⟩ : K))

theorem top_le_of_kOutNormalSylow {X : Type} [Group X] [Finite X] (R : Sylow 3 X)
    (K : Subgroup X) [K.Normal] (hout : CFSG.AGLEmbedding.KOutNormalSylow 3 K) {Γ : Subgroup X}
    (hKΓ : K ≤ Γ) (hCΓ : centralizer (K : Set X) ≤ Γ) (hRΓ : (R : Subgroup X) ≤ Γ)
    (hNΓ : normalizer ((R : Subgroup X) : Set X) ≤ Γ) : ⊤ ≤ Γ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (MulAut.conj : K →* MulAut K).range.Normal :=
    CFSG.AGLEmbedding.normal_range_mulAutConj K
  obtain ⟨S, hS⟩ := (R.isPGroup'.map (MulAut.conjNormal (H := K))).exists_le_sylow
  have hWn := (hout S).comap (MulAut.conjNormal (H := K))
  have hNΓ' : (MulAut.conj : K →* MulAut K).range.comap (MulAut.conjNormal (H := K)) ≤ Γ :=
    CFSG.AGLEmbedding.comap_range_conj_le hKΓ hCΓ
  have hRW : (R : Subgroup X) ≤ ((MulAut.conj : K →* MulAut K).range ⊔
      (S : Subgroup (MulAut K))).comap (MulAut.conjNormal (H := K)) := fun r hr =>
    Subgroup.mem_sup_right (hS ⟨r, hr, rfl⟩)
  have hW : ∀ w ∈ ((MulAut.conj : K →* MulAut K).range ⊔
      (S : Subgroup (MulAut K))).comap (MulAut.conjNormal (H := K)), ∃ k : ℕ,
      w ^ 3 ^ k ∈ (MulAut.conj : K →* MulAut K).range.comap (MulAut.conjNormal (H := K)) :=
    fun w hw => by
      obtain ⟨k, hk⟩ := CFSG.AGLEmbedding.exists_pow_mem_of_mem_sup S.isPGroup' hw
      exact ⟨k, by rw [Subgroup.mem_comap, map_pow]; exact hk⟩
  have hWΓ : ((MulAut.conj : K →* MulAut K).range ⊔
      (S : Subgroup (MulAut K))).comap (MulAut.conjNormal (H := K)) ≤ Γ :=
    (CFSG.AGLEmbedding.le_sylow_sup_of_pow_mem R hW).trans (sup_le hRΓ hNΓ')
  by_contra hne
  have hΓ : Γ ≠ ⊤ := fun h => hne (h ▸ le_rfl)
  refine CFSG.AGLEmbedding.not_le_of_normalizer_inf_le R (N := ((MulAut.conj : K →* MulAut K).range
    ⊔ (S : Subgroup (MulAut K))).comap (MulAut.conjNormal (H := K))) ?_ hΓ hWΓ
  rw [inf_eq_left.mpr hRW]
  exact hNΓ

theorem ngkW_of_facts (hList : KFactAlphaListM3) (hSmall : KFactAlphaSmallAut3Card)
    (hOn : KFactAlphaOnan3Comm) (hLift : KFactSL3LiftGen) (hOut : KFactSL3OutNormalSylow) :
    CentralizerGenerationKFact3W := by
  intro X _ _ hcat he3 hcore P z D hrank hz3 hzc hzE hplane hnorm hzD hcard
  have h : NGKData X P z D := ⟨hcat, he3, hcore, hrank, hz3, hzc, hzE, hplane, hnorm, hzD, hcard⟩
  have hF : PlaneFacts (P : Subgroup X) D z := h.planeData.facts
  have hprime : Nat.Prime 3 := Nat.prime_three
  have hPcore : normalizer ((P : Subgroup X) : Set X) ≤ rankThreeAschCore 2 3 (P : Subgroup X) :=
    aschCore_normalizer_le 2 3 (P : Subgroup X) (P : Subgroup X) le_rfl (by omega)
      (hrank.ge.trans (pRank_mono 3 (by norm_num) le_sup_left))
  by_cases hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z
  · obtain ⟨L, hL, hLn, hzL, hzcL, hZne, hZcyc, hΩ, B, hBL, hBD, hBcard, hBe, hBn⟩ :=
      h.layer_structure hF hB
    have : L.Normal := hLn
    have hZp : IsPGroup 3 (center L) :=
      CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf hprime hcore hL
    have hkg : CFSG.IsKGroup L := cfsgIsKGroup_of_catalogSimpleSections (hcat.subgroup L)
    have hLe : CFSG.twoLocalOddRank L ≤ 3 :=
      (CFSG.RankThree.OddKernel.twoLocalOddRank_subgroup_le L).trans he3
    have hglob : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 :=
      (CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank 3 hprime P).symm.trans hrank
    have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3 := by
      have hf : Function.Injective L.subtype := L.subtype_injective
      exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3 hprime _ hf
        ⊤).trans ((CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 hprime le_top).trans
        hglob.le)
    have hzP : z ∈ (P : Subgroup X) := SL3Lift.mem_sylow_of_central P hzc hz3
    obtain ⟨D', hD'P, hD'3, hzD', hD'n⟩ := hF.not_normal
    obtain ⟨⟨A, hAP, hAe, hA3, hgen⟩, hout'⟩ := exists_generation_and_out_of_beta_data (Y := X)
      P L hL.2.2 hkg hLe (hcat.isCatalogGroup_center_quotient hL) hZne hZp hZcyc hrk hzL hzcL hzc
      hz3 hΩ hrank hD'P hD'3 hzD' hD'n hList hSmall hOn hLift hOut
    have hLcore : L ≤ rankThreeAschCore 2 3 (P : Subgroup X) :=
      le_rankThreeAschCore_of_generation_top hz3 hzP (fun g _ => h.zc' g) hzcL hAP hAe hA3 hgen
    have hB2 : 2 ≤ CFSG.Open.pRank 3 B := by
      unfold CFSG.Open.pRank
      exact le_csSup (pRank_set_bddAbove 3 hprime.one_lt _)
        ⟨B, le_rfl, hBe, by rw [hBcard]; norm_num⟩
    have hBP : B ≤ (P : Subgroup X) := hBD.trans h.plane.1
    have hB3 : 3 ≤ CFSG.Open.pRank 3 (B ⊔ ((P : Subgroup X) ⊓ centralizer (B : Set X))) :=
      three_le_pRank_sup_centralizer_of_normal_elemAbelian hprime hrank.ge hBn hBe
        (by rw [hBcard]; norm_num)
    have hCcore : centralizer (L : Set X) ≤ rankThreeAschCore 2 3 (P : Subgroup X) :=
      ((Subgroup.centralizer_le hBL).trans (centralizer_le_normalizer B)).trans
        (aschCore_normalizer_le 2 3 (P : Subgroup X) B hBP hB2 hB3)
    exact top_le_of_kOutNormalSylow P L hout' hLcore hCcore
      (le_normalizer.trans hPcore) hPcore
  · push Not at hB
    obtain ⟨w, hw, hw3, hwz⟩ := hB
    exact h.caseA hw hw3 hwz

end CFSG.LocalAnalysis.RankThreeTheoremC
