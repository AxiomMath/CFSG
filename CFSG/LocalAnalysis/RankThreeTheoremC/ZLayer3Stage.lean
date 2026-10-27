module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Small
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3SmallAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Onan
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Open Subgroup

variable {Y : Type} [Group Y] [Finite Y]

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

private theorem onan_hypotheses (R : Sylow 3 Y) (K : Subgroup Y) [K.Normal] {z : Y} (hzK : z ∈ K)
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

theorem exists_generation_of_beta_data (R : Sylow 3 Y) (K : Subgroup Y) [K.Normal] {z : Y}
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
    (hOn : KFactAlphaOnan3Comm) (hLift : KFactSL3LiftGen) :
    ∃ A : Subgroup Y, A ≤ (R : Subgroup Y) ∧ CFSG.Open.IsElemAbelian 3 A ∧
      3 ≤ CFSG.Open.pRank 3 A ∧
      closure {k : K | ∃ f ∈ A, f ∉ centralizer (K : Set Y) ∧ f * (k : Y) * f⁻¹ = k} = ⊤ := by
  rcases hList K hq hkg he hcat hZ hZp hZc hrk with e | e | e | e | ⟨d, hd, e⟩
  · exact (false_of_small_automorphism_group R K hq hzK hzc hz3
      (hSmall K hq hZ hZp hZc (Or.inl e)) hΩ (by omega)).elim
  · exact (false_of_small_automorphism_group R K hq hzK hzc hz3
      (hSmall K hq hZ hZp hZc (Or.inr (Or.inl e))) hΩ (by omega)).elim
  · exact (false_of_small_automorphism_group R K hq hzK hzc hz3
      (hSmall K hq hZ hZp hZc (Or.inr (Or.inr e))) hΩ (by omega)).elim
  · exfalso
    obtain ⟨hout, hexp, hcomm⟩ := hOn K hq hZ hZp hZc e
    obtain ⟨hexp', hcomm'⟩ := onan_hypotheses R K hzK hzc hz3 hZp hZc hexp hcomm
    exact hDn (normalizer_of_exponent_three_onan_type R K hout hzK (hDR hzD) hexp' hcomm' hΩ hDR
      hD3 hzD)
  · exact hLift Y R K z d hd hq e hzY hzK hz3 hΩ (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC
