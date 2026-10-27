module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TitsRankTwoCount
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8Cover

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem CFSG.AGLEmbeddingD2.McLaughlin.Lie
  CFSG.AGLEmbedding.ParabPrime

variable {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

section Rank1

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem rankOne_le_parabolic (i : Fin D.rank) :
    haveI := cartan_borel_weylN_normal hct hext
    rankOne D.rootGroup i ≤ parabolic (borel D H) (weylN n H) {((⟨n i, n_mem_weylN i⟩ :
      weylN n H) : WeylGroup (borel D H) (weylN n H))} := by
  haveI := cartan_borel_weylN_normal hct hext
  have hBN := isBNPair_borel_weylN hct hext
  set B := borel D H with hB
  set N := weylN n H with hN
  set s : WeylGroup B N := ((⟨n i, n_mem_weylN i⟩ : N) : WeylGroup B N) with hs
  have hsS : s ∈ simpleRefl D n H := ⟨i, rfl⟩
  have hJS : ({s} : Set (WeylGroup B N)) ⊆ simpleRefl D n H := Set.singleton_subset_iff.2 hsS
  have hnP : n i ∈ parabolic B N {s} := by
    rw [hBN.mem_parabolic_iff hJS]
    exact ⟨s, Subgroup.subset_closure rfl,
      mem_dc_mk_iff.2 ⟨1, one_mem _, 1, one_mem _, by simp [hB]⟩⟩
  intro g hg
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  rcases hext.rankOne_bruhat i g hg with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
  · exact mul_mem (hBN.le_parabolic hJS (iSup_le_borel (le_iSup H i hh)))
      (hBN.le_parabolic hJS (rootGroup_le_borel hα (ht_single_pos i) hu))
  · exact mul_mem (mul_mem (mul_mem
      (hBN.le_parabolic hJS (rootGroup_le_borel hα (ht_single_pos i) hu)) hnP)
      (hBN.le_parabolic hJS (iSup_le_borel (le_iSup H i hh))))
      (hBN.le_parabolic hJS (rootGroup_le_borel hα (ht_single_pos i) hv))


include hct hext in
theorem parabolic_single_eq (i : Fin D.rank) :
    haveI := cartan_borel_weylN_normal hct hext
    parabolic (borel D H) (weylN n H) {((⟨n i, n_mem_weylN i⟩ : weylN n H) :
      WeylGroup (borel D H) (weylN n H))} = borel D H ⊔ rankOne D.rootGroup i := by
  haveI := cartan_borel_weylN_normal hct hext
  have hBN := isBNPair_borel_weylN hct hext
  set s : WeylGroup (borel D H) (weylN n H) :=
    ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)) with hs
  have hsS : s ∈ simpleRefl D n H := ⟨i, rfl⟩
  have hJS : ({s} : Set (WeylGroup (borel D H) (weylN n H))) ⊆ simpleRefl D n H :=
    Set.singleton_subset_iff.2 hsS
  refine le_antisymm (fun x hx => ?_)
    (sup_le (hBN.le_parabolic hJS) (rankOne_le_parabolic hct hext i))
  have hx' : x ∈ (borel D H : Set K) ∪ dc (borel D H) (weylN n H) s := by
    rw [← coe_parabolic_single hBN hsS]; exact hx
  rcases hx' with hx' | hx'
  · exact Subgroup.mem_sup_left hx'
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_dc_mk_iff.1 hx'
    exact mul_mem (mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right (hct.n_mem i)))
      (Subgroup.mem_sup_left hb')

end Rank1

section Pair

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem simpleRefl_ne {i j : Fin D.rank} (hij : i ≠ j) (hAji : D.cartan j i = -1) :
    haveI := cartan_borel_weylN_normal hct hext
    ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)) ≠
      ((⟨n j, n_mem_weylN j⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)) := by
  haveI := cartan_borel_weylN_normal hct hext
  intro h
  have hker := cartan_borel_weylN_eq_ker hct hext
  have h1 : weylNHom hct hext ⟨n i, n_mem_weylN i⟩ = weylNHom hct hext ⟨n j, n_mem_weylN j⟩ := by
    have hh := QuotientGroup.eq.mp h
    rw [hker, MonoidHom.mem_ker, map_mul, map_inv] at hh
    exact inv_mul_eq_one.mp hh
  rw [weylNHom_n hct hext i, weylNHom_n hct hext j] at h1
  have h2 := congrArg (fun w => weylAction D.isFiniteType w (pair i j (1, 0))) h1
  rw [weylAction_simple_pair_left, weylAction_simple_pair_right] at h2
  have h3 := congrFun h2 i
  rw [pair_apply_left hij, pair_apply_left hij] at h3
  simp at h3

include hct in
theorem braid_three {i j : Fin D.rank} (hij : i ≠ j) (hAij : D.cartan i j = -1)
    (hAji : D.cartan j i = -1) : n i * n j * n i = n j * n i * n j := by
  have hb := hct.braid i j
  have h1 : (-1 : ℤ) * -1 = 1 := by norm_num
  simp [CoxeterSystem.braidWord, CoxeterSystem.alternatingWord, hAij, hAji, h1] at hb
  rw [mul_assoc, mul_assoc]
  exact hb.symm

include hct hext in
theorem not_nine_dvd_card_rankOne_sup (hH : ∀ k, H k = ⊥) (hU2 : IsPGroup 2 (posUnipotent D))
    (h6 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    {i j : Fin D.rank} (hij : i ≠ j) (hAij : D.cartan i j = -1) (hAji : D.cartan j i = -1) :
    ¬ 9 ∣ Nat.card ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) := by
  haveI := cartan_borel_weylN_normal hct hext
  have hBN := isBNPair_borel_weylN hct hext
  have hBU : borel D H ≤ posUnipotent D :=
    sup_le (iSup_le fun j => (hH j).le.trans bot_le) le_rfl
  have hB : IsPGroup 2 (borel D H) := hU2.to_le hBU
  set a : WeylGroup (borel D H) (weylN n H) :=
    ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)) with ha
  set b : WeylGroup (borel D H) (weylN n H) :=
    ((⟨n j, n_mem_weylN j⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)) with hb
  have haS : a ∈ simpleRefl D n H := ⟨i, rfl⟩
  have hbS : b ∈ simpleRefl D n H := ⟨j, rfl⟩
  have hPa : Nat.card (parabolic (borel D H) (weylN n H) {a}) = 3 * Nat.card (borel D H) := by
    rw [ha, parabolic_single_eq hct hext i]
    exact card_borel_sup_rankOne_of hct hext hH hU2 i (h6 i).1 (h6 i).2
  have hPb : Nat.card (parabolic (borel D H) (weylN n H) {b}) = 3 * Nat.card (borel D H) := by
    rw [hb, parabolic_single_eq hct hext j]
    exact card_borel_sup_rankOne_of hct hext hH hU2 j (h6 j).1 (h6 j).2
  have hab : a ≠ b := simpleRefl_ne hct hext hij hAji
  have hbraid : a * b * a = b * a * b := by
    have h1 := braid_three hct hij hAij hAji
    have h2 : (⟨n i, n_mem_weylN i⟩ * ⟨n j, n_mem_weylN j⟩ * ⟨n i, n_mem_weylN i⟩ : weylN n H) =
        ⟨n j, n_mem_weylN j⟩ * ⟨n i, n_mem_weylN i⟩ * ⟨n j, n_mem_weylN j⟩ := Subtype.ext h1
    rw [ha, hb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, h2]
  have hcount := not_nine_dvd_card_parabolic_pair hBN hB haS hbS hab hbraid hPa hPb
  have hJS : ({a, b} : Set (WeylGroup (borel D H) (weylN n H))) ⊆ simpleRefl D n H := by
    intro x hx
    rcases hx with rfl | rfl
    · exact haS
    · exact hbS
  have hsingle : ∀ (c : WeylGroup (borel D H) (weylN n H)), c ∈ ({a, b} : Set _) →
      parabolic (borel D H) (weylN n H) {c} ≤ parabolic (borel D H) (weylN n H) {a, b} :=
    fun c hc => (hBN.parabolic_le_iff (Set.singleton_subset_iff.2 (hJS hc)) hJS).2
      (Set.singleton_subset_iff.2 hc)
  have hV : rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ≤
      parabolic (borel D H) (weylN n H) {a, b} :=
    sup_le ((rankOne_le_parabolic hct hext i).trans (hsingle a (by simp)))
      ((rankOne_le_parabolic hct hext j).trans (hsingle b (by simp)))
  intro h9
  exact hcount (h9.trans (Subgroup.card_dvd_of_le hV))

end Pair

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
