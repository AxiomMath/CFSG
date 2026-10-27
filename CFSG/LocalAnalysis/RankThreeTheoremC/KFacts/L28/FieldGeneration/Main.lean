module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.FieldGeneration.Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.FieldGeneration.Families
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankOneFinal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsL28

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28

open CFSG.RankThree.PartOne.CTP TauCeti

namespace FieldGeneration

theorem isCyclic_of_isPGroup_three {K : Type} [Group K] [Finite K] {T : Subgroup K}
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤) (hcyc : IsCyclic T) (X : Subgroup K)
    (hX : IsPGroup 3 X) : IsCyclic X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hTp, hTi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  rw [Subgroup.relIndex_top_right] at hTi
  set P : Sylow 3 K := hTp.toSylow hTi with hPdef
  have hPT : (P : Subgroup K) = T := IsPGroup.toSylow_coe hTp hTi
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  have hP : IsCyclic (P : Subgroup K) := by rw [hPT]; exact hcyc
  have hQ : IsCyclic (Q : Subgroup K) :=
    isCyclic_of_surjective (Sylow.equiv P Q).toMonoidHom (Sylow.equiv P Q).surjective
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hXQ).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hXQ).surjective

theorem isRankThreeL28_of_card_eight {K : Type} [Group K] {q : PrimePower}
    (hv : (LieTypeIndex.A 1 q).Valid) (h8 : q.card = 8)
    (e : K ≃* (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) : IsRankThreeL28 K := by
  have hp : q.p = 2 := by
    have h1 : q.p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h8, PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp (q.prime_p.dvd_of_dvd_pow h1)
  have hexp : q.exponent = 3 := by
    have h3 : q.p ^ q.exponent = q.p ^ 3 := by
      rw [← PrimePower.card_def, h8, hp]
      norm_num
    exact Nat.pow_right_injective q.prime_p.two_le h3
  have hq : q = ⟨2, 3, Nat.prime_two, by norm_num⟩ := PrimePower.ext hp hexp
  subst hq
  exact ⟨hv, ⟨e⟩⟩

end FieldGeneration

section Main

namespace FieldGeneration

theorem fieldAutData_three_of_catalog
    {K : Type} [Group K] [Finite K]
    (hsimple : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (hcat : CFSG.Open.IsCatalogGroup K) (hL28 : ¬ IsRankThreeL28 K) {T : Subgroup K}
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤) (hcyc : IsCyclic T) (hT9 : Nat.card T = 3 ^ 2) :
    FieldAutData K 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, he⟩ := hcat
  have h9 : 9 ∣ Nat.card K := by
    have h := Subgroup.card_subgroup_dvd_card T
    rwa [hT9] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (dvd_trans (by norm_num) h9)
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1 :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.pRank_three_eq_one_of_cyclic
      (isCyclic_of_isPGroup_three hT hcyc) (A := Subgroup.zpowers x)
      (by rw [Nat.card_zpowers, hx])
  rcases CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple K hsimple
      hnab i he hr with
    ⟨⟨d, hv⟩, (⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩), ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain rfl : d = .A 1 q := hd
    exact fieldAutData_three_A1 hv (fun h8 => hL28 (isRankThreeL28_of_card_eight hv h8 e)) e
  · obtain rfl : d = .A 2 q := hd
    exact fieldAutData_three_A2 hv hq e
  · obtain rfl : d = .twistedA 2 q := hd
    exact fieldAutData_three_twistedA2 hv hq e
  · exfalso
    obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
    have hJ : Nat.card K = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      show Nat.card TauCeti.SporadicName.J1.Group = 175560
      rw [← Nat.card_congr f.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    rw [hJ] at h9
    norm_num at h9
  · exfalso
    have hA : Nat.card K = 60 := by
      rw [Nat.card_congr e.toEquiv]
      show Nat.card (alternatingGroup (Fin 5)) = 60
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [hA] at h9
    norm_num at h9

end FieldGeneration

open FieldGeneration in
theorem kFactFieldGeneration_holds
    : KFactFieldGeneration := by
  intro K _ _ hsimple hnab hcat hL28 T hT hcyc hT9 α hα hαT hne
  have hcomm : IsMulCommutative T := IsCyclic.isMulCommutative
  have hout := isOuterOfOrder_three hsimple hnab hT hcomm hα hαT hne
  have hα3 : α ^ 3 = 1 := hα ▸ pow_orderOf_eq_one α
  obtain ⟨t, ht, hw1, hwα, hw3⟩ :=
    exists_twist_of_cyclic_nine hcyc (by rw [hT9]; norm_num) hα3 hαT hne
  have hd := fieldAutData_three_of_catalog hsimple hnab hcat hL28 hT hcyc hT9
  rw [eqLocus_eq_fixedSubgroup]
  exact sup_fixedSubgroup_eq_top hd hout ht hw1 hwα hw3

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.L28
