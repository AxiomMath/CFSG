module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.RestEvenCount
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.RestEvenRoot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddNormalizer
public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

private lemma oddIdxRest_isSolvable_normalizer_rootU (hF : Nat.card F = (2 ^ f) ^ 2)
    {D : Subgroup (SU (unitaryInvolution F 2 f) 3)} (hDcyc : IsCyclic D)
    (hDsup : rootU hF ⊔ D = Subgroup.normalizer ((rootU hF :
      Subgroup (SU (unitaryInvolution F 2 f) 3)) :
        Set (SU (unitaryInvolution F 2 f) 3))) :
    Group.IsSolvable ↥(Subgroup.normalizer ((rootU hF :
      Subgroup (SU (unitaryInvolution F 2 f) 3)) :
        Set (SU (unitaryInvolution F 2 f) 3))) := by
  classical
  let B : Subgroup (SU (unitaryInvolution F 2 f) 3) :=
    Subgroup.normalizer ((rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3)) :
      Set (SU (unitaryInvolution F 2 f) 3))
  have hUleB : rootU hF ≤ B := Subgroup.le_normalizer
  have hDnorm : D ≤ Subgroup.normalizer (rootU hF : Set (SU (unitaryInvolution F 2 f) 3)) := by
    rw [← hDsup]; exact le_sup_right
  have hBnorm : B ≤ Subgroup.normalizer (rootU hF : Set (SU (unitaryInvolution F 2 f) 3)) :=
    le_rfl
  haveI : ((rootU hF).subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hBnorm
  haveI : ((rootU hF).subgroupOf D).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hDnorm
  haveI : ((rootU hF).subgroupOf
      (D ⊔ rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3))).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hDnorm
  have hU2 : IsPGroup 2 (rootU hF) := isPGroup_rootU hF
  have hUsolv : Group.IsSolvable ↥(rootU hF) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥(rootU hF) := IsPGroup.isNilpotent hU2
    infer_instance
  have hDsolv : Group.IsSolvable ↥D := by
    haveI : IsCyclic ↥D := hDcyc
    infer_instance
  haveI hDsolv' : Group.IsSolvable (↥D ⧸ (rootU hF).subgroupOf D) := by
    haveI : Group.IsSolvable ↥D := hDsolv
    infer_instance
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient D (rootU hF) hDnorm
  have hquot : Group.IsSolvable
      ((D ⊔ rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3)) ⧸
        (rootU hF).subgroupOf (D ⊔ rootU hF)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  have hDsupU : rootU hF ≤ (D ⊔ rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3)) :=
    le_sup_right
  haveI : Group.IsSolvable
      ↥((rootU hF).subgroupOf
        (D ⊔ rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3))) := by
    haveI : Group.IsSolvable ↥(rootU hF) := hUsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hDsupU).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hDsupU).injective
  haveI : Group.IsSolvable
      ((D ⊔ rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3)) ⧸
        (rootU hF).subgroupOf (D ⊔ rootU hF)) := hquot
  have htop : Group.IsSolvable
      ↥(D ⊔ rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3)) :=
    Group.isSolvable_of_subgroup_quotient
      ((rootU hF).subgroupOf (D ⊔ rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3)))
  have hDsup' : (D ⊔ rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3)) =
      Subgroup.normalizer ((rootU hF : Subgroup (SU (unitaryInvolution F 2 f) 3)) :
        Set (SU (unitaryInvolution F 2 f) 3)) := by
    rw [sup_comm]; exact hDsup
  exact hDsup' ▸ htop

theorem eq_top_of_not_two_dvd_index (hF : Nat.card F = (2 ^ f) ^ 2) (hq3 : 2 ^ f % 3 = 1)
    (hB : CFSG.Open.fusionBenderBorel (SU (unitaryInvolution F 2 f) 3) (2 ^ f) 3)
    {ω : Fˣ} (hω : orderOf ω = 3) {W : Subgroup (SU (unitaryInvolution F 2 f) 3)}
    (hNW : Subgroup.normalizer ((Subgroup.zpowers (tSU hF ω) :
      Subgroup (SU (unitaryInvolution F 2 f) 3)) : Set (SU (unitaryInvolution F 2 f) 3)) ≤ W)
    (hodd : ¬ 2 ∣ W.index) (hns : ¬ Group.IsSolvable ↥W) : W = ⊤ := by
  classical
  let G : Type := SU (unitaryInvolution F 2 f) 3
  let U : Subgroup G := rootU hF
  let B : Subgroup G := Subgroup.normalizer ((U : Set G))
  let f' : G →* G := (MulAut.conj (g0SU (unitaryInvolution F 2 f))⁻¹).toMonoidHom
  have hf'inj : Function.Injective f' :=
    (MulAut.conj (g0SU (unitaryInvolution F 2 f))⁻¹ : G ≃* G).injective
  have hf1 : 1 ≤ f := one_le_f hF
  have h2q : 2 ≤ 2 ^ f := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hf1
  obtain ⟨hUW', hZW'⟩ := rootU_le_conj_of_not_two_dvd_index hF hq3 hω hNW hodd
  have hnsW' : ¬ Group.IsSolvable ↥(W.map f') := by
    intro hsol
    refine hns ?_
    let e : W ≃* W.map f' := Subgroup.equivMapOfInjective W f' hf'inj
    haveI : Group.IsSolvable ↥(W.map f') := hsol
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hUi : ¬ 2 ∣ (rootU hF).index := by
    rw [index_rootU hF]; exact odd_index_factor hF
  have hBQ := hB ((isPGroup_rootU hF).toSylow hUi)
  simp only [IsPGroup.toSylow_coe] at hBQ
  have hBstrong : CFSG.Open.fusionStronglyEmbedded B := hBQ.1
  obtain ⟨D, hDcyc, hDodd, hDdisj, hDsup⟩ := hBQ.2.1
  have hBsolv : Group.IsSolvable ↥B :=
    oddIdxRest_isSolvable_normalizer_rootU hF hDcyc hDsup
  have hWB : ¬ W.map f' ≤ B := by
    intro hle
    refine hnsW' ?_
    have hsub : Group.IsSolvable ↥((W.map f').subgroupOf B) := by
      haveI : Group.IsSolvable ↥B := hBsolv
      infer_instance
    haveI : Group.IsSolvable ↥((W.map f').subgroupOf B) := hsub
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).symm.injective
  have hUleB : U ≤ B := Subgroup.le_normalizer
  have hTleB : (tSU hF).range ≤ B := by
    rintro x ⟨μ, rfl⟩
    refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · exact tSU_conj_mem_rootU hF μ hy
    · have h := tSU_conj_mem_rootU hF μ⁻¹ hy
      simp only [map_inv, inv_inv] at h
      convert h using 1
      group
  have hUdivB : Nat.card U ∣ Nat.card B := Subgroup.card_dvd_of_le hUleB
  have hTdivB : Nat.card (tSU hF).range ∣ Nat.card B := Subgroup.card_dvd_of_le hTleB
  have hodd_q2 : Odd ((2 ^ f) ^ 2 - 1) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    have he : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega : f ≠ 0)
    have h2dvd : 2 ∣ (2 ^ f) ^ 2 := he.trans (dvd_pow_self _ (by norm_num))
    have hpos : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hcop : Nat.Coprime (Nat.card U) (Nat.card (tSU hF).range) := by
    rw [show Nat.card U = (2 ^ f) ^ 3 from card_rootGroup_three hF, card_range_tSU hF]
    rw [show (2 ^ f) ^ 3 = 2 ^ (3 * f) by rw [mul_comm 3 f, pow_mul]]
    rw [Nat.coprime_pow_left_iff (by omega : 0 < 3 * f)]
    exact Nat.coprime_two_left.mpr hodd_q2
  have hdvdB : (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) ∣ Nat.card B := by
    have h := hcop.mul_dvd_of_dvd_of_dvd hUdivB hTdivB
    rwa [show Nat.card U = (2 ^ f) ^ 3 from card_rootGroup_three hF,
      card_range_tSU hF] at h
  have hcardG : Nat.card G = (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
    change Nat.card (SU (unitaryInvolution F 2 f) 3) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))
    rw [card_SU_even hF, mul_comm 3 f, pow_mul]
  have hcardBmul : Nat.card B * B.index = Nat.card G :=
    Subgroup.card_mul_index (H := B)
  obtain ⟨k, hk⟩ := hdvdB
  have hk_index : k * B.index = (2 ^ f) ^ 3 + 1 := by
    have h1 : ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1)) * (k * B.index) =
        ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1)) * ((2 ^ f) ^ 3 + 1) := by
      calc ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1)) * (k * B.index)
          = ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1)) * k * B.index := by ac_rfl
        _ = Nat.card B * B.index := by rw [← hk]
        _ = Nat.card G := hcardBmul
        _ = ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1)) * ((2 ^ f) ^ 3 + 1) := by
              rw [hcardG]; ac_rfl
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos (by norm_num) _)
      (Nat.sub_pos_of_lt (one_lt_pow' (by omega : 1 < 2 ^ f) (by norm_num : (2 : ℕ) ≠ 0)))) h1
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
    rw [hk0, mul_zero] at hk
    exact (Nat.card_pos (α := ↥B)).ne' hk
  have hBidx_le : B.index ≤ (2 ^ f) ^ 3 + 1 :=
    (Nat.le_mul_of_pos_left B.index hkpos).trans_eq hk_index
  have hU2 : IsPGroup 2 U := isPGroup_rootU hF
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card U = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [show Nat.card U = (2 ^ f) ^ 3 from card_rootGroup_three hF] at hcard1
    have h8 : 8 ≤ (2 ^ f) ^ 3 := by
      have := Nat.pow_le_pow_left h2q 3
      norm_num at this
      exact this
    omega
  have hBidx_le' : B.index ≤ Nat.card U + 1 := by
    rw [show Nat.card U = (2 ^ f) ^ 3 from card_rootGroup_three hF]
    exact hBidx_le
  have hstrong := stronglyEmbedded_card_eq_mul_inf hBstrong hU2 hUne hUleB hBidx_le' hUW' hWB
  have hBidx : B.index = Nat.card U + 1 := hstrong.1
  let N : Subgroup G := W.map f' ⊓ B
  have hW'card : Nat.card (W.map f') = B.index * Nat.card N := hstrong.2
  have hBcard : Nat.card B = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) := by
    have hbindex : B.index = (2 ^ f) ^ 3 + 1 := by
      rw [hBidx, show Nat.card U = (2 ^ f) ^ 3 from card_rootGroup_three hF]
    have hk1 : k = 1 := by
      have h2 : k * ((2 ^ f) ^ 3 + 1) = 1 * ((2 ^ f) ^ 3 + 1) := by
        rw [one_mul, ← hbindex, hk_index, hbindex]
      exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
    rw [hk, hk1, mul_one]
  have hUle_inf : U ≤ N := le_inf hUW' hUleB
  have hq3_dvd : (2 ^ f) ^ 3 ∣ Nat.card N := by
    have h := Subgroup.card_dvd_of_le hUle_inf
    rwa [show Nat.card U = (2 ^ f) ^ 3 from card_rootGroup_three hF] at h
  let Z : Subgroup G := (rootsOfUnity (2 ^ f + 1) F).map (tSU hF)
  have hZcard : Nat.card Z = 2 ^ f + 1 := by
    change Nat.card ((rootsOfUnity (2 ^ f + 1) F).map (tSU hF)) = 2 ^ f + 1
    rw [Subgroup.card_map_of_injective (tSU_injective hF)]
    refine CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := F) (d := 2 ^ f + 1) ?_
    rw [hF]
    refine ⟨2 ^ f - 1, ?_⟩
    simpa using Nat.sq_sub_sq (2 ^ f) 1
  have hZleW' : Z ≤ W.map f' := by
    rintro x ⟨μ, hμ, rfl⟩
    exact hZW' μ hμ
  have hZleB : Z ≤ B := by
    rintro x ⟨μ, hμ, rfl⟩
    exact hTleB ⟨μ, rfl⟩
  have hq1_dvd : 2 ^ f + 1 ∣ Nat.card N := by
    have h := Subgroup.card_dvd_of_le (le_inf hZleW' hZleB : Z ≤ N)
    rwa [hZcard] at h
  have hn_dvd : Nat.card N ∣ (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) := by
    have h := Subgroup.card_dvd_of_le (inf_le_right : N ≤ B)
    rwa [hBcard] at h
  have hTleW : (tSU hF).range ≤ W := (range_tSU_le_normA0 hF hω hq3).trans hNW
  have hq2m1_dvd : (2 ^ f) ^ 2 - 1 ∣ ((2 ^ f) ^ 3 + 1) * Nat.card N := by
    have h := Subgroup.card_dvd_of_le hTleW
    have hWW' : Nat.card W = Nat.card (W.map f') :=
      (Subgroup.card_map_of_injective hf'inj).symm
    have hbindex : B.index = (2 ^ f) ^ 3 + 1 := by
      rw [hBidx, show Nat.card U = (2 ^ f) ^ 3 from card_rootGroup_three hF]
    rw [card_range_tSU hF, hWW', hW'card, hbindex] at h
    exact h
  have hq_even : Even (2 ^ f) :=
    even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : f ≠ 0))
  have hn : Nat.card N = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) :=
    oddIdxRest_nat_eq_of_dvd (q := 2 ^ f) hq_even h2q hq3_dvd hq1_dvd hn_dvd hq2m1_dvd
  have hbindex : B.index = (2 ^ f) ^ 3 + 1 := by
    rw [hBidx, show Nat.card U = (2 ^ f) ^ 3 from card_rootGroup_three hF]
  have hW'cardG : Nat.card (W.map f') = Nat.card G := by
    rw [hW'card, hbindex, hn, hcardG]
    ac_rfl
  have hW'map : W.map f' = ⊤ := Subgroup.eq_top_of_card_eq (W.map f') hW'cardG
  rw [← Subgroup.comap_map_eq_self_of_injective (f := f') hf'inj W, hW'map,
    Subgroup.comap_top]

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
