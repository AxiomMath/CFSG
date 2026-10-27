module

public import CFSG.ClassicalInvolution.AschTight.S19RStd
public import CFSG.ClassicalInvolution.AschTight.S1911Basic
public import CFSG.ClassicalInvolution.Asc77.AscMuTabAbel

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_muIsoZ2_of_muIsoS3 {Ω : Set (Subgroup G)} {W : Subgroup G} (h3 : MuIsoS3 Ω W) :
    ¬ MuIsoZ2 Ω W := by
  rintro ⟨e2⟩
  obtain ⟨e3⟩ := h3
  have h := (Nat.card_congr e2.toEquiv).symm.trans (Nat.card_congr e3.toEquiv)
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_perm, Nat.card_fin] at h
  norm_num [Nat.factorial] at h

theorem not_allTypeTwo_of_muIsoS3 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R : Subgroup G} {z : G} (hstd : Std6 p f Ω K S R z) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hS3 : MuIsoS3 Ω W) : ¬ AllTypeTwo K z := by
  intro hA
  have ht := tightStd_of_std6 hstd
  have htb := ht.toTightBranch
  obtain rfl := T6A.eq_conjClass hstd.stand
  have hP : PartIHyp p f (CoreAssembly.conjClass K) :=
    ⟨hstd.stand.odd, hstd.stand.five, hstd.stand.hyp, hstd.stand.aEmpty⟩
  refine not_muIsoZ2_of_muIsoS3 hS3
    (MuTab.muIsoZ2_of_shape hP hW ⟨K, CoreAssembly.mem_conjClass_self K⟩ fun J hJ => ?_)
  refine Set.eq_empty_of_forall_notMem ?_
  rintro J' ⟨hJ', hne, U, hU, hUJ', hUN⟩
  obtain ⟨w, hw⟩ := S1911.exists_isUniqueInvolution_member htb hJ
  obtain ⟨u, hu⟩ := S1911.exists_isUniqueInvolution_member htb hJ'
  obtain ⟨x, rfl⟩ := CoreAssembly.single_class K J hJ
  have hwx : x * z * x⁻¹ = w := ((isUniqueInvolution_of_tight htb).conj x).eq hw
  have hUw : U ≤ Subgroup.centralizer ({w} : Set G) :=
    (S1911.normalizer_eq_centralizer_member htb hJ hw) ▸ hUN
  obtain ⟨R', hR', hUR', -, hidx⟩ := hU
  have h8 := (exists_ne_comm_of_mem_rSet hstd.stand.odd hstd.stand.five ht.branch.member hR').2
  have hcard : Nat.card R' = 2 * Nat.card U := by
    have h1 := Subgroup.relIndex_mul_card (H := U) (K := R')
    rw [inf_eq_left.mpr hUR', hidx] at h1
    exact h1.symm
  have hU2 : IsPGroup 2 U := (isPGroup_of_mem_rSet hR').to_le hUR'
  have huU : u ∈ U := mem_of_uniqueInvolution_of_pGroup hu hUJ' hU2 (by omega)
  have hwu : w ≠ u := by
    rintro rfl
    exact hne (S1911.eq_of_isUniqueInvolution_member htb hJ' hJ hu hw)
  have hcomm : w * u = u * w := (Subgroup.mem_centralizer_singleton_iff.mp (hUw huU)).symm
  have h2 := hA J' hJ' u w hu ⟨x, hwx⟩ hwu hcomm U hU2 hUJ' hUw
  omega

theorem exists_sylow_le_of_std6 {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
    {R : Subgroup G} {z : G} (hstd : Std6 p f Ω K S R z) :
    ∃ Q₀ : Sylow 2 K, (Q₀ : Subgroup K).map K.subtype = R := by
  have hRK : IsSylow2In R K := Sec7.isSylow2In_of_mem_RSet_of_le hstd.stand.odd hstd.stand.hyp
    hstd.hR hstd.stand.mem hstd.hRK
  obtain ⟨Q, hQ⟩ := (hRK.2.1.comap_subtype : IsPGroup 2 (R.subgroupOf K)).exists_le_sylow
  refine ⟨Q, hRK.2.2 _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map _) ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hRK.1]
  exact Subgroup.map_mono hQ

theorem le_centralizer_of_std6 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R : Subgroup G} {z : G} (hstd : Std6 p f Ω K S R z) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  have ht := tightStd_of_std6 hstd
  obtain ⟨Q₀, hQR⟩ := exists_sylow_le_of_std6 hstd
  have hQS : (Q₀ : Subgroup K).map K.subtype ≤ (S : Subgroup G) := hQR ▸ hstd.hRS
  have hzR : IsUniqueInvolution ((Q₀ : Subgroup K).map K.subtype) z :=
    isUniqueInvolution_of_mem_rSet_of_le ht.toTightBranch
      ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩ (Subgroup.map_subtype_le _)
  have hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (((Q₀ : Subgroup K).map K.subtype : Subgroup G) : Set G) := by
    intro s hs
    have hle : conjSubgroup s ((Q₀ : Subgroup K).map K.subtype) ≤ (S : Subgroup G) := by
      intro x hx
      have hx' := mem_conjSubgroup_iff.mp hx
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hQS hx')) (Subgroup.inv_mem _ hs)
    exact conjSubgroup_eq_self_iff.mp
      (conjSubgroup_sylow_eq_of_tightD ht Q₀ S.isPGroup' hQS hle)
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hzR.conj_eq (conjSub_eq_of_mem_normalizer (hSN hs))
  calc s * z = s * z * s⁻¹ * s := by group
    _ = z * s := by rw [h1]

theorem sec19Data_of_std6 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R : Subgroup G} {z : G} (hstd : Std6 p f Ω K S R z) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hWS : W ≤ (S : Subgroup G)) (hS3 : MuIsoS3 Ω W) :
    Sec19Data p f K z S W := by
  obtain ⟨Q₀, hQR⟩ := exists_sylow_le_of_std6 hstd
  have hmu := not_allTypeTwo_of_muIsoS3 hstd hW hS3
  have hSz := le_centralizer_of_std6 hstd
  have ht := tightStd_of_std6 hstd
  obtain rfl := T6A.eq_conjClass hstd.stand
  exact ⟨ht, hmu, hstd.stand.below, hstd.cex, ⟨Q₀, hQR ▸ hstd.hRS⟩, hSz, hW, hWS⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19R
