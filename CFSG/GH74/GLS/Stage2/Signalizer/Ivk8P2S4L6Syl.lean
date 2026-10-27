module

public import CFSG.GH74.Defs
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

theorem ka6syl_sylow_conj {G : Type*} [Group G] [Finite G] {K P Q : Subgroup G}
    (hPK : P ≤ K) (hQK : Q ≤ K) (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) :
    ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ P ≤ T ∧
      ∃ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ T := by
  obtain ⟨SP, hSP⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨SQ, hSQ⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K SQ SP
  refine ⟨(SP : Subgroup K).map K.subtype, ?_, ?_, ?_, k, k.2, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact SP.isPGroup'.map _
  · intro x hx
    exact ⟨⟨x, hPK hx⟩, hSP hx, rfl⟩
  · intro q hq
    have h1 : (⟨q, hQK hq⟩ : K) ∈ (SQ : Subgroup K) := hSQ hq
    have h2 : (MulAut.conj k) ⟨q, hQK hq⟩ ∈ (SP : Subgroup K) := by
      rw [← hk, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    exact ⟨_, h2, rfl⟩

theorem ka6syl_central_conj {G : Type*} [Group G] [Finite G] {z : G}
    (hz : CFSG.GH74.IsCentralInvolution z) (T : Sylow 2 G) :
    ∃ g : G, g * z * g⁻¹ ∈ (T : Subgroup G) ∧
      ∀ t ∈ (T : Subgroup G), t * (g * z * g⁻¹) = (g * z * g⁻¹) * t := by
  obtain ⟨S, hzS, hSc⟩ := hz.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  refine ⟨g, ?_, ?_⟩
  · rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul z (MulAut.conj g) _ hzS
  · intro t ht
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at ht
    have h1 : (MulAut.conj g)⁻¹ • t = g⁻¹ * t * g := by
      simp [MulAut.smul_def, ← map_inv]
    rw [h1] at ht
    have h2 := hSc _ ht
    calc t * (g * z * g⁻¹) = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [h2]
      _ = (g * z * g⁻¹) * t := by group

theorem ka6syl_mem_of_commute {G : Type*} [Group G] [Finite G] (hrank : CFSG.pRank 2 G ≤ 4)
    {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) (hBc : Nat.card ↥B = 2 ^ 4) {y : G}
    (hy : y ^ 2 = 1) (hyc : ∀ b ∈ B, b * y = y * b) : y ∈ B := by
  by_contra hyB
  have hY : CFSG.IsElementaryAbelian 2 ↥(zpowers y) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hy
  have hcent : zpowers y ≤ centralizer (B : Set G) := by
    rw [zpowers_le]
    exact fun b hb => hyc b hb
  have hE : CFSG.IsElementaryAbelian 2 ↥(B ⊔ zpowers y : Subgroup G) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer (E := B) (C := zpowers y) hcent
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥(B ⊔ zpowers y : Subgroup G))
  have hdvd : 2 ^ 4 ∣ 2 ^ n :=
    hBc ▸ hn ▸ Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ zpowers y)
  have h4n : 4 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hn5 : 5 ≤ n := by
    by_contra h
    have hn4 : n = 4 := by omega
    have hEq : B = B ⊔ zpowers y := by
      refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
      rw [hn, hBc, hn4]
    exact hyB (hEq ▸ mem_sup_right (mem_zpowers y))
  have := CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two _ hE hn
  omega

theorem exists_central_conj_mem_comm {G : Type} [Group G] [Finite G] {z : G}
    (hz : CFSG.GH74.IsCentralInvolution z) (hrank : CFSG.pRank 2 G ≤ 4)
    {J : Subgroup G} (hzJ : z ∈ normalizer (J : Set G)) {A : Subgroup G} (hAJ : A ≤ J)
    (hA : CFSG.IsElementaryAbelian 2 ↥A) (hcard : Nat.card ↥A = 2 ^ 4) :
    ∃ g : G, g * z * g⁻¹ ∈ J ∧ (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
  have hKN : J ⊔ zpowers z ≤ normalizer (J : Set G) :=
    sup_le le_normalizer (zpowers_le.mpr hzJ)
  have hzp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hz.1, pow_one])
  obtain ⟨T0, -, hT0p, hzT0, k, hkK, hkA⟩ := ka6syl_sylow_conj (K := J ⊔ zpowers z)
    (zpowers_le.mpr (mem_sup_right (mem_zpowers z))) (hAJ.trans le_sup_left) hzp
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥A)
  obtain ⟨T, hT0T⟩ := hT0p.exists_le_sylow
  obtain ⟨g, hgT, hgc⟩ := ka6syl_central_conj hz T
  set B : Subgroup G := A.map (MulAut.conj k).toMonoidHom with hB
  have hBT : ∀ b ∈ B, b ∈ (T : Subgroup G) := by
    rintro _ ⟨a, ha, rfl⟩
    exact hT0T (hkA a ha)
  have hBJ : B ≤ J := by
    rintro _ ⟨a, ha, rfl⟩
    exact (mem_normalizer_iff.mp (hKN hkK) a).mp (hAJ ha)
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := CFSG.IsElementaryAbelian.map _
  have hBcard : Nat.card ↥B = 2 ^ 4 := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.conj k).injective, hcard]
  have hy2 : (g * z * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ← hz.1, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hmem : g * z * g⁻¹ ∈ B :=
    ka6syl_mem_of_commute hrank hBel hBcard hy2 fun b hb => hgc b (hBT b hb)
  exact ⟨g, hBJ hmem, (hgc z (hT0T (hzT0 (mem_zpowers z)))).symm⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
