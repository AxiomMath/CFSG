module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Syl
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6L0
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6PSp

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ABGLocalTools

namespace Cat7E6

open CatFactsSp4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

theorem factorization_two_pow_mul_odd {k c : ℕ} (hc : Odd c) : (2 ^ k * c).factorization 2 = k := by
  rw [Nat.factorization_mul (by positivity) hc.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]),
    add_zero]

theorem sq_add_one_eq {q : ℕ} (hq : Odd q) : ∃ d, Odd d ∧ q ^ 2 + 1 = 2 * d := by
  obtain ⟨k, rfl⟩ := hq
  refine ⟨2 * k ^ 2 + 2 * k + 1, ⟨k ^ 2 + k, by ring⟩, by ring⟩

theorem pow_four_sub_one {q : ℕ} (hq : 1 ≤ q) : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  zify [h1, h2]
  ring

variable {K : Type} [Field K]

theorem card_innA_P [Finite K] (hodd : Odd (Nat.card K)) {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα2 : α * α = 1) (hout : α ∉ Cat8.Inn (StatedProj (StatedSp 2 K))) :
    Nat.card (Cat8.innA (StatedProj (StatedSp 2 K)) α) =
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
  have hc : ∀ z : StatedProj (StatedSp 2 K), z ∈ center _ → z = 1 :=
    fun z hz => center_P_eq_one hodd hz
  have : (Cat8.Inn (StatedProj (StatedSp 2 K))).Normal := inn_normal
  have hrel := relIndex_sup_zpowers hα2 hout
  have h1 := Subgroup.relIndex_mul_card (H := Cat8.Inn (StatedProj (StatedSp 2 K)))
    (K := Cat8.innA (StatedProj (StatedSp 2 K)) α)
  rw [hrel, inf_of_le_left le_sup_left] at h1
  have hI : Nat.card (Cat8.Inn (StatedProj (StatedSp 2 K))) =
      Nat.card (StatedProj (StatedSp 2 K)) :=
    (Nat.card_congr (MonoidHom.ofInjective (f := (MulAut.conj : _ →* MulAut _))
      fun g h hgh => conj_injective_of_center hc hgh).toEquiv).symm
  rw [← h1, hI, mul_comm, two_mul_card_P (two_ne_zero_of_odd_card hodd)]

theorem sect_model [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (c : Cat8.QConf (StatedProj (StatedSp 2 K)) (p ^ f))
    {R : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hRN : R ≤ Cat8.innA (StatedProj (StatedSp 2 K)) c.a) (hR2 : IsPGroup 2 R) :
    (∃ s : Finset (MulAut (StatedProj (StatedSp 2 K))), s.card ≤ 4 ∧
      closure (s : Set (MulAut (StatedProj (StatedSp 2 K)))) = R) ∧
      Nat.card R ≤ 2 * Nat.card c.D ^ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StatedProj (StatedSp 2 K))) :=
    Finite.of_injective (fun φ : MulAut (StatedProj (StatedSp 2 K)) => (φ : _ → _))
      (fun φ ψ h => MulEquiv.ext (congrFun h))
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  set q := Nat.card K with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')
  obtain ⟨m, c', u, v, hm3, hc', hqm, horho, hv, hv2⟩ := exists_uv hodd
  obtain ⟨d, hd, hqd⟩ := sq_add_one_eq hodd
  set N := Cat8.innA (StatedProj (StatedSp 2 K)) c.a with hNdef
  have hNcard : Nat.card N = 2 ^ (2 * m + 1) * (q ^ 4 * (c' * c' * d)) := by
    rw [hNdef, card_innA_P hodd c.adm.sq c.adm.out, pow_four_sub_one hq1, hqm, hqd]
    ring
  have hNodd : Odd (q ^ 4 * (c' * c' * d)) := (hodd.pow).mul ((hc'.mul hc').mul hd)
  have hNeq : N = (conjAut 2 K).range := innA_eq_range hp hp2 hf (hqdef ▸ hK) c.adm
  have ho4 : 4 ≤ orderOf (rho u) := by
    rw [horho]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set W := W3 u v hv ⊔ zpowers (a4 v hv) with hWdef
  have hWcard : Nat.card W = 2 ^ (2 * m + 1) := by
    rw [hWdef, card_W4 u v hv h2 ho4 hv2, horho, ← pow_add,
      show 8 = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega
  have hWN : W ≤ N := by
    rw [hNeq]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rw [zpowers_le]
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have hWsyl : IsSylowOf 2 W N := by
    rw [isSylowOf_iff]
    refine ⟨hWN, IsPGroup.of_card hWcard, ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := W) (K := N)
    rw [inf_of_le_left hWN, hWcard, hNcard, mul_comm] at h1
    have h3 : W.relIndex N = q ^ 4 * (c' * c' * d) :=
      Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h3, ← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hNodd
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨k, -, hk⟩ := FooteLit.exists_conj_le_of_isSylowOf hWsyl hRN hR2
    set R' := R.map (MulAut.conj k⁻¹).toMonoidHom with hR'
    have hR'W : R' ≤ zpowers (a1 u) ⊔ zpowers (a2 u) ⊔ zpowers (a3 v hv) ⊔ zpowers (a4 v hv) := by
      rintro _ ⟨x, hx, rfl⟩
      have := hk x hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact this
    obtain ⟨s', hs', hcl⟩ := exists_finset_card_le_four (a2_mem_normalizer u)
      (a3_mem_normalizer u v hv) (a4_mem_normalizer u v hv hv2) hR'W
    refine ⟨s'.image (MulAut.conj k), (Finset.card_image_le).trans hs', ?_⟩
    rw [Finset.coe_image, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure, hcl, hR',
      Subgroup.map_map]
    ext x
    simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [show k * (k⁻¹ * y * k) * k⁻¹ = y by group]
    · intro hx
      exact ⟨x, hx, by group⟩
  ·
    obtain ⟨j, hj⟩ := hR2.exists_card_eq
    have hdvd : 2 ^ j ∣ 2 ^ (2 * m + 1) := by
      have h1 : Nat.card R ∣ Nat.card N := Subgroup.card_dvd_of_le hRN
      rw [hj, hNcard] at h1
      exact (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hNodd)).dvd_of_dvd_mul_right h1
    have hjle : j ≤ 2 * m + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    obtain ⟨A, hA, d₀, hd0, hdsq, hAA, hμ⟩ := admissible_data hp hp2 hf (hqdef ▸ hK) c.adm
    obtain ⟨hQ, hcardC⟩ := fixOf_conjSp_nonsquare hp hp2 hf (hqdef ▸ hK) A hd0 hdsq hAA hμ
    have hL0 := card_L0 hodd A hQ.1
    rw [hcardC, ← hA] at hL0
    have hL0' : Nat.card (Cat8.L0 (StatedProj (StatedSp 2 K)) c.a) = 2 ^ m * (q ^ 2 * c' * d) := by
      have e : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) = (2 ^ m * (q ^ 2 * c' * d)) * 2 := by
        rw [← hK, show (q ^ 2) ^ 2 = q ^ 4 by ring, pow_four_sub_one hq1, hqm, hqd]
        ring
      rw [e] at hL0
      exact Nat.eq_of_mul_eq_mul_right two_pos hL0
    have hD : Nat.card c.D = 2 ^ m := by
      rw [(isSylowOf_D c).card_eq, hL0', factorization_two_pow_mul_odd
        (((hodd.pow).mul hc').mul hd)]
    rw [hj, hD, ← pow_mul, ← pow_succ']
    calc 2 ^ j ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) hjle
      _ = 2 ^ (m * 2 + 1) := by rw [mul_comm]

end Cat7E6

open Cat7E6 in
theorem cf81E6SectPSp : CF81E6SectPSp := by
  classical
  intro K₀ _ _ p f hp hp2 hf hL c R hRN hR2
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hL
  set Φ := MulAut.congr e with hΦ
  have hRN' : R.map Φ.toMonoidHom ≤ Cat8.innA _ (qConfCongr e c).a := by
    rw [qConfCongr_a, ← map_innA]
    exact Subgroup.map_mono hRN
  obtain ⟨⟨s', hs', hcl⟩, hcard⟩ := sect_model hp hp2 hf hK (qConfCongr e c) hRN'
    (hR2.map Φ.toMonoidHom)
  refine ⟨⟨s'.image Φ.symm, (Finset.card_image_le).trans hs', ?_⟩, ?_⟩
  · rw [Finset.coe_image, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure, hcl,
      Subgroup.map_map]
    ext x
    simp
  · rw [qConfCongr_D, Subgroup.card_map_of_injective Φ.injective,
      Subgroup.card_map_of_injective Φ.injective] at hcard
    exact hcard

end CFSG.ComponentClassification.GSThmB
