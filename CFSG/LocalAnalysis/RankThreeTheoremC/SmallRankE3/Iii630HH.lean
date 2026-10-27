module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.HHModule
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Iii630Facts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.ABGLocalTools Subgroup

theorem kFactHallHigmanOdd_holds : KFactHallHigmanOdd := by
  intro K _ _ F V z f r hf hr hrf h5 hFe hV hVN hzN hz3 hzV hfix
  by_cases hF1 : F = ⊥
  · intro v _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ F := hh
    rw [hF1, Subgroup.mem_bot] at hh'
    rw [hh', one_mul, mul_one]
  have hf3 : f ≠ 3 := by
    intro h3
    subst h3
    have hF3 : IsPGroup 3 F := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro g
      exact ⟨1, Subtype.ext (by simpa using hFe.2 g.1 g.2)⟩
    have hZ : IsPGroup 3 (zpowers z) :=
      IsPGroup.of_card_dvd_pow (n := 1)
        (by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_of_pow_eq_one hz3)
    obtain ⟨a, haF, ha1, hafix⟩ :=
      exists_fixed_ne_one_of_isPGroup hf hZ hF3 hF1 (zpowers_le.mpr hzN)
    exact ha1 (hfix a haF (hafix z (mem_zpowers z)))
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hcomm : ∀ a b : F, a * b = b * a := fun a b => hFe.1.is_comm.comm a b
  have hexp : ∀ w : F, w ^ f = 1 := fun w => Subtype.ext (by simpa using hFe.2 w.1 w.2)
  obtain ⟨zN, hzNe⟩ : ∃ zN : normalizer (F : Set K), (zN : K) = z := ⟨⟨z, hzN⟩, rfl⟩
  have hz3N : zN ^ 3 = 1 := Subtype.ext (by simpa [hzNe] using hz3)
  have hxp : F.normalizerMonoidHom zN ^ 3 = 1 := by
    rw [← map_pow F.normalizerMonoidHom zN 3, hz3N, map_one]
  have hW : IsPGroup r (V.subgroupOf (normalizer (F : Set K))) := hV.comap_subtype
  have hS : IsPGroup r ((V.subgroupOf (normalizer (F : Set K))).map F.normalizerMonoidHom) :=
    hW.map F.normalizerMonoidHom
  have hzW : ∀ w ∈ V.subgroupOf (normalizer (F : Set K)),
      zN * w * zN⁻¹ ∈ V.subgroupOf (normalizer (F : Set K)) := by
    intro w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hzNe]
    exact (Subgroup.mem_normalizer_iff.1 hzV _).1 hw
  have hzW' : ∀ w ∈ V.subgroupOf (normalizer (F : Set K)),
      zN⁻¹ * w * zN ∈ V.subgroupOf (normalizer (F : Set K)) := by
    intro w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hzNe]
    refine (Subgroup.mem_normalizer_iff.1 hzV _).2 ?_
    rwa [show z * (z⁻¹ * (w : K) * z) * z⁻¹ = (w : K) by group]
  have hx : F.normalizerMonoidHom zN ∈ Subgroup.normalizer
      (((V.subgroupOf (normalizer (F : Set K))).map F.normalizerMonoidHom : Subgroup _) :
        Set (MulAut F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨zN * w * zN⁻¹, hzW w hw, by simp [map_mul, map_inv]⟩
    · rintro ⟨w', hw', hw'eq⟩
      refine ⟨zN⁻¹ * w' * zN, hzW' w' hw', ?_⟩
      rw [map_mul, map_mul, map_inv, hw'eq]
      group
  have hfixF : ∀ a : F, F.normalizerMonoidHom zN a = a → a = 1 := by
    intro a ha
    have h1 := congrArg Subtype.val ha
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hzNe] at h1
    exact Subtype.ext (hfix (a : K) a.2 h1)
  have hfixed := HHModule.kl_mulAut_gen (V := ↥F) hcomm
    (ℓ := f) hexp (p := 3) (q := r) (by norm_num) (by omega) (by omega) (Ne.symm hf3) hrf
    _ hS _ hx hxp hfixF
  intro v hv
  obtain ⟨vN, hvNe⟩ : ∃ vN : normalizer (F : Set K), (vN : K) = v := ⟨⟨v, hVN hv⟩, rfl⟩
  have hvS : F.normalizerMonoidHom vN ∈
      (V.subgroupOf (normalizer (F : Set K))).map F.normalizerMonoidHom :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (by rw [hvNe]; exact hv))
  have hcomm_eq := hfixed _ hvS
  have hc : F.normalizerMonoidHom (zN * vN * zN⁻¹ * vN⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm_eq]
    group
  have hcK : ∀ a : F, z * v * z⁻¹ * v⁻¹ * (a : K) * (z * v * z⁻¹ * v⁻¹)⁻¹ = (a : K) := by
    intro a
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hc a)
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, hzNe, hvNe] at h1
    exact h1
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (mul_inv_eq_iff_eq_mul.mp (hcK ⟨h, hh⟩)).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
