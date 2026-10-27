module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCSp48
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGamma
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.Adapters.CatalogueFieldBridges.Symplectic
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCSp48Syl
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

namespace Sp48

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F (F8)
open Subgroup

theorem wS_sq : wS * wS = 1 := Subtype.ext (Units.ext wmat_mul_self)

theorem Jg_sq : Jg * Jg = 1 := Units.ext jmat_mul_self

theorem dS_sq : dS * dS = 1 := by
  apply Subtype.ext
  show psi (Jg, 1) * psi (Jg, 1) = 1
  rw [← map_mul, Prod.mk_mul_mk, Jg_sq, one_mul]
  exact map_one psi

theorem fuse_T0_sq {a : ↥(StatedSp 2 F8)} (ha : a ∈ T0) (ha3 : orderOf a = 3) :
    ∃ n : ↥(StatedSp 2 F8), n * n = 1 ∧ n * a * n⁻¹ ∈ T0 ∧ n * a * n⁻¹ ∉ zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := mem_T0_iff.1 ha
  have hxy' : ((a : GL Ix F8)) = psi (x, y) := hxy.symm
  have hord : orderOf (x, y) = 3 := by
    rw [← orderOf_injective psi psi_injective, ← hxy', Subgroup.orderOf_coe, ha3]
  have hp3 : (x, y) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (x, y)
    rwa [hord] at h
  have hx3 : x ^ 3 = 1 := congrArg Prod.fst hp3
  have hy3 : y ^ 3 = 1 := congrArg Prod.snd hp3
  have h1 : (x, y) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hzp : ∀ s ∈ zpowers a, ∃ k : ℤ, (s : GL Ix F8) = psi (x ^ k, y ^ k) := by
    intro s hs
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs
    refine ⟨k, ?_⟩
    rw [Subgroup.coe_zpow, hxy', ← map_zpow]
    exact congrArg psi (Prod.ext (by simp) (by simp))
  have hsub : ∀ {s : ↥(StatedSp 2 F8)} {p : GL (Fin 2) F8 × GL (Fin 2) F8},
      (s : GL Ix F8) = psi p → p.1 ∈ zpowers Ag → p.2 ∈ zpowers Ag → s ∈ T0 := by
    intro s p hs h1 h2
    exact mem_T0_iff.2 (hs ▸ ⟨p, ⟨h1, h2⟩, rfl⟩)
  by_cases hy1 : y = 1
  ·
    subst hy1
    have hx1 : x ≠ 1 := fun h => h1 (by rw [h]; rfl)
    have hc : ((wS * a * wS⁻¹ : ↥(StatedSp 2 F8)) : GL Ix F8) = psi (1, x) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, wS]
      rw [hxy', wU_conj]
    refine ⟨wS, wS_sq, hsub hc (one_mem _) hx, fun hm => ?_⟩
    obtain ⟨k, hk⟩ := hzp _ hm
    rw [hc] at hk
    have := congrArg Prod.snd (psi_injective hk)
    simp only [_root_.one_zpow] at this
    exact hx1 this
  by_cases hx1 : x = 1
  · subst hx1
    have hc : ((wS * a * wS⁻¹ : ↥(StatedSp 2 F8)) : GL Ix F8) = psi (y, 1) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, wS]
      rw [hxy', wU_conj]
    refine ⟨wS, wS_sq, hsub hc hy (one_mem _), fun hm => ?_⟩
    obtain ⟨k, hk⟩ := hzp _ hm
    rw [hc] at hk
    have := congrArg Prod.fst (psi_injective hk)
    simp only [_root_.one_zpow] at this
    exact hy1 this
  ·
    have hc : ((dS * a * dS⁻¹ : ↥(StatedSp 2 F8)) : GL Ix F8) = psi (x⁻¹, y) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, dS]
      rw [hxy', ← map_inv, ← map_mul, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk,
        Jg_conj_mem hx, inv_one, one_mul, mul_one]
    refine ⟨dS, dS_sq, hsub hc (inv_mem hx) hy, fun hm => ?_⟩
    obtain ⟨k, hk⟩ := hzp _ hm
    rw [hc] at hk
    have hp := psi_injective hk
    have hxk : x⁻¹ = x ^ k := congrArg Prod.fst hp
    have hyk : y = y ^ k := congrArg Prod.snd hp
    have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hy' : y ^ (k - 1) = 1 := by rw [_root_.zpow_sub_one, ← hyk, mul_inv_cancel]
    have h3 : (3 : ℤ) ∣ k - 1 := by
      have := orderOf_dvd_iff_zpow_eq_one.2 hy'
      rwa [hoy] at this
    have hx' : x ^ (k - 1) = 1 := by
      have h3' : ((orderOf x : ℕ) : ℤ) ∣ k - 1 := by rw [hox]; exact_mod_cast h3
      exact orderOf_dvd_iff_zpow_eq_one.1 h3'
    have hxk1 : x ^ k = x := by
      calc x ^ k = x ^ (k - 1) * x := by rw [← zpow_add_one, sub_add_cancel]
        _ = x := by rw [hx', one_mul]
    have hxx : x⁻¹ = x := hxk.trans hxk1
    have hx2 : x * x = 1 := by
      nth_rewrite 2 [← hxx]
      exact mul_inv_cancel x
    have : x = 1 := by
      calc x = x ^ 3 * (x * x)⁻¹ := by group
        _ = 1 := by rw [hx3, hx2, inv_one, one_mul]
    exact hx1 this

end Sp48

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F Sp48 in
theorem kFactTenNineWCGammaSp48 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal], IsSpFourEight K →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ hK S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨d1, hv⟩, ⟨q, hqp, hqe, hd1⟩, ⟨e⟩⟩ := hK
  change d1 = _ at hd1
  subst hd1
  have hKc : Nat.card K = 3 ^ 4 * 13045760 := by
    rcases CFSG.Models.lieModel_B 2 q hv e with hL | hL
    · rw [hqp, hqe] at hL
      have hM := CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num)
        (CFSG.Models.LieModel.toBlueprint (by decide) hL)
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.1 rfl]
      decide
    · rw [hqp] at hL
      exact absurd hL.1.2.2.2 (by simp)
  have hk : Nat.card F8 = q.card := by
    rw [TauCeti.PrimePower.card_def, hqp, hqe, card_F8]
    norm_num
  obtain ⟨eT⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj hv hk
  set eK : K ≃* TF := e.trans eT.symm
  set eS : K ≃* ↥(StatedSp 2 F8) := eK.trans eQ
  have hZK : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1 := by
    haveI hs : IsSimpleGroup TF := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
      F8 2 (by norm_num) (Or.inl (Or.inr (by rw [card_F8]; norm_num)))
    have hZ : Subgroup.center TF = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center TF) with h | h
      · exact h
      · exfalso
        have hc : IsMulCommutative TF := Subgroup.center_eq_top_iff.mp h
        have hp := Group.is_simple_iff_prime_card.mp hs
        rw [← Nat.card_congr eK.toEquiv, hKc] at hp
        norm_num at hp
    intro k hk
    have hc : eK k ∈ Subgroup.center TF := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg eK (hk (eK.symm y))
      simpa using this.symm
    rw [hZ, Subgroup.mem_bot] at hc
    exact eK.injective (by rw [hc, map_one])
  have hfac : (Nat.card K).factorization 3 = 4 := by rw [hKc]; exact factorization_sp48
  refine false_of_fuse_gamma hZK ?_ ?_ S A hA3 Y hY hwc
  ·
    intro T φ hφ hfix
    set β : MulAut TF := MulAut.congr eK φ
    have hβ : β ^ 3 = 1 := by rw [← map_pow, hφ, map_one]
    have hT : Nat.card ((T : Subgroup K).map eK.toMonoidHom) = 81 := by
      rw [Subgroup.card_map_of_injective eK.injective, T.card_eq_multiplicity, hfac]
      norm_num
    have hfixβ : ∀ t ∈ (T : Subgroup K).map eK.toMonoidHom, β t = t := by
      rintro _ ⟨t, ht, rfl⟩
      simp [β, MulAut.congr_apply, hfix t ht]
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (sp48_inner_of_fix β hβ _ hT hfixβ)
    refine ⟨eK.symm g, fun x => eK.injective ?_⟩
    have h1 : β (eK x) = eK (φ x) := by simp [β, MulAut.congr_apply]
    rw [← h1, ← hg, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  ·
    intro T a haT hoa _
    refine gamma_of_fuse_sq haT hoa ?_
    have hidx : ¬ 3 ∣ T0.index := by
      have h := T0.card_mul_index
      rw [card_T0, ← Nat.card_congr eS.toEquiv, hKc] at h
      have : T0.index = 13045760 := by omega
      rw [this]
      norm_num
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow eS
      (IsPGroup.of_card (card_T0.trans (by norm_num : (81 : ℕ) = 3 ^ 4))) hidx T
    rw [hΦ] at haT ⊢
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp haT
    have ha03 : orderOf a0 = 3 := by
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hoa
      exact hoa
    obtain ⟨n0, hn0sq, hn0T, hn0⟩ := fuse_T0_sq ha0 ha03
    refine ⟨Φ n0, by rw [← map_mul, hn0sq, map_one], ⟨n0 * a0 * n0⁻¹, hn0T, ?_⟩, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    · intro hm
      apply hn0
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Φ.injective ?_⟩
      rw [map_zpow, map_mul, map_mul, map_inv]
      simpa using hk

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
