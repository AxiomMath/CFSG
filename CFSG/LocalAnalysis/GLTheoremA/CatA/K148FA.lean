module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I148XOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2A
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

variable {G : Type} [Group G] [Finite G]

theorem k148f_setup {X K : Subgroup G} (hK : GLAPComponent 3 X K) (hTD4 : IsTD4 3 K)
    (hchev : IsChevSimple 2 (PSimple 3 K)) :
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧ Subgroup.center (PQuot 3 K) = ⊥ ∧
      catalogIs (PQuot 3 K) (CFSG.LocalAnalysis.GLTheoremA.I2023.isTD4Of q) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨q, hv, ⟨eS⟩⟩ := td4_index hTD4
  have hq2 : q.p = 2 := td4g2_p_two hv eS hchev
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent hp3 hK
  have hm : CFSG.Models.LieModel (PQuot 3 K ⧸ Subgroup.center (PQuot 3 K)) .trialityD4 0 q.p
      q.exponent :=
    CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ eS
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl
    (by norm_num)
  have hc1 : Nat.card (Subgroup.center (PQuot 3 K)) = 1 := Nat.dvd_one.1 (by simpa using hdvd)
  have hcenter : Subgroup.center (PQuot 3 K) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  have eQS : PQuot 3 K ≃* PSimple 3 K :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  exact ⟨q, hq2, hcenter, TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩, rfl, ⟨eQS.trans eS⟩⟩

theorem k148f_inner {X K : Subgroup G} (hK : GLAPComponent 3 X K) (hTD4 : IsTD4 3 K) {y : G}
    (hyK : InnDiagOn 3 (Subgroup.zpowers y) K) : InducesInnerMod 3 K y := by
  by_contra hne
  exact (MI.td4_nonInnDiag_any hK hTD4 ⟨hyK.1 (Subgroup.mem_zpowers y), hne⟩).2 hyK

theorem k148f_elem {K : Subgroup G} {y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hin : InducesInnerMod 3 K y) :
    ∃ c : PQuot 3 K, MulAut.conj c = CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩ := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 ((inducesInnerMod_iff_barAut_mem_inner hyN).1 hin)
  exact ⟨c, hc⟩

theorem k148f_barAut_pow_three {K : Subgroup G} {y : G} (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hy3 : y ^ 3 = 1) : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have h3 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext hy3
  rw [h3, map_one]

theorem k148f_pow_three {K : Subgroup G} (hcenter : Subgroup.center (PQuot 3 K) = ⊥) {y : G}
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hy3 : y ^ 3 = 1) {c : PQuot 3 K}
    (hc : MulAut.conj c = CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩) : c ^ 3 = 1 := by
  have h3 : MulAut.conj (c ^ 3) = 1 := by
    rw [map_pow, hc, k148f_barAut_pow_three hyN hy3]
  have hmem : c ^ 3 ∈ Subgroup.center (PQuot 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun φ : MulAut (PQuot 3 K) => φ g) h3
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    exact (mul_inv_eq_iff_eq_mul.1 hg).symm
  rw [hcenter] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem k148f_conj_inj {Q : Type} [Group Q] (hZ : Subgroup.center Q = ⊥) {a b : Q}
    (h : MulAut.conj a = MulAut.conj b) : a = b := by
  have hz : ∀ g : Q, (b⁻¹ * a) * g = g * (b⁻¹ * a) := by
    intro g
    have hg := congrArg (fun φ : MulAut Q => φ g) h
    simp only [MulAut.conj_apply] at hg
    have hb : b⁻¹ * (a * g * a⁻¹) * b = g := by rw [hg]; group
    calc (b⁻¹ * a) * g = (b⁻¹ * (a * g * a⁻¹) * b) * (b⁻¹ * a) := by group
      _ = g * (b⁻¹ * a) := by rw [hb]
  have hc : b⁻¹ * a ∈ Subgroup.center Q := Subgroup.mem_center_iff.2 fun g => (hz g).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem k148f_comm_fix {K : Subgroup G} (hcenter : Subgroup.center (PQuot 3 K) = ⊥) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    (hxy : x * y = y * x) {c : PQuot 3 K}
    (hc : MulAut.conj c = CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩) :
    CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ c = c := by
  have hcomm : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ *
      CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩ =
      CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨y, hyN⟩ *
        CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxy
  have hcomm' : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ * MulAut.conj c =
      MulAut.conj c * CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ := by
    rw [hc]
    exact hcomm
  have key : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ * MulAut.conj c =
      MulAut.conj (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ c) *
        CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ := by
    refine MulEquiv.ext fun g => ?_
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have h2 : MulAut.conj c * CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ =
      MulAut.conj (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ c) *
        CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩ :=
    hcomm'.symm.trans key
  exact k148f_conj_inj hcenter (mul_right_cancel h2).symm

end CFSG.LocalAnalysis.GLTheoremA.K148F

end
