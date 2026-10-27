module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Torus
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Classes
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)
open scoped commutatorElement Matrix

section UnipHm

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem eq_d4x₄_of_commute_hm
    [Finite K] [CharP K 2] (hσ3 : σ.toRingHom ^ 3 = 1)
    {β : (trialityFixedField K σ.toRingHom)ˣ} (hβ : β ≠ 1) {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (hc : trialityMiddleTorus K σ β * u = u * trialityMiddleTorus K σ β) :
    ∃ d : K, u = d4x₄ K σ d := by
  obtain ⟨a, b, c, d, e, f, -, -, -, rfl⟩ := exists_d4coord σ hσ3 hu
  set μ : K := ((trialityFixedUnit K σ β : Kˣ) : K) with hμdef
  have hμ1 : μ ≠ 1 := by
    intro h
    apply hβ
    exact Units.ext (Subtype.ext h)
  have hμi : μ⁻¹ ≠ 1 := fun h => hμ1 (inv_eq_one.1 h)
  have hμ2 : μ ^ 2 ≠ 1 := fun h => hμ1 (CharTwo.sq_injective (show μ ^ 2 = 1 ^ 2 by rw [h,
      one_pow]))
  have hconj : trialityMiddleTorus K σ β * (d4x₁ K σ a * d4v K σ b c d e f) *
      (trialityMiddleTorus K σ β)⁻¹ =
        d4x₁ K σ (μ⁻¹ * a) * d4v K σ (μ ^ 2 * b) (μ * c) d (μ⁻¹ * e) (μ * f) := by
    rw [show trialityMiddleTorus K σ β * (d4x₁ K σ a * d4v K σ b c d e f) *
        (trialityMiddleTorus K σ β)⁻¹ =
          (trialityMiddleTorus K σ β * d4x₁ K σ a * (trialityMiddleTorus K σ β)⁻¹) *
            (trialityMiddleTorus K σ β * d4v K σ b c d e f * (trialityMiddleTorus K σ β)⁻¹) by
        group, hm_conj_d4x₁, hm_conj_d4v]
  have hfix : trialityMiddleTorus K σ β * (d4x₁ K σ a * d4v K σ b c d e f) *
      (trialityMiddleTorus K σ β)⁻¹ = d4x₁ K σ a * d4v K σ b c d e f := by
    rw [hc, mul_inv_cancel_right]
  obtain ⟨ha, hb, hc', -, he, hf⟩ := d4coord_injective σ (hconj.symm.trans hfix)
  rw [eq_zero_of_mul_eq_self_d4 hμi ha, eq_zero_of_mul_eq_self_d4 hμ2 hb,
    eq_zero_of_mul_eq_self_d4 hμ1 hc', eq_zero_of_mul_eq_self_d4 hμi he,
    eq_zero_of_mul_eq_self_d4 hμ1 hf, d4x₁_zero, one_mul]
  exact ⟨d, (d4x₄_eq_d4v σ d).symm⟩

end UnipHm

section WeylHm

open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

abbrev d4Wv : WeylGroup TwistTag.D4.tag :=
  TwistTag.D4.orbitReflection ⟨0, by decide⟩ * TwistTag.D4.orbitReflection ⟨1, by decide⟩ *
    TwistTag.D4.orbitReflection ⟨0, by decide⟩ * TwistTag.D4.orbitReflection ⟨1, by decide⟩ *
      TwistTag.D4.orbitReflection ⟨0, by decide⟩

theorem d4Wv_mem :
    d4Wv ∈ relWeylTwist TwistTag.D4 :=
  mul_mem (mul_mem (mul_mem (mul_mem (TwistTag.D4.orbitReflection_mem _)
    (TwistTag.D4.orbitReflection_mem _)) (TwistTag.D4.orbitReflection_mem _))
      (TwistTag.D4.orbitReflection_mem _)) (TwistTag.D4.orbitReflection_mem _)

@[expose] def d4HmExp (v : Fin TwistTag.D4.tag.rank → ℤ) : ℤ :=
  2 * v ⟨2, by decide⟩ - v ⟨0, by decide⟩ - v ⟨1, by decide⟩ - v ⟨3, by decide⟩

theorem d4HmExp_add (u v : Fin TwistTag.D4.tag.rank → ℤ) :
    d4HmExp (u + v) = d4HmExp u + d4HmExp v := by
  simp only [d4HmExp, Pi.add_apply]
  ring

theorem d4HmExp_permLattice (v : Fin TwistTag.D4.tag.rank → ℤ) :
    d4HmExp (permLattice TwistTag.D4.perm v) = d4HmExp v := by
  have h0 : permLattice TwistTag.D4.perm v ⟨0, by decide⟩ = v ⟨3, by decide⟩ := rfl
  have h1 : permLattice TwistTag.D4.perm v ⟨1, by decide⟩ = v ⟨0, by decide⟩ := rfl
  have h2 : permLattice TwistTag.D4.perm v ⟨2, by decide⟩ = v ⟨2, by decide⟩ := rfl
  have h3 : permLattice TwistTag.D4.perm v ⟨3, by decide⟩ = v ⟨1, by decide⟩ := rfl
  simp only [d4HmExp, h0, h1, h2, h3]
  ring

theorem rootChar_hm_d4 {K : Type} [Field K] (μ : Kˣ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (d4Tuple μ⁻¹ μ⁻¹ (μ ^ 2) μ⁻¹) v = μ ^ d4HmExp v := by
  rw [rootChar_d4Tuple μ⁻¹ μ⁻¹ (μ ^ 2) μ⁻¹ (v ⟨0, by decide⟩) (v ⟨1, by decide⟩)
    (v ⟨2, by decide⟩) (v ⟨3, by decide⟩) (by funext i; fin_cases i <;> rfl)]
  rw [inv_zpow', inv_zpow', inv_zpow', ← zpow_natCast μ 2, ← zpow_mul, ← zpow_add, ← zpow_add,
    ← zpow_add, d4HmExp]
  congr 1
  push_cast
  ring

theorem foldMap_alpha₂ : TwistTag.D4.foldMap g2r = Pi.single ⟨2, by decide⟩ 1 := by
  decide +kernel

theorem d4SumBar_eq : d4SumBar = g2c := by
  funext i
  fin_cases i <;> rfl

theorem smul_permLattice_of_mem
    {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    w • permLattice TwistTag.D4.perm v = permLattice TwistTag.D4.perm (w • v) := by
  have h := weylTwist_smul_permLattice TwistTag.D4 w v
  rwa [(mem_relWeylTwist TwistTag.D4).1 hw] at h

theorem three_mul_d4HmExp
    {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) :
    3 * d4HmExp (w • trialityRoot 3) = d4HmExp (w • d4Sum4) := by
  rw [d4Sum4, smul_add, smul_add, ← permLattice_D4_perm_perm, smul_permLattice_of_mem hw,
    smul_permLattice_of_mem hw, smul_permLattice_of_mem hw, d4HmExp_add, d4HmExp_add,
    d4HmExp_permLattice, d4HmExp_permLattice, d4HmExp_permLattice]
  ring

theorem eq_one_of_zpow_d4 {K : Type} [Field K] [CharP K 2] {μ : Kˣ} {n : ℤ}
    (hn : n = 1 ∨ n = -1 ∨ n = 4 ∨ n = -4) (h : μ ^ n = 1) : μ = 1 := by
  have sq1 : ∀ x : Kˣ, x ^ 2 = 1 → x = 1 := fun x hx => Units.ext
    (CharTwo.sq_injective (show (x : K) ^ 2 = (1 : K) ^ 2 by
      rw [one_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one]))
  have h4 : μ ^ (4 : ℕ) = 1 → μ = 1 := fun h4 => sq1 μ (sq1 (μ ^ 2) (by rw [← pow_mul]; exact h4))
  rcases hn with rfl | rfl | rfl | rfl
  · simpa using h
  · simpa using h
  · exact h4 (by exact_mod_cast h)
  · exact h4 (by
      have : (μ ^ (4 : ℤ))⁻¹ = 1 := by rw [← zpow_neg]; exact h
      exact_mod_cast inv_eq_one.1 this)

theorem g2_wv_smul :
    (simple .G2 g2ia * simple .G2 g2ir * simple .G2 g2ia * simple .G2 g2ir * simple .G2 g2ia) •
        g2a = -g2b ∧
      (simple .G2 g2ia * simple .G2 g2ir * simple .G2 g2ia * simple .G2 g2ir *
        simple .G2 g2ia) • g2r = g2r := by
  simp only [mul_smul, simple_smul]
  exact ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

theorem foldedWeylEquiv_d4Wv :
    foldedWeylEquiv TwistTag.D4 ⟨d4Wv, d4Wv_mem⟩ =
      simple .G2 g2ia * simple .G2 g2ir * simple .G2 g2ia * simple .G2 g2ir * simple .G2 g2ia := by
  have h : (⟨d4Wv, d4Wv_mem⟩ : relWeylTwist TwistTag.D4) =
      ⟨_, TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩⟩ *
        ⟨_, TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩⟩ *
        ⟨_, TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩⟩ *
        ⟨_, TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩⟩ *
        ⟨_, TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩⟩ := rfl
  rw [h, map_mul, map_mul, map_mul, map_mul, foldedWeylEquiv_orbitReflection,
    foldedWeylEquiv_orbitReflection]
  rfl

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem weyl_eq_of_commute_hm
    [CharP K 2] {β : (trialityFixedField K σ.toRingHom)ˣ}
    (hβ : β ≠ 1) {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    (hc : trialityMiddleTorus K σ β * canonicalRep (coxeterSystem TwistTag.D4.tag) K w =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * trialityMiddleTorus K σ β) :
    w = 1 ∨ w = d4Wv := by
  set μ : Kˣ := trialityFixedUnit K σ β with hμ
  have hμ1 : μ ≠ 1 := fun h => hβ (Units.ext (Subtype.ext (congrArg Units.val h)))
  rw [trialityMiddleTorus_eq_rootDiagUnit] at hc
  have hstab := (conj_canonicalRep_eq_iff _ w).1 (by rw [hc, mul_inv_cancel_right])
  have hexp : ∀ v, μ ^ (d4HmExp (w • v) - d4HmExp v) = 1 := fun v => by
    have h1 := hstab v
    rw [← hμ, rootChar_hm_d4, rootChar_hm_d4] at h1
    rw [zpow_sub, h1, mul_inv_cancel]
  have h2 := hexp (Pi.single ⟨2, by decide⟩ 1)
  have h4 := hexp (trialityRoot 3)
  have h43 := three_mul_d4HmExp hw
  set w' : relWeylTwist TwistTag.D4 := ⟨w, hw⟩ with hw'
  set W : WeylGroup .G2 := foldedWeylEquiv TwistTag.D4 w' with hW
  have hf2 : w • (Pi.single ⟨2, by decide⟩ 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      TwistTag.D4.foldMap (W • g2r) := by
    rw [← foldMap_alpha₂]
    exact smul_foldMap_foldedWeylEquiv (t := TwistTag.D4) w' _
  have hf4 : w • d4Sum4 = TwistTag.D4.foldMap (W • g2c) := by
    rw [← foldMap_sumBar, d4SumBar_eq]
    exact smul_foldMap_foldedWeylEquiv (t := TwistTag.D4) w' _
  rw [hf2] at h2
  rw [hf4, smul_g2c] at h43
  have hα₂ : d4HmExp (Pi.single ⟨2, by decide⟩ 1) = 2 := by decide +kernel
  have hα₄ : d4HmExp (trialityRoot 3) = 0 := by decide +kernel
  rw [hα₂] at h2
  rw [hα₄, sub_zero] at h4
  rcases g2_weyl_cases W with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩
  · left
    have : w' = 1 := (foldedWeylEquiv TwistTag.D4).injective (by
      rw [map_one]
      exact eq_one_of_smul ha hr)
    exact congrArg Subtype.val this
  · exfalso
    rw [ha, hr, show d4HmExp (TwistTag.D4.foldMap (-g2a + -g2a + (g2u + g2u + g2u))) = 3 by
      decide +kernel] at h43
    rw [show d4HmExp (w • trialityRoot 3) = 1 by omega] at h4
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h4)
  · exfalso
    rw [hr, show d4HmExp (TwistTag.D4.foldMap (-g2r)) - 2 = -4 by decide +kernel] at h2
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h2)
  · exfalso
    rw [hr, show d4HmExp (TwistTag.D4.foldMap (-g2u)) - 2 = -1 by decide +kernel] at h2
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h2)
  · exfalso
    rw [hr, show d4HmExp (TwistTag.D4.foldMap (g2v)) - 2 = -1 by decide +kernel] at h2
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h2)
  · exfalso
    rw [hr, show d4HmExp (TwistTag.D4.foldMap (g2v)) - 2 = -1 by decide +kernel] at h2
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h2)
  · exfalso
    rw [ha, hr, show d4HmExp (TwistTag.D4.foldMap (g2c + g2c + (-g2v + -g2v + -g2v))) = -3 by
      decide +kernel] at h43
    rw [show d4HmExp (w • trialityRoot 3) = -1 by omega] at h4
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h4)
  · exfalso
    rw [ha, hr, show d4HmExp (TwistTag.D4.foldMap (-g2c + -g2c + (g2u + g2u + g2u))) = -3 by
      decide +kernel] at h43
    rw [show d4HmExp (w • trialityRoot 3) = -1 by omega] at h4
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h4)
  · exfalso
    rw [ha, hr, show d4HmExp (TwistTag.D4.foldMap (g2b + g2b + (-g2v + -g2v + -g2v))) = 3 by
      decide +kernel] at h43
    rw [show d4HmExp (w • trialityRoot 3) = 1 by omega] at h4
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h4)
  rotate_left
  · exfalso
    rw [hr, show d4HmExp (TwistTag.D4.foldMap (-g2u)) - 2 = -1 by decide +kernel] at h2
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h2)
  · exfalso
    rw [hr, show d4HmExp (TwistTag.D4.foldMap (-g2r)) - 2 = -4 by decide +kernel] at h2
    exact hμ1 (eq_one_of_zpow_d4 (by norm_num) h2)
  right
  obtain ⟨hva, hvr⟩ := g2_wv_smul
  have hw1 : foldedWeylEquiv TwistTag.D4 w' = foldedWeylEquiv TwistTag.D4 ⟨d4Wv, d4Wv_mem⟩ := by
    rw [foldedWeylEquiv_d4Wv]
    change W = _
    have h := eq_one_of_smul (w := (simple .G2 g2ia * simple .G2 g2ir * simple .G2 g2ia *
        simple .G2 g2ir * simple .G2 g2ia)⁻¹ * W)
      (by rw [mul_smul, ha, inv_smul_eq_iff, hva])
      (by rw [mul_smul, hr, inv_smul_eq_iff, hvr])
    exact (inv_mul_eq_one.1 h).symm
  exact congrArg Subtype.val ((foldedWeylEquiv TwistTag.D4).injective hw1)

end WeylHm

section RankOne

variable {K : Type} [Field K] (σ : K ≃+* K)

omit [Field K] in
theorem mem_orbitField_zero_d4 {K : Type} [Field K] {σ : K ≃+* K} (hσ3 : σ.toRingHom ^ 3 = 1)
    (c : K) : c ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ := by
  rw [mem_orbitField, show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide]
  exact congrArg (fun φ : K →+* K => φ c) hσ3

@[expose] noncomputable def d4OuterIncl (hσ3 : σ.toRingHom ^ 3 = 1) :
    K →+* orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ :=
  (RingHom.id K).codRestrict _ (mem_orbitField_zero_d4 hσ3)

theorem coe_d4OuterIncl (hσ3 : σ.toRingHom ^ 3 = 1) (c : K) :
    ((d4OuterIncl σ hσ3 c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) : K) = c :=
  rfl

abbrev d4Nt :
    ModGL TwistTag.D4.tag K :=
  trialityOuterRep K * trialityMiddleRep K

variable [CharP K 2]

theorem d4Nt_conj_d4x₁
    (c : K) : d4Nt (K := K) * d4x₁ K σ c * (d4Nt (K := K))⁻¹ =
    d4x₄ K σ c := by
  rw [show d4Nt (K := K) * d4x₁ K σ c * (d4Nt (K := K))⁻¹ = trialityOuterRep K *
      (trialityMiddleRep K * d4x₁ K σ c * (trialityMiddleRep K)⁻¹) * (trialityOuterRep K)⁻¹ by
    simp only [d4Nt]; group, trialityMiddleRep_conj_d4x₁, trialityOuterRep_conj_d4x₃]

theorem d4Nt_conj_d4y₁
    (c : K) : d4Nt (K := K) * d4y₁ K σ c * (d4Nt (K := K))⁻¹ =
    d4y₄ K σ c := by
  rw [show d4Nt (K := K) * d4y₁ K σ c * (d4Nt (K := K))⁻¹ = trialityOuterRep K *
      (trialityMiddleRep K * d4y₁ K σ c * (trialityMiddleRep K)⁻¹) * (trialityOuterRep K)⁻¹ by
    simp only [d4Nt]; group, trialityMiddleRep_conj_d4y₁, trialityOuterRep_conj_d4y₃]

@[expose] noncomputable def d4LtHom
    (hσ3 : σ.toRingHom ^ 3 = 1) :
    SL2 K →* ModGL TwistTag.D4.tag K :=
  (MulAut.conj (d4Nt (K := K))).toMonoidHom.comp
    ((orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩).comp
      (Matrix.SpecialLinearGroup.map (d4OuterIncl σ hσ3)))

omit [CharP K 2] in
theorem d4LtHom_apply
    (hσ3 : σ.toRingHom ^ 3 = 1) (g : SL2 K) :
    d4LtHom σ hσ3 g = d4Nt (K := K) * orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
      (Matrix.SpecialLinearGroup.map (d4OuterIncl σ hσ3) g) * (d4Nt (K := K))⁻¹ :=
  rfl

omit [CharP K 2] in
theorem d4LtHom_injective
    (hσ3 : σ.toRingHom ^ 3 = 1) (hσ : σ ^ 3 = 1) :
    Function.Injective (d4LtHom σ hσ3) := by
  refine (MulAut.conj _).injective.comp ((orbitRankOneHom_injective_D4 hσ _).comp ?_)
  intro g g' h
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have h1 := congrArg (fun x : SL2 (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) =>
    (x : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)) i j) h
  have h2 := congrArg Subtype.val h1
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    coe_d4OuterIncl] at h2
  exact h2

theorem range_d4LtHom
    (hσ3 : σ.toRingHom ^ 3 = 1) :
    (d4LtHom σ hσ3).range = d4Lt K σ := by
  have hsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.map (d4OuterIncl σ hσ3) :
        SL2 K →* SL2 (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)) := by
    intro g
    refine ⟨Matrix.SpecialLinearGroup.map (orbitField TwistTag.D4 K σ.toRingHom ⟨0,
        by decide⟩).subtype g,
      Subtype.ext (Matrix.ext fun i j => Subtype.ext ?_)⟩
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      coe_d4OuterIncl]
    rfl
  rw [d4LtHom, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj,
    ← MonoidHom.range_eq_map, orbitRankOneHom_range, MonoidHom.map_closure, d4Lt]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · left
      exact ⟨(c : K), by
        change d4x₄ K σ (c : K) = d4Nt (K := K) * _ * (d4Nt (K := K))⁻¹
        rw [coe_orbitX_zero_d4, d4Nt_conj_d4x₁]⟩
    · right
      exact ⟨(c : K), by
        change d4y₄ K σ (c : K) = d4Nt (K := K) * _ * (d4Nt (K := K))⁻¹
        rw [coe_orbitY_zero_d4, d4Nt_conj_d4y₁]⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, Or.inl ⟨d4OuterIncl σ hσ3 c, rfl⟩, by
        change d4Nt (K := K) * _ * (d4Nt (K := K))⁻¹ = _
        rw [coe_orbitX_zero_d4, coe_d4OuterIncl, d4Nt_conj_d4x₁]⟩
    · exact ⟨_, Or.inr ⟨d4OuterIncl σ hσ3 c, rfl⟩, by
        change d4Nt (K := K) * _ * (d4Nt (K := K))⁻¹ = _
        rw [coe_orbitY_zero_d4, coe_d4OuterIncl, d4Nt_conj_d4y₁]⟩

end RankOne

section LtTorus

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

theorem d4LtHom_WSL
    (hσ3 : σ.toRingHom ^ 3 = 1) :
    d4LtHom σ hσ3 WSL = canonicalRep (coxeterSystem TwistTag.D4.tag) K d4Wv := by
  obtain ⟨-, -, -, -, -, hN, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
  rw [d4LtHom_apply, map_WSL, orbitRankOneHom_WSL, hN, d4Wv, canonicalRep_mul_d4,
    canonicalRep_mul_d4, canonicalRep_mul_d4, canonicalRep_mul_d4]
  simp only [d4Nt, trialityOuterRep, trialityMiddleRep, mul_inv_rev,
    canonicalRep_orbitReflection_inv_d4]
  group

omit [CharP K 2] in
theorem d4LtHom_HSL
    (hσ3 : σ.toRingHom ^ 3 = 1) (hσ : σ ^ 3 = 1) (u : Kˣ) :
    d4LtHom σ hσ3 (HSL u) = trialityTorusHom σ
      (u⁻¹ * trialityFixedUnit K σ (trialityNorm σ hσ u), trialityNorm σ hσ u) := by
  have hH : (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
      (Units.map (d4OuterIncl σ hσ3).toMonoidHom u) : ModGL TwistTag.D4.tag K) =
        trialityOuterTorus K σ u := by
    have h := orbitH_mul_orbitH_eq_trialityTorusHom (σ := σ)
      (Units.map (d4OuterIncl σ hσ3).toMonoidHom u) 1 1 (by rw [map_one, Units.val_one]; rfl)
    rw [orbitH_one', mul_one] at h
    rw [h, trialityTorusHom_apply_d4, hm_one_d4, mul_one]
    exact congrArg _ (Units.ext rfl)
  rw [d4LtHom_apply, map_HSL, orbitRankOneHom_HSL, hH,
    show d4Nt (K := K) * trialityOuterTorus K σ u * (d4Nt (K := K))⁻¹ = trialityOuterRep K *
      (trialityMiddleRep K * trialityOuterTorus K σ u * (trialityMiddleRep K)⁻¹) *
        (trialityOuterRep K)⁻¹ by simp only [d4Nt]; group,
    trialityMiddleRep_conj_outer hσ,
    show trialityOuterRep K * (trialityOuterTorus K σ u * trialityMiddleTorus K σ
      (trialityNorm σ hσ u)) * (trialityOuterRep K)⁻¹ =
        (trialityOuterRep K * trialityOuterTorus K σ u * (trialityOuterRep K)⁻¹) *
          (trialityOuterRep K * trialityMiddleTorus K σ (trialityNorm σ hσ u) *
            (trialityOuterRep K)⁻¹) by group,
    trialityOuterRep_conj_outer, trialityOuterRep_conj_middle, ho_eq_d4, ho_eq_d4, hm_eq_d4,
    ← map_mul, ← map_mul]
  congr 1
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

theorem exists_d4LtHom_HSL
    [Finite K] (hσ3 : σ.toRingHom ^ 3 = 1) (hσ : σ ^ 3 = 1)
    (a : Kˣ) : ∃ u : Kˣ, ∃ s : (trialityFixedField K σ.toRingHom)ˣ,
      d4LtHom σ hσ3 (HSL u) = trialityTorusHom σ (a, s) := by
  have hN : σ ((a : K) * σ a * σ (σ a)) = (a : K) * σ a * σ (σ a) :=
    (mem_trialityFixedField).1 (norm_mem_trialityFixedField hσ (a : K))
  obtain ⟨s₀, hs₀σ, hs₀⟩ := exists_mul_self_eq_fixed_d4 σ hN
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hσa : σ (a : K) ≠ 0 := (map_ne_zero σ).2 ha0
  have hσσa : σ (σ (a : K)) ≠ 0 := (map_ne_zero σ).2 hσa
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hs₀
    exact mul_ne_zero (mul_ne_zero ha0 hσa) hσσa hs₀.symm
  set sK : Kˣ := Units.mk0 s₀ hs₀0
  refine ⟨sK * a⁻¹, trialityNorm σ hσ (sK * a⁻¹), ?_⟩
  have key : (sK * a⁻¹)⁻¹ * trialityFixedUnit K σ (trialityNorm σ hσ (sK * a⁻¹)) = a := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_trialityNorm hσ]
    simp only [sK, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_mk0, map_mul, map_inv₀,
      hs₀σ]
    field_simp
    linear_combination hs₀
  rw [d4LtHom_HSL σ hσ3 hσ, key]

end LtTorus

section CentQt

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

omit [Finite K] [CharP K 2] in
theorem mem_d4Qt
    (b : (trialityFixedField K σ.toRingHom)ˣ) : trialityTorusHom σ (1, b) ∈ d4Qt K σ :=
  ⟨b, rfl⟩

theorem exists_inv_mul_mem_d4Lt_of_torus
    (hσ3 : σ.toRingHom ^ 3 = 1) (hσ : σ ^ 3 = 1)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    ∃ y ∈ d4Qt K σ, y⁻¹ * trialityTorusHom σ p ∈ d4Lt K σ := by
  obtain ⟨u, s, hus⟩ := exists_d4LtHom_HSL σ hσ3 hσ p.1
  refine ⟨trialityTorusHom σ (1, s⁻¹ * p.2), mem_d4Qt σ _, ?_⟩
  rw [← map_inv, ← map_mul, show ((1, s⁻¹ * p.2) : Kˣ × (trialityFixedField K σ.toRingHom)ˣ)⁻¹ *
    p = (p.1, s) from Prod.ext (by simp only [Prod.fst_mul, Prod.fst_inv, inv_one, one_mul]) (by
      simp only [Prod.snd_mul, Prod.snd_inv]
      rw [mul_inv_rev, inv_inv, mul_comm p.2⁻¹ s, mul_assoc, inv_mul_cancel, mul_one]),
    ← hus, ← range_d4LtHom σ hσ3]
  exact ⟨_, rfl⟩

theorem exists_inv_mul_mem_d4Lt
    (hσ3 : σ.toRingHom ^ 3 = 1) (hσ : σ ^ 3 = 1)
    {β : (trialityFixedField K σ.toRingHom)ˣ} (hβ : β ≠ 1) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ d4C K σ) (hc : trialityMiddleTorus K σ β * g = g * trialityMiddleTorus K σ β) :
    ∃ y ∈ d4Qt K σ, y⁻¹ * g ∈ d4Lt K σ := by
  have hs : trialityMiddleTorus K σ β ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
    rw [hm_eq_d4]
    exact trialityTorusHom_mem_d4H σ hσ _
  obtain ⟨w, hw, h, hh, u₀, hu₀, u, hu, rfl, h1, h2, h3⟩ :=
    exists_bruhat_of_commute_torus_d4 σ hs hg hc
  obtain ⟨d₀, rfl⟩ := eq_d4x₄_of_commute_hm σ hσ3 hβ hu₀ h1
  obtain ⟨d, rfl⟩ := eq_d4x₄_of_commute_hm σ hσ3 hβ hu h2
  have hnL : canonicalRep (coxeterSystem TwistTag.D4.tag) K w ∈ d4Lt K σ := by
    rcases weyl_eq_of_commute_hm σ hβ hw h3 with rfl | rfl
    · rw [canonicalRep_one]
      exact one_mem _
    · rw [← d4LtHom_WSL σ hσ3, ← range_d4LtHom σ hσ3]
      exact ⟨_, rfl⟩
  have hx : ∀ c, d4x₄ K σ c ∈ d4Lt K σ := fun c => subset_closure (Or.inl ⟨c, rfl⟩)
  obtain ⟨p, rfl⟩ := exists_trialityTorusHom_eq_d4 σ hσ hh
  obtain ⟨y, hy, hyL⟩ := exists_inv_mul_mem_d4Lt_of_torus σ hσ3 hσ p
  refine ⟨y, hy, ?_⟩
  rw [show y⁻¹ * (trialityTorusHom σ p * d4x₄ K σ d₀ *
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * d4x₄ K σ d) =
    y⁻¹ * trialityTorusHom σ p * d4x₄ K σ d₀ *
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * d4x₄ K σ d by group]
  exact mul_mem (mul_mem (mul_mem hyL (hx d₀)) hnL) (hx d)

end CentQt

section LeviDataT

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

omit [Finite K] in
theorem d4Lt_le
    (hσ3 : σ.toRingHom ^ 3 = 1) : d4Lt K σ ≤ d4C K σ :=
  (closure_le _).2 (by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact (d4x_short_mem σ hσ3 c).2.2
    · exact (d4y_short_mem σ hσ3 c).2.2)

theorem d4Qt_le
    (hσ : ∀ c, σ (σ (σ c)) = c) : d4Qt K σ ≤ d4C K σ := by
  rintro _ ⟨b, rfl⟩
  change trialityTorusHom σ (1, b) ∈ d4C K σ
  rw [← hm_eq_d4]
  exact trialityMiddleTorus_mem_d4C σ hσ b

omit [Finite K] [CharP K 2] in
theorem d4Qt_commute_d4Lt
    : ∀ y ∈ d4Qt K σ, ∀ l ∈ d4Lt K σ, y * l = l * y := by
  rintro _ ⟨b, rfl⟩ l hl
  change trialityTorusHom σ (1, b) * l = l * trialityTorusHom σ (1, b)
  rw [← hm_eq_d4]
  have hle : d4Lt K σ ≤ centralizer {trialityMiddleTorus K σ b} := (closure_le _).2 (by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;> rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    · exact (mul_inv_eq_iff_eq_mul.1 (hm_conj_d4x₄ σ b c)).symm
    · exact (mul_inv_eq_iff_eq_mul.1 (hm_conj_d4y₄ σ b c)).symm)
  exact (mem_centralizer_singleton_iff.1 (hle hl)).symm

omit [Finite K] in
theorem d4Ma_commute_d4Zt :
    ∀ x ∈ d4Ma K σ, ∀ z ∈ d4Zt K σ, z * x = x * z := by
  have hgen : ∀ x ∈ (Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =>
      (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K)) ∪
      Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =>
        (orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K))),
      ∀ c : K, d4x₄ K σ c * x = x * d4x₄ K σ c := by
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩) c <;> dsimp only
    · rw [coe_orbitX_one_d4]
      exact commute_d4x₄_d4x₂ σ c (b : K)
    · rw [coe_orbitY_one_d4]
      have h := commute_d4x₄_d4x₂ σ c (b : K)
      rw [← trialityMiddleRep_conj_d4x₂, ← trialityMiddleRep_conj_d4x₄ σ c]
      calc trialityMiddleRep K * d4x₄ K σ c * (trialityMiddleRep K)⁻¹ *
            (trialityMiddleRep K * d4x₂ K (b : K) * (trialityMiddleRep K)⁻¹) =
          trialityMiddleRep K * (d4x₄ K σ c * d4x₂ K (b : K)) * (trialityMiddleRep K)⁻¹ := by
            group
        _ = trialityMiddleRep K * (d4x₂ K (b : K) * d4x₄ K σ c) * (trialityMiddleRep K)⁻¹ := by
            rw [h.eq]
        _ = _ := by group
  intro x hx z hz
  have hle : d4Ma K σ ≤ centralizer (d4Zt K σ : Set (ModGL TwistTag.D4.tag K)) := by
    rw [d4Zt, centralizer_closure]
    refine (closure_le _).2 fun x hx => ?_
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ ⟨c, rfl⟩
    exact hgen x hx c
  exact mem_centralizer_iff.1 (hle hx) z hz

omit [Finite K] [CharP K 2] in
theorem d4Qt_le_d4Ma
    (hσ : σ ^ 3 = 1) : d4Qt K σ ≤ d4Ma K σ := by
  rintro _ ⟨b, rfl⟩
  change trialityTorusHom σ (1, b) ∈ d4Ma K σ
  rw [trialityTorusHom_eq_orbitH hσ, show trialityOuterParam hσ (1 : Kˣ) = 1 from Units.ext rfl,
    orbitH_one', one_mul, ← orbitRankOneHom_HSL, d4Ma, orbitRankOneGroup,
    ← orbitRankOneHom_range]
  exact ⟨_, rfl⟩

omit [CharP K 2] in
theorem d4Ma_commutator
    (h4 : 4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)) :
    ⁅d4Ma K σ, d4Ma K σ⁆ = d4Ma K σ := by
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) := Subtype.finite
  rw [d4Ma, orbitRankOneGroup, ← orbitRankOneHom_range, MonoidHom.range_eq_map, ← map_commutator,
    ← commutator_def, sl2_commutator_d4 h4]

omit [Finite K] [CharP K 2] in
theorem d4Zt_le_d4Lt :
    d4Zt K σ ≤ d4Lt K σ :=
  (closure_le _).2 (by
    rintro _ ⟨c, rfl⟩
    exact subset_closure (Or.inl ⟨(c : K), rfl⟩))

theorem d4_leviData_t
    (m : ℕ) (hm : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) :
    Exc.LeviData ((d4Zt K σ).subgroupOf (d4C K σ)) ((d4Ma K σ).subgroupOf (d4C K σ))
        ((d4Qt K σ).subgroupOf (d4C K σ)) ((d4Qt K σ).subgroupOf (d4C K σ))
        ((d4Lt K σ).subgroupOf (d4C K σ)) ∧
      StatedClassicalModel (rankTwoQuot ((d4Lt K σ).subgroupOf (d4C K σ))) .PSL 2 2 (3 * m) ∧
      (m = 2 → ¬ StatedClassicalModel (rankTwoQuot ((d4Lt K σ).subgroupOf (d4C K σ)))
        .PSL 3 2 2) := by
  have hσ3' := sigma_cube_of_card_d4 σ hK hσq
  have hσ3 := toRingHom_pow_three_d4 σ hσ3'
  have hσ := ringEquiv_cube_d4 σ hσ3'
  have hm1 : 1 ≤ m := by omega
  have hq4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hk : Nat.card (d4k K σ) = 2 ^ m := card_d4k_of_card σ hm1 hK hσq
  obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ
  have hk' : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) = 2 ^ m := by
    rw [hL2]; exact hk
  have hQinj : Function.Injective ((trialityTorusHom σ).comp
      (MonoidHom.inr Kˣ (trialityFixedField K σ.toRingHom)ˣ)) :=
    (trialityTorusHom_injective_all hσ).comp fun _ _ h => (Prod.mk.inj h).2
  have hQcard : Nat.card (d4Qt K σ) = 2 ^ m - 1 := by
    rw [d4Qt, ← Nat.card_congr (MonoidHom.ofInjective hQinj).toEquiv, Nat.card_units]
    exact congrArg (· - 1) hk
  have hQsub : Nat.card ((d4Qt K σ).subgroupOf (d4C K σ)) = 2 ^ m - 1 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (d4Qt_le σ hσ3')).toEquiv, hQcard]
  have hQodd : Odd (2 ^ m - 1) := by
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨2 ^ j - 1, ?_⟩
    rw [hj, pow_succ]
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  obtain ⟨β, hβ⟩ : ∃ β : (trialityFixedField K σ.toRingHom)ˣ, β ≠ 1 := by
    have h3 : 1 < Nat.card (trialityFixedField K σ.toRingHom)ˣ := by
      rw [Nat.card_units]
      change 1 < Nat.card (d4k K σ) - 1
      omega
    have := Finite.one_lt_card_iff_nontrivial.1 h3
    exact exists_ne 1
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ m := hq4
      _ ≤ (2 ^ m) ^ 3 := Nat.le_self_pow (by norm_num) _
  let eL : ↥((d4Lt K σ).subgroupOf (d4C K σ)) ≃* SL2 K :=
    (subgroupOfEquivOfLe (d4Lt_le σ hσ3)).trans ((MulEquiv.subgroupCongr
      (range_d4LtHom σ hσ3)).symm.trans (MonoidHom.ofInjective (d4LtHom_injective σ hσ3 hσ)).symm)
  obtain ⟨-, -, hcen, hqs, ⟨eP⟩⟩ := sl2_facts_d4 eL hK4
  have hKm : Nat.card K = 2 ^ (3 * m) := by rw [hK, ← pow_mul, mul_comm]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, hqs, ?_, ?_⟩, ?_, ?_⟩
  ·
    have hMaC : d4Ma K σ ≤ d4C K σ := by
      rw [d4Ma, orbitRankOneGroup, ← orbitRankOneHom_range]
      exact ((triality_all_characteristic_faithful_torus_coordinates K σ hσ).2.2.2.2.1
        ⟨1, by decide⟩).1
    exact Exc.commutator_subgroupOf_of_perfect hMaC (d4Ma_commutator σ (by rw [hk']; exact hq4))
  ·
    intro x hx
    rw [mem_centralizer_iff]
    intro z hz
    exact Subtype.ext (d4Ma_commute_d4Zt σ x (mem_subgroupOf.1 hx) z (mem_subgroupOf.1 hz))
  ·
    intro x hx
    exact mem_subgroupOf.2 (d4Qt_le_d4Ma σ hσ (mem_subgroupOf.1 hx))
  ·
    intro h
    have hmem : (⟨trialityTorusHom σ (1, β), d4Qt_le σ hσ3' (mem_d4Qt σ β)⟩ : ↥(d4C K σ)) ∈
        (d4Qt K σ).subgroupOf (d4C K σ) := mem_subgroupOf.2 (mem_d4Qt σ β)
    rw [h, mem_bot] at hmem
    have h1 : trialityTorusHom σ (1, β) = trialityTorusHom σ 1 := by
      rw [map_one]; exact congrArg Subtype.val hmem
    exact hβ (Prod.mk.inj (trialityTorusHom_injective_all hσ h1)).2
  · rw [hQsub]; exact hQodd
  ·
    intro a ha b hb
    obtain ⟨x, hx⟩ := mem_subgroupOf.1 ha
    obtain ⟨y, hy⟩ := mem_subgroupOf.1 hb
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, ← hx, ← hy, MonoidHom.comp_apply, ← map_mul, mul_comm]
  ·
    intro y hy
    rw [mem_normalizer_iff]
    intro l
    have hc := d4Qt_commute_d4Lt σ (y : ModGL TwistTag.D4.tag K) (mem_subgroupOf.1 hy)
    have hconj : ∀ n ∈ d4Lt K σ, (y : ModGL TwistTag.D4.tag K) * n * (y : ModGL TwistTag.D4.tag K)⁻¹
        = n := fun n hn => by rw [hc n hn, mul_inv_cancel_right]
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro hl
      rw [hconj _ hl]
      exact hl
    · intro hl
      have h4 : (l : ModGL TwistTag.D4.tag K) = (y : ModGL TwistTag.D4.tag K) * l *
          (y : ModGL TwistTag.D4.tag K)⁻¹ := by
        calc (l : ModGL TwistTag.D4.tag K) = (y : ModGL TwistTag.D4.tag K)⁻¹ *
              ((y : ModGL TwistTag.D4.tag K) * l * (y : ModGL TwistTag.D4.tag K)⁻¹) * y := by
              group
          _ = (y : ModGL TwistTag.D4.tag K)⁻¹ * ((y : ModGL TwistTag.D4.tag K) *
              ((y : ModGL TwistTag.D4.tag K) * l * (y : ModGL TwistTag.D4.tag K)⁻¹) *
                (y : ModGL TwistTag.D4.tag K)⁻¹) * y := by rw [hconj _ hl]
          _ = (y : ModGL TwistTag.D4.tag K) * l * (y : ModGL TwistTag.D4.tag K)⁻¹ := by group
      rw [h4]
      exact hl
  ·
    intro l hl
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (d4Qt_commute_d4Lt σ _ (mem_subgroupOf.1 hy) _ (mem_subgroupOf.1 hl))
  ·
    intro c hc
    have hmem : (⟨trialityTorusHom σ (1, β), d4Qt_le σ hσ3' (mem_d4Qt σ β)⟩ : ↥(d4C K σ)) ∈
        (d4Qt K σ).subgroupOf (d4C K σ) := mem_subgroupOf.2 (mem_d4Qt σ β)
    have h1 := congrArg Subtype.val (mem_centralizer_iff.1 hc _ hmem)
    simp only [Subgroup.coe_mul] at h1
    rw [← hm_eq_d4] at h1
    obtain ⟨y, hy, hyL⟩ := exists_inv_mul_mem_d4Lt σ hσ3 hσ hβ c.2 h1
    refine ⟨⟨y, d4Qt_le σ hσ3' hy⟩, mem_subgroupOf.2 hy, mem_subgroupOf.2 ?_⟩
    simpa using hyL
  ·
    rw [hcen, Subgroup.card_bot]
    exact odd_one
  ·
    intro z hz
    exact mem_subgroupOf.2 (d4Zt_le_d4Lt σ (mem_subgroupOf.1 hz))
  ·
    refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hKm, ⟨eP⟩⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
  ·
    rintro rfl ⟨-, F, _, _, hF, ⟨e⟩⟩
    have h1 : Nat.card (rankTwoQuot ((d4Lt K σ).subgroupOf (d4C K σ))) = 262080 := by
      rw [Nat.card_congr eP.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 2), hK]
      decide
    have h2 : Nat.card (rankTwoQuot ((d4Lt K σ).subgroupOf (d4C K σ))) = 20160 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hF]
      decide
    omega

end LeviDataT

end CFSG.ComponentClassification.RankTwoExceptional.D4
