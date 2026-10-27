module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLData
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLModel
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLDescent

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartOne CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns Matrix

@[expose] def BGLFieldPairGenerationL : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F % 3 ≠ 0 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSL 3 F))) →
    ∀ b x : MulAut K,
      IsFieldAutThree b → b ≠ 1 → b ^ 3 = 1 → IsInnDiagThree x → x ≠ 1 → x ^ 3 = 1 →
        b * x = x * b →
          (⊤ : Subgroup K) ≤
            GLAPLayer 3 (Lemma512Ns.fixedSub b) ⊔ GLAPLayer 3 (Lemma512Ns.fixedSub (b * x))

theorem bgll_pair_generation (hcore : BGL.SL3SubfieldJoin) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (hL : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSL 3 F)))
    {b x : MulAut K} (hb : IsFieldAutThree b) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hx : IsInnDiagThree x) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hbx : b * x = x * b) :
    (⊤ : Subgroup K) ≤
      GLAPLayer 3 (Lemma512Ns.fixedSub b) ⊔ GLAPLayer 3 (Lemma512Ns.fixedSub (b * x)) := by
  obtain ⟨F, hFf, hFfin, η, σ, g, hσ, hηb, hηx⟩ := bgll_data hK hL hb hb1 hb3 hx
  have hcomm : conjAut 3 F g * fieldAut 3 F σ = fieldAut 3 F σ * conjAut 3 F g := by
    have := congrArg (fun z : MulAut K => MulAut.congr η (centerDescend K z)) hbx
    simp only [map_mul] at this
    rw [hηb, hηx] at this
    exact this.symm
  have h3 : conjAut 3 F g ^ 3 = 1 := by
    rw [← hηx, ← map_pow, ← map_pow, hx3, map_one, map_one]
  obtain ⟨h, hh⟩ := bgll_exists_h hσ g hcomm h3
  have hg1 : conjAut 3 F g ≠ 1 := by
    intro h1
    apply hx1
    refine eq_one_of_centerDescend_eq_one hK ?_
    apply (MulAut.congr η).injective
    rw [hηx, h1, map_one]
  have hcg : conjAut 3 F g = conjAut 3 F (h * GeneralLinearGroup.map (σ : F →+* F) h⁻¹) := by
    have := conjAut_mul_fieldAut_mul (n := 3) (K := F) h h⁻¹ σ 1
    rw [map_inv, map_one, mul_one, mul_one] at this
    exact mul_right_cancel (hh.trans this)
  have hnot : ¬ ∃ c : F, c ≠ 0 ∧ ∀ i j, σ (c * (h : Matrix (Fin 3) (Fin 3) F) i j) =
      c * (h : Matrix (Fin 3) (Fin 3) F) i j := by
    rintro ⟨c, hc0, hc⟩
    apply hg1
    have hσc : σ c ≠ 0 := (map_ne_zero σ).2 hc0
    set d : Fˣ := Units.mk0 (c * (σ c)⁻¹) (mul_ne_zero hc0 (inv_ne_zero hσc)) with hd
    have hs : GeneralLinearGroup.map (σ : F →+* F) h = h * GeneralLinearGroup.scalar (Fin 3) d := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      ext i j
      have := hc i j
      rw [map_mul] at this
      simp only [Matrix.mul_diagonal]
      change σ ((h : Matrix (Fin 3) (Fin 3) F) i j) = (h : Matrix (Fin 3) (Fin 3) F) i j * (c * (σ c)⁻¹)
      field_simp
      linear_combination this
    have hsi : GeneralLinearGroup.map (σ : F →+* F) h⁻¹ =
        (GeneralLinearGroup.scalar (Fin 3) d)⁻¹ * h⁻¹ := by
      rw [map_inv, hs, _root_.mul_inv_rev]
    rw [hcg, hsi]
    simp only [map_mul, map_inv, conjAut_scalar, inv_one, one_mul, mul_inv_cancel]
  let k : Subfield F := RingHom.eqLocusField σ.toRingHom (RingHom.id F)
  have hk : ∀ y, y ∈ k ↔ σ y = y := fun y => Iff.rfl
  have hN₁ : BglNSP (fieldAut 3 F σ) (linearSubfieldInclusion 3 k).range := bgll_range_nsp hk
  have hjoin := bgll_model_join hcore hσ hk h hnot
  have hβ₂ : MulAut.congr η (centerDescend K (b * x)) =
      conjAut 3 F h * fieldAut 3 F σ * (conjAut 3 F h)⁻¹ := by
    rw [map_mul, map_mul, hηb, hηx, ← hcomm]
    exact hh
  have hN₂ : BglNSP (conjAut 3 F h * fieldAut 3 F σ * (conjAut 3 F h)⁻¹)
      ((linearSubfieldInclusion 3 k).range.map (conjAut 3 F h).toMonoidHom) := by
    refine bglNSP_map ((conjAut 3 F h).symm) ?_ hN₁
    change (conjAut 3 F h)⁻¹ * (conjAut 3 F h * fieldAut 3 F σ * (conjAut 3 F h)⁻¹) *
      (conjAut 3 F h)⁻¹⁻¹ = _
    group
  have hB₁ := bglNSP_map η hηb hN₁
  have hB₂ := bglNSP_map η hβ₂ hN₂
  have hQ : (linearSubfieldInclusion 3 k).range.map η.symm.toMonoidHom ⊔
      ((linearSubfieldInclusion 3 k).range.map (conjAut 3 F h).toMonoidHom).map η.symm.toMonoidHom
        = ⊤ := by
    rw [← Subgroup.map_sup, hjoin, Subgroup.map_top_of_surjective _ η.symm.surjective]
  have hK1 : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    have := hK.1
    rwa [commutator_def] at this
  have key := glaPLayer_fixSubgroup_sup_eq_top_of_perfect (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.ker_mk' _).le (QuotientGroup.mk'_surjective _) hK1 b (b * x)
    (centerDescend K b) (centerDescend K (b * x)) (fun _ => rfl) (fun _ => rfl) Nat.prime_three
    (bglNSP_le_layer hB₁) (bglNSP_le_layer hB₂) hQ
  exact le_of_eq key.symm

theorem bglFieldPairGenerationL_of_core (hcore : BGL.SL3SubfieldJoin) :
    BGLFieldPairGenerationL := by
  intro K _ _ hK hL b x hb hb1 hb3 hx hx1 hx3 hbx
  obtain ⟨F, hF, hfin, -, he⟩ := hL
  exact bgll_pair_generation hcore hK ⟨F, hF, hfin, he⟩ hb hb1 hb3 hx hx1 hx3 hbx

@[expose] def BGLFieldGenerationThreeL : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    (∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSL 3 F))) →
    ∀ f x : MulAut K, IsFieldAutThree f → f ≠ 1 → f ^ 3 = 1 → IsInnDiagThree x → x ≠ 1 →
      x ^ 3 = 1 → f * x = x * f →
        (⊤ : Subgroup K) ≤ ⨆ (i : ℕ) (_ : i < 3), Lemma512Ns.fixedSub (f * x ^ i)

theorem bglFieldGenerationThreeL_of_core (hcore : BGL.SL3SubfieldJoin) :
    BGLFieldGenerationThreeL := by
  intro K _ _ hK hL f x hf hf1 hf3 hx hx1 hx3 hfx
  have h := bgll_pair_generation hcore hK hL hf hf1 hf3 hx hx1 hx3 hfx
  refine h.trans (sup_le ?_ ?_)
  · refine le_trans (sSup_le fun L hL => hL.1) ?_
    refine le_iSup₂_of_le 0 (by norm_num) ?_
    simp
  · refine le_trans (sSup_le fun L hL => hL.1) ?_
    refine le_iSup₂_of_le 1 (by norm_num) ?_
    simp

end CFSG.HardMathSupport.Solomon.Coordinator
