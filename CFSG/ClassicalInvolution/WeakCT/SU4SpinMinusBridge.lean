module

public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusSU
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusField
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame

public section

namespace CFSG.ClassicalInvolution.WeakCT.SU4

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.ModelFacts CFSG.Timmesfeld
open scoped Matrix MatrixGroups

section RootGroups

variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c)

theorem rootGroup_four_one_eq_range :
    rootGroup σ hσ 4 (Pi.single 1 1) = (longRootHom σ (i := (1 : Fin 4)) (by decide)).range := by
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      exfalso
      revert hij hi hj hji hw
      fin_cases i <;> fin_cases j <;> decide
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      have hi1 : i = 1 := by
        revert hw
        fin_cases i <;> decide
      subst hi1
      exact le_rfl
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact longRootHom_mem hσ _ (by decide) c

theorem rootGroup_four_neg_one_eq_range :
    rootGroup σ hσ 4 (-Pi.single 1 1) = (longRootHom σ (i := (2 : Fin 4)) (by decide)).range := by
  refine le_antisymm ?_ ?_
  · unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      exfalso
      revert hij hi hj hji hw
      fin_cases i <;> fin_cases j <;> decide
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      have hi1 : i = 2 := by
        revert hw
        fin_cases i <;> decide
      subst hi1
      exact le_rfl
    · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
        iSup_le fun hk => iSup_le fun hw => ?_
      exfalso
      revert hk
      fin_cases k <;> decide
  · rintro _ ⟨c, rfl⟩
    exact longRootHom_mem hσ _ (by decide) c

end RootGroups

namespace KleinData

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] {p f : ℕ} [Fact p.Prime]
  [CharP K p] [Finite K] {b c : F} (D : KleinData F K (unitaryInvolution K p f) b c)
  (hF : Nat.card K = (p ^ f) ^ 2) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)

include hF hirr h2 in
theorem range_PhiSU_eq_top : (D.PhiSU hirr h2).range = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hD := isCTGroupDatum hF 4 (by norm_num) ζ hζ
  rw [eq_top_iff, ← hD.iSup_eq_top]
  refine iSup₂_le fun γ _ => ?_
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
    rintro _ ⟨x, rfl⟩
    exact D.rootHom_mem_range_PhiSU hirr h2 i j hij hi hj hji x
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun _ => ?_
    rintro _ ⟨x, rfl⟩
    exact D.longRootHom_mem_range_PhiSU hirr h2 i hi x
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun _ => ?_
    exfalso
    revert hk
    fin_cases k <;> decide

include hirr h2 in
theorem longRootHom_one_mem_map_lb (hi : (1 : Fin 4) ≠ Fin.rev 1)
    (x : Multiplicative (traceZero (unitaryInvolution K p f))) :
    longRootHom (unitaryInvolution K p f) hi x ∈
      (minusLongBlock b c).range.map (D.PhiSU hirr h2) := by
  have hc := eq_neg_of_mem_traceZero' (unitaryInvolution K p f) x.toAdd.2
  obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq (y := (x.toAdd : K) * D.δ)
    (by rw [map_mul, hc, D.σ_δ]; ring)
  refine ⟨minusLongBlock b c (tv 0 1 r), ⟨_, rfl⟩, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  rw [coe_PhiSU, minusLongBlock_tv01, D.PhiMon_long_e0f1, hr]
  show longRootMatrix (1 : Fin 4) (↑x.toAdd * D.δ * D.ε) = longRootMatrix (1 : Fin 4) ↑x.toAdd
  rw [mul_assoc, D.δ_mul_ε, mul_one]

include hirr h2 in
theorem longRootHom_two_mem_map_lb (hi : (2 : Fin 4) ≠ Fin.rev 2)
    (x : Multiplicative (traceZero (unitaryInvolution K p f))) :
    longRootHom (unitaryInvolution K p f) hi x ∈
      (minusLongBlock b c).range.map (D.PhiSU hirr h2) := by
  have hc := eq_neg_of_mem_traceZero' (unitaryInvolution K p f) x.toAdd.2
  obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq (y := (x.toAdd : K) * D.ε)
    (by rw [map_mul, hc, D.σ_ε]; ring)
  refine ⟨minusLongBlock b c (tv 1 0 r), ⟨_, rfl⟩, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  rw [coe_PhiSU, minusLongBlock_tv10, D.PhiMon_long_e1f0, hr]
  show longRootMatrix (2 : Fin 4) (↑x.toAdd * D.ε * D.δ) = longRootMatrix (2 : Fin 4) ↑x.toAdd
  rw [mul_assoc, mul_comm D.ε, D.δ_mul_ε, mul_one]

include hF hirr h2 in
theorem map_minusLongBlock_eq :
    (minusLongBlock b c).range.map (D.PhiSU hirr h2) =
      rootGroup (unitaryInvolution K p f) (unitaryInvolution_involutive hF) 4 (Pi.single 1 1) ⊔
        rootGroup (unitaryInvolution K p f) (unitaryInvolution_involutive hF) 4
          (-Pi.single 1 1) := by
  rw [rootGroup_four_one_eq_range, rootGroup_four_neg_one_eq_range]
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    refine sl2_mem_of_tv ((D.PhiSU hirr h2).comp (minusLongBlock b c))
      (H := (longRootHom (unitaryInvolution K p f) (i := (1 : Fin 4)) (by decide)).range ⊔
        (longRootHom (unitaryInvolution K p f) (i := (2 : Fin 4)) (by decide)).range)
      (fun x => ?_) (fun x => ?_) A
    · refine Subgroup.mem_sup_left ⟨Multiplicative.ofAdd ⟨algebraMap F K x * D.ε,
        mem_traceZero_of_eq_neg _ D.σ_ε_mul⟩, ?_⟩
      refine Subtype.ext (Units.ext ?_)
      rw [MonoidHom.comp_apply, minusLongBlock_tv01, coe_PhiSU, D.PhiMon_long_e0f1]
      rfl
    · refine Subgroup.mem_sup_right ⟨Multiplicative.ofAdd ⟨algebraMap F K x * D.δ,
        mem_traceZero_of_eq_neg _ D.σ_δ_mul⟩, ?_⟩
      refine Subtype.ext (Units.ext ?_)
      rw [MonoidHom.comp_apply, minusLongBlock_tv10, coe_PhiSU, D.PhiMon_long_e1f0]
      rfl
  · rintro _ ⟨x, rfl⟩
    exact D.longRootHom_one_mem_map_lb hirr h2 _ x
  · rintro _ ⟨x, rfl⟩
    exact D.longRootHom_two_mem_map_lb hirr h2 _ x

end KleinData

theorem su4SpinMinus_exists {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : f ≠ 0)
    {b c : GaloisField p f} (hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0) :
    ∃ e : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
        Su (GaloisField p (2 * f)) p f 4,
      (minusLongBlock b c).range.map e.toMonoidHom ∈
        longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4) := by
  have : NeZero f := ⟨hf⟩
  have : NeZero (2 * f) := ⟨by omega⟩
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinData hp2 hf hirr
  let _ := inst
  have := fact_shortField hirr
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    card_galoisField_two_mul p f (Nat.one_le_iff_ne_zero.mpr hf)
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_galoisField f hp2
  let ePhi : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
      SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4 :=
    MulEquiv.ofBijective (D.PhiSU hirr h2)
      ⟨D.PhiSU_injective hirr h2, fun g => by
        have h := D.range_PhiSU_eq_top hF hirr h2
        have hg : g ∈ (D.PhiSU hirr h2).range := by rw [h]; exact Subgroup.mem_top g
        exact hg⟩
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 4
  refine ⟨ePhi.trans (conjEquiv P hP), ?_⟩
  have hk1 : ¬ (1 : Fin (4 / 2)).val + 1 < 4 / 2 := by decide
  have hγ : toStd 4 (Pi.single (1 : Fin (4 / 2)) 1) = 2 • weight 4 (lowIdx (1 : Fin (4 / 2))) := by
    decide
  have hγ' : toStd 4 (-Pi.single (1 : Fin (4 / 2)) 1) =
      2 • weight 4 (Fin.rev (lowIdx (1 : Fin (4 / 2)))) := by
    decide
  obtain ⟨i, hi⟩ := exists_isLongRootSU2_map_rankOne hF hp2 (by norm_num : 2 ≤ 4) hγ hγ' P hP
  refine ⟨i, ?_⟩
  have hmap : (minusLongBlock b c).range.map (ePhi.trans (conjEquiv P hP)).toMonoidHom =
      (((minusLongBlock b c).range.map (D.PhiSU hirr h2)).map (conjEquiv P hP).toMonoidHom) := by
    rw [Subgroup.map_map]
    rfl
  rw [hmap, D.map_minusLongBlock_eq hF hirr h2]
  exact hi

end CFSG.ClassicalInvolution.WeakCT.SU4
