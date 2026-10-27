module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharCls
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Stab

variable {F : Type} [Field F]

@[expose] def blk (a b c d e : F) (h : (a * d - b * c) * e = 1) : SL(3, F) :=
  ⟨!![a, b, 0; c, d, 0; 0, 0, e], by
    rw [Matrix.det_fin_three]
    simp
    linear_combination h⟩

theorem coe_blk (a b c d e : F) (h : (a * d - b * c) * e = 1) :
    ((blk a b c d e h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![a, b, 0; c, d, 0; 0, 0, e] := rfl

theorem blk_mem_CenD (a b c d e : F) (h : (a * d - b * c) * e = 1) : blk a b c d e h ∈ CenD F := by
  rw [mem_CenD]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_blk, coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three]

theorem mem_stabilizer_of_forall {g : SL(3, F)} {W : Submodule F (Fin 3 → F)}
    (h : ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) : g ∈ stabilizer W := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  simpa [Matrix.mulVecLin_apply] using h v hv

theorem forall_of_mem_stabilizer {g : SL(3, F)} {W : Submodule F (Fin 3 → F)} (hg : g ∈ stabilizer W)
    (v : Fin 3 → F) (hv : v ∈ W) : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := by
  have : Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) F) v ∈ W.map (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) F)) :=
    Submodule.mem_map_of_mem hv
  rw [mem_stabilizer.mp hg] at this
  simpa [Matrix.mulVecLin_apply] using this

theorem radP_le_stabilizer : radP F ≤ stabilizer (vPlus F) := by
  rintro _ ⟨w, rfl⟩
  refine mem_stabilizer_of_forall fun v hv => ?_
  obtain ⟨hv0, hv1⟩ := mem_vPlus.mp hv
  refine mem_vPlus.mpr ⟨?_, ?_⟩
  · simp [elPHom, coe_elP, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv0, hv1]
  · simp [elPHom, coe_elP, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv0, hv1]

theorem radM_le_stabilizer : radM F ≤ stabilizer (vMinus F) := by
  rintro _ ⟨w, rfl⟩
  refine mem_stabilizer_of_forall fun v hv => ?_
  have hv2 := mem_vMinus.mp hv
  refine mem_vMinus.mpr ?_
  simp [elMHom, coe_elM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv2]

theorem CenD_le_stabilizer_vPlus (h2 : (2 : F) ≠ 0) : CenD F ≤ stabilizer (vPlus F) := by
  intro g hg
  obtain ⟨h02, h12, -, -⟩ := entries_of_mem_CenD h2 hg
  refine mem_stabilizer_of_forall fun v hv => ?_
  obtain ⟨hv0, hv1⟩ := mem_vPlus.mp hv
  refine mem_vPlus.mpr ⟨?_, ?_⟩
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv0, hv1, h02]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv0, hv1, h12]

theorem CenD_le_stabilizer_vMinus (h2 : (2 : F) ≠ 0) : CenD F ≤ stabilizer (vMinus F) := by
  intro g hg
  obtain ⟨-, -, h20, h21⟩ := entries_of_mem_CenD h2 hg
  refine mem_stabilizer_of_forall fun v hv => ?_
  have hv2 := mem_vMinus.mp hv
  refine mem_vMinus.mpr ?_
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv2, h20, h21]

theorem entries_of_mem_stabilizer_vPlus {g : SL(3, F)} (hg : g ∈ stabilizer (vPlus F)) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  have := forall_of_mem_stabilizer hg (Pi.single 2 1) (by simp [mem_vPlus])
  obtain ⟨h0, h1⟩ := mem_vPlus.mp this
  simp [Matrix.mulVec_single] at h0 h1
  exact ⟨h0, h1⟩

theorem entries_of_mem_stabilizer_vMinus {g : SL(3, F)} (hg : g ∈ stabilizer (vMinus F)) :
    (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have h0 := mem_vMinus.mp (forall_of_mem_stabilizer hg (Pi.single 0 1) (by simp [mem_vMinus]))
  have h1 := mem_vMinus.mp (forall_of_mem_stabilizer hg (Pi.single 1 1) (by simp [mem_vMinus]))
  simp [Matrix.mulVec_single] at h0 h1
  exact ⟨h0, h1⟩

theorem exists_factor_vPlus {g : SL(3, F)} (hg : g ∈ stabilizer (vPlus F)) :
    ∃ c ∈ CenD F, ∃ a b : F, g = c * elP a b := by
  obtain ⟨h02, h12⟩ := entries_of_mem_stabilizer_vPlus hg
  have hdet := g.2
  rw [Matrix.det_fin_three, h02, h12] at hdet
  have key : ((g : Matrix (Fin 3) (Fin 3) F) 0 0 * (g : Matrix (Fin 3) (Fin 3) F) 1 1 -
      (g : Matrix (Fin 3) (Fin 3) F) 0 1 * (g : Matrix (Fin 3) (Fin 3) F) 1 0) *
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
    linear_combination hdet
  refine ⟨blk _ _ _ _ _ key, blk_mem_CenD _ _ _ _ _ key,
    (g : Matrix (Fin 3) (Fin 3) F) 2 0 * ((g : Matrix (Fin 3) (Fin 3) F) 0 0 * (g : Matrix (Fin 3) (Fin 3) F) 1 1 -
      (g : Matrix (Fin 3) (Fin 3) F) 0 1 * (g : Matrix (Fin 3) (Fin 3) F) 1 0),
    (g : Matrix (Fin 3) (Fin 3) F) 2 1 * ((g : Matrix (Fin 3) (Fin 3) F) 0 0 * (g : Matrix (Fin 3) (Fin 3) F) 1 1 -
      (g : Matrix (Fin 3) (Fin 3) F) 0 1 * (g : Matrix (Fin 3) (Fin 3) F) 1 0), ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_blk, coe_elP, Matrix.mul_apply, Fin.sum_univ_three, h02, h12]
  · linear_combination (-(g : Matrix (Fin 3) (Fin 3) F) 2 0) * key
  · linear_combination (-(g : Matrix (Fin 3) (Fin 3) F) 2 1) * key

theorem exists_factor_vMinus {g : SL(3, F)} (hg : g ∈ stabilizer (vMinus F)) :
    ∃ c ∈ CenD F, ∃ a b : F, g = c * elM a b := by
  obtain ⟨h20, h21⟩ := entries_of_mem_stabilizer_vMinus hg
  have hdet := g.2
  rw [Matrix.det_fin_three, h20, h21] at hdet
  have key : ((g : Matrix (Fin 3) (Fin 3) F) 0 0 * (g : Matrix (Fin 3) (Fin 3) F) 1 1 -
      (g : Matrix (Fin 3) (Fin 3) F) 0 1 * (g : Matrix (Fin 3) (Fin 3) F) 1 0) *
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
    linear_combination hdet
  refine ⟨blk _ _ _ _ _ key, blk_mem_CenD _ _ _ _ _ key,
    (g : Matrix (Fin 3) (Fin 3) F) 2 2 * ((g : Matrix (Fin 3) (Fin 3) F) 1 1 * (g : Matrix (Fin 3) (Fin 3) F) 0 2 -
      (g : Matrix (Fin 3) (Fin 3) F) 0 1 * (g : Matrix (Fin 3) (Fin 3) F) 1 2),
    (g : Matrix (Fin 3) (Fin 3) F) 2 2 * ((g : Matrix (Fin 3) (Fin 3) F) 0 0 * (g : Matrix (Fin 3) (Fin 3) F) 1 2 -
      (g : Matrix (Fin 3) (Fin 3) F) 1 0 * (g : Matrix (Fin 3) (Fin 3) F) 0 2), ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_blk, coe_elM, Matrix.mul_apply, Fin.sum_univ_three, h20, h21]
  · linear_combination (-(g : Matrix (Fin 3) (Fin 3) F) 0 2) * key
  · linear_combination (-(g : Matrix (Fin 3) (Fin 3) F) 1 2) * key

theorem proj_mem_centralizer_of_mem_CenD {g : SL(3, F)} (hg : g ∈ CenD F) :
    proj 3 F g ∈ centralizer ({tInv} : Set (projectiveSL 3 F)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, tInv, ← map_mul, ← map_mul, mem_CenD.mp hg]

theorem projStabilizer_vPlus (h2 : (2 : F) ≠ 0) :
    projStabilizer (vPlus F) =
      (radP F).map (proj 3 F) ⊔ centralizer ({tInv} : Set (projectiveSL 3 F)) := by
  refine le_antisymm ?_ (sup_le (Subgroup.map_mono radP_le_stabilizer) ?_)
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, hc, a, b, rfl⟩ := exists_factor_vPlus hg
    rw [map_mul]
    exact mul_mem (Subgroup.mem_sup_right (proj_mem_centralizer_of_mem_CenD hc))
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (mem_radP.mpr ⟨a, b, rfl⟩)))
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := exists_CenD_of_mem_centralizer h2 hx
    exact Subgroup.mem_map_of_mem _ (CenD_le_stabilizer_vPlus h2 hg)

theorem projStabilizer_vMinus (h2 : (2 : F) ≠ 0) :
    projStabilizer (vMinus F) =
      (radM F).map (proj 3 F) ⊔ centralizer ({tInv} : Set (projectiveSL 3 F)) := by
  refine le_antisymm ?_ (sup_le (Subgroup.map_mono radM_le_stabilizer) ?_)
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, hc, a, b, rfl⟩ := exists_factor_vMinus hg
    rw [map_mul]
    exact mul_mem (Subgroup.mem_sup_right (proj_mem_centralizer_of_mem_CenD hc))
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (mem_radM.mpr ⟨a, b, rfl⟩)))
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := exists_CenD_of_mem_centralizer h2 hx
    exact Subgroup.mem_map_of_mem _ (CenD_le_stabilizer_vMinus h2 hg)

theorem eq_zero_of_elP_mem_scalars {a b : F} (h : elP a b ∈ scalars 3 F) : a = 0 ∧ b = 0 := by
  obtain ⟨c, -, hc⟩ := h
  have h20 := congrFun (congrFun hc 2) 0
  have h21 := congrFun (congrFun hc 2) 1
  simp [coe_elP, Matrix.scalar_apply] at h20 h21
  exact ⟨h20, h21⟩

theorem eq_zero_of_elM_mem_scalars {a b : F} (h : elM a b ∈ scalars 3 F) : a = 0 ∧ b = 0 := by
  obtain ⟨c, -, hc⟩ := h
  have h02 := congrFun (congrFun hc 0) 2
  have h12 := congrFun (congrFun hc 1) 2
  simp [coe_elM, Matrix.scalar_apply] at h02 h12
  exact ⟨h02, h12⟩

theorem proj_elPHom_injective : Function.Injective ((proj 3 F).comp (elPHom F)) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hmem : elPHom F w ∈ scalars 3 F := proj_eq_one_iff.mp hw
  have h0 := eq_zero_of_elP_mem_scalars (a := (Multiplicative.toAdd w).1) (b := (Multiplicative.toAdd w).2) hmem
  apply Multiplicative.toAdd.injective
  exact Prod.ext h0.1 h0.2

theorem proj_elMHom_injective : Function.Injective ((proj 3 F).comp (elMHom F)) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hmem : elMHom F w ∈ scalars 3 F := proj_eq_one_iff.mp hw
  have h0 := eq_zero_of_elM_mem_scalars (a := (Multiplicative.toAdd w).1) (b := (Multiplicative.toAdd w).2) hmem
  apply Multiplicative.toAdd.injective
  exact Prod.ext h0.1 h0.2

end Stab

section Model

variable {F : Type} [Field F]

theorem bot_lt_vPlus : ⊥ < vPlus F := bot_lt_iff_ne_bot.mpr vPlus_ne_bot

theorem bot_lt_vMinus : ⊥ < vMinus F := bot_lt_iff_ne_bot.mpr vMinus_ne_bot

theorem vPlus_lt_top : vPlus F < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun h => ?_
  have : (Pi.single 0 1 : Fin 3 → F) ∈ vPlus F := by rw [h]; trivial
  rw [mem_vPlus] at this
  simp at this

theorem vMinus_lt_top : vMinus F < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun h => ?_
  have : (Pi.single 2 1 : Fin 3 → F) ∈ vMinus F := by rw [h]; trivial
  rw [mem_vMinus] at this
  simp at this

theorem classify_model [Finite F] (h2 : (2 : F) ≠ 0) (r : ℕ) [Fact r.Prime] [CharP F r]
    (Y : Subgroup (projectiveSL 3 F)) (hY : IsPGroup r Y) (hne : Y ≠ ⊥)
    (hN : ∀ g ∈ CenD F, proj 3 F g ∈ normalizer (Y : Set (projectiveSL 3 F))) :
    ∃ (W : Submodule F (Fin 3 → F)) (ψ : Multiplicative (F × F) →* projectiveSL 3 F),
      ⊥ < W ∧ W < ⊤ ∧ Function.Injective ψ ∧ ψ.range = Y ∧
        projStabilizer W = Y ⊔ centralizer ({tInv} : Set (projectiveSL 3 F)) := by
  rcases classify_p_subgroup h2 r Y hY hne hN with h | h
  · refine ⟨vPlus F, (proj 3 F).comp (elPHom F), bot_lt_vPlus, vPlus_lt_top,
      proj_elPHom_injective, ?_, ?_⟩
    · rw [h, MonoidHom.range_comp]
      rfl
    · rw [h]
      exact projStabilizer_vPlus h2
  · refine ⟨vMinus F, (proj 3 F).comp (elMHom F), bot_lt_vMinus, vMinus_lt_top,
      proj_elMHom_injective, ?_, ?_⟩
    · rw [h, MonoidHom.range_comp]
      rfl
    · rw [h]
      exact projStabilizer_vMinus h2

theorem pow_char_eq_one {p : ℕ} [CharP F p] (w : Multiplicative (F × F)) : w ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext <;> simp [nsmul_eq_mul]

theorem isElementaryAbelian_range {p : ℕ} [CharP F p] {G : Type*} [Group G]
    (ψ : Multiplicative (F × F) →* G) : IsElementaryAbelian p ψ.range := by
  have hcomm : ∀ x y : ↥ψ.range, x * y = y * x := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mul_comm]
  refine { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  rintro ⟨_, a, rfl⟩
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← map_pow, pow_char_eq_one, map_one]

theorem card_range_eq [Finite F] {G : Type*} [Group G] (ψ : Multiplicative (F × F) →* G)
    (hψ : Function.Injective ψ) : Nat.card ψ.range = Nat.card F ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
  show Nat.card (F × F) = _
  rw [Nat.card_prod, sq]

end Model

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
