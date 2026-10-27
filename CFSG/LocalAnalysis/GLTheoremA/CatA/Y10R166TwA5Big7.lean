module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks4
public import CFSG.Timmesfeld.Bridge.RootStructR2Torus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open TwA5Big
open Matrix


namespace TwA5Big

section Certs


variable {n q : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 n F) {ζu : Fˣ}

private noncomputable def twA5E2Param {ζu : Fˣ} : Fin 3 → Subgroup.zpowers ζu :=
  ![1, ⟨ζu, Subgroup.mem_zpowers ζu⟩, 1]

private noncomputable def twA5E3Param {ζu : Fˣ} : Fin 3 → Subgroup.zpowers ζu :=
  ![1, 1, ⟨ζu, Subgroup.mem_zpowers ζu⟩]

private theorem twA5Vec_twA5EParam_e2 :
    twA5Vec (fun i => ((twA5EParam (twA5E2Param (ζu := ζu)) i : Fˣ) : F)) =
      (fun i : Fin 6 => if i ∈ ({0, 1, 2, 3} : Finset (Fin 6)) then (ζu : F)
        else ((ζu : F) ^ 2)⁻¹) := by
  funext i
  fin_cases i <;> simp [twA5Vec, twA5EParam, twA5E2Param] <;> field_simp

private theorem twA5Vec_twA5EParam_e3 :
    twA5Vec (fun i => ((twA5EParam (twA5E3Param (ζu := ζu)) i : Fˣ) : F)) =
      (fun i : Fin 6 => if i ∈ ({0, 1, 4, 5} : Finset (Fin 6)) then (ζu : F)
        else ((ζu : F) ^ 2)⁻¹) := by
  funext i
  fin_cases i <;> simp [twA5Vec, twA5EParam, twA5E3Param] <;> field_simp

private theorem twA5_zeta_ne_inv_sq {ζu : Fˣ} (hζo : orderOf ζu = q) (hq3 : ¬ q ∣ 3) :
    (ζu : F) ≠ ((ζu : F) ^ 2)⁻¹ := by
  intro heq
  have h3 : ζu ^ 3 = 1 := by
    apply Units.ext
    have h := congrArg (fun x : F => x * (ζu : F) ^ 2) heq
    rw [inv_mul_cancel₀ (pow_ne_zero 2 (Units.ne_zero ζu))] at h
    simpa [show (ζu : F) ^ 3 = (ζu : F) * (ζu : F) ^ 2 by ring] using h
  have hdvd : orderOf ζu ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 h3
  rw [hζo] at hdvd
  exact hq3 hdvd

private theorem centralizer_twA5E2 (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q)
    (hq3 : ¬ q ∣ 3) :
    Subgroup.centralizer
        ({unitaryProj h 6 (twA5TorusHom h hζ (twA5EParam (twA5E2Param (ζu := ζu))))} :
          Set (unitaryPSU h 6)) =
      (unitaryBlockDiag h ({0, 1, 2, 3} : Finset (Fin 6))).map (unitaryProj h 6) :=
  centralizer_unitaryProj_diagSU_eq_unitaryBlockDiag h
    (I := ({0, 1, 2, 3} : Finset (Fin 6))) (by decide)
    (twA5_zeta_ne_inv_sq (q := q) hζo hq3)
    (fun i => congrFun (twA5Vec_twA5EParam_e2 (ζu := ζu)) i)
    (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
      (twA5EParam (twA5E2Param (ζu := ζu)) i).2)
    (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
      (twA5EParam (twA5E2Param (ζu := ζu)) i).2)

private theorem centralizer_twA5E3 (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q)
    (hq3 : ¬ q ∣ 3) :
    Subgroup.centralizer
        ({unitaryProj h 6 (twA5TorusHom h hζ (twA5EParam (twA5E3Param (ζu := ζu))))} :
          Set (unitaryPSU h 6)) =
      (unitaryBlockDiag h ({0, 1, 4, 5} : Finset (Fin 6))).map (unitaryProj h 6) :=
  centralizer_unitaryProj_diagSU_eq_unitaryBlockDiag h
    (I := ({0, 1, 4, 5} : Finset (Fin 6))) (by decide)
    (twA5_zeta_ne_inv_sq (q := q) hζo hq3)
    (fun i => congrFun (twA5Vec_twA5EParam_e3 (ζu := ζu)) i)
    (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
      (twA5EParam (twA5E3Param (ζu := ζu)) i).2)
    (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
      (twA5EParam (twA5E3Param (ζu := ζu)) i).2)

theorem diagSU_commute_unitaryBlock_of_eq_on {I : Finset (Fin 6)} {d : Fin 6 → F}
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) (hc : ∀ i ∈ I, d i = d 0)
    {B : unitarySU 2 n F 6} (hB : B ∈ unitaryBlock h I) :
    Commute B (diagSU h d hd hdet) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, coe_diagSU,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i ∈ I <;> by_cases hj : j ∈ I
  · rw [hc i hi, hc j hj, mul_comm]
  · have h1 : (((B : GL (Fin 6) F)) : Matrix (Fin 6) (Fin 6) F) i j = 0 := by
      have h := (mem_unitaryBlock h).1 hB i j (Or.inr hj)
      have hij : i ≠ j := by rintro rfl; exact hj hi
      simpa [Matrix.one_apply, hij] using h
    rw [h1, zero_mul, mul_zero]
  · have h1 : (((B : GL (Fin 6) F)) : Matrix (Fin 6) (Fin 6) F) i j = 0 := by
      have h := (mem_unitaryBlock h).1 hB i j (Or.inl hi)
      have hij : i ≠ j := by rintro rfl; exact hi hj
      simpa [Matrix.one_apply, hij] using h
    rw [h1, zero_mul, mul_zero]
  · have h1 := (mem_unitaryBlock h).1 hB i j (Or.inl hi)
    by_cases hij : i = j
    · subst hij
      rw [h1]
      simp
    · have h0 : (((B : GL (Fin 6) F)) : Matrix (Fin 6) (Fin 6) F) i j = 0 := by
        simpa [Matrix.one_apply, hij] using h1
      rw [h0, zero_mul, mul_zero]

private theorem unitaryBlock_pair_le_centralizer_twA5E (hζ : h.norm (ζu : F) = 1) :
    (unitaryBlock h ({0, 1} : Finset (Fin 6))).map (unitaryProj h 6) ≤
      Subgroup.centralizer (twA5E h hζ : Set (unitaryPSU h 6)) := by
  rintro _ ⟨B, hB, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨c, rfl⟩ := hz
  have hcomm : B * twA5TorusHom h hζ (twA5EParam c) =
      twA5TorusHom h hζ (twA5EParam c) * B :=
    diagSU_commute_unitaryBlock_of_eq_on h
      (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ (twA5EParam c i).2)
      (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ (twA5EParam c i).2)
      (by intro i hi; fin_cases i <;> simp_all) hB
  exact (congrArg (unitaryProj h 6) hcomm).symm

theorem twA5E_layer_ne_bot (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) (hq : q.Prime)
    (hn : 2 ≤ n) (hq3 : ¬ q ∣ 3) (hqd : q ∣ 2 ^ (2 * n) - 1) :
    GLAPLayer q (blockSU h suFiveIndex ⊓
      Subgroup.centralizer (twA5E h hζ : Set (unitaryPSU h 6))) ≠ ⊥ := by
  set H : Subgroup (unitaryPSU h 6) :=
    blockSU h suFiveIndex ⊓ Subgroup.centralizer (twA5E h hζ : Set (unitaryPSU h 6))
    with hH
  refine glaPLayer_ne_bot_of_map_unitaryBlockDiag_inf_card_eq_two (h := h) (q := q) hq
    hn (I := ({0, 1} : Finset (Fin 6)))
    (J₁ := ({0, 1, 2, 3} : Finset (Fin 6))) (J₂ := ({0, 1, 4, 5} : Finset (Fin 6)))
    (H := H) (by decide) (by decide) ⟨2, by decide⟩ ?_ ?_ hqd
  ·
    have h1a : (unitaryBlock h ({0, 1} : Finset (Fin 6))).map (unitaryProj h 6) ≤
        blockSU h suFiveIndex :=
      Subgroup.map_mono (unitaryBlock_mono h (by decide))
    exact le_inf h1a (unitaryBlock_pair_le_centralizer_twA5E h hζ)
  ·
    intro x hx
    obtain ⟨hxJ, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨A, hA, rfl⟩ := (mem_blockSU h).1 hxJ
    have he2 : unitaryProj h 6 (twA5TorusHom h hζ (twA5EParam (twA5E2Param (ζu := ζu)))) ∈
        twA5E h hζ := MonoidHom.mem_range.mpr ⟨twA5E2Param, rfl⟩
    have he3 : unitaryProj h 6 (twA5TorusHom h hζ (twA5EParam (twA5E3Param (ζu := ζu)))) ∈
        twA5E h hζ := MonoidHom.mem_range.mpr ⟨twA5E3Param, rfl⟩
    have hA2 : A ∈ unitaryBlockDiag h ({0, 1, 2, 3} : Finset (Fin 6)) := by
      have hcomm : A * diagSU h
          (twA5Vec fun i => ((twA5EParam (twA5E2Param (ζu := ζu)) i : Fˣ) : F))
          (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
            (twA5EParam (twA5E2Param (ζu := ζu)) i).2)
          (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
            (twA5EParam (twA5E2Param (ζu := ζu)) i).2) =
          diagSU h (twA5Vec fun i => ((twA5EParam (twA5E2Param (ζu := ζu)) i : Fˣ) : F))
            (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
              (twA5EParam (twA5E2Param (ζu := ζu)) i).2)
            (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
              (twA5EParam (twA5E2Param (ζu := ζu)) i).2) * A :=
        mul_eq_mul_of_unitaryProj_commute_diagSU h (by decide)
          (twA5_zeta_ne_inv_sq (q := q) hζo hq3)
          (fun i => congrFun (twA5Vec_twA5EParam_e2 (ζu := ζu)) i)
          (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
            (twA5EParam (twA5E2Param (ζu := ζu)) i).2)
          (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
            (twA5EParam (twA5E2Param (ζu := ζu)) i).2)
          ((Subgroup.mem_centralizer_iff.1 hxC _ he2).symm)
      rw [← centralizer_diagSU_eq_unitaryBlockDiag h
        (twA5_zeta_ne_inv_sq (q := q) hζo hq3)
        (fun i => congrFun (twA5Vec_twA5EParam_e2 (ζu := ζu)) i)
        (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
          (twA5EParam (twA5E2Param (ζu := ζu)) i).2)
        (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
          (twA5EParam (twA5E2Param (ζu := ζu)) i).2)]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hA3 : A ∈ unitaryBlockDiag h ({0, 1, 4, 5} : Finset (Fin 6)) := by
      have hcomm : A * diagSU h
          (twA5Vec fun i => ((twA5EParam (twA5E3Param (ζu := ζu)) i : Fˣ) : F))
          (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
            (twA5EParam (twA5E3Param (ζu := ζu)) i).2)
          (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
            (twA5EParam (twA5E3Param (ζu := ζu)) i).2) =
          diagSU h (twA5Vec fun i => ((twA5EParam (twA5E3Param (ζu := ζu)) i : Fˣ) : F))
            (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
              (twA5EParam (twA5E3Param (ζu := ζu)) i).2)
            (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
              (twA5EParam (twA5E3Param (ζu := ζu)) i).2) * A :=
        mul_eq_mul_of_unitaryProj_commute_diagSU h (by decide)
          (twA5_zeta_ne_inv_sq (q := q) hζo hq3)
          (fun i => congrFun (twA5Vec_twA5EParam_e3 (ζu := ζu)) i)
          (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
            (twA5EParam (twA5E3Param (ζu := ζu)) i).2)
          (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
            (twA5EParam (twA5E3Param (ζu := ζu)) i).2)
          ((Subgroup.mem_centralizer_iff.1 hxC _ he3).symm)
      rw [← centralizer_diagSU_eq_unitaryBlockDiag h
        (twA5_zeta_ne_inv_sq (q := q) hζo hq3)
        (fun i => congrFun (twA5Vec_twA5EParam_e3 (ζu := ζu)) i)
        (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ
          (twA5EParam (twA5E3Param (ζu := ζu)) i).2)
        (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ
          (twA5EParam (twA5E3Param (ζu := ζu)) i).2)]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mpr ⟨hA2, hA3⟩)

theorem twA5_eight (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) :
    twA5B h hζ ⊓ blockSU h suFiveIndex ⊓
      Subgroup.centralizer
        (((unitaryLineRadical h).map (unitaryProj h 6) : Subgroup (unitaryPSU h 6)) :
          Set (unitaryPSU h 6)) ≤
      Subgroup.zpowers (unitaryProj h 6 (diagFiveLast h (ζu : F) hζ)) := by
  have hB : ∀ A ∈ twA5Torus h hζ,
      ∃ (d : Fin 6 → F) (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) (n : ℕ),
        A = diagSU h d hd hdet ∧ d 0 = d 1 ∧ d 0 = ((ζu ^ n : Fˣ) : F) := by
    intro A hA
    obtain ⟨c, rfl⟩ := hA
    obtain ⟨m, hm⟩ := CFSG.Timmesfeld.Bridge.exists_pow_eq_of_mem_zpowers
      (h := ζu) (g := (c 0 : Fˣ)) (c 0).2
    refine ⟨twA5Vec fun i => ((c i : Fˣ) : F),
      twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ (c i).2,
      twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ (c i).2, m, rfl, rfl, ?_⟩
    rw [twA5Vec_zero]
    exact (congrArg (fun u : Fˣ => (u : F)) hm).symm
  have hmap := map_unitaryProj_inf_centralizer_le_zpowers h hζ hB
  intro b hb
  obtain ⟨hbBJ, hbC⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨hbB, _⟩ := Subgroup.mem_inf.1 hbBJ
  obtain ⟨c, rfl⟩ := hbB
  have hAc : twA5TorusHom h hζ c ∈
      Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 n F 6)) :=
    centralizes_of_unitaryProj_centralizes h (unitaryLineRadical_isPGroup h)
      (fun s hs => by
        have hmem : unitaryProj h 6 s ∈
            (unitaryLineRadical h).map (unitaryProj h 6) := Subgroup.mem_map_of_mem _ hs
        exact (Subgroup.mem_centralizer_iff.1 hbC _ hmem).symm)
  exact hmap (Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mpr ⟨⟨c, rfl⟩, hAc⟩))

end Certs

end TwA5Big

end CFSG.LocalAnalysis.GLTheoremA.Y10F
