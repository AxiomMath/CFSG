module

public import CFSG.GH74.Generic.BProg.B3.LocBalL3Abs
public import CFSG.GH74.KGroups.L3EpsUniInv
public import CFSG.GH74.Generic.BProg.B2.GenLocU3Blk
public import CFSG.GH74.Generic.S3.L3Class

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.ClassicalInvolution.Phan CFSG.GH74.KGroups.L3Eps CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.GH74.Generic.BProg.B2 CFSG.GH74.Generic.BProg.B2.GenLocU3Blk
  Subgroup Matrix
open scoped MatrixGroups commutatorElement

namespace LocBalL3Uni

section Elements

variable {p f : ℕ} {F : Type} [Field F] [Finite F] [Fact p.Prime] [CharP F p]
  (h : UnitaryFieldData p f F)

@[expose] noncomputable def nI : Su F p f 2 := (suEquiv h 2).symm (negI h)

theorem coe_nI : (((nI h : Su F p f 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have h1 := coe_suEquiv h 2 (nI h)
  have h2 : suEquiv h 2 (nI h) = negI h := MulEquiv.apply_symm_apply _ _
  rw [h2] at h1
  exact (congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h1).symm.trans
    (matU_negI h)

theorem nI_mul_self : nI h * nI h = (1 : Su F p f 2) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_nI]
  simp

theorem nI_comm (A : Su F p f 2) : A * nI h = nI h * A := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_nI]
  simp

@[expose] noncomputable def x2 : Su F p f 3 := embSUid (unitaryInvolution F p f) 2 (nI h)

@[expose] noncomputable def x0 : Su F p f 3 := embSUid (unitaryInvolution F p f) 0 (nI h)

theorem coe_x2 : (((x2 h : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [x2, coe_embSUid, coe_nI]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair]

theorem coe_x0 : (((x0 h : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by
  rw [x0, coe_embSUid, coe_nI]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair]

theorem x2_mul_self : x2 h * x2 h = (1 : Su F p f 3) := by
  rw [x2, ← map_mul, nI_mul_self, map_one]

theorem x0_mul_self : x0 h * x0 h = (1 : Su F p f 3) := by
  rw [x0, ← map_mul, nI_mul_self, map_one]

theorem x2_comm (A : Su F p f 2) :
    embSUid (unitaryInvolution F p f) 2 A * x2 h =
      x2 h * embSUid (unitaryInvolution F p f) 2 A := by
  rw [x2, ← map_mul, ← map_mul, nI_comm]

theorem x0_comm (A : Su F p f 2) :
    embSUid (unitaryInvolution F p f) 0 A * x0 h =
      x0 h * embSUid (unitaryInvolution F p f) 0 A := by
  rw [x0, ← map_mul, ← map_mul, nI_comm]

end Elements

section Cover

variable {p f : ℕ} {F : Type} [Field F] [Finite F] [Fact p.Prime] [CharP F p]
  (h : UnitaryFieldData p f F) {K : Type} [Group K] (θ : ↥(unitarySU p f F 3) →* K)

@[expose] noncomputable def Theta : Su F p f 3 →* K := θ.comp (suEquiv h 3).toMonoidHom

theorem Theta_apply (x : Su F p f 3) : Theta h θ x = θ (suEquiv h 3 x) := rfl

theorem Theta_surj (hθ : IsCover h θ) : Function.Surjective (Theta h θ) :=
  hθ.surj.comp (suEquiv h 3).surjective

theorem matU_suEquiv (x : Su F p f 3) :
    matU (suEquiv h 3 x) = ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) (coe_suEquiv h 3 x)

omit [Finite F] in
theorem neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : F) ≠ 1 := by
  intro h1
  apply h2
  linear_combination -h1

theorem Theta_x2_ne_one (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0) : Theta h θ (x2 h) ≠ 1 := by
  intro hcontra
  have h1 : θ (suEquiv h 3 (x2 h)) = θ (suEquiv h 3 1) := by
    rw [Theta_apply] at hcontra
    rw [hcontra, map_one, map_one]
  obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 h1
  rw [matU_suEquiv, matU_suEquiv, coe_x2] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e22 := congrFun (congrFun hc 2) 2
  simp [Matrix.scalar_apply] at e00 e22
  apply neg_one_ne_one h2
  linear_combination -e00 - e22

theorem Theta_x0_ne_one (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0) : Theta h θ (x0 h) ≠ 1 := by
  intro hcontra
  have h1 : θ (suEquiv h 3 (x0 h)) = θ (suEquiv h 3 1) := by
    rw [Theta_apply] at hcontra
    rw [hcontra, map_one, map_one]
  obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 h1
  rw [matU_suEquiv, matU_suEquiv, coe_x0] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp [Matrix.scalar_apply] at e00 e11
  apply neg_one_ne_one h2
  linear_combination -e00 - e11

theorem Theta_x2_ne_x0 (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0) :
    Theta h θ (x2 h) ≠ Theta h θ (x0 h) := by
  intro hcontra
  have h1 : θ (suEquiv h 3 (x2 h)) = θ (suEquiv h 3 (x0 h)) := hcontra
  obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 h1
  rw [matU_suEquiv, matU_suEquiv, coe_x2, coe_x0] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp [Matrix.scalar_apply] at e00 e11
  apply neg_one_ne_one h2
  linear_combination -e00 - e11

theorem x2_x0_comm : x2 h * x0 h = (x0 h * x2 h : Su F p f 3) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_x2, coe_x0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

omit [Finite F] in
include h in
theorem quasisimple_unitarySU_two (h4 : 4 ≤ p ^ f) :
    CFSG.IsQuasisimple ↥(unitarySU p f F 2) := by
  have := h.finite
  obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := F) (r := p)
    (f := f) h.card_eq_sq
  have hq2 : IsQuasisimple SL(2, CFSG.LieType.Steinberg.fixedSubfield F p f) :=
    isQuasisimple_sl2c (by rw [CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq]; exact h4)
  exact LocalCores.isQuasisimple_of_mulEquiv e hq2

include h in
theorem commutator_Su_two (h4 : 4 ≤ p ^ f) : commutator (Su F p f 2) = ⊤ :=
  (LocalCores.isQuasisimple_of_mulEquiv (suEquiv h 2).symm
    (quasisimple_unitarySU_two h h4)).1.commutator_eq_top

variable {θ}

theorem genPair_cover (hθ : IsCover h θ) (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ p ^ f) (hq2 : p ^ f ≠ 2) :
    ∃ E : Subgroup K, (∀ e ∈ E, e * e = 1) ∧ Nat.card ↥E = 4 ∧ LocBalL3Abs.GenPair E := by
  have ht1 : Theta h θ (x2 h) * Theta h θ (x2 h) = 1 := by rw [← map_mul, x2_mul_self, map_one]
  have ht2 : Theta h θ (x0 h) * Theta h θ (x0 h) = 1 := by rw [← map_mul, x0_mul_self, map_one]
  have hcomm : Theta h θ (x2 h) * Theta h θ (x0 h) = Theta h θ (x0 h) * Theta h θ (x2 h) := by
    rw [← map_mul, ← map_mul, x2_x0_comm]
  obtain ⟨E, hE1, hE2, hsq, hcard⟩ := LocBalL3Abs.exists_four_group ht1 ht2 hcomm
    (Theta_x2_ne_one h θ hθ h2) (Theta_x0_ne_one h θ hθ h2) (Theta_x2_ne_x0 h θ hθ h2)
  refine ⟨E, hsq, hcard, _, hE1, _, hE2, ht1, Theta_x2_ne_one h θ hθ h2, ht2,
    Theta_x0_ne_one h θ hθ h2, Theta_x2_ne_x0 h θ hθ h2,
    (B12 F p f).map (Theta h θ), (B23 F p f).map (Theta h θ), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, x2_comm]
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, x0_comm]
  · have e1 : (B12 F p f).map (Theta h θ) =
        ((Theta h θ).comp (embSUid (unitaryInvolution F p f) 2)).range :=
      (MonoidHom.range_comp _ _).symm
    rw [e1]
    exact LocBalL3Abs.range_perfect _ (commutator_Su_two h h4)
  · have e1 : (B23 F p f).map (Theta h θ) =
        ((Theta h θ).comp (embSUid (unitaryInvolution F p f) 0)).range :=
      (MonoidHom.range_comp _ _).symm
    rw [e1]
    exact LocBalL3Abs.range_perfect _ (commutator_Su_two h h4)
  · rw [← Subgroup.map_sup, B12_sup_B23 h.card_eq_sq hq2,
      Subgroup.map_top_of_surjective _ (Theta_surj h θ hθ)]

omit [Finite F] [Fact p.Prime] [CharP F p] in
include h in
theorem layer_of_cover (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f)) (hθ : IsCover h θ) :
    LocBalL3Abs.Layer (θ (dU hq)) (levS hq θ) := by
  have hI := invData_of_cover h hp h5 hq hθ
  refine ⟨hI.mem, hI.quasisimple, hI.le_centralizer, hI.conj_mem, hI.commutator_mem, ?_⟩
  intro s hs hcen
  exact hI.center ⟨s, hs⟩ (Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hcen g g.2)))

theorem modelData_cover (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f)) (hθ : IsCover h θ)
    (hsimple : IsSimpleGroup K) (hcls : S3.SingleInv K) : LocBalL3Abs.ModelData K := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_pow h hq
  obtain ⟨E, hsq, hcard, hG⟩ := genPair_cover h hθ h2 (by omega) (by omega)
  exact ⟨hsimple, ⟨θ (dU hq), levS hq θ, theta_dU_sq hq θ, theta_dU_ne_one h hq hθ,
    layer_of_cover h hp h5 hq hθ⟩, hcls, E, hsq, hcard, hG⟩

end Cover

end LocBalL3Uni

end CFSG.GH74.Generic.BProg.B3
