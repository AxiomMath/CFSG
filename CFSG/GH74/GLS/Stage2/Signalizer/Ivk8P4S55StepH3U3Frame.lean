module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U3

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

structure OFrame (F : Fin 3 → Fin 3 → K) : Prop where
  orth : ∀ i j, i ≠ j → stdHermForm h 3 (F i) (F j) = 0
  aniso : ∀ j, stdHermForm h 3 (F j) (F j) ≠ 0

namespace OFrame

variable {h} {F : Fin 3 → Fin 3 → K} (hF : OFrame h F)
include hF

theorem form_sum (j : Fin 3) (a : Fin 3 → K) :
    stdHermForm h 3 (F j) (∑ k, a k • F k) = a j * stdHermForm h 3 (F j) (F j) := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [map_smul, smul_eq_mul]
  · intro k _ hk
    rw [map_smul, hF.orth j k (Ne.symm hk), smul_zero]
  · simp

theorem linearIndependent : LinearIndependent K F := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h1 := hF.form_sum j g
  rw [hg, map_zero] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_right (hF.aniso j)

noncomputable def basis : Module.Basis (Fin 3) K (Fin 3 → K) :=
  basisOfLinearIndependentOfCardEqFinrank hF.linearIndependent (by simp)

theorem coe_basis : ⇑hF.basis = F := coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem resolution (y : Fin 3 → K) :
    ∑ j, (stdHermForm h 3 (F j) y / stdHermForm h 3 (F j) (F j)) • F j = y := by
  have hy := hF.basis.sum_repr y
  rw [hF.coe_basis] at hy
  have hc : ∀ j, hF.basis.repr y j =
      stdHermForm h 3 (F j) y / stdHermForm h 3 (F j) (F j) := by
    intro j
    rw [eq_div_iff (hF.aniso j), ← hF.form_sum j, hy]
  simp only [← hc]
  exact hy

theorem form_sum_sum (a b : Fin 3 → K) :
    stdHermForm h 3 (∑ j, a j • F j) (∑ j, b j • F j) =
      ∑ j, h.bar (a j) * b j * stdHermForm h 3 (F j) (F j) := by
  rw [map_sum (stdHermForm h 3) (fun j => a j • F j) Finset.univ, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : stdHermForm h 3 (a j • F j) = h.bar (a j) • stdHermForm h 3 (F j) :=
    LinearMap.map_smulₛₗ _ _ _
  rw [e1, LinearMap.smul_apply, hF.form_sum, smul_eq_mul]
  ring

end OFrame

noncomputable def signMap (F : Fin 3 → Fin 3 → K) (ε : Fin 3 → K) :
    (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
  ∑ j, (ε j / stdHermForm h 3 (F j) (F j)) • (stdHermForm h 3 (F j)).smulRight (F j)

theorem signMap_apply (F : Fin 3 → Fin 3 → K) (ε : Fin 3 → K) (y : Fin 3 → K) :
    signMap h F ε y =
      ∑ j, (ε j * (stdHermForm h 3 (F j) y / stdHermForm h 3 (F j) (F j))) • F j := by
  rw [signMap, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul]
  congr 1
  ring

namespace OFrame

variable {h} {F : Fin 3 → Fin 3 → K} (hF : OFrame h F)
include hF

theorem signMap_frame (ε : Fin 3 → K) (k : Fin 3) : signMap h F ε (F k) = ε k • F k := by
  rw [signMap_apply, Finset.sum_eq_single k]
  · rw [div_self (hF.aniso k), mul_one]
  · intro j _ hj
    rw [hF.orth j k hj, zero_div, mul_zero, zero_smul]
  · simp

theorem ext_frame {φ ψ : (Fin 3 → K) →ₗ[K] (Fin 3 → K)} (hφψ : ∀ k, φ (F k) = ψ (F k)) :
    φ = ψ :=
  hF.basis.ext fun k => by rw [hF.coe_basis]; exact hφψ k

theorem signMap_mul (ε ε' : Fin 3 → K) :
    signMap h F ε ∘ₗ signMap h F ε' = signMap h F (ε * ε') :=
  hF.ext_frame fun k => by
    rw [LinearMap.comp_apply, hF.signMap_frame, map_smul, hF.signMap_frame, hF.signMap_frame,
      smul_smul, Pi.mul_apply, mul_comm]

theorem signMap_isometry {ε : Fin 3 → K} (hε : ∀ j, ε j * ε j = 1)
    (hεb : ∀ j, h.bar (ε j) = ε j) (x y : Fin 3 → K) :
    stdHermForm h 3 (signMap h F ε x) (signMap h F ε y) = stdHermForm h 3 x y := by
  have hn : ∀ j, h.bar (stdHermForm h 3 (F j) (F j)) = stdHermForm h 3 (F j) (F j) :=
    fun j => (stdHermForm_isSymm h 3).eq (F j) (F j)
  rw [signMap_apply, signMap_apply, hF.form_sum_sum]
  conv_rhs => rw [← hF.resolution x, ← hF.resolution y, hF.form_sum_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hεb j]
  calc ε j * h.bar (stdHermForm h 3 (F j) x / stdHermForm h 3 (F j) (F j)) *
        (ε j * (stdHermForm h 3 (F j) y / stdHermForm h 3 (F j) (F j))) *
        stdHermForm h 3 (F j) (F j) =
      (ε j * ε j) * (h.bar (stdHermForm h 3 (F j) x / stdHermForm h 3 (F j) (F j)) *
        (stdHermForm h 3 (F j) y / stdHermForm h 3 (F j) (F j)) *
        stdHermForm h 3 (F j) (F j)) := by ring
    _ = _ := by rw [hε j, one_mul]

theorem det_signMap (ε : Fin 3 → K) : LinearMap.det (signMap h F ε) = ∏ j, ε j := by
  rw [← LinearMap.det_toMatrix hF.basis]
  have hdiag : LinearMap.toMatrix hF.basis hF.basis (signMap h F ε) = diagonal ε := by
    ext i j
    have hb : hF.basis j = F j := congrFun hF.coe_basis j
    rw [LinearMap.toMatrix_apply, hb, hF.signMap_frame, map_smul, ← hb,
      Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Finsupp.single_eq_of_ne hij, if_neg hij, mul_zero]
  rw [hdiag, det_diagonal]

end OFrame

noncomputable def signTriple (st : Fin 2 → ℤˣ) : Fin 3 → K :=
  ![((st 0 : ℤ) : K), ((st 1 : ℤ) : K), ((st 0 : ℤ) : K) * ((st 1 : ℤ) : K)]

theorem signTriple_mul (st st' : Fin 2 → ℤˣ) :
    (signTriple (st * st') : Fin 3 → K) = signTriple st * signTriple st' := by
  funext j
  fin_cases j <;>
    simp [signTriple, Pi.mul_apply, Units.val_mul, Int.cast_mul] <;> ring

theorem unit_sq (u : ℤˣ) : ((u : ℤ) : K) * ((u : ℤ) : K) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

theorem signTriple_sq (st : Fin 2 → ℤˣ) (j : Fin 3) :
    (signTriple st : Fin 3 → K) j * signTriple st j = 1 := by
  fin_cases j
  · exact unit_sq _
  · exact unit_sq _
  · change ((st 0 : ℤ) : K) * ((st 1 : ℤ) : K) * (((st 0 : ℤ) : K) * ((st 1 : ℤ) : K)) = 1
    calc _ = (((st 0 : ℤ) : K) * ((st 0 : ℤ) : K)) * (((st 1 : ℤ) : K) * ((st 1 : ℤ) : K)) := by
          ring
      _ = 1 := by rw [unit_sq, unit_sq, one_mul]

theorem signTriple_bar (st : Fin 2 → ℤˣ) (j : Fin 3) :
    h.bar ((signTriple st : Fin 3 → K) j) = signTriple st j := by
  fin_cases j <;> simp [signTriple, map_intCast]

theorem prod_signTriple (st : Fin 2 → ℤˣ) : ∏ j, (signTriple st : Fin 3 → K) j = 1 := by
  rw [Fin.prod_univ_three]
  change ((st 0 : ℤ) : K) * ((st 1 : ℤ) : K) * (((st 0 : ℤ) : K) * ((st 1 : ℤ) : K)) = 1
  calc _ = (((st 0 : ℤ) : K) * ((st 0 : ℤ) : K)) * (((st 1 : ℤ) : K) * ((st 1 : ℤ) : K)) := by
        ring
    _ = 1 := by rw [unit_sq, unit_sq, one_mul]

namespace OFrame

variable {h} {F : Fin 3 → Fin 3 → K} (hF : OFrame h F)
include hF

omit hF in
@[expose] noncomputable def signMat (_hF : OFrame h F) (st : Fin 2 → ℤˣ) : Matrix (Fin 3) (Fin 3) K :=
  LinearMap.toMatrix' (signMap h F (signTriple st))

theorem det_signMat (st : Fin 2 → ℤˣ) : (hF.signMat st).det = 1 := by
  rw [signMat, LinearMap.det_toMatrix', hF.det_signMap, prod_signTriple]

theorem signMat_mulVec (st : Fin 2 → ℤˣ) (y : Fin 3 → K) :
    hF.signMat st *ᵥ y = signMap h F (signTriple st) y := by
  rw [signMat, LinearMap.toMatrix'_mulVec]

@[expose] noncomputable def signGL (st : Fin 2 → ℤˣ) : GL (Fin 3) K :=
  Matrix.nonsingInvUnit (hF.signMat st) (by rw [hF.det_signMat]; exact isUnit_one)

theorem coe_signGL (st : Fin 2 → ℤˣ) : ((hF.signGL st : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = hF.signMat st := rfl

theorem signGL_mem (st : Fin 2 → ℤˣ) : hF.signGL st ∈ StatedSU 3 (p ^ f) K := by
  have := (mem_unitarySU_iff_isometry h (n := 3) (A := hF.signGL st)).mpr
  refine this ⟨by rw [coe_signGL, det_signMat], fun x y => ?_⟩
  rw [coe_signGL, signMat_mulVec, signMat_mulVec]
  exact hF.signMap_isometry (signTriple_sq st) (signTriple_bar h st) x y

theorem signMat_mul (st st' : Fin 2 → ℤˣ) :
    hF.signMat st * hF.signMat st' = hF.signMat (st * st') := by
  rw [signMat, signMat, signMat, ← LinearMap.toMatrix'_comp, hF.signMap_mul, signTriple_mul]

noncomputable def frameHom : (Fin 2 → ℤˣ) →* StatedProj (StatedSU 3 (p ^ f) K) where
  toFun st := projH _ ⟨hF.signGL st, hF.signGL_mem st⟩
  map_one' := by
    rw [← map_one (projH (StatedSU 3 (p ^ f) K))]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [coe_signGL]
    change LinearMap.toMatrix' (signMap h F (signTriple 1)) = 1
    have h1 : signMap h F (signTriple (1 : Fin 2 → ℤˣ)) = LinearMap.id :=
      hF.ext_frame fun k => by
        rw [hF.signMap_frame, LinearMap.id_apply]
        fin_cases k <;> simp [signTriple]
    rw [h1, LinearMap.toMatrix'_id]
  map_mul' st st' := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change hF.signMat (st * st') = hF.signMat st * hF.signMat st'
    rw [hF.signMat_mul]

end OFrame

variable {h}

theorem hhObs_of_frame (hp2 : p ≠ 2) {F : Fin 3 → Fin 3 → K} (hF : OFrame h F) (A : uU h 3)
    {l₀ l₁ l₂ : K} (h0 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ F 0 = l₀ • F 1)
    (h1 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ F 1 = l₁ • F 2)
    (h2 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ F 2 = l₂ • F 0) :
    HHObsAt 3 2 (StatedProj (StatedSU 3 (p ^ f) K)) (uConjAut h (by norm_num) A) := by
  classical
  have hK : CharP K p := h.charP
  have h2K : (2 : K) ≠ 0 := by
    intro h0'
    have h0'' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0'
    rw [CharP.cast_eq_zero_iff K p] at h0''
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp h0'')
  set α : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    Matrix.toLin' ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hα
  let sh : (Fin 2 → ℤˣ) → (Fin 2 → ℤˣ) := fun st => ![st 0 * st 1, st 0]
  have hshift : ∀ st : Fin 2 → ℤˣ, α ∘ₗ signMap h F (signTriple st) =
      signMap h F (signTriple (sh st)) ∘ₗ α := by
    intro st
    refine hF.ext_frame fun k => ?_
    have hu : ∀ u : ℤˣ, ((u : ℤ) : K) * ((u : ℤ) : K) = 1 := unit_sq
    simp only [LinearMap.comp_apply, hF.signMap_frame, map_smul]
    fin_cases k
    · change signTriple st 0 • α (F 0) = signMap h F (signTriple (sh st)) (α (F 0))
      rw [hα, Matrix.toLin'_apply, h0, map_smul, hF.signMap_frame, smul_smul, smul_smul]
      congr 1
      simp [signTriple, sh, mul_comm]
    · change signTriple st 1 • α (F 1) = signMap h F (signTriple (sh st)) (α (F 1))
      rw [hα, Matrix.toLin'_apply, h1, map_smul, hF.signMap_frame, smul_smul, smul_smul]
      congr 1
      simp only [signTriple, sh, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.tail_cons, Matrix.head_cons, Units.val_mul, Int.cast_mul]
      have := hu (st 0)
      linear_combination (-(l₁ * ((st 1 : ℤ) : K))) * this
    · change signTriple st 2 • α (F 2) = signMap h F (signTriple (sh st)) (α (F 2))
      rw [hα, Matrix.toLin'_apply, h2, map_smul, hF.signMap_frame, smul_smul, smul_smul]
      congr 1
      simp [signTriple, sh, Units.val_mul, Int.cast_mul, mul_comm]
  have hconj : ∀ st : Fin 2 → ℤˣ, uConjAut h (by norm_num) A (hF.frameHom st) =
      hF.frameHom (sh st) := by
    intro st
    change uConjAut h _ A (projH _ ⟨hF.signGL st, hF.signGL_mem st⟩) =
      projH _ ⟨hF.signGL (sh st), hF.signGL_mem (sh st)⟩
    rw [uConjAut_proj]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * hF.signMat st *
        ((((A : GL (Fin 3) K))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hF.signMat (sh st)
    have hm : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * hF.signMat st =
        hF.signMat (sh st) * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have e := congrArg LinearMap.toMatrix' (hshift st)
      rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hα, LinearMap.toMatrix'_toLin',
        ← OFrame.signMat, ← OFrame.signMat] at e
    rw [hm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine ⟨Nat.prime_two, by norm_num, hF.frameHom.range, ?_, ?_, ?_, ?_⟩
  ·
    have h2 : IsPGroup 2 (Fin 2 → ℤˣ) := fun st => ⟨1, by
      funext i
      rw [pow_one, Pi.pow_apply, sq, Pi.one_apply]
      rcases Int.units_eq_one_or (st i) with h | h <;> rw [h] <;> simp⟩
    exact h2.of_surjective hF.frameHom.rangeRestrict hF.frameHom.rangeRestrict_surjective
  ·
    rintro - _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  ·
    rintro _ ⟨st, rfl⟩
    exact ⟨sh st, (hconj st).symm⟩
  ·
    refine ⟨hF.frameHom ![-1, 1], ⟨_, rfl⟩, fun heq => ?_⟩
    rw [hconj] at heq
    have hq := (QuotientGroup.eq (s := (StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 (p ^ f) K))).mp heq
    rw [Subgroup.mem_subgroupOf] at hq
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hq
    have hcM : Matrix.scalar (Fin 3) (c : K) =
        ((((⟨hF.signGL (sh ![-1, 1]), hF.signGL_mem _⟩ : StatedSU 3 (p ^ f) K)⁻¹ *
          ⟨hF.signGL ![-1, 1], hF.signGL_mem _⟩ : StatedSU 3 (p ^ f) K) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) :=
      congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
    have key : ∀ k, (c : K) • F k = (signTriple (K := K) (sh ![-1, 1]) k)⁻¹ •
        (signTriple (K := K) ![-1, 1] k • F k) := by
      intro k
      have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M *ᵥ F k) hcM
      rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec] at e
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← Matrix.mulVec_mulVec,
        OFrame.coe_signGL, hF.signMat_mulVec, hF.signMap_frame] at e
      have hinvM : (((hF.signGL (sh ![-1, 1]))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          F k = (signTriple (K := K) (sh ![-1, 1]) k)⁻¹ • F k := by
        have hne : (signTriple (K := K) (sh ![-1, 1]) k) ≠ 0 := fun h0 => by
          have := signTriple_sq (K := K) (sh ![-1, 1]) k
          rw [h0, zero_mul] at this
          exact zero_ne_one this
        have e2 : hF.signMat (sh ![-1, 1]) *ᵥ ((signTriple (K := K) (sh ![-1, 1]) k)⁻¹ • F k) = F k := by
          rw [Matrix.mulVec_smul, hF.signMat_mulVec, hF.signMap_frame, smul_smul,
            inv_mul_cancel₀ hne, one_smul]
        calc (((hF.signGL (sh ![-1, 1]))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ F k =
            (((hF.signGL (sh ![-1, 1]))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
              (hF.signMat (sh ![-1, 1]) *ᵥ ((signTriple (K := K) (sh ![-1, 1]) k)⁻¹ • F k)) := by
                rw [e2]
          _ = _ := by
                rw [Matrix.mulVec_mulVec, ← OFrame.coe_signGL, ← Units.val_mul, inv_mul_cancel,
                  Units.val_one, Matrix.one_mulVec]
      rw [e, Matrix.mulVec_smul, hinvM, smul_smul, smul_smul, mul_comm]
    have hF0 : F 0 ≠ 0 := fun h0 => hF.aniso 0 (by simp [h0])
    have hF1 : F 1 ≠ 0 := fun h0 => hF.aniso 1 (by simp [h0])
    have k0 := key 0
    have k1 := key 1
    simp only [signTriple, sh, Matrix.cons_val_zero, Matrix.cons_val_one,
      Units.val_mul, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, smul_smul] at k0 k1
    norm_num at k0 k1
    have hc0 : (c : K) = 1 := by
      have h' : ((c : K) - 1) • F 0 = 0 := by rw [sub_smul, one_smul, k0, sub_self]
      rcases smul_eq_zero.mp h' with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hF0
    rw [hc0, one_smul] at k1
    apply hF1
    have : (2 : K) • F 1 = 0 := by
      rw [two_smul]
      nth_rewrite 1 [k1]
      simp
    rwa [smul_eq_zero, or_iff_right h2K] at this

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U3
