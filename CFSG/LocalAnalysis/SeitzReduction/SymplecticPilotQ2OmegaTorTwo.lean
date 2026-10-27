module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaTorForm
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PerfectEight
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ComponentClassification.PresentationLocal (sympFour isPerfect_commutator_sympFour)
open CFSG.LieType.Steinberg.Sp (blockMat)

variable {K : Type} [Field K]

section SpFour

theorem commutator_commutator_statedSp_two [Finite K] (hK : Nat.card K = 2) :
    ⁅commutator (StatedSp 2 K), commutator (StatedSp 2 K)⁆ = commutator (StatedSp 2 K) := by
  set H : Subgroup sympFour := commutator sympFour with hHdef
  have hHperf : ⁅H, H⁆ = H := by
    have h := congrArg (Subgroup.map H.subtype)
      (Group.isPerfect_def.1 isPerfect_commutator_sympFour)
    clear_value H
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  set φ : sympFour →* StatedSp 2 K := (F4Pilot.sp4EquivSympFour (K := K) hK).symm.toMonoidHom
  have htop : (⊤ : Subgroup sympFour).map φ = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact (F4Pilot.sp4EquivSympFour (K := K) hK).symm.surjective
  have hφ : commutator (StatedSp 2 K) = H.map φ := by
    rw [hHdef, _root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator, htop]
  rw [hφ, ← Subgroup.map_commutator, hHperf]

theorem nsElt_mem_commutator_statedSp_two [CharP K 2] :
    nsElt (K := K) (0 : Fin 2) ∈ commutator (StatedSp 2 K) := by
  rw [_root_.commutator_def]
  exact commutator_mono le_top le_top (nsElt_mem_commutator_longRootSp2 0)

@[expose] def aTwoMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks 1 !![0, 1; 1, 0] 0 1

@[expose] def cTwoMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 1 1 0 1

theorem not_commute_nsElt_aTwoMat :
    aTwoMat * mat 2 K (nsElt 0) ≠ mat 2 K (nsElt 0) * aTwoMat := by
  intro h
  have e := congrFun (congrFun h (Sum.inr 0)) (Sum.inr 1)
  simp [aTwoMat, mat_nsElt, blockMat, zThreeMat, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two] at e

theorem not_commute_nsElt_cTwoMat :
    cTwoMat * mat 2 K (nsElt 0) ≠ mat 2 K (nsElt 0) * cTwoMat := by
  intro h
  have e := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
  simp [cTwoMat, mat_nsElt, blockMat, zThreeMat, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.one_apply] at e

end SpFour

section Frames

variable {N j : ℕ}

theorem spForm_spANil_left (x y : Fin N ⊕ Fin N → K) :
    spForm (spANil K N j *ᵥ x) y = spBForm j x y := rfl

theorem spForm_spANil_right (x y : Fin N ⊕ Fin N → K) :
    spForm x (spANil K N j *ᵥ y) = -spBForm j y x := spForm_swap

theorem spBForm_spANil_right (x y : Fin N ⊕ Fin N → K) :
    spBForm j x (spANil K N j *ᵥ y) = 0 := spForm_spANil_spANil x y

theorem mul_colMat_eq_colMat_mul {ι : Type} [Fintype ι]
    {M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K}
    {u : ι → Fin N ⊕ Fin N → K} {D : Matrix ι ι K} (h : ∀ c, M *ᵥ u c = ∑ c', D c' c • u c') :
    M * colMat u = colMat u * D := by
  rw [mul_colMat, colMat_mul]
  exact congrArg colMat (funext h)

theorem mat_inv_mulVec_of_mulVec_eq {s : StatedSp N K} {y : Fin N ⊕ Fin N → K}
    (h : mat N K s *ᵥ y = y) : mat N K s⁻¹ *ᵥ y = y := by
  conv_lhs => rw [← h]
  rw [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec]

theorem mat_mulVec_spANil {s : StatedSp N K}
    (hsN : mat N K s * spANil K N j = spANil K N j * mat N K s) (x : Fin N ⊕ Fin N → K) :
    mat N K s *ᵥ (spANil K N j *ᵥ x) = spANil K N j *ᵥ (mat N K s *ᵥ x) := by
  rw [mulVec_mulVec, hsN, ← mulVec_mulVec]

theorem mat_spARep_mulVec (x : Fin N ⊕ Fin N → K) :
    mat N K (spARep N j) *ᵥ x = x + spANil K N j *ᵥ x := by
  rw [mat_spARep_eq, add_mulVec, one_mulVec]

theorem spANil_mul_self : spANil K N j * spANil K N j = 0 := by
  rw [spANil, fromBlocks_multiply]
  simp

theorem mat_spARep_mul_spANil : mat N K (spARep N j) * spANil K N j = spANil K N j := by
  rw [mat_spARep_eq, Matrix.add_mul, Matrix.one_mul, spANil_mul_self, add_zero]

theorem spARep_inv [CharP K 2] : (spARep N j : StatedSp N K)⁻¹ = spARep N j :=
  inv_eq_of_mul_eq_one_right (spARep_mul_self N j)

end Frames

section FixedPair

variable {N j : ℕ}

@[expose] def frameFixed (j : ℕ) (v v' : Fin N ⊕ Fin N → K) :
    Fin 2 ⊕ Fin 2 → Fin N ⊕ Fin N → K :=
  Sum.elim ![spANil K N j *ᵥ v, spANil K N j *ᵥ v'] ![v', v]

variable [CharP K 2] (hjn : 2 * j ≤ N) {v v' : Fin N ⊕ Fin N → K} (hv : IsFVec j v)
  (hv' : IsFVec j v') (hvv' : spBForm j v v' = 1)
include hjn hv hv' hvv'

theorem frameFixed_gram :
    (colMat (frameFixed j v v'))ᵀ * gram K N * colMat (frameFixed j v v') = gram K 2 := by
  have h1 : spBForm j v' v = 1 := by rw [spBForm_comm, hvv']
  have h2 := spBForm_self hjn v
  have h3 := spBForm_self hjn v'
  have h4 := spForm_eq_zero_of_isFVec hv hv'
  have h5 := spForm_eq_zero_of_isFVec hv' hv
  have h6 := spForm_eq_zero_of_isFVec hv hv
  have h7 := spForm_eq_zero_of_isFVec hv' hv'
  ext c c'
  rw [colMat_gram_apply]
  rcases c with c | c <;> rcases c' with c' | c' <;> fin_cases c <;> fin_cases c' <;>
    simp [frameFixed, spForm_spANil_left, spForm_spANil_right,
      spBForm_spANil_right, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, hvv', h1,
      h2, h3, h4, h5, h6, h7]

theorem exists_perfect_of_fixedPair [Finite K] (hK : Nat.card K = 2) {s : StatedSp N K}
    (hsN : mat N K s * spANil K N j = spANil K N j * mat N K s)
    (hsv : mat N K s *ᵥ v = v) (hsv' : mat N K s *ᵥ v' = v') :
    ∃ P : Subgroup (StatedSp N K), ⁅P, P⁆ = P ∧ P ≤ centralizer ({s} : Set (StatedSp N K)) ∧
      ¬ P ≤ centralizer ({spARep N j} : Set (StatedSp N K)) := by
  set u := frameFixed j v v' with hu
  set A := colMat u with hA
  have hG : Aᵀ * gram K N * A = gram K 2 := frameFixed_gram hjn hv hv' hvv'
  have hGG : gram K 2 * gram K 2 = (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
    gram_mul_gram
  set Φ := frameHom A (gram K 2) hG hGG (mat 2 K) mat_transpose_mul_gram_mul with hΦ
  have hsu : ∀ c, mat N K s *ᵥ u c = u c := by
    intro c
    rcases c with c | c <;> fin_cases c <;>
      simp [hu, frameFixed, mat_mulVec_spANil hsN, hsv, hsv']
  have hsA : mat N K s * A = A * (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [Matrix.mul_one, hA, mul_colMat]
    exact congrArg colMat (funext hsu)
  have hsA' : mat N K s⁻¹ * A = A * (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [Matrix.mul_one, hA, mul_colMat]
    exact congrArg colMat (funext fun c => mat_inv_mulVec_of_mulVec_eq (hsu c))
  have hsB := frameInv_mul_mat hG hGG hsA hsA'
  have hau : ∀ c, mat N K (spARep N j) *ᵥ u c =
      ∑ c', (aTwoMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) c' c • u c' := by
    intro c
    rcases c with c | c <;> fin_cases c <;>
      simp [hu, frameFixed, mat_spARep_mulVec, mat_spARep_mul_spANil, aTwoMat,
        Fintype.sum_sum_type, Fin.sum_univ_two] <;> abel
  have haA : mat N K (spARep N j) * A = A * aTwoMat := mul_colMat_eq_colMat_mul hau
  have haA' : mat N K (spARep N j)⁻¹ * A = A * aTwoMat := by
    rw [spARep_inv]
    exact haA
  have haB := frameInv_mul_mat hG hGG haA haA'
  refine ⟨(commutator (StatedSp 2 K)).map Φ, ?_, ?_, fun hP => ?_⟩
  · rw [← Subgroup.map_commutator, commutator_commutator_statedSp_two hK]
  · rintro _ ⟨g, -, rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply mat_injective
    rw [map_mul, map_mul, mat_frameHom]
    exact (commute_frameMat hsA hsB (by rw [Matrix.one_mul, Matrix.mul_one])).symm
  · have hmem := hP (Subgroup.mem_map_of_mem Φ (nsElt_mem_commutator_statedSp_two (K := K)))
    rw [mem_centralizer_singleton_iff] at hmem
    have h := congrArg (mat N K) hmem
    rw [map_mul, map_mul, mat_frameHom] at h
    exact not_commute_nsElt_aTwoMat (commute_of_commute_frameMat hG hGG haA haB h.symm)

end FixedPair

section Fpf

variable {N j : ℕ}

abbrev FpfIdx : Type := (Fin 2 ⊕ Fin 2) ⊕ (Fin 2 ⊕ Fin 2)

@[expose] def frameFpf (j : ℕ) (v w v₁ w₁ : Fin N ⊕ Fin N → K) : FpfIdx → Fin N ⊕ Fin N → K :=
  Sum.elim (Sum.elim ![spANil K N j *ᵥ v, spANil K N j *ᵥ w] ![v, w])
    (Sum.elim ![spANil K N j *ᵥ v₁, spANil K N j *ᵥ w₁] ![v₁, w₁])

variable (K) in
@[expose] def gramFpf : Matrix FpfIdx FpfIdx K := fromBlocks 0 (gram K 2) (gram K 2) 0

theorem gramFpf_mul_self : gramFpf K * gramFpf K = -1 := by
  rw [gramFpf, fromBlocks_multiply, gram_mul_gram]
  simp [← fromBlocks_one, fromBlocks_neg]

@[expose] noncomputable def diagTwo : StatedSp 2 K →* Matrix FpfIdx FpfIdx K where
  toFun g := fromBlocks (mat 2 K g) 0 0 (mat 2 K g)
  map_one' := by rw [map_one, fromBlocks_one]
  map_mul' g h := by
    rw [map_mul, fromBlocks_multiply]
    simp

theorem diagTwo_apply (g : StatedSp 2 K) : diagTwo g = fromBlocks (mat 2 K g) 0 0 (mat 2 K g) :=
  rfl

theorem diagTwo_isometry (g : StatedSp 2 K) :
    (diagTwo g)ᵀ * gramFpf K * diagTwo g = gramFpf K := by
  have h := mat_transpose_mul_gram_mul g
  rw [diagTwo_apply, gramFpf, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [h]

@[expose] def sFpfMat : Matrix FpfIdx FpfIdx K := fromBlocks 0 1 1 1

@[expose] def sInvFpfMat : Matrix FpfIdx FpfIdx K := fromBlocks 1 1 1 0

@[expose] def aFpfMat : Matrix FpfIdx FpfIdx K := fromBlocks cTwoMat 0 0 cTwoMat

theorem sFpfMat_mul_diagTwo (g : StatedSp 2 K) :
    sFpfMat * diagTwo g = diagTwo g * sFpfMat := by
  rw [diagTwo_apply, sFpfMat, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem not_commute_aFpfMat_diagTwo_nsElt :
    aFpfMat * diagTwo (nsElt (K := K) (0 : Fin 2)) ≠ diagTwo (nsElt 0) * aFpfMat := by
  intro h
  rw [diagTwo_apply, aFpfMat, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact not_commute_nsElt_cTwoMat (fromBlocks_inj.1 h).1

theorem sFpfMat_mul_self [CharP K 2] :
    (sFpfMat : Matrix FpfIdx FpfIdx K) * sFpfMat = sInvFpfMat := by
  rw [sFpfMat, sInvFpfMat, fromBlocks_multiply]
  have h : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [h]

theorem mat_inv_eq_mul_self {s : StatedSp N K} (hs3 : s ^ 3 = 1) :
    mat N K s⁻¹ = mat N K s * mat N K s := by
  rw [← map_mul, inv_eq_of_mul_eq_one_right (show s * (s * s) = 1 by rw [← pow_three, hs3])]

theorem exists_perfect_of_fpf [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hjn : 2 * j ≤ N)
    {s : StatedSp N K} (hsN : mat N K s * spANil K N j = spANil K N j * mat N K s)
    (hsF : ∀ x, IsFVec j x → IsFVec j (mat N K s *ᵥ x)) (hs3 : s ^ 3 = 1)
    (hsq : ∀ x, IsFVec j x → mat N K s *ᵥ (mat N K s *ᵥ x) + mat N K s *ᵥ x + x = 0)
    {v w : Fin N ⊕ Fin N → K} (hv : IsFVec j v) (hw : IsFVec j w)
    (hvsv : spBForm j v (mat N K s *ᵥ v) = 1) (hwsw : spBForm j w (mat N K s *ᵥ w) = 1)
    (hwv : spBForm j w v = 0) (hwsv : spBForm j w (mat N K s *ᵥ v) = 0) :
    ∃ P : Subgroup (StatedSp N K), ⁅P, P⁆ = P ∧ P ≤ centralizer ({s} : Set (StatedSp N K)) ∧
      ¬ P ≤ centralizer ({spARep N j} : Set (StatedSp N K)) := by
  set S := mat N K s with hSdef
  have hsq' : ∀ x, IsFVec j x → S *ᵥ (S *ᵥ x) = S *ᵥ x + x := by
    intro x hx
    have h := hsq x hx
    rw [add_assoc] at h
    rw [add_eq_zero_iff_eq_neg.1 h, neg_vec_eq_self]
  have hssv := hsq' v hv
  have hssw := hsq' w hw
  have hv₁ := hsF v hv
  have hw₁ := hsF w hw
  have hvv := spBForm_self hjn v
  have hww := spBForm_self hjn w
  have hv₁v₁ := spBForm_self hjn (S *ᵥ v)
  have hw₁w₁ := spBForm_self hjn (S *ᵥ w)
  have hv₁v : spBForm j (S *ᵥ v) v = 1 := by rw [spBForm_comm, hvsv]
  have hw₁w : spBForm j (S *ᵥ w) w = 1 := by rw [spBForm_comm, hwsw]
  have hvw : spBForm j v w = 0 := by rw [spBForm_comm, hwv]
  have hv₁w : spBForm j (S *ᵥ v) w = 0 := by rw [spBForm_comm, hwsv]
  have hw₁v : spBForm j (S *ᵥ w) v = 0 := by
    calc spBForm j (S *ᵥ w) v = spBForm j (S *ᵥ w) (S *ᵥ (S *ᵥ (S *ᵥ v))) := by
          rw [mat_mulVec_cube hs3]
      _ = spBForm j w (S *ᵥ (S *ᵥ v)) := spBForm_mulVec hsN _ _
      _ = 0 := by rw [hssv, spBForm_add_right, hwsv, hwv, add_zero]
  have hvw₁ : spBForm j v (S *ᵥ w) = 0 := by rw [spBForm_comm, hw₁v]
  have hv₁w₁ : spBForm j (S *ᵥ v) (S *ᵥ w) = 0 := by rw [spBForm_mulVec hsN, hvw]
  have hw₁v₁ : spBForm j (S *ᵥ w) (S *ᵥ v) = 0 := by rw [spBForm_mulVec hsN, hwv]
  have hSNv : S *ᵥ (spANil K N j *ᵥ v) = spANil K N j *ᵥ (S *ᵥ v) := mat_mulVec_spANil hsN v
  have hSNw : S *ᵥ (spANil K N j *ᵥ w) = spANil K N j *ᵥ (S *ᵥ w) := mat_mulVec_spANil hsN w
  have hSNv₁ : S *ᵥ (spANil K N j *ᵥ (S *ᵥ v)) =
      spANil K N j *ᵥ (S *ᵥ v) + spANil K N j *ᵥ v := by
    rw [mat_mulVec_spANil hsN, hssv, mulVec_add]
  have hSNw₁ : S *ᵥ (spANil K N j *ᵥ (S *ᵥ w)) =
      spANil K N j *ᵥ (S *ᵥ w) + spANil K N j *ᵥ w := by
    rw [mat_mulVec_spANil hsN, hssw, mulVec_add]
  clear_value S
  generalize hv1 : S *ᵥ v = v₁ at *
  generalize hw1 : S *ᵥ w = w₁ at *
  set u := frameFpf j v w v₁ w₁ with hu
  set A := colMat u with hA
  have hG : Aᵀ * gram K N * A = gramFpf K := by
    ext c c'
    rw [colMat_gram_apply]
    rcases c with (c | c) | (c | c) <;> rcases c' with (c' | c') | (c' | c') <;> fin_cases c <;>
      fin_cases c' <;>
      simp [hu, frameFpf, gramFpf, spForm_spANil_left, spForm_spANil_right,
        spBForm_spANil_right, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
        hvv, hww, hv₁v₁, hw₁w₁, hvsv, hwsw, hwv, hwsv,
        hv₁v, hw₁w, hvw, hv₁w, hw₁v, hvw₁, hv₁w₁, hw₁v₁,
        spForm_eq_zero_of_isFVec hv hv, spForm_eq_zero_of_isFVec hv hw,
        spForm_eq_zero_of_isFVec hv hv₁, spForm_eq_zero_of_isFVec hv hw₁,
        spForm_eq_zero_of_isFVec hw hv, spForm_eq_zero_of_isFVec hw hw,
        spForm_eq_zero_of_isFVec hw hv₁, spForm_eq_zero_of_isFVec hw hw₁,
        spForm_eq_zero_of_isFVec hv₁ hv, spForm_eq_zero_of_isFVec hv₁ hw,
        spForm_eq_zero_of_isFVec hv₁ hv₁, spForm_eq_zero_of_isFVec hv₁ hw₁,
        spForm_eq_zero_of_isFVec hw₁ hv, spForm_eq_zero_of_isFVec hw₁ hw,
        spForm_eq_zero_of_isFVec hw₁ hv₁, spForm_eq_zero_of_isFVec hw₁ hw₁]
  have hGG : gramFpf K * gramFpf K = -1 := gramFpf_mul_self
  set Φ := frameHom A (gramFpf K) hG hGG diagTwo diagTwo_isometry with hΦ
  have hsu : ∀ c, S *ᵥ u c = ∑ c', (sFpfMat : Matrix FpfIdx FpfIdx K) c' c • u c' := by
    intro c
    rcases c with (c | c) | (c | c) <;> fin_cases c <;>
      simp [-Matrix.mulVec_mulVec, hu, frameFpf, sFpfMat, Fintype.sum_sum_type, Fin.sum_univ_two,
        hSNv, hSNw, hSNv₁, hSNw₁, hssv, hssw, hv1, hw1] <;> abel
  set D : Matrix FpfIdx FpfIdx K := sFpfMat with hD
  have hsA : S * A = A * D := mul_colMat_eq_colMat_mul hsu
  have hsA' : mat N K s⁻¹ * A = A * sInvFpfMat := by
    rw [mat_inv_eq_mul_self hs3, ← hSdef, ← sFpfMat_mul_self, ← hD]
    calc S * S * A = S * (S * A) := Matrix.mul_assoc _ _ _
      _ = S * (A * D) := by rw [hsA]
      _ = (S * A) * D := (Matrix.mul_assoc _ _ _).symm
      _ = A * D * D := by rw [hsA]
      _ = A * (D * D) := Matrix.mul_assoc _ _ _
  rw [hSdef] at hsA
  have hsB := frameInv_mul_mat hG hGG hsA hsA'
  have hau : ∀ c, mat N K (spARep N j) *ᵥ u c =
      ∑ c', (aFpfMat : Matrix FpfIdx FpfIdx K) c' c • u c' := by
    intro c
    rcases c with (c | c) | (c | c) <;> fin_cases c <;>
      simp [hu, frameFpf, mat_spARep_mulVec, mat_spARep_mul_spANil, aFpfMat, cTwoMat,
        Fintype.sum_sum_type, Fin.sum_univ_two] <;> abel
  have haA : mat N K (spARep N j) * A = A * aFpfMat := mul_colMat_eq_colMat_mul hau
  have haA' : mat N K (spARep N j)⁻¹ * A = A * aFpfMat := by
    rw [spARep_inv]
    exact haA
  have haB := frameInv_mul_mat hG hGG haA haA'
  refine ⟨(commutator (StatedSp 2 K)).map Φ, ?_, ?_, fun hP => ?_⟩
  · rw [← Subgroup.map_commutator, commutator_commutator_statedSp_two hK]
  · rintro _ ⟨g, -, rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply mat_injective
    rw [map_mul, map_mul, mat_frameHom]
    exact (commute_frameMat hsA hsB (sFpfMat_mul_diagTwo g)).symm
  · have hmem := hP (Subgroup.mem_map_of_mem Φ (nsElt_mem_commutator_statedSp_two (K := K)))
    rw [mem_centralizer_singleton_iff] at hmem
    have h := congrArg (mat N K) hmem
    rw [map_mul, map_mul, mat_frameHom] at h
    exact not_commute_aFpfMat_diagTwo_nsElt (commute_of_commute_frameMat hG hGG haA haB h.symm)

end Fpf

theorem exists_perfect_of_mem_range_spALeviHom [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {N j : ℕ} (hj : 2 ≤ j) (hjn : 2 * j ≤ N) {s : StatedSp N K}
    (hs : s ∈ (spALeviHom hjn).range) (hs3 : s ^ 3 = 1) :
    ∃ P : Subgroup (StatedSp N K), ⁅P, P⁆ = P ∧ P ≤ centralizer ({s} : Set (StatedSp N K)) ∧
      ¬ P ≤ centralizer ({spARep N j} : Set (StatedSp N K)) := by
  have hsN := mat_mul_spANil_of_mem_range hjn hs
  have hsF : ∀ x, IsFVec j x → IsFVec j (mat N K s *ᵥ x) := fun x hx =>
    isFVec_mulVec_of_mem_range hjn hs hx
  rcases exists_fixedPair_or_fpf hjn hsN hsF hs3 hK hj with
    ⟨v, v', hv, hv', hsv, hsv', hvv'⟩ | ⟨hsq, v, w, hv, hw, hvsv, hwsw, hwv, hwsv⟩
  · exact exists_perfect_of_fixedPair hjn hv hv' hvv' hK hsN hsv hsv'
  · exact exists_perfect_of_fpf hK hjn hsN hsF hs3 hsq hv hw hvsv hwsw hwv hwsv

theorem spATwoTorusInput_holds : SpATwoTorusInput := by
  intro N j K _ _ _ hK hj hjN S hSC hS3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu, hle⟩ := F4Pilot.exists_mem_map_conj_le_of_le_sup (isPGroup_spARadical hjN)
    (range_spALeviHom_le_normalizer hjN) (spARadical_inf_range_eq_bot hjN)
    (hSC.trans (centralizer_spARep_le_sup hjN)) (by rw [hS3]; decide)
  have hua : u * spARep N j = spARep N j * u :=
    mem_centralizer_singleton_iff.1 (spARadical_le_centralizer hjN hu)
  set S' := S.map (MulAut.conj u).toMonoidHom with hS'
  have hS'3 : Nat.card S' = 3 := by
    rw [hS', Subgroup.card_map_of_injective (MulAut.conj u).injective, hS3]
  have hcyc : IsCyclic S' := isCyclic_of_prime_card hS'3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S')
  have hs : (g : StatedSp N K) ∈ (spALeviHom hjN).range := hle g.2
  have hs3 : (g : StatedSp N K) ^ 3 = 1 := by
    have h : g ^ Nat.card S' = 1 := pow_card_eq_one'
    rw [hS'3] at h
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  obtain ⟨P₀, hP₀perf, hP₀s, hP₀a⟩ := exists_perfect_of_mem_range_spALeviHom hK hj hjN hs hs3
  have hP₀S' : P₀ ≤ centralizer (S' : Set (StatedSp N K)) := by
    intro p hp
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    have hps : Commute p (g : StatedSp N K) := mem_centralizer_singleton_iff.1 (hP₀s hp)
    have hx' : x = (g : StatedSp N K) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [hx']
    exact ((hps.zpow_right k).eq).symm
  refine ⟨P₀.map (MulAut.conj u⁻¹).toMonoidHom, ?_, ?_, fun hP => ?_⟩
  · rw [← Subgroup.map_commutator, hP₀perf]
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    have hux : u * x * u⁻¹ ∈ S' := ⟨x, hx, rfl⟩
    have hc := mem_centralizer_iff.1 (hP₀S' hy) _ hux
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc x * (u⁻¹ * y * u) = u⁻¹ * ((u * x * u⁻¹) * y) * u := by group
      _ = u⁻¹ * (y * (u * x * u⁻¹)) * u := by rw [hc]
      _ = u⁻¹ * y * u * x := by group
  · apply hP₀a
    intro y hy
    have hmem := hP ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff] at hmem ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hmem
    have hconj : u * spARep N j * u⁻¹ = spARep N j := by rw [hua, mul_inv_cancel_right]
    calc y * spARep N j = y * (u * spARep N j * u⁻¹) := by rw [hconj]
      _ = u * ((u⁻¹ * y * u) * spARep N j) * u⁻¹ := by group
      _ = u * (spARep N j * (u⁻¹ * y * u)) * u⁻¹ := by rw [hmem]
      _ = (u * spARep N j * u⁻¹) * y := by group
      _ = spARep N j * y := by rw [hconj]

end CFSG.SeitzReduction.SymplecticPilot
