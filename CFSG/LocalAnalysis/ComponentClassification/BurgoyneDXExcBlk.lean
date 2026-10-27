module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcSign
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOCent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.C (blkL blkL_mul blkL_one compInd_mul_self compInd_compl
  blkLGL coe_blkLGL)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat compInd compInd_apply
  signMat_mul_self)

variable {K : Type} [Field K] {d : ℕ}

structure ExcData (R : GL (Fin d) K) (M : Subgroup (GL (Fin d) K)) : Prop where
  le : M ≤ matrixDerived (oQ R)
  perf : ⁅M, M⁆ = M
  par : ∀ u ∈ M, u * u = 1 → u ≠ 1 →
    finrank K (negE ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) % 4 = 2
  klein : ∃ u₁ ∈ M, ∃ u₂ ∈ M, u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ ∧
    u₁ * u₂ = u₂ * u₁
  normal : ∀ N : Subgroup (GL (Fin d) K), N ≤ M → (N.subgroupOf M).Normal →
    (∃ u ∈ N, u * u = 1 ∧ u ≠ 1) → N = M

theorem ExcData.transport {R R' : GL (Fin d) K} {M : Subgroup (GL (Fin d) K)}
    (h : ExcData R M) (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, oQ R' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * oQ R v) :
    ExcData R' (M.map (MulAut.conj S).toMonoidHom) := by
  set φ := (MulAut.conj S).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj S).injective
  have hφv : ∀ g : GL (Fin d) K, ((φ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (S : Matrix (Fin d) (Fin d) K) * g * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    fun g => by simp [hφ, MulAut.conj_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_matrixDerived_conj S ν hS]
    exact map_mono h.le
  · rw [← Subgroup.map_commutator, h.perf]
  · rintro _ ⟨u, hu, rfl⟩ huu hu1
    have huu' : u * u = 1 := hφinj (by rw [map_mul, huu, map_one])
    have hu1' : u ≠ 1 := fun h1 => hu1 (by rw [h1, map_one])
    rw [hφv, finrank_negE_conj]
    exact h.par u hu huu' hu1'
  · obtain ⟨u₁, h₁, u₂, h₂, e₁, e₂, n₁, n₂, n₁₂, c₁₂⟩ := h.klein
    refine ⟨φ u₁, ⟨u₁, h₁, rfl⟩, φ u₂, ⟨u₂, h₂, rfl⟩, by rw [← map_mul, e₁, map_one],
      by rw [← map_mul, e₂, map_one], fun h1 => n₁ (hφinj (by rw [h1, map_one])),
      fun h1 => n₂ (hφinj (by rw [h1, map_one])), fun h1 => n₁₂ (hφinj h1),
      by rw [← map_mul, c₁₂, map_mul]⟩
  · intro N hN hn ⟨u, huN, huu, hu1⟩
    set N₀ := N.comap φ with hN₀
    have hN₀M : N₀ ≤ M := by
      intro g hg
      obtain ⟨m, hm, hmg⟩ := hN hg
      rw [← hφinj hmg]
      exact hm
    have hN₀n : (N₀.subgroupOf M).Normal := by
      refine ⟨fun a ha b => ?_⟩
      rw [mem_subgroupOf] at ha ⊢
      have hb : φ b ∈ M.map φ := ⟨b, b.2, rfl⟩
      have := hn.conj_mem ⟨φ a, hN ha⟩ (mem_subgroupOf.2 ha) ⟨φ b, hb⟩
      rw [mem_subgroupOf] at this
      change φ ((b : GL (Fin d) K) * a * (b : GL (Fin d) K)⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact this
    obtain ⟨u₀, hu₀, rfl⟩ := hN huN
    have hu₀u : u₀ * u₀ = 1 := hφinj (by rw [map_mul, huu, map_one])
    have hu₀1 : u₀ ≠ 1 := fun h1 => hu1 (by rw [h1, map_one])
    have heq := h.normal N₀ hN₀M hN₀n ⟨u₀, huN, hu₀u, hu₀1⟩
    refine le_antisymm hN ?_
    rintro _ ⟨m, hm, rfl⟩
    rw [← heq] at hm
    exact hm

theorem mem_negE_signMat (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)} {v : Fin d → K} :
    v ∈ negE (signMat K I) ↔ ∀ i, i ∉ I → v i = 0 := by
  rw [mem_negE]
  constructor
  · intro h i hi
    have e := congrFun h i
    simp only [signMat, mulVec_diagonal, hi, ↓reduceIte, one_mul, Pi.neg_apply] at e
    have h2v : (2 : K) * v i = 0 := by linear_combination e
    exact (mul_eq_zero.1 h2v).resolve_left h2
  · intro h
    funext i
    simp only [signMat, mulVec_diagonal, Pi.neg_apply]
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi, h i hi]

theorem compInd_mulVec_eq_zero_iff {I : Finset (Fin d)} {v : Fin d → K} :
    compInd K I *ᵥ v = 0 ↔ ∀ i, i ∉ I → v i = 0 := by
  constructor
  · intro h i hi
    have e := congrFun h i
    simpa [compInd, mulVec_diagonal, hi] using e
  · intro h
    funext i
    by_cases hi : i ∈ I
    · simp [compInd, mulVec_diagonal, hi]
    · simp [compInd, mulVec_diagonal, hi, h i hi]

theorem posE_signMat (h2 : (2 : K) ≠ 0) (J : Finset (Fin d)) :
    posE (signMat K J) = negE (signMat K Jᶜ) := by
  ext v
  rw [mem_negE_signMat h2, mem_posE]
  constructor
  · intro h i hi
    rw [Finset.mem_compl, not_not] at hi
    have e := congrFun h i
    simp only [signMat, mulVec_diagonal, hi, ↓reduceIte, neg_one_mul] at e
    have h2v : (2 : K) * v i = 0 := by linear_combination -e
    exact (mul_eq_zero.1 h2v).resolve_left h2
  · intro h
    funext i
    simp only [signMat, mulVec_diagonal]
    by_cases hi : i ∈ J
    · simp [hi, h i (by simp [hi])]
    · simp [hi]

theorem negE_blkL (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)} {B : Matrix (Fin d) (Fin d) K}
    (hB : B * compInd K I = compInd K I * B) :
    negE (blkL (compInd K I) B) = negE B ⊓ negE (signMat K I) := by
  set c := compInd K I with hc
  have hcc : c * c = c := compInd_mul_self I
  ext v
  rw [Submodule.mem_inf, mem_negE, mem_negE, mem_negE_signMat h2,
    ← compInd_mulVec_eq_zero_iff, blkL, add_mulVec]
  constructor
  · intro h
    have e := congrArg (fun z => c *ᵥ z) h
    simp only [mulVec_add, mulVec_mulVec, mulVec_neg] at e
    rw [← Matrix.mul_assoc, ← hB, Matrix.mul_assoc, C.mul_one_sub_self hcc, Matrix.mul_zero,
      zero_mulVec, zero_add, hcc] at e
    have hcv : c *ᵥ v = 0 := by
      have h2v : (2 : K) • (c *ᵥ v) = 0 := by rw [two_smul]; nth_rw 1 [e]; rw [neg_add_cancel]
      exact (smul_eq_zero.1 h2v).resolve_left h2
    refine ⟨?_, hcv⟩
    rw [hcv, add_zero, ← mulVec_mulVec, sub_mulVec, one_mulVec, hcv, sub_zero] at h
    exact h
  · rintro ⟨h, hcv⟩
    rw [hcv, add_zero, ← mulVec_mulVec, sub_mulVec, one_mulVec, hcv, sub_zero, h]

theorem even_finrank_negE_inf (h2 : (2 : K) ≠ 0) {M : Subgroup (GL (Fin d) K)}
    (hperf : ⁅M, M⁆ = M) {I : Finset (Fin d)}
    (hc : ∀ m ∈ M, (m : Matrix (Fin d) (Fin d) K) * compInd K I = compInd K I * m)
    {u : GL (Fin d) K} (hu : u ∈ M) (huu : u * u = 1) :
    Even (finrank K ↥(negE ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ⊓
      negE (signMat K I))) := by
  set c := compInd K I with hcdef
  have hcc : c * c = c := compInd_mul_self I
  let F : M →* Kˣ :=
    { toFun := fun m => GeneralLinearGroup.det (blkLGL hcc (m : GL (Fin d) K) (hc m m.2))
      map_one' := by
        apply Units.ext
        simp only [GeneralLinearGroup.val_det_apply, coe_blkLGL, OneMemClass.coe_one,
          Units.val_one, blkL_one, det_one]
      map_mul' := fun x y => by
        apply Units.ext
        simp only [GeneralLinearGroup.val_det_apply, coe_blkLGL, Subgroup.coe_mul, Units.val_mul]
        rw [← blkL_mul hcc (hc y y.2), det_mul] }
  have hF : F ⟨u, hu⟩ = 1 := by
    have hperf' : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hperf
    have hle := Abelianization.commutator_subset_ker F
    rw [Group.isPerfect_def.1 hperf'] at hle
    exact hle (mem_top _)
  have hdet1 : (blkL c ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).det = 1 := by
    have := congrArg Units.val hF
    simpa [F, GeneralLinearGroup.val_det_apply, coe_blkLGL] using this
  have hinv : blkL c ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      blkL c ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [blkL_mul hcc (hc u hu), ← Units.val_mul, huu, Units.val_one, blkL_one]
  have hdet := CFSG.GH74.Generic.involution_det h2 _ hinv
  rw [hdet1] at hdet
  rw [← negE_blkL h2 (hc u hu)]
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  exact (neg_one_pow_eq_one_iff_even hne).1 hdet.symm

end CFSG.ComponentClassification.Burgoyne.DX
