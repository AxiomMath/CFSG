module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOSgnF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOPc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPcCore
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.C (isQuasisimple_isoCent_pc)
open CFSG.ComponentClassification.Burgoyne.PSL (signMat reflGL rotGL)
open scoped commutatorElement

variable {K : Type} [Field K] {n : ℕ}

theorem sq_eq_one_of_smul_isometry {d : ℕ} (hd : 0 < d) (R : GL (Fin d) K) {μ : K}
    (h : (μ • (1 : Matrix (Fin d) (Fin d) K))ᵀ * R * (μ • 1) = R) : μ ^ 2 = 1 := by
  rw [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul] at h
  have e := congrArg (fun M => M * ((R⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) h
  simp only [Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one] at e
  have e' := congrFun (congrFun e ⟨0, hd⟩) ⟨0, hd⟩
  simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at e'
  rw [sq]
  exact e'

theorem eq_blkDiag_of_commute_isoCent (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    {W₀ j : Matrix (Fin 2) (Fin 2) K} {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n W₀)
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n j)
    {D : Matrix (Fin (2 * n)) (Fin (2 * n)) K}
    (hD : ∀ Y ∈ ⁅isoCent R A, isoCent R A⁆, D * (Y : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      Y * D) :
    D = blkDiag n (Matrix.of fun a b =>
      D (pairEquiv n (⟨0, by omega⟩, a)) (pairEquiv n (⟨0, by omega⟩, b))) := by
  have hmem : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K)ᵀ * X = 1 →
      kronGL K n X ∈ isoCent R A := fun X hX => kronGL_mem_isoCent_blkDiag hR hA hX
  have hcomm2 : ∀ X Y : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K)ᵀ * X = 1 →
      (Y : Matrix (Fin n) (Fin n) K)ᵀ * Y = 1 →
        D * kronI K n ((⁅X, Y⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          kronI K n ((⁅X, Y⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D := by
    intro X Y hX hY
    have hm : kronGL K n ⁅X, Y⁆ ∈ ⁅isoCent R A, isoCent R A⁆ := by
      rw [map_commutatorElement]
      exact commutator_mem_commutator (hmem X hX) (hmem Y hY)
    have e := hD _ hm
    rwa [coe_kronGL] at e
  refine eq_blkDiag_of_kron h2 hn (fun i j hij => ?_) (fun i j k _ _ _ => ?_)
  · have h01 : (0 : K) ^ 2 + (1 : K) ^ 2 = 1 := by ring
    have e := hcomm2 _ _ (reflGL_orth i) (rotGL_orth hij h01)
    rwa [signMat_pair_eq_commutator hij h01] at e
  · have e := hcomm2 _ _ (permGL_orth (Equiv.swap i j)) (permGL_orth (Equiv.swap j k))
    rwa [coe_commutator_permGL] at e

theorem det_jMat_neg_one : (jMat (-1 : K)).det = 1 := by
  rw [det_fin_two]
  simp [jMat]

theorem eq_jMat_of_mul_self_eq_neg_one (h2 : (2 : K) ≠ 0) {Y : Matrix (Fin 2) (Fin 2) K}
    (hY : Yᵀ * diagonal ![1, 1] * Y = diagonal ![1, 1]) (hd : Y.det = 1) (hY2 : Y * Y = -1) :
    Y = jMat (-1) ∨ Y = -jMat (-1) := by
  have hw : ∀ i, (![1, 1] : Fin 2 → K) i ≠ 0 := by
    intro i
    fin_cases i <;> simp
  obtain ⟨he, hc⟩ := binary_isometry_entries hw hY
  rw [hd, one_mul] at he hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, one_mul] at hc
  have h00 : (Y * Y) 0 0 = -1 := by rw [hY2]; simp
  rw [binary_mul_apply] at h00
  rw [det_fin_two] at hd
  have ha : Y 0 0 = 0 := by
    have h1 : 2 * (Y 0 0 * Y 0 0) = 0 := by linear_combination h00 + hd - Y 0 0 * he
    exact mul_self_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left h2)
  have hb : Y 0 1 * Y 0 1 = 1 := by
    rw [ha, he, hc] at hd
    linear_combination hd
  rcases mul_self_eq_one_iff.1 hb with h | h
  · right
    refine binary_ext ?_ ?_ ?_ ?_ <;> simp [jMat, ha, he, hc, h]
  · left
    refine binary_ext ?_ ?_ ?_ ?_ <;> simp [jMat, ha, he, hc, h]

theorem lift_eq_blkDiag_pc [Finite K] (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) (hn : 3 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))))
    {A : matrixDerived (oQ R)}
    (hA : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat (-1 : K)))
    {X : Type} [Group X] [Finite X] (π : matrixDerived (oQ R) →* X)
    (hπ : Function.Surjective π) (hker : ∀ s, π s = 1 → s ∈ center (matrixDerived (oQ R)))
    {g : X} (hg : ∀ L : Subgroup (centralizer ({π A} : Set X)), IsComponent L →
      Even (Nat.card L) → ∀ k ∈ L, (k : X) * g = g * k)
    {g' : matrixDerived (oQ R)} (hg' : π g' = g) :
    ∃ D₀ : Matrix (Fin 2) (Fin 2) K,
      ((g' : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n D₀ ∧
        D₀ᵀ * diagonal ![1, 1] * D₀ = diagonal ![1, 1] := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hc : (-1 : K) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hR, blkDiag_transpose, wMat, diagonal_transpose]
  have hq := isQuasisimple_isoCent_pc hK hp hKc hc hn hR hA
  have hZΩ : ⁅isoCent R (A : GL (Fin (2 * n)) K), isoCent R (A : GL (Fin (2 * n)) K)⁆ ≤
      matrixDerived (oQ R) :=
    (commutator_mono inf_le_left inf_le_left).trans (matrixDerived_oQ h2 R hRs).ge
  have hZn : ∀ x ∈ isoCent R (A : GL (Fin (2 * n)) K),
      ∀ m ∈ ⁅isoCent R (A : GL (Fin (2 * n)) K), isoCent R (A : GL (Fin (2 * n)) K)⁆,
        x * m * x⁻¹ ∈ ⁅isoCent R (A : GL (Fin (2 * n)) K), isoCent R (A : GL (Fin (2 * n)) K)⁆ := by
    intro x hx m hm
    have hle : ⁅isoCent R (A : GL (Fin (2 * n)) K), isoCent R (A : GL (Fin (2 * n)) K)⁆ ≤
        (⁅isoCent R (A : GL (Fin (2 * n)) K), isoCent R (A : GL (Fin (2 * n)) K)⁆).comap
          (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by group
      rw [e]
      exact commutator_mem_commutator (mul_mem (mul_mem hx ha) (inv_mem hx))
        (mul_mem (mul_mem hx hb) (inv_mem hx))
    exact hle hm
  have hMq : IsQuasisimple ((⁅isoCent R (A : GL (Fin (2 * n)) K),
      isoCent R (A : GL (Fin (2 * n)) K)⁆).subgroupOf (matrixDerived (oQ R))) :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hZΩ).symm hq
  have hNC : (⁅isoCent R (A : GL (Fin (2 * n)) K),
      isoCent R (A : GL (Fin (2 * n)) K)⁆).subgroupOf (matrixDerived (oQ R)) ≤
        centralizer ({A} : Set (matrixDerived (oQ R))) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 (commutator_le_self _ hx)).2)
  have hNn : ∀ x ∈ centralizer ({A} : Set (matrixDerived (oQ R))),
      ∀ m ∈ (⁅isoCent R (A : GL (Fin (2 * n)) K),
        isoCent R (A : GL (Fin (2 * n)) K)⁆).subgroupOf (matrixDerived (oQ R)),
        x * m * x⁻¹ ∈ (⁅isoCent R (A : GL (Fin (2 * n)) K),
          isoCent R (A : GL (Fin (2 * n)) K)⁆).subgroupOf (matrixDerived (oQ R)) := by
    intro x hx m hm
    rw [mem_subgroupOf] at hm ⊢
    have hxZ : (x : GL (Fin (2 * n)) K) ∈ isoCent R (A : GL (Fin (2 * n)) K) := by
      refine mem_inf.2 ⟨(mem_matrixIsometries_oQ h2 R hRs _).1
        (matrixDerived_le_isometries _ x.2), ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx)
    simpa only [coe_mul, coe_inv] using hZn _ hxZ _ hm
  have key := lift_commute_of_subnormal π hπ hker A hMq le_rfl
    (fun x hx m hm => mul_mem (mul_mem hx hm) (inv_mem hx)) hNC hNn hg hg'
  have hD : ∀ Y ∈ ⁅isoCent R (A : GL (Fin (2 * n)) K), isoCent R (A : GL (Fin (2 * n)) K)⁆,
      ((g' : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
        (Y : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
          Y * ((g' : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
    intro Y hY
    have e := key ⟨Y, hZΩ hY⟩ (by rw [mem_subgroupOf]; exact hY)
    exact congrArg (fun s : matrixDerived (oQ R) =>
      ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) e
  have hblk := eq_blkDiag_of_commute_isoCent h2 hn hR hA hD
  refine ⟨_, hblk, ?_⟩
  have hiso := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
    ((mem_matrixIsometries_oQ h2 R hRs _).1 (matrixDerived_le_isometries _ g'.2))
  change ((g' : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ *
    (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
      ((g' : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = R at hiso
  rw [hblk, hR, blkDiag_transpose, blkDiag_mul, blkDiag_mul] at hiso
  have e := eq_of_blkDiag_eq (by omega) hiso
  simpa only [wMat, neg_neg] using e

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
