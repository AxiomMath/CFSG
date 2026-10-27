module

public import CFSG.GH74.GLS.IVK.Proofs2.Stmt41U
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
  CFSG.RankThree.CentralCover CFSG.RankThree.SubgroupLists CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

namespace Lemma41aU3

section GU2

variable {p n : ℕ} {F : Type} [Field F]

theorem bar_eq_pow (h : UnitaryFieldData p n F) : (⇑h.bar : F → F) = (· ^ p ^ n) :=
  funext h.bar_apply

theorem mem_GU2Stated_iff (h : UnitaryFieldData p n F) {A : GL (Fin 2) F} :
    A ∈ GU2Stated (p ^ n) F ↔
      ((A : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
  constructor
  · intro hA
    induction hA using Subgroup.closure_induction with
    | mem A hA =>
      rw [bar_eq_pow h]
      exact hA
    | one => rw [Units.val_one, Matrix.map_one h.bar (map_zero _) (map_one _),
        Matrix.transpose_one, Matrix.mul_one]
    | mul A B _ _ hA hB =>
      rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
      calc _ = ((B : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ *
            (((A : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * (A : Matrix (Fin 2) (Fin 2) F)) *
            (B : Matrix (Fin 2) (Fin 2) F) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hA, Matrix.mul_one, hB]
    | inv A _ hA =>
      have hB : ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          ((A : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ := by
        rw [Matrix.coe_units_inv]
        exact Matrix.inv_eq_left_inv hA
      have hBB : ((((A : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ).map h.bar)ᵀ =
          (A : Matrix (Fin 2) (Fin 2) F) := by
        ext i j
        simp [h.bar_bar]
      rw [hB, hBB, ← hB]
      exact Units.mul_inv A
  · intro hA
    apply Subgroup.subset_closure
    rw [← bar_eq_pow h]
    exact hA

end GU2

section Blocks

variable {F : Type} [Field F]

theorem blkMat_map (f : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) (d : F) :
    (Lemma41aL3.blkMat A d).map f = Lemma41aL3.blkMat (A.map f) (f d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]

theorem blkMat_transpose (A : Matrix (Fin 2) (Fin 2) F) (d : F) :
    (Lemma41aL3.blkMat A d)ᵀ = Lemma41aL3.blkMat Aᵀ d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]

theorem blkMat_conjTr_mul (f : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) (d : F) :
    ((Lemma41aL3.blkMat A d).map f)ᵀ * Lemma41aL3.blkMat A d =
      Lemma41aL3.blkMat ((A.map f)ᵀ * A) (f d * d) := by
  rw [blkMat_map, blkMat_transpose, Lemma41aL3.blkMat_mul]

theorem bar_det_mul_det {bar : F →+* F} {A : Matrix (Fin 2) (Fin 2) F}
    (hA : (A.map bar)ᵀ * A = 1) : bar A.det * A.det = 1 := by
  have := congrArg Matrix.det hA
  rwa [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_one] at this

theorem blk_mem_iff {p n : ℕ} (h : UnitaryFieldData p n F) (A : GL (Fin 2) F) :
    Lemma41aL3.blk A ∈ unitarySU p n F 3 ↔ A ∈ GU2Stated (p ^ n) F := by
  rw [mem_unitarySU_iff h, mem_GU2Stated_iff h]
  have hdet := Lemma41aL3.det_blk A
  have hmat : (((Lemma41aL3.blk A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((Lemma41aL3.blk A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Lemma41aL3.blkMat
        (((A : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * (A : Matrix (Fin 2) (Fin 2) F))
        (h.bar (A : Matrix (Fin 2) (Fin 2) F).det⁻¹ * (A : Matrix (Fin 2) (Fin 2) F).det⁻¹) := by
    rw [Lemma41aL3.coe_blk, blkMat_conjTr_mul]
  rw [hmat]
  refine ⟨fun ⟨_, hU⟩ => ?_, fun hA => ⟨hdet, ?_⟩⟩
  · have := congrArg ulBlock hU
    rwa [Lemma41aL3.ulBlock_blkMat, ulBlock_one] at this
  · rw [hA]
    have h1 := bar_det_mul_det hA
    have h2 : h.bar ((A : Matrix (Fin 2) (Fin 2) F).det⁻¹) *
        (A : Matrix (Fin 2) (Fin 2) F).det⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, h1, inv_one]
    rw [h2]
    exact Lemma41aL3.blkMat_one

end Blocks

section Kernel

variable {p n : ℕ} {F : Type} [Field F]

theorem ker_pow_three (h : UnitaryFieldData p n F) (z : ↥(StatedSU 3 (p ^ n) F))
    (hz : z ∈ (statedProjMk (StatedSU 3 (p ^ n) F)).ker) : z ^ 3 = 1 := by
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hdet := ((mem_unitarySU_iff h).mp z.2).1
  rw [← hc] at hdet
  have hc3 : (c : F) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_smul] using hdet
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, ← hc, ← map_pow]
  have : c ^ 3 = 1 := Units.ext (by simpa using hc3)
  rw [this, map_one]
  rfl

theorem card_ker (h : UnitaryFieldData p n F) :
    Nat.card (statedProjMk (StatedSU 3 (p ^ n) F)).ker = Nat.gcd 3 (p ^ n + 1) := by
  have := (CFSG.LinearGroups.unitary_scalar_kernel h.prime h.card_eq_sq (n := 3)
    (by norm_num)).2.2
  rw [← this, statedProjMk, QuotientGroup.ker_mk']

end Kernel

section Main

variable {p n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def blkU (h : UnitaryFieldData p n F) :
    ↥(GU2Stated (p ^ n) F) →* ↥(StatedSU 3 (p ^ n) F) :=
  (Lemma41aL3.blk.comp (GU2Stated (p ^ n) F).subtype).codRestrict (StatedSU 3 (p ^ n) F)
    fun A => (blk_mem_iff h A).2 A.2

theorem blkU_injective (h : UnitaryFieldData p n F) : Function.Injective (blkU h) := by
  intro A B hAB
  apply Subtype.ext
  exact Lemma41aL3.blk_injective (congrArg Subtype.val hAB)

theorem blkU_commute (h : UnitaryFieldData p n F) (A : ↥(GU2Stated (p ^ n) F)) :
    blkU h A * unitaryInvT h = unitaryInvT h * blkU h A := by
  apply Subtype.ext
  exact Lemma41aL3.blk_commute_negDiag3 (A : GL (Fin 2) F)

theorem mem_range_blkU_of_commute (h : UnitaryFieldData p n F) (hp2 : p ≠ 2)
    {y : ↥(StatedSU 3 (p ^ n) F)} (hy : y * unitaryInvT h = unitaryInvT h * y) :
    y ∈ (blkU h).range := by
  have : CharP F p := h.charP
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
  have hdet : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    ((mem_unitarySU_iff h).mp y.2).1
  have hcomm : (y : GL (Fin 3) F) * negDiag3 F = negDiag3 F * (y : GL (Fin 3) F) :=
    congrArg Subtype.val hy
  obtain ⟨A, hA⟩ := Lemma41aL3.exists_blk_of_commute h2 hcomm hdet
  have hAmem : A ∈ GU2Stated (p ^ n) F := (blk_mem_iff h A).1 (hA ▸ y.2)
  exact ⟨⟨A, hAmem⟩, Subtype.ext hA⟩

@[expose] noncomputable def phi (h : UnitaryFieldData p n F) (c : ↥(StatedSU 3 (p ^ n) F)) :
    ↥(GU2Stated (p ^ n) F) →* ↥(StatedSU 3 (p ^ n) F) :=
  (MulAut.conj c).toMonoidHom.comp (blkU h)

theorem phi_injective (h : UnitaryFieldData p n F) (c : ↥(StatedSU 3 (p ^ n) F)) :
    Function.Injective (phi h c) :=
  (MulAut.conj c).injective.comp (blkU_injective h)

theorem phi_range (h : UnitaryFieldData p n F) (hp2 : p ≠ 2) (c : ↥(StatedSU 3 (p ^ n) F)) :
    (phi h c).range =
      centralizer ({c * unitaryInvT h * c⁻¹} : Set ↥(StatedSU 3 (p ^ n) F)) := by
  ext s
  constructor
  · rintro ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hA := blkU_commute h A
    show c * blkU h A * c⁻¹ * (c * unitaryInvT h * c⁻¹) =
      c * unitaryInvT h * c⁻¹ * (c * blkU h A * c⁻¹)
    calc c * blkU h A * c⁻¹ * (c * unitaryInvT h * c⁻¹)
        = c * (blkU h A * unitaryInvT h) * c⁻¹ := by group
      _ = c * (unitaryInvT h * blkU h A) * c⁻¹ := by rw [hA]
      _ = c * unitaryInvT h * c⁻¹ * (c * blkU h A * c⁻¹) := by group
  · intro hs
    have hs' := Subgroup.mem_centralizer_singleton_iff.mp hs
    have hy : (c⁻¹ * s * c) * unitaryInvT h = unitaryInvT h * (c⁻¹ * s * c) := by
      calc (c⁻¹ * s * c) * unitaryInvT h
          = c⁻¹ * (s * (c * unitaryInvT h * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * unitaryInvT h * c⁻¹) * s) * c := by rw [hs']
        _ = unitaryInvT h * (c⁻¹ * s * c) := by group
    obtain ⟨A, hA⟩ := mem_range_blkU_of_commute h hp2 hy
    refine ⟨A, ?_⟩
    show c * blkU h A * c⁻¹ = s
    rw [hA]
    group

theorem exists_centralizer_quotient (h : UnitaryFieldData p n F) (hp2 : p ≠ 2)
    {w : StatedProj (StatedSU 3 (p ^ n) F)} (hw : orderOf w = 2) :
    ∃ (N : Subgroup ↥(GU2Stated (p ^ n) F)) (_ : N.Normal), (Nat.card N = 1 ∨ Nat.card N = 3) ∧
      Nonempty (↥(centralizer ({w} : Set (StatedProj (StatedSU 3 (p ^ n) F)))) ≃*
        (↥(GU2Stated (p ^ n) F) ⧸ N)) := by
  have hw1 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSU 3 (p ^ n) F))
    (statedProjMk_surjective _) (fun z hz => ker_pow_three h z hz) hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 ha_ord)
  obtain ⟨N, hN, hcard, hiso⟩ := Lemma41aL3.exists_normal_quotient_equiv
    (statedProjMk (StatedSU 3 (p ^ n) F)) (statedProjMk_surjective _)
    (ker_statedProjMk_le_center _) (fun z hz => ker_pow_three h z hz) ha
    (phi h c) (phi_injective h c) (by rw [phi_range h hp2 c, hc])
  refine ⟨N, hN, ?_, hiso⟩
  rw [hcard, card_ker h]
  exact (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 _)

end Main

end Lemma41aU3

theorem ivk_4_1a_U3 : IVK_4_1a_U3 := by
  intro K _ _ p n hp hp2 hK z hz
  rcases hK with ⟨h1, -⟩ | ⟨-, F, hF, hFin, hcardF, ⟨e⟩⟩
  · exact absurd h1 (by norm_num)
  · have hn : 1 ≤ n := by
      by_contra hn0
      have hn0' : n = 0 := by omega
      subst hn0'
      have h1 := Finite.one_lt_card (α := F)
      rw [hcardF] at h1
      simp at h1
    have hdata : UnitaryFieldData p n F := ⟨hp, hn, by rw [hcardF, ← pow_mul, mul_comm]⟩
    have hw : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
    obtain ⟨N, hN, hcard, ⟨iso⟩⟩ := Lemma41aU3.exists_centralizer_quotient hdata hp2 hw
    exact ⟨F, hF, hFin, N, hN, hcardF, hcard, ⟨(centralizerEquiv e z).trans iso⟩⟩

end CFSG.GH74.GLS.IVK.Proofs2
