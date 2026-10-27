module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.GH74.GLS.Stage2.Local.P34Sp4OddM
import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympLevi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer fieldSp conjSp conjAut fieldAut gsp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

theorem mat_fieldSp (σ : K ≃+* K) (x : StatedSp r K) :
    mat r K (fieldSp r K σ x) = (mat r K x).map σ := rfl

theorem fieldSp_mem_flagStabilizer (hI : ∀ i ∈ I, i ≤ r) (σ : K ≃+* K) {x : StatedSp r K}
    (hx : x ∈ flagStabilizer r K I) : fieldSp r K σ x ∈ flagStabilizer r K I := by
  have key : ∀ y ∈ flagStabilizer r K I, ∀ c ∈ I, ∀ v ∈ SymplecticFlag.isoFlag r K c,
      mat r K (fieldSp r K σ y) *ᵥ v ∈ SymplecticFlag.isoFlag r K c := by
    intro y hy c hc v hv
    refine spFlag_mulVec_mem_isoFlag (fun l hl k hk => ?_) hv
    rw [mat_fieldSp, Matrix.map_apply]
    have hs := spFlag_mem_stabilizer hI hy hc
    rcases k with j | j
    · rw [spFlag_inl_inl_eq_zero hs hl (hk j rfl), map_zero]
    · rw [spFlag_inr_inl_eq_zero hs hl, map_zero]
  refine spFlag_mem_flagStabilizer hI fun c hc v hv => ⟨key x hx c hc v hv, ?_⟩
  rw [← map_inv]
  exact key x⁻¹ (inv_mem hx) c hc v hv

theorem mem_flagStabilizer_of_conj_mem (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {g : StatedSp r K}
    (h : ∀ q ∈ flagStabilizer r K I, g * q * g⁻¹ ∈ flagStabilizer r K I) :
    g ∈ flagStabilizer r K I := by
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  refine SymplecticHigher.mem_flagStabilizer.mpr fun c hc => ?_
  obtain ⟨hc1, hcr⟩ := hI c hc
  have hflag : ∀ i, i ≤ r → SymplecticFlag.flag r K i = SymplecticFlag.isoFlag r K i :=
    fun i hi => by rw [SymplecticFlag.flag, ite_eq_left hi]
  obtain ⟨F, hF⟩ : ∃ F : Submodule K (Fin r ⊕ Fin r → K), F = SymplecticFlag.isoFlag r K c :=
    ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, M = mat r K g⁻¹ := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Submodule K (Fin r ⊕ Fin r → K), W = F.map (mulVecLin M) := ⟨_, rfl⟩
  have hWiso : SymplecticFlag.IsTotallyIsotropic (pairedSympForm K r) W := by
    rw [hW]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply, hM, mat_apply]
    rw [SymplecticHigher.pairedSympForm_mulVec g⁻¹ u u']
    rw [hF] at hu hu'
    exact SymplecticHigher.isTotallyIsotropic_isoFlag c u hu u' hu'
  have hmul : ∀ q : StatedSp r K, mat r K q * M = M * mat r K (g * q * g⁻¹) := by
    intro q
    have h1 : mat r K (g⁻¹ * (g * q * g⁻¹)) = mat r K (q * g⁻¹) := by
      congr 1
      group
    rw [map_mul, map_mul] at h1
    rw [hM]
    exact h1.symm
  have hWinv : ∀ q ∈ flagStabilizer r K I, W.map (mulVecLin (mat r K q)) = W := by
    intro q hq
    have hq' : F.map (mulVecLin (mat r K (g * q * g⁻¹))) = F := by
      have := SymplecticHigher.mem_flagStabilizer.mp (h q hq) c hc
      rw [SymplecticFlag.mem_stabilizer, hflag c hcr] at this
      rw [hF]
      exact this
    rw [hW, ← Submodule.map_comp, ← Matrix.mulVecLin_mul, hmul, Matrix.mulVecLin_mul,
      Submodule.map_comp, hq']
  have hinj : Function.Injective (mulVecLin M) := by
    refine Matrix.mulVec_injective_iff_isUnit.2 ?_
    rw [hM, mat_apply]
    exact (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K)).isUnit
  have hrank : Module.finrank K W = c := by
    rw [hW, ← (Submodule.equivMapOfInjective _ hinj F).finrank_eq, hF,
      SymplecticHigher.finrank_isoFlag hcr]
  have hle : flagStabilizer r K I ≤ SymplecticFlag.stabilizer r K W := fun q hq =>
    SymplecticFlag.mem_stabilizer.mpr (hWinv q hq)
  have hWF : W = F := by
    rcases ((SymplecticHigher.subflag_generation (r := r) (K := K) I hI').2.2 W hWiso).mp hle with
      h0 | ⟨i, hi, hWi⟩
    · exfalso
      rw [SymplecticHigher.flag_zero] at h0
      rw [h0, finrank_bot] at hrank
      omega
    · have hir := hI' i hi
      rw [hflag i hir] at hWi
      have hic : i = c := by
        rw [hWi, SymplecticHigher.finrank_isoFlag hir] at hrank
        exact hrank
      rw [hWi, hF, hic]
  have hgM : mat r K g * M = 1 := by rw [hM, ← map_mul, mul_inv_cancel, map_one]
  rw [SymplecticFlag.mem_stabilizer, hflag c hcr, ← hF]
  calc F.map (mulVecLin (mat r K g)) = W.map (mulVecLin (mat r K g)) := by rw [hWF]
    _ = F.map (mulVecLin (mat r K g * M)) := by
        rw [hW, ← Submodule.map_comp, ← Matrix.mulVecLin_mul]
    _ = F := by rw [hgM, Matrix.mulVecLin_one, Submodule.map_id]

theorem proj_injective [CharP K 2] : Function.Injective (SymplecticFlag.proj r K) := by
  rw [← MonoidHom.ker_eq_bot_iff, SymplecticHigher.ker_proj]
  exact CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot r

theorem exists_conj_fieldSp_of_odd [Finite K] [CharP K 2] (hr : 2 ≤ r)
    {α : MulAut (StatedSp r K)} (hα : Odd (orderOf α)) :
    ∃ (g : StatedSp r K) (σ : K ≃+* K), ∀ x, α x = g * fieldSp r K σ x * g⁻¹ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let e : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective (SymplecticFlag.proj r K)
      ⟨proj_injective, SymplecticHigher.proj_surjective⟩
  let α' : MulAut (StatedProj (StatedSp r K)) := (MulAut.congr e) α
  have hα' : Odd (orderOf α') := by
    have : orderOf α' = orderOf α := MulEquiv.orderOf_eq (MulAut.congr e) α
    rwa [this]
  obtain ⟨A, σ, hA⟩ : ∃ (A : gsp r K) (σ : K ≃+* K), α' = conjAut r K A * fieldAut r K σ := by
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · obtain rfl : r = 2 := by omega
      exact CFSG.GH74.GLS.Stage2.Local.P34.exists_conj_field_of_odd hα'
    · exact (SymplecticHigher.automorphism_generation (K := K) h3).2 α'
  have hαx : ∀ x : StatedSp r K, α x = conjSp r K A (fieldSp r K σ x) := by
    intro x
    apply proj_injective
    have h2 : SymplecticFlag.proj r K (α x) = α' (SymplecticFlag.proj r K x) := by
      change e (α x) = α' (e x)
      simp [α', MulAut.congr_apply]
    rw [h2, hA]
    rfl
  obtain ⟨μ, hμ⟩ := SymplecticHigher.mem_gsp.mp A.2
  obtain ⟨ν₀, hν₀⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (μ : K)
  have hν₀ne : ν₀ ≠ 0 := by
    rintro rfl
    exact μ.ne_zero (by simpa using hν₀)
  set ν : Kˣ := Units.mk0 ν₀ hν₀ne with hν
  set z : GL (Fin r ⊕ Fin r) K := Matrix.GeneralLinearGroup.scalar _ ν⁻¹ with hz
  have hzc : z ∈ Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hzmat : ((z : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((ν⁻¹ : Kˣ) : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [hz, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hmem : z * (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, Units.val_mul, hzmat, Matrix.smul_mul,
      Matrix.one_mul]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hc : ((ν⁻¹ : Kˣ) : K) * ((ν⁻¹ : Kˣ) : K) * (μ : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, hν, Units.val_mk0, hν₀]
      field_simp
    have hJ := hμ
    change (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      SymplecticHigher.formJ r K * ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        (μ : K) • SymplecticHigher.formJ r K at hJ
    rw [hJ, smul_smul, hc, one_smul]
  refine ⟨⟨z * (A : GL (Fin r ⊕ Fin r) K), hmem⟩, σ, fun x => ?_⟩
  apply Subtype.ext
  rw [hαx x, Subgroup.coe_mul, Subgroup.coe_mul, SymplecticHigher.coe_conjSp]
  have hcomm := Subgroup.mem_center_iff.mp hzc
    ((A : GL (Fin r ⊕ Fin r) K) * (fieldSp r K σ x : GL (Fin r ⊕ Fin r) K) *
      (A : GL (Fin r ⊕ Fin r) K)⁻¹)
  have hinv : (((⟨z * (A : GL (Fin r ⊕ Fin r) K), hmem⟩ : StatedSp r K)⁻¹ : StatedSp r K) :
      GL (Fin r ⊕ Fin r) K) = (A : GL (Fin r ⊕ Fin r) K)⁻¹ * z⁻¹ := by
    rw [Subgroup.coe_inv]
    simp [_root_.mul_inv_rev]
  rw [hinv]
  calc (A : GL (Fin r ⊕ Fin r) K) * (fieldSp r K σ x : GL (Fin r ⊕ Fin r) K) *
        (A : GL (Fin r ⊕ Fin r) K)⁻¹
      = (A * (fieldSp r K σ x : GL (Fin r ⊕ Fin r) K) * (A : GL (Fin r ⊕ Fin r) K)⁻¹) * z *
          z⁻¹ := by group
    _ = z * (A * (fieldSp r K σ x : GL (Fin r ⊕ Fin r) K) *
          (A : GL (Fin r ⊕ Fin r) K)⁻¹) * z⁻¹ := by rw [hcomm]
    _ = _ := by group

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
