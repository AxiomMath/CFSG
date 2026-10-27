module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3Adapt
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.Steinberg Matrix
open scoped MatrixGroups commutatorElement

section Quasisimple

theorem isQuasisimple_of_perfect_simple {Q : Type*} [Group Q] (hperf : commutator Q = ⊤)
    (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : CFSG.IsQuasisimple Q := by
  refine ⟨Group.isPerfect_def.mpr hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hab ((QuotientGroup.mk' (Subgroup.center Q)) x), mul_inv_cancel_right,
      mul_inv_cancel]
  rw [hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem isQuasisimple_sl2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple SL(2, F) :=
  isQuasisimple_of_perfect_simple
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4).commutator_eq_top
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)

end Quasisimple

section SL3

variable {F : Type} [Field F]

theorem mem_statedSL_iff_det {n : ℕ} (A : GL (Fin n) F) :
    A ∈ StatedSL n F ↔ (A : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

@[expose] def embSL2GL (F : Type) [Field F] : SL(2, F) →* GL (Fin 3) F where
  toFun B := ⟨embPair 2 (B : Matrix (Fin 2) (Fin 2) F),
    embPair 2 ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F),
    by rw [← embPair_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, embPair_one],
    by rw [← embPair_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, embPair_one]⟩
  map_one' := by
    apply Units.ext
    simp [embPair_one]
  map_mul' B C := by
    apply Units.ext
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_mul, embPair_mul]

theorem coe_embSL2GL (B : SL(2, F)) :
    ((embSL2GL F B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      embPair 2 (B : Matrix (Fin 2) (Fin 2) F) := rfl

theorem embSL2GL_mem_blockSub (B : SL(2, F)) : embSL2GL F B ∈ blockSub F := by
  refine ⟨?_, ?_⟩
  · rw [coe_embSL2GL, Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> simp [embPair]
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_embSL2GL, coe_D3GL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [embPair, D3, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem det_conj_GL (Q E : GL (Fin 3) F) :
    ((Q * E * Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
      ((E : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det := by
  have h1 : ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
      ((Q : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  calc _ = ((E : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
        (((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
          ((Q : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det) := by ring
    _ = _ := by rw [h1, mul_one]

theorem nonempty_mulEquiv_Nst_sl3 (h2 : (2 : F) ≠ 0) (Q : GL (Fin 3) F) :
    Nonempty (SL(2, F) ≃* Nst (StatedSL 3 F) Q) := by
  let Φ : SL(2, F) →* GL (Fin 3) F := (MulAut.conj Q).toMonoidHom.comp (embSL2GL F)
  have hΦ : ∀ B, Φ B = Q * embSL2GL F B * Q⁻¹ := fun B => rfl
  have hinj : Function.Injective Φ := by
    intro B C h
    rw [hΦ, hΦ] at h
    have h1 : embSL2GL F B = embSL2GL F C := by
      have := mul_left_cancel (mul_right_cancel h)
      exact this
    have h2' := congrArg (fun y : GL (Fin 3) F => ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
    simp only [coe_embSL2GL] at h2'
    exact Subtype.ext (embPair_injective 2 h2')
  have hrange : Φ.range = Nst (StatedSL 3 F) Q := by
    ext x
    constructor
    · rintro ⟨B, rfl⟩
      rw [mem_Nst_iff, hΦ]
      refine ⟨(mem_statedSL_iff_det _).2 ?_, ?_⟩
      · rw [det_conj_GL, coe_embSL2GL, det_embPair]
        exact B.2
      · have : Q⁻¹ * (Q * embSL2GL F B * Q⁻¹) * Q = embSL2GL F B := by group
        rw [this]
        exact embSL2GL_mem_blockSub B
    · intro hx
      obtain ⟨hxH, hxb⟩ := mem_Nst_iff.1 hx
      set x' : GL (Fin 3) F := Q⁻¹ * x * Q with hx'
      have hdx : ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
        (mem_statedSL_iff_det _).1 hxH
      have hcomm : ((x' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * D3 =
          D3 * ((x' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        have := congrArg (fun y : GL (Fin 3) F => ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
          hxb.2
        simpa [coe_D3GL] using this
      have hemb := eq_embPair_of_commute_fix h2 hcomm hxb.1
      have hdetB : (!![((x' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0,
          ((x' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1;
          ((x' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0,
          ((x' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1] : Matrix (Fin 2) (Fin 2) F).det =
          1 := by
        rw [← det_embPair 2, ← hemb]
        have hxx : x = Q * x' * Q⁻¹ := by rw [hx']; group
        have := det_conj_GL Q x'
        rw [← hxx, hdx] at this
        exact this.symm
      let B₀ : SL(2, F) := ⟨_, hdetB⟩
      refine ⟨B₀, ?_⟩
      have h3 : embSL2GL F B₀ = x' := Units.ext (by rw [coe_embSL2GL]; exact hemb.symm)
      rw [hΦ, h3, hx']
      group
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem not_charTwo_centralizer_statedSL3 [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {s : StatedProj (StatedSL 3 F)} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ¬ CharTwo (Subgroup.centralizer ({s} : Set (StatedProj (StatedSL 3 F)))) := by
  classical
  have hdet : ∀ g ∈ StatedSL 3 F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    fun g hg => (mem_statedSL_iff_det g).1 hg
  obtain ⟨A, rfl, hA2, hAs⟩ := exists_involution_lift (by simp) (StatedSL 3 F) hdet hs2 hs1
  have hA2m : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have := congrArg (fun y : StatedSL 3 F => ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hA2
    simpa using this
  have hA1 : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
    intro h
    apply hAs
    have : (A : GL (Fin 3) F) = 1 := Units.ext h
    rw [this]
    exact one_mem _
  obtain ⟨Q, hQ⟩ := exists_adapted_basis h2 hA2m (hdet _ A.2) hA1
  have hAQ : (A : GL (Fin 3) F) * Q = Q * D3GL := Units.ext (by simpa [coe_D3GL] using hQ)
  obtain ⟨e⟩ := nonempty_mulEquiv_Nst_sl3 h2 Q
  exact not_charTwo_centralizer_of_adapted (StatedSL 3 F) A Q h2 hdet hA2 hAQ
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_sl2 h4))

end SL3

end CFSG.QuasithinUnique.Ch1
