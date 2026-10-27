module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Hat
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace FourU3

variable {F : Type} [Field F]

@[expose] def signDiag (ε : Fin 3 → F) (hε : ∀ i, ε i * ε i = 1) : GL (Fin 3) F :=
  ⟨diagonal ε, diagonal ε,
    by rw [diagonal_mul_diagonal]; simp only [hε]; exact diagonal_one,
    by rw [diagonal_mul_diagonal]; simp only [hε]; exact diagonal_one⟩

theorem coe_signDiag (ε : Fin 3 → F) (hε : ∀ i, ε i * ε i = 1) :
    ((signDiag ε hε : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ε :=
  rfl

theorem signDiag_mul_self (ε : Fin 3 → F) (hε : ∀ i, ε i * ε i = 1) :
    signDiag ε hε * signDiag ε hε = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_signDiag, diagonal_mul_diagonal]
  simp only [hε]
  exact diagonal_one

theorem signDiag_mem_statedSU {q : ℕ} (hq : Odd q) (ε : Fin 3 → F) (hε : ∀ i, ε i * ε i = 1)
    (hdet : ε 0 * ε 1 * ε 2 = 1) : signDiag ε hε ∈ StatedSU 3 q F := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [coe_signDiag, det_diagonal, Fin.prod_univ_three, hdet]
  · have hpow : ∀ i, ε i ^ q = ε i := by
      intro i
      obtain ⟨m, hm⟩ := hq
      rw [hm, pow_succ, pow_mul, sq, hε, one_pow, one_mul]
    have hq0 : (0 : F) ^ q = 0 := zero_pow (by obtain ⟨m, hm⟩ := hq; omega)
    rw [coe_signDiag, diagonal_map (f := fun x : F => x ^ q) hq0,
      diagonal_transpose, diagonal_mul_diagonal]
    simp only [hpow, hε]
    exact diagonal_one

theorem not_mem_statedScalars_of_diagonal {g : GL (Fin 3) F} {δ : Fin 3 → F} {i j : Fin 3}
    (hg : (g : Matrix (Fin 3) (Fin 3) F) = diagonal δ) (hij : δ i ≠ δ j) :
    g ∉ StatedScalars (Fin 3) F := by
  rintro ⟨c, hc⟩
  have h : (g : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) (c : F) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  rw [hg] at h
  have hi := congrFun (congrFun h i) i
  have hj := congrFun (congrFun h j) j
  simp only [diagonal_apply_eq, scalar_apply] at hi hj
  exact hij (hi.trans hj.symm)

theorem exists_involutions {q : ℕ} (hq : Odd q) (h2 : (2 : F) ≠ 0) :
    ∃ a b : StatedProj (StatedSU 3 q F),
      a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  set ε₁ : Fin 3 → F := ![-1, -1, 1]
  set ε₂ : Fin 3 → F := ![-1, 1, -1]
  have h1 : ∀ i, ε₁ i * ε₁ i = 1 := by
    intro i; fin_cases i <;> simp [ε₁]
  have h1' : ∀ i, ε₂ i * ε₂ i = 1 := by
    intro i; fin_cases i <;> simp [ε₂]
  have hne : (1 : F) ≠ -1 := by
    intro h; apply h2; linear_combination h
  let A : StatedSU 3 q F :=
    ⟨signDiag ε₁ h1, signDiag_mem_statedSU hq ε₁ h1 (by simp [ε₁])⟩
  let B : StatedSU 3 q F :=
    ⟨signDiag ε₂ h1', signDiag_mem_statedSU hq ε₂ h1' (by simp [ε₂])⟩
  have hAA : A * A = 1 := Subtype.ext (signDiag_mul_self ε₁ h1)
  have hBB : B * B = 1 := Subtype.ext (signDiag_mul_self ε₂ h1')
  have hAB : A * B = B * A := Subtype.ext (Units.ext (by
    change diagonal ε₁ * diagonal ε₂ = diagonal ε₂ * diagonal ε₁
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _))
  have hAB1 : (QuotientGroup.mk (s := (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F))
      (A * B)) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    refine not_mem_statedScalars_of_diagonal (δ := fun i => ε₁ i * ε₂ i) (i := 0) (j := 1)
      ?_ ?_ h
    · change diagonal ε₁ * diagonal ε₂ = diagonal _
      rw [diagonal_mul_diagonal]
    · simpa [ε₁, ε₂] using hne
  have hA1 : (QuotientGroup.mk (s := (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F))
      A) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact not_mem_statedScalars_of_diagonal (δ := ε₁) (i := 0) (j := 2) rfl
      (by simpa [ε₁] using hne.symm) h
  have hB1 : (QuotientGroup.mk (s := (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F))
      B) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact not_mem_statedScalars_of_diagonal (δ := ε₂) (i := 0) (j := 1) rfl
      (by simpa [ε₂] using hne.symm) h
  refine ⟨QuotientGroup.mk A, QuotientGroup.mk B, ?_, ?_, ?_, hA1, hB1, ?_⟩
  · rw [← QuotientGroup.mk_mul, hAA, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, hBB, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hAB]
  · intro h
    apply hAB1
    rw [QuotientGroup.mk_mul, h, ← QuotientGroup.mk_mul, hBB, QuotientGroup.mk_one]

end FourU3

theorem exists_four_of_FU3 {Y : Type} [Group Y] [Finite Y] (hY : FU3 Y) :
    ∃ U : Subgroup Y, IVK.IsFourSubgroup U := by
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := GH74.Generic.lieModel_psu_data hLie
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 :=
    Ring.two_ne_zero (GH74.Generic.ringChar_ne_two_of_card_eq hp hp2
      (by rw [hF, ← pow_mul, mul_comm]))
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne⟩ := FourU3.exists_involutions hq h2
  obtain ⟨V, hV⟩ := hat_exists_isFourSubgroup_of_involutions ha hb hab ha1 hb1 hne
  exact ⟨V.map e.symm.toMonoidHom, hat_isFourSubgroup_map hV _ e.symm.injective⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
