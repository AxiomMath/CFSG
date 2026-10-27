module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsAlg
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.U43Lift

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers.U43 TauCeti

@[expose] def mY0 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 1⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨1, 1⟩;
    ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩;
    ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩;
    ⟨2, 1⟩, ⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩]

@[expose] def mY1 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩;
    ⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩;
    ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩;
    ⟨2, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩]

@[expose] def mY2 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 0⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩;
    ⟨0, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩;
    ⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 0⟩;
    ⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 0⟩, ⟨1, 0⟩]

@[expose] def mN0 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 2⟩;
    ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩;
    ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨2, 2⟩;
    ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩]

@[expose] def mN1 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 2⟩, ⟨2, 1⟩;
    ⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩;
    ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩;
    ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩]

@[expose] def mN2 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 2⟩;
    ⟨0, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩;
    ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩]

@[expose] def mS01 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨2, 0⟩, ⟨1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩;
    ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩;
    ⟨0, 1⟩, ⟨0, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩]

@[expose] def mS02 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 2⟩;
    ⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩;
    ⟨2, 0⟩, ⟨2, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩;
    ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]

@[expose] def mS12 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩;
    ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩;
    ⟨2, 2⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨2, 2⟩;
    ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 2⟩]

abbrev IsSU (M : Matrix (Fin 4) (Fin 4) F9) : Prop :=
  M.det = 1 ∧ (M.map (· ^ 3))ᵀ * M = 1

theorem isSU_all : IsSU mY0 ∧ IsSU mY1 ∧ IsSU mY2 ∧ IsSU mN0 ∧ IsSU mN1 ∧ IsSU mN2 ∧
    IsSU mS01 ∧ IsSU mS02 ∧ IsSU mS12 := by
  decide +kernel

theorem relations_matrix :
    (mY0 * mY0 * mY0 = 1 ∧ mY1 * mY1 * mY1 = 1 ∧ mY2 * mY2 * mY2 = 1) ∧
    (mY0 * mY1 = mY1 * mY0 ∧ mY0 * mY2 = mY2 * mY0 ∧ mY1 * mY2 = mY2 * mY1) ∧
    (mN0 * mY0 = mY0 * mY0 * mN0 ∧ mN1 * mY1 = mY1 * mY1 * mN1 ∧
      mN2 * mY2 = mY2 * mY2 * mN2) ∧
    (mS01 * mY0 = mY1 * mS01 ∧ mS01 * mY1 = mY0 * mS01) ∧
    (mS02 * mY0 = mY2 * mS02 ∧ mS02 * mY2 = mY0 * mS02) ∧
    (mS12 * mY1 = mY2 * mS12 ∧ mS12 * mY2 = mY1 * mS12) := by
  decide +kernel

theorem independent_matrix : ∀ a b c : ZMod 3,
    (∃ u : F9, mY0 ^ a.val * mY1 ^ b.val * mY2 ^ c.val = u • 1) → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide +kernel

@[expose] noncomputable def suMk (M : Matrix (Fin 4) (Fin 4) F9) (h : IsSU M) : StatedSU 4 3 F9 :=
  ⟨Matrix.GeneralLinearGroup.mk'' M (by rw [h.1]; exact isUnit_one), Subgroup.subset_closure h⟩

theorem val_su_mul (A B : StatedSU 4 3 F9) :
    (((A * B : StatedSU 4 3 F9) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) *
        ((B : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) := rfl

theorem val_su_pow (A : StatedSU 4 3 F9) (k : ℕ) :
    (((A ^ k : StatedSU 4 3 F9) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) ^ k := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem su_ext {A B : StatedSU 4 3 F9}
    (h : ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = (B : GL (Fin 4) F9)) : A = B :=
  Subtype.ext (Units.ext h)

theorem exists_smul_of_mk_eq_one {x : StatedSU 4 3 F9} (h : (QuotientGroup.mk x : X₀) = 1) :
    ∃ a : F9, ((x : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = a • 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  refine Matrix.ext fun i j => ?_
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

@[expose] noncomputable def suY : Fin 3 → StatedSU 4 3 F9
  | 0 => suMk mY0 isSU_all.1
  | 1 => suMk mY1 isSU_all.2.1
  | 2 => suMk mY2 isSU_all.2.2.1

@[expose] noncomputable def suN : Fin 3 → StatedSU 4 3 F9
  | 0 => suMk mN0 isSU_all.2.2.2.1
  | 1 => suMk mN1 isSU_all.2.2.2.2.1
  | 2 => suMk mN2 isSU_all.2.2.2.2.2.1

@[expose] noncomputable def suS : Fin 3 → Fin 3 → StatedSU 4 3 F9
  | 0, 1 => suMk mS01 isSU_all.2.2.2.2.2.2.1
  | 0, 2 => suMk mS02 isSU_all.2.2.2.2.2.2.2.1
  | 1, 2 => suMk mS12 isSU_all.2.2.2.2.2.2.2.2
  | _, _ => 1

theorem mk_eq_of_val_eq {A B : StatedSU 4 3 F9}
    (h : ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = (B : GL (Fin 4) F9)) :
    (QuotientGroup.mk A : X₀) = QuotientGroup.mk B := by
  rw [su_ext h]

theorem mk_mul_eq_mk_mul {A B C D : StatedSU 4 3 F9}
    (h : ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) * (B : GL (Fin 4) F9) =
      (C : GL (Fin 4) F9) * (D : GL (Fin 4) F9)) :
    (QuotientGroup.mk A : X₀) * QuotientGroup.mk B = QuotientGroup.mk C * QuotientGroup.mk D := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact mk_eq_of_val_eq h

theorem hasLiftableTriple_X₀ : HasLiftableTriple X₀ := by
  obtain ⟨⟨c0, c1, c2⟩, ⟨d01, d02, d12⟩, ⟨i0, i1, i2⟩, ⟨s01a, s01b⟩, ⟨s02a, s02b⟩,
    ⟨s12a, s12b⟩⟩ := relations_matrix
  refine HasLiftableTriple.of_relations (fun i => QuotientGroup.mk (suY i)) ?_ ?_ ?_
    (fun i => QuotientGroup.mk (suN i)) ?_ (fun i j => QuotientGroup.mk (suS i j)) ?_
  · intro i
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_one]
    refine mk_eq_of_val_eq ?_
    fin_cases i
    · exact c0
    · exact c1
    · exact c2
  · intro i j
    refine mk_mul_eq_mk_mul ?_
    fin_cases i <;> fin_cases j
    · rfl
    · exact d01
    · exact d02
    · exact d01.symm
    · rfl
    · exact d12
    · exact d02.symm
    · exact d12.symm
    · rfl
  · intro a b c h
    have hmk : (QuotientGroup.mk (suY 0 ^ a.val * suY 1 ^ b.val * suY 2 ^ c.val) : X₀) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow,
        QuotientGroup.mk_pow]
      exact h
    obtain ⟨u, hu⟩ := exists_smul_of_mk_eq_one hmk
    rw [val_su_mul, val_su_mul, val_su_pow, val_su_pow, val_su_pow] at hu
    exact independent_matrix a b c ⟨u, hu⟩
  · intro i
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine mk_eq_of_val_eq ?_
    fin_cases i
    · exact i0
    · exact i1
    · exact i2
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · exact ⟨mk_mul_eq_mk_mul s01a, mk_mul_eq_mk_mul s01b⟩
    · exact ⟨mk_mul_eq_mk_mul s02a, mk_mul_eq_mk_mul s02b⟩
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact ⟨mk_mul_eq_mk_mul s12a, mk_mul_eq_mk_mul s12b⟩
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)

theorem hasLiftableTriple_U43 (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid)
    (hq : q.card = 3) : HasLiftableTriple (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group := by
  obtain ⟨hp, he⟩ := primePower_eq_three hq
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = 3 :=
    (LieTypeIndex.characteristic_twistedA 3 q).trans hp
  have he1 : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = 1 :=
    (LieTypeIndex.fieldExponent_twistedA 3 q).trans he
  have hK : Nat.card (GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
      (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩)) = 9 := by
    rw [GaloisField.card _ _ (by rw [he1]; norm_num), hc, he1]
    norm_num
  have hq3 : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ ^
      ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = 3 := by rw [hc, he1]; rfl
  have e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv
  rw [hq3] at e
  have : Fintype (GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
      (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩)) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
      (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩)) = Fintype.card F9 := by
    rw [← Nat.card_eq_fintype_card, hK, F9.card_eq]
  exact HasLiftableTriple.of_mulEquiv
    (e.trans (CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hcard) 4 3)).symm hasLiftableTriple_X₀

end CFSG.LocalAnalysis.RankThreeTheoremC.U43Lift
