module

public import CFSG.GH74.Exceptional.UnitaryFourTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

open Matrix CFSG.GH74.Exceptional CFSG.Open

abbrev T3 : Type := ZMod 3 × ZMod 3 × ZMod 3

@[expose] def symM (s : T3) : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![s.1, s.2.1; s.2.1, s.2.2]

theorem symM_add (s t : T3) : symM (s + t) = symM s + symM t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symM]

theorem symM_zero : symM 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symM]

theorem symM_transpose (s : T3) : (symM s)ᵀ = symM s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symM]

@[expose] def uMat (s : T3) : SpMat3 := fromBlocks 1 (symM s) 0 1

theorem uMat_mul (s t : T3) : uMat s * uMat t = uMat (s + t) := by
  simp [uMat, fromBlocks_multiply, symM_add, add_comm]

theorem uMat_zero : uMat 0 = 1 := by
  simp [uMat, symM_zero]

@[expose] def uGL (s : T3) : GL (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ⟨uMat s, uMat (-s), by rw [uMat_mul, add_neg_cancel, uMat_zero],
    by rw [uMat_mul, neg_add_cancel, uMat_zero]⟩

theorem uGL_mem (s : T3) : uGL s ∈ StatedSp 2 (ZMod 3) := by
  rw [StatedAPI.mem_statedSp_iff]
  show (uMat s)ᵀ * fromBlocks 0 1 (-1) 0 * uMat s = fromBlocks 0 1 (-1) 0
  simp [uMat, fromBlocks_transpose, fromBlocks_multiply, symM_transpose]

@[expose] def uSpHom : Multiplicative T3 →* StatedSp 2 (ZMod 3) where
  toFun s := ⟨uGL (Multiplicative.toAdd s), uGL_mem _⟩
  map_one' := Subtype.ext (Units.ext uMat_zero)
  map_mul' s t := Subtype.ext (Units.ext (uMat_mul _ _).symm)

abbrev Z43 : Subgroup (StatedSp 2 (ZMod 3)) :=
  (StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 3)).subgroupOf (StatedSp 2 (ZMod 3))

@[expose] noncomputable def uPSp : Multiplicative T3 →* PSp43 :=
  (QuotientGroup.mk' Z43).comp uSpHom

theorem uPSp_apply (s : Multiplicative T3) :
    uPSp s = (QuotientGroup.mk (uSpHom s) : PSp43) := rfl

theorem uPSp_injective : Function.Injective uPSp := by
  rw [injective_iff_map_eq_one]
  intro s hs
  rw [uPSp_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hs
  obtain ⟨c, hc⟩ := hs
  have hc' : (Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) = uMat (Multiplicative.toAdd s) :=
    congrArg Units.val hc
  rcases units_zmod_three c with rfl | rfl
  · rw [map_one, Units.val_one] at hc'
    have h1 := congrFun (congrFun hc' (.inl 0)) (.inr 0)
    have h2 := congrFun (congrFun hc' (.inl 0)) (.inr 1)
    have h3 := congrFun (congrFun hc' (.inl 1)) (.inr 1)
    simp [uMat, symM] at h1 h2 h3
    apply Multiplicative.toAdd.injective
    simp only [toAdd_one]
    exact Prod.ext h1.symm (Prod.ext h2.symm h3.symm)
  · rw [scalar_neg_one, Units.val_neg, Units.val_one] at hc'
    have h1 := congrFun (congrFun hc' (.inl 0)) (.inl 0)
    simp [uMat] at h1
    exact absurd h1 (by decide)

@[expose] noncomputable def E0 : Subgroup PSp43 := uPSp.range

theorem card_E0 : Nat.card E0 = 27 := by
  rw [E0, ← Nat.card_congr (MonoidHom.ofInjective uPSp_injective).toEquiv,
    Nat.card_eq_fintype_card]
  decide

theorem E0_comm {a b : PSp43} (ha : a ∈ E0) (hb : b ∈ E0) : a * b = b * a := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

@[expose] def levA : Fin 7 → Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  ![!![1, 0; 0, 1], !![1, 1; 0, 1], !![1, 0; 1, 1], !![0, 1; 1, 0], !![1, 2; 0, 1],
    !![1, 0; 2, 1], !![1, 1; 1, 2]]

@[expose] def levA' : Fin 7 → Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  ![!![1, 0; 0, 1], !![1, 0; 2, 1], !![1, 2; 0, 1], !![0, 1; 1, 0], !![1, 0; 1, 1],
    !![1, 1; 0, 1], !![2, 2; 2, 1]]

theorem levA_mul (i : Fin 7) : levA i * (levA' i)ᵀ = 1 := by
  revert i
  decide +kernel

theorem levA'_mul (i : Fin 7) : levA' i * (levA i)ᵀ = 1 := by
  revert i
  decide +kernel

theorem levA'_mul_left (i : Fin 7) : (levA' i)ᵀ * levA i = 1 := by
  revert i
  decide +kernel

theorem levA_mul_left (i : Fin 7) : (levA i)ᵀ * levA' i = 1 := by
  revert i
  decide +kernel

@[expose] def levGL (i : Fin 7) : GL (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ⟨fromBlocks (levA i) 0 0 (levA' i), fromBlocks (levA' i)ᵀ 0 0 (levA i)ᵀ,
    by simp [fromBlocks_multiply, levA_mul, levA'_mul],
    by simp [fromBlocks_multiply, levA'_mul_left, levA_mul_left]⟩

theorem levGL_mem (i : Fin 7) : levGL i ∈ StatedSp 2 (ZMod 3) := by
  rw [StatedAPI.mem_statedSp_iff]
  show (fromBlocks (levA i) 0 0 (levA' i))ᵀ * fromBlocks 0 1 (-1) 0 *
    fromBlocks (levA i) 0 0 (levA' i) = fromBlocks 0 1 (-1) 0
  simp [fromBlocks_transpose, fromBlocks_multiply, levA_mul_left, levA'_mul_left]

@[expose] noncomputable def levPSp (i : Fin 7) : PSp43 :=
  (QuotientGroup.mk ⟨levGL i, levGL_mem i⟩ : PSp43)

@[expose] def levAct (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (s : T3) : T3 :=
  ((A * symM s * Aᵀ) 0 0, (A * symM s * Aᵀ) 0 1, (A * symM s * Aᵀ) 1 1)

theorem symM_levAct (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (s : T3) :
    symM (levAct A s) = A * symM s * Aᵀ := by
  have hT : (A * symM s * Aᵀ)ᵀ = A * symM s * Aᵀ := by
    simp [transpose_mul, symM_transpose, Matrix.mul_assoc]
  have h10 : (A * symM s * Aᵀ) 1 0 = (A * symM s * Aᵀ) 0 1 := by
    have := congrFun (congrFun hT 0) 1
    simpa [transpose_apply] using this
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · exact h10.symm
  · rfl

theorem levPSp_conj (i : Fin 7) (s : Multiplicative T3) :
    levPSp i * uPSp s * (levPSp i)⁻¹ =
      uPSp (Multiplicative.ofAdd (levAct (levA i) (Multiplicative.toAdd s))) := by
  rw [levPSp, uPSp_apply, uPSp_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  show fromBlocks (levA i) 0 0 (levA' i) * uMat (Multiplicative.toAdd s) *
      fromBlocks (levA' i)ᵀ 0 0 (levA i)ᵀ = uMat (levAct (levA i) (Multiplicative.toAdd s))
  simp only [uMat, fromBlocks_multiply, symM_levAct]
  simp [levA_mul, levA'_mul, Matrix.mul_assoc]

@[expose] def aniso (s : T3) : Prop := s.1 * s.2.2 - s.2.1 * s.2.1 = 1

instance (s : T3) : Decidable (aniso s) := inferInstanceAs (Decidable (_ = _))

@[expose] def lineDist (u v : T3) : Prop := v ≠ u ∧ v ≠ -u ∧ v ≠ 0

instance (u v : T3) : Decidable (lineDist u v) := inferInstanceAs (Decidable (_ ∧ _))

@[expose] def code (s : T3) : Fin 27 :=
  ⟨9 * s.1.val + 3 * s.2.1.val + s.2.2.val, by
    have h1 := ZMod.val_lt s.1
    have h2 := ZMod.val_lt s.2.1
    have h3 := ZMod.val_lt s.2.2
    omega⟩

@[expose] def wTab : Fin 27 → Fin 4 → Fin 7 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 4], ![0, 1, 3, 4],
    ![0, 1, 2, 4], ![0, 1, 2, 3], ![0, 1, 2, 3],
    ![0, 1, 2, 4], ![0, 1, 2, 3], ![0, 1, 2, 3],
    ![0, 2, 3, 5], ![0, 1, 2, 3], ![0, 1, 2, 4],
    ![0, 1, 2, 3], ![0, 1, 4, 5], ![0, 1, 2, 3],
    ![0, 1, 2, 3], ![0, 1, 2, 4], ![0, 1, 2, 3],
    ![0, 2, 3, 5], ![0, 1, 2, 4], ![0, 1, 2, 3],
    ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 4],
    ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 4, 5]]

@[expose] def aTab : Fin 27 → Fin 7 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 2, 0, 0, 6, 0, 4, 0, 0, 1, 0]

theorem nonAniso_check : ∀ s : T3, s ≠ 0 → ¬ aniso s → ∀ i j : Fin 4, i ≠ j →
    lineDist (levAct (levA (wTab (code s) i)) s) (levAct (levA (wTab (code s) j)) s) := by
  decide +kernel

theorem aniso_check : ∀ s : T3, aniso s → levAct (levA (aTab (code s))) s = (1, 0, 1) := by
  decide +kernel

theorem smul_trichotomy (c : ZMod 3) (u : T3) : c • u = 0 ∨ c • u = u ∨ c • u = -u := by
  have hc : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide
  rcases hc with rfl | rfl | rfl
  · exact Or.inl (zero_smul _ u)
  · exact Or.inr (Or.inl (one_smul _ u))
  · right; right
    rw [show (2 : ZMod 3) = -1 by decide, neg_smul, one_smul]

theorem eq_of_zpowers_eq {u v : T3}
    (h : Subgroup.zpowers (uPSp (Multiplicative.ofAdd u)) =
      Subgroup.zpowers (uPSp (Multiplicative.ofAdd v))) : v = u ∨ v = -u ∨ v = 0 := by
  have hv : uPSp (Multiplicative.ofAdd v) ∈ Subgroup.zpowers (uPSp (Multiplicative.ofAdd u)) := by
    rw [h]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← map_zpow] at hk
  have hk' := uPSp_injective hk
  have hkv : k • u = v := by
    have := congrArg Multiplicative.toAdd hk'
    simpa using this
  rw [← hkv, ← Int.cast_smul_eq_zsmul (ZMod 3)]
  rcases smul_trichotomy (k : ZMod 3) u with h0 | h1 | h2
  · exact Or.inr (Or.inr h0)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
