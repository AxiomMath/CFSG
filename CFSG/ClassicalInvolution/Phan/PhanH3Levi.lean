module

public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.DLLevis
public import CFSG.LieType.Steinberg.Classical.SpinOdd

public section

namespace CFSG.ClassicalInvolution.PhanB3.H

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock
  shortBlock_sup_longBlock_eq_top)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups

variable {F : Type} [Field F]

variable {F : Type} [Field F]

@[expose] noncomputable def iota5 :
    (Fin 2 ⊕ Fin 2 ⊕ Unit → F) →ₗ[F] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F where
  toFun v := Matrix.fromBlocks !![0, v (.inl 0); -v (.inl 0), 0]
    !![v (.inr (.inr ())), v (.inl 1); v (.inr (.inl 1)), -v (.inr (.inr ()))]
    !![-v (.inr (.inr ())), -v (.inr (.inl 1)); -v (.inl 1), v (.inr (.inr ()))]
    !![0, v (.inr (.inl 0)); -v (.inr (.inl 0)), 0]
  map_add' v w := by
    ext a b
    rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.fromBlocks] <;> ring
  map_smul' c v := by
    ext a b
    rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.fromBlocks]

theorem iota5_apply (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    iota5 v = Matrix.fromBlocks !![0, v (.inl 0); -v (.inl 0), 0]
    !![v (.inr (.inr ())), v (.inl 1); v (.inr (.inl 1)), -v (.inr (.inr ()))]
    !![-v (.inr (.inr ())), -v (.inr (.inl 1)); -v (.inl 1), v (.inr (.inr ()))]
    !![0, v (.inr (.inl 0)); -v (.inr (.inl 0)), 0] := rfl

theorem iota5_injective : Function.Injective (iota5 (F := F)) := by
  intro v w h
  have e1 := congrFun (congrFun h (.inl 0)) (.inl 1)
  have e2 := congrFun (congrFun h (.inr 0)) (.inr 1)
  have e3 := congrFun (congrFun h (.inl 0)) (.inr 1)
  have e4 := congrFun (congrFun h (.inl 1)) (.inr 0)
  have e5 := congrFun (congrFun h (.inl 0)) (.inr 0)
  simp [iota5_apply, Matrix.fromBlocks] at e1 e2 e3 e4 e5
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i
    · exact e1
    · exact e3
  · fin_cases i
    · exact e2
    · exact e4
  · exact e5

theorem gen_Lu (c : F) (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    iota5 (spinAction (quadOdd 2 F)
      ((oddFrame 2 F).longRoot (i := 0) (j := 1) (by decide) true false (.ofAdd c)) v) =
    blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) !![1, c; 0, 1] * iota5 v *
      (blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) !![1, c; 0, 1]).transpose := by
  rw [HypFrame.spinAction_longRoot]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota5_apply, Matrix.fromBlocks, blockMat, Matrix.mul_apply, Matrix.transpose_apply,
      polar_quadOdd, Fin.sum_univ_two, Fintype.sum_sum_type, oddVec, Pi.single_apply] <;> ring

theorem gen_Ll (c : F) (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    iota5 (spinAction (quadOdd 2 F)
      ((oddFrame 2 F).longRoot (i := 1) (j := 0) (by decide) true false (.ofAdd c)) v) =
    blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) !![1, 0; c, 1] * iota5 v *
      (blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) !![1, 0; c, 1]).transpose := by
  rw [HypFrame.spinAction_longRoot]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota5_apply, Matrix.fromBlocks, blockMat, Matrix.mul_apply, Matrix.transpose_apply,
      polar_quadOdd, Fin.sum_univ_two, Fintype.sum_sum_type, oddVec, Pi.single_apply] <;> ring

theorem gen_Su (c : F) (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    iota5 (spinAction (quadOdd 2 F) ((oddFrame 2 F).shortRoot 1 true (.ofAdd c)) v) =
    Matrix.fromBlocks (blockMat (0 : Fin 2) 1 !![1, c; 0, 1]) 0 0
      (blockMat (0 : Fin 2) 1 !![1, -c; 0, 1]).transpose * iota5 v *
    (Matrix.fromBlocks (blockMat (0 : Fin 2) 1 !![1, c; 0, 1]) 0 0
      (blockMat (0 : Fin 2) 1 !![1, -c; 0, 1]).transpose).transpose := by
  rw [OddFrame.spinAction_shortRoot]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota5_apply, Matrix.fromBlocks, blockMat, Matrix.mul_apply, Matrix.transpose_apply,
      polar_quadOdd, Fin.sum_univ_two, Fintype.sum_sum_type, oddVec, oddZ, Pi.single_apply] <;> ring

theorem gen_Sl (c : F) (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    iota5 (spinAction (quadOdd 2 F) ((oddFrame 2 F).shortRoot 1 false (.ofAdd (-c))) v) =
    Matrix.fromBlocks (blockMat (0 : Fin 2) 1 !![1, 0; c, 1]) 0 0
      (blockMat (0 : Fin 2) 1 !![1, 0; -c, 1]).transpose * iota5 v *
    (Matrix.fromBlocks (blockMat (0 : Fin 2) 1 !![1, 0; c, 1]) 0 0
      (blockMat (0 : Fin 2) 1 !![1, 0; -c, 1]).transpose).transpose := by
  rw [OddFrame.spinAction_shortRoot]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota5_apply, Matrix.fromBlocks, blockMat, Matrix.mul_apply, Matrix.transpose_apply,
      polar_quadOdd, Fin.sum_univ_two, Fintype.sum_sum_type, oddVec, oddZ, Pi.single_apply] <;> ring

@[expose] def spGens (F : Type) [Field F] : Set (StatedSp 2 F) :=
  {g | ∃ c : F, g = spBlock F 0 (tv 0 1 c) ∨ g = spBlock F 0 (tv 1 0 c) ∨
    g = spBlock F 1 (tv 0 1 c) ∨ g = spBlock F 1 (tv 1 0 c)}

theorem range_spBlock_le (i : Fin 2) : (spBlock F i).range ≤ Subgroup.closure (spGens F) := by
  rintro _ ⟨A, rfl⟩
  have hA : A ∈ Subgroup.closure ({g | ∃ c : F, g = tv 0 1 c} ∪ {g | ∃ c : F, g = tv 1 0 c}) := by
    rw [closure_tv_two]; trivial
  have h := Subgroup.mem_map_of_mem (spBlock F i) hA
  rw [MonoidHom.map_closure] at h
  refine (Subgroup.closure_mono ?_) h
  rintro _ ⟨g, hg | hg, rfl⟩
  · obtain ⟨c, rfl⟩ := hg
    fin_cases i
    · exact ⟨c, Or.inl rfl⟩
    · exact ⟨c, Or.inr (Or.inr (Or.inl rfl))⟩
  · obtain ⟨c, rfl⟩ := hg
    fin_cases i
    · exact ⟨c, Or.inr (Or.inl rfl)⟩
    · exact ⟨c, Or.inr (Or.inr (Or.inr rfl))⟩

theorem closure_spGens : Subgroup.closure (spGens F) = ⊤ := by
  rw [eq_top_iff, ← shortBlock_sup_longBlock_eq_top (K := F), sup_le_iff]
  rw [← spBlock_zero_eq_shortBlock, ← spBlock_one_eq_longBlock]
  exact ⟨range_spBlock_le 0, range_spBlock_le 1⟩


theorem exists_levi [Finite F] (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) :
    ∃ φ : StatedSp 2 F →* spinGroup (quadOdd 2 F), Function.Injective φ ∧
      ∀ c : F, φ (spBlock F 0 (tv 0 1 c)) =
          Steinberg.SpinOdd.x 2 F (Pi.single (1 : Fin 2) (1 : ℤ)) c ∧
        φ (spBlock F 0 (tv 1 0 c)) =
          Steinberg.SpinOdd.x 2 F (-Pi.single (1 : Fin 2) (1 : ℤ)) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = Steinberg.SpinOdd.x 2 F (Pi.single (0 : Fin 2) (1 : ℤ)) c ∧
        φ (spBlock F 1 (tv 1 0 c)) =
          Steinberg.SpinOdd.x 2 F (-Pi.single (0 : Fin 2) (1 : ℤ)) c := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.oddDatum 2 F).isFiniteType
    (Dv := (Spin.oddDatum 2 F).divisible) rfl
  have hE := Steinberg.SpinOdd.chevalleyExtras (by omega : 2 ≤ 2) O Steinberg.SpinOdd.commC
    (Steinberg.SpinOdd.commutatorFormula O)
  obtain ⟨φ, hinj, -, hv⟩ := exists_sp4Levi (i := (1 : Fin 2)) (j := (0 : Fin 2)) hF h2 hE
    rfl (by show Spin.cartanB 2 1 0 = -2; decide) (by show Spin.cartanB 2 0 1 = -1; decide)
  exact ⟨φ, hinj, hv⟩


theorem mat_gen_Lu (c : F) : mat 2 F (spBlock F 1 (tv 0 1 c)) =
    blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) !![1, c; 0, 1] := by
  rw [spBlock_one_eq_longBlock, CFSG.ClassicalInvolution.Models.SymplecticPairs.mat_longBlock,
    tv01_eq_sl2Upper]
  rfl

theorem mat_gen_Ll (c : F) : mat 2 F (spBlock F 1 (tv 1 0 c)) =
    blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) !![1, 0; c, 1] := by
  rw [spBlock_one_eq_longBlock, CFSG.ClassicalInvolution.Models.SymplecticPairs.mat_longBlock,
    tv10_eq_sl2Lower]
  rfl

theorem sl2Upper_inv (c : F) :
    ((Steinberg.sl2Upper c)⁻¹ : SL(2, F)) = Steinberg.sl2Upper (-c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Steinberg.sl2Upper]

theorem sl2Lower_inv (c : F) :
    ((Steinberg.sl2Lower c)⁻¹ : SL(2, F)) = Steinberg.sl2Lower (-c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Steinberg.sl2Lower]

theorem mat_gen_Su (c : F) : mat 2 F (spBlock F 0 (tv 0 1 c)) =
    Matrix.fromBlocks (blockMat (0 : Fin 2) 1 !![1, c; 0, 1]) 0 0
      (blockMat (0 : Fin 2) 1 !![1, -c; 0, 1]).transpose := by
  rw [spBlock_zero_eq_shortBlock, CFSG.ClassicalInvolution.Models.SymplecticPairs.mat_shortBlock,
    tv01_eq_sl2Upper, sl2Upper_inv]
  rfl

theorem mat_gen_Sl (c : F) : mat 2 F (spBlock F 0 (tv 1 0 c)) =
    Matrix.fromBlocks (blockMat (0 : Fin 2) 1 !![1, 0; c, 1]) 0 0
      (blockMat (0 : Fin 2) 1 !![1, 0; -c, 1]).transpose := by
  rw [spBlock_zero_eq_shortBlock, CFSG.ClassicalInvolution.Models.SymplecticPairs.mat_shortBlock,
    tv10_eq_sl2Lower, sl2Lower_inv]
  rfl


section Levi

variable (φ : StatedSp 2 F →* spinGroup (quadOdd 2 F))

@[expose] def IsLevi (φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)) : Prop :=
  ∀ c : F, φ (spBlock F 0 (tv 0 1 c)) =
      Steinberg.SpinOdd.x 2 F (Pi.single (1 : Fin 2) (1 : ℤ)) c ∧
    φ (spBlock F 0 (tv 1 0 c)) = Steinberg.SpinOdd.x 2 F (-Pi.single (1 : Fin 2) (1 : ℤ)) c ∧
    φ (spBlock F 1 (tv 0 1 c)) = Steinberg.SpinOdd.x 2 F (Pi.single (0 : Fin 2) (1 : ℤ)) c ∧
    φ (spBlock F 1 (tv 1 0 c)) = Steinberg.SpinOdd.x 2 F (-Pi.single (0 : Fin 2) (1 : ℤ)) c

variable {φ}

theorem phi_Lu (hφ : IsLevi φ) (c : F) : φ (spBlock F 1 (tv 0 1 c)) =
    (oddFrame 2 F).longRoot (i := 0) (j := 1) (by decide) true false (.ofAdd c) := by
  rw [(hφ c).2.2.1, Steinberg.SpinOdd.x_single, rootB_of_lt F (k := 0) (j := 1) (by decide) rfl
    (by decide)]

theorem phi_Ll (hφ : IsLevi φ) (c : F) : φ (spBlock F 1 (tv 1 0 c)) =
    (oddFrame 2 F).longRoot (i := 1) (j := 0) (by decide) true false (.ofAdd c) := by
  rw [(hφ c).2.2.2, Steinberg.SpinOdd.x_neg_single, negRootB_of_lt F (k := 0) (j := 1)
    (by decide) rfl (by decide)]

theorem phi_Su (hφ : IsLevi φ) (c : F) : φ (spBlock F 0 (tv 0 1 c)) =
    (oddFrame 2 F).shortRoot 1 true (.ofAdd c) := by
  rw [(hφ c).1, Steinberg.SpinOdd.x_single, rootB_of_not_lt F (k := 1) (by decide)]

theorem phi_Sl (hφ : IsLevi φ) (c : F) : φ (spBlock F 0 (tv 1 0 c)) =
    (oddFrame 2 F).shortRoot 1 false (.ofAdd (-c)) := by
  rw [(hφ c).2.1, Steinberg.SpinOdd.x_neg_single, negRootB_of_not_lt F (k := 1) (by decide)]

theorem levi_intertwine (hφ : IsLevi φ) (g : StatedSp 2 F) (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    iota5 (spinAction (quadOdd 2 F) (φ g) v) = mat 2 F g * iota5 v * (mat 2 F g).transpose := by
  have hg : g ∈ Subgroup.closure (spGens F) := by rw [closure_spGens]; trivial
  induction hg using Subgroup.closure_induction generalizing v with
  | mem s hs =>
    obtain ⟨c, h | h | h | h⟩ := hs
    · subst h
      rw [phi_Su hφ, mat_gen_Su]
      exact gen_Su c v
    · subst h
      rw [phi_Sl hφ, mat_gen_Sl]
      exact gen_Sl c v
    · subst h
      rw [phi_Lu hφ, mat_gen_Lu]
      exact gen_Lu c v
    · subst h
      rw [phi_Ll hφ, mat_gen_Ll]
      exact gen_Ll c v
  | one => simp
  | mul a b _ _ ha hb =>
    rw [map_mul, map_mul, LinearEquiv.mul_apply, ha, hb, map_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  | inv a _ ha =>
    have h1 : iota5 v = mat 2 F a * iota5 (spinAction (quadOdd 2 F) (φ a⁻¹) v) *
        (mat 2 F a).transpose := by
      rw [← ha]
      congr 1
      rw [← LinearEquiv.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
      rfl
    have hm : mat 2 F a⁻¹ * mat 2 F a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have hmt : (mat 2 F a).transpose * (mat 2 F a⁻¹).transpose = 1 := by
      rw [← Matrix.transpose_mul, hm, Matrix.transpose_one]
    calc iota5 (spinAction (quadOdd 2 F) (φ a⁻¹) v)
        = (mat 2 F a⁻¹ * mat 2 F a) * iota5 (spinAction (quadOdd 2 F) (φ a⁻¹) v) *
            ((mat 2 F a).transpose * (mat 2 F a⁻¹).transpose) := by rw [hm, hmt]; simp
      _ = mat 2 F a⁻¹ * (mat 2 F a * iota5 (spinAction (quadOdd 2 F) (φ a⁻¹) v) *
            (mat 2 F a).transpose) * (mat 2 F a⁻¹).transpose := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [← h1]

end Levi

section Roots

theorem exists_levi_roots [Finite F] (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) :
    ∃ φ : StatedSp 2 F →* spinGroup (quadOdd 2 F), Function.Injective φ ∧ IsLevi φ ∧
      ∀ γ ∈ (Spin.oddDatum 2 F).roots, (Spin.oddDatum 2 F).rootGroup γ ≤ φ.range := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.oddDatum 2 F).isFiniteType
    (Dv := (Spin.oddDatum 2 F).divisible) rfl
  have hE := Steinberg.SpinOdd.chevalleyExtras (by omega : 2 ≤ 2) O Steinberg.SpinOdd.commC
    (Steinberg.SpinOdd.commutatorFormula O)
  obtain ⟨φ, hinj, hle, hv⟩ := exists_sp4Levi (i := (1 : Fin 2)) (j := (0 : Fin 2)) hF h2 hE
    rfl (by show Spin.cartanB 2 1 0 = -2; decide) (by show Spin.cartanB 2 0 1 = -1; decide)
  refine ⟨φ, hinj, hv, fun γ hγ => hle γ ⟨hγ, fun k hk1 hk0 => ?_⟩⟩
  exfalso
  rcases k with ⟨k, hk⟩
  have hk' : k < 2 := hk
  interval_cases k
  · exact hk0 rfl
  · exact hk1 rfl

@[expose] def LeviRoots (φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)) : Prop :=
  (∀ {i j : Fin 2} (hij : i ≠ j) (s t : Bool) (c : F),
    (oddFrame 2 F).longRoot hij s t (.ofAdd c) ∈ φ.range) ∧
  ∀ (i : Fin 2) (s : Bool) (c : F), (oddFrame 2 F).shortRoot i s (.ofAdd c) ∈ φ.range

theorem leviRoots_of_roots {φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)}
    (h : ∀ γ ∈ (Spin.oddDatum 2 F).roots, (Spin.oddDatum 2 F).rootGroup γ ≤ φ.range) :
    LeviRoots φ := by
  refine ⟨fun {i j} hij s t c => ?_, fun i s c => ?_⟩
  · have hγ := ofStdB_mem_rootsB 2 (Or.inl ⟨i, j, boolSign s, boolSign t, hij,
      boolSign_eq_one_or_eq_neg_one s, boolSign_eq_one_or_eq_neg_one t, rfl⟩)
    have hmem : (oddFrame 2 F).longRoot hij s t (.ofAdd c) ∈
        oddRootGroup 2 F (ofStdB 2 (Pi.single i (boolSign s) + Pi.single j (boolSign t))) := by
      rw [oddRootGroup_eq_long hij s t (toStdB_ofStdB 2 _)]
      exact ⟨_, rfl⟩
    exact h _ hγ hmem
  · have hγ := ofStdB_mem_rootsB 2 (Or.inr ⟨i, boolSign s, boolSign_eq_one_or_eq_neg_one s, rfl⟩)
    have hmem : (oddFrame 2 F).shortRoot i s (.ofAdd c) ∈
        oddRootGroup 2 F (ofStdB 2 (Pi.single i (boolSign s))) := by
      rw [oddRootGroup_eq_short i s (toStdB_ofStdB 2 _)]
      exact ⟨_, rfl⟩
    exact h _ hγ hmem

end Roots

end CFSG.ClassicalInvolution.PhanB3.H
