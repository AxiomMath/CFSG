module

public import Certificates.Certificate18002
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.CharacterTheory.SteinbergBY.AlternatingSix

open Matrix Equiv FieldFour
open scoped Kronecker

theorem permMat_mul (σ τ : Perm (Fin 6)) : permMat (σ * τ) = permMat σ * permMat τ := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ j)]
  · show (if σ (τ j) = i then (1 : ZMod 2) else 0) =
      (if σ (τ j) = i then 1 else 0) * (if τ j = τ j then 1 else 0)
    simp only [ite_true, mul_one]
  · intro b _ hb
    simp [permMat, Ne.symm hb]
  · simp

theorem permMat_one : permMat 1 = 1 := by
  ext i j
  simp only [permMat, Matrix.of_apply, Perm.one_apply, Matrix.one_apply, eq_comm]

theorem permMat_mulVec_single (σ : Perm (Fin 6)) (a : Fin 6) :
    permMat σ *ᵥ Pi.single a 1 = Pi.single (σ a) 1 := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single a]
  · simp [permMat, Pi.single_apply, eq_comm]
  · intro b _ hb
    simp [hb]
  · simp

theorem permMat_mulVec_one (σ : Perm (Fin 6)) :
    permMat σ *ᵥ (fun _ => 1) = fun _ => 1 := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (σ.symm i)]
  · simp [permMat]
  · intro b _ hb
    have : σ b ≠ i := fun h => hb (by rw [← h, Equiv.symm_apply_apply])
    simp [permMat, this]
  · simp

theorem heartMatrixOf_eq (σ : Perm (Fin 6)) :
    heartMatrixOf σ = heartCoord * permMat σ * heartBasis := by
  ext i j
  have h1 : ∀ l, (heartCoord * permMat σ) i l = heartCoord i (σ l) := by
    intro l
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ l)]
    · simp [permMat]
    · intro b _ hb
      simp [permMat, Ne.symm hb]
    · simp
  have key : ∀ (f : Fin 6 → ZMod 2) (a b : Fin 6),
      ∑ l, f l * (Pi.single a 1 + Pi.single b 1 : Fin 6 → ZMod 2) l = f a + f b := by
    intro f a b
    simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
  rw [Matrix.mul_apply]
  simp only [h1]
  change heartCoord i (σ j.castSucc.castSucc) + heartCoord i (σ j.succ.castSucc) =
    ∑ x, heartCoord i (σ x) *
      (Pi.single j.castSucc.castSucc 1 + Pi.single j.succ.castSucc 1 : Fin 6 → ZMod 2) x
  rw [key]

theorem heartCoord_mul_heartBasis : heartCoord * heartBasis = 1 := by decide

theorem heartCoord_mulVec_one : heartCoord *ᵥ (fun _ => 1) = 0 := by decide

theorem heartBasis_complement : ∀ a b : Fin 6, a ≠ b → ∃ c : ZMod 2,
    (1 - heartBasis * heartCoord) *ᵥ (Pi.single a 1 + Pi.single b 1) = c • fun _ => 1 := by
  decide

theorem heartMatrixOf_mul (σ τ : Perm (Fin 6)) :
    heartMatrixOf ⇑(σ * τ) = heartMatrixOf σ * heartMatrixOf τ := by
  rw [heartMatrixOf_eq, heartMatrixOf_eq, heartMatrixOf_eq, permMat_mul]
  set N := 1 - heartBasis * heartCoord with hN
  have hcol : ∀ j : Fin 4, ∃ c : ZMod 2,
      (fun l => (N * permMat τ * heartBasis) l j) = c • fun _ => 1 := by
    intro j
    have hne : j.castSucc.castSucc ≠ j.succ.castSucc := by
      rw [Ne, Fin.ext_iff]
      simp
    obtain ⟨c, hc⟩ := heartBasis_complement (τ j.castSucc.castSucc) (τ j.succ.castSucc)
      (τ.injective.ne hne)
    refine ⟨c, ?_⟩
    have h1 : (fun l => (N * permMat τ * heartBasis) l j) =
        N *ᵥ (permMat τ *ᵥ fun l => heartBasis l j) := by
      rw [Matrix.mulVec_mulVec]
      rfl
    have h2 : (fun l => heartBasis l j) =
        (Pi.single j.castSucc.castSucc 1 + Pi.single j.succ.castSucc 1 : Fin 6 → ZMod 2) := rfl
    rw [h1, h2, Matrix.mulVec_add, permMat_mulVec_single, permMat_mulVec_single, hc]
  have hzero : heartCoord * permMat σ * (N * permMat τ * heartBasis) = 0 := by
    ext i j
    obtain ⟨c, hc⟩ := hcol j
    have h1 : (heartCoord * permMat σ * (N * permMat τ * heartBasis)) i j =
        ((heartCoord * permMat σ) *ᵥ fun l => (N * permMat τ * heartBasis) l j) i := rfl
    rw [h1, hc, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, permMat_mulVec_one,
      heartCoord_mulVec_one]
    simp
  have hsplit : permMat τ * heartBasis =
      heartBasis * (heartCoord * permMat τ * heartBasis) + N * permMat τ * heartBasis := by
    rw [hN, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
    abel
  calc heartCoord * (permMat σ * permMat τ) * heartBasis
      = heartCoord * permMat σ * (permMat τ * heartBasis) := by
        simp only [Matrix.mul_assoc]
    _ = heartCoord * permMat σ * (heartBasis * (heartCoord * permMat τ * heartBasis)) +
        heartCoord * permMat σ * (N * permMat τ * heartBasis) := by
        rw [hsplit, Matrix.mul_add]
    _ = heartCoord * permMat σ * heartBasis * (heartCoord * permMat τ * heartBasis) := by
        rw [hzero, add_zero]
        simp only [Matrix.mul_assoc]

theorem heartMatrixOf_one : heartMatrixOf ⇑(1 : Perm (Fin 6)) = 1 := by
  rw [heartMatrixOf_eq, permMat_one, Matrix.mul_one, heartCoord_mul_heartBasis]

@[expose] def heartHom : Perm (Fin 6) →* Matrix (Fin 4) (Fin 4) (ZMod 2) where
  toFun σ := heartMatrixOf σ
  map_one' := heartMatrixOf_one
  map_mul' := heartMatrixOf_mul

theorem total_eq_of_two_synthemes : ∀ (i i' : Fin 6) (b₀ b₁ b₀' b₁' : Fin 5), b₀ ≠ b₁ →
    (∀ x, partner i b₀ x = partner i' b₀' x) → (∀ x, partner i b₁ x = partner i' b₁' x) →
    i = i' := by
  decide +kernel

theorem partner_zero_ne_one : ∀ j : Fin 6, ∃ x, partner j 0 x ≠ partner j 1 x := by
  decide

theorem MapsTotal.comp {σ τ : Fin 6 → Fin 6} {j i l : Fin 6} (h₁ : MapsTotal τ j i)
    (h₂ : MapsTotal σ i l) : MapsTotal (σ ∘ τ) j l := by
  intro a
  obtain ⟨b, hb⟩ := h₁ a
  obtain ⟨c, hc⟩ := h₂ b
  exact ⟨c, fun x => by simp only [Function.comp_apply, hb, hc]⟩

theorem totalCheckIfSwap_all : ∀ σ : Perm (Fin 6), totalCheckIfSwap σ = true := by
  decide +kernel

theorem totalCheckVec_spec (v : Vector (Fin 6) 6) (h : totalCheckVec v = true) :
    ∀ j : Fin 6, ∃ i : Fin 6, MapsTotal (fun x => v[x]) j i := by
  unfold totalCheckVec at h
  exact of_decide_eq_true h

theorem exists_mapsTotal_of_isSwap (σ : Perm (Fin 6)) (hσ : σ.IsSwap) (j : Fin 6) :
    ∃ i, MapsTotal σ j i := by
  have h := totalCheckIfSwap_all σ
  have hc : σ.support.card = 2 := Perm.card_support_eq_two.mpr hσ
  simp only [totalCheckIfSwap, hc, ite_true] at h
  have h' := totalCheckVec_spec (Vector.ofFn σ) h
  have hv : (fun x => (Vector.ofFn σ)[x]) = ⇑σ := funext fun x => by simp
  rw [hv] at h'
  exact h' j

theorem exists_mapsTotal (σ : Perm (Fin 6)) (j : Fin 6) : ∃ i, MapsTotal σ j i := by
  have hσ : σ ∈ Subgroup.closure {τ : Perm (Fin 6) | τ.IsSwap} := by
    rw [Perm.closure_isSwap]
    exact Subgroup.mem_top σ
  induction hσ using Subgroup.closure_induction'' generalizing j with
  | mem x hx => exact exists_mapsTotal_of_isSwap x hx j
  | inv_mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    rw [Equiv.swap_inv]
    exact exists_mapsTotal_of_isSwap _ ⟨a, b, hab, rfl⟩ j
  | one => exact ⟨j, fun a => ⟨a, fun _ => rfl⟩⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, hi⟩ := hy j
    obtain ⟨l, hl⟩ := hx i
    exact ⟨l, hi.comp hl⟩

theorem MapsTotal.unique {σ : Perm (Fin 6)} {j i i' : Fin 6} (h : MapsTotal σ j i)
    (h' : MapsTotal σ j i') : i = i' := by
  obtain ⟨b₀, hb₀⟩ := h 0
  obtain ⟨b₁, hb₁⟩ := h 1
  obtain ⟨b₀', hb₀'⟩ := h' 0
  obtain ⟨b₁', hb₁'⟩ := h' 1
  have hne : b₀ ≠ b₁ := by
    rintro rfl
    obtain ⟨x, hx⟩ := partner_zero_ne_one j
    apply hx
    apply σ.injective
    rw [hb₀, hb₁]
  refine total_eq_of_two_synthemes i i' b₀ b₁ b₀' b₁' hne (fun y => ?_) (fun y => ?_)
  · obtain ⟨x, rfl⟩ := σ.surjective y
    rw [← hb₀, hb₀']
  · obtain ⟨x, rfl⟩ := σ.surjective y
    rw [← hb₁, hb₁']

theorem mapsTotal_totalIdx (σ : Perm (Fin 6)) (j : Fin 6) : MapsTotal σ j (totalIdx σ j) := by
  obtain ⟨i, hi⟩ := exists_mapsTotal σ j
  have hne : (List.finRange 6).find? (fun i => decide (MapsTotal σ j i)) ≠ none := by
    rw [Ne, List.find?_eq_none]
    push Not
    exact ⟨i, List.mem_finRange i, decide_eq_true hi⟩
  obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp hne
  have hp := List.find?_some hi'
  rw [totalIdx, hi', Option.getD_some]
  exact of_decide_eq_true hp

theorem totalIdx_mul (σ τ : Perm (Fin 6)) (j : Fin 6) :
    totalIdx ⇑(σ * τ) j = totalIdx σ (totalIdx τ j) :=
  (mapsTotal_totalIdx (σ * τ) j).unique
    ((mapsTotal_totalIdx τ j).comp (mapsTotal_totalIdx σ (totalIdx τ j)))

theorem totalIdx_one (j : Fin 6) : totalIdx ⇑(1 : Perm (Fin 6)) j = j :=
  (mapsTotal_totalIdx 1 j).unique fun a => ⟨a, fun _ => rfl⟩

@[expose] def totalPerm (σ : Perm (Fin 6)) : Perm (Fin 6) where
  toFun := totalIdx σ
  invFun := totalIdx ⇑σ⁻¹
  left_inv j := by rw [← totalIdx_mul, inv_mul_cancel, totalIdx_one]
  right_inv j := by rw [← totalIdx_mul, mul_inv_cancel, totalIdx_one]

theorem totalPerm_apply (σ : Perm (Fin 6)) (j : Fin 6) : totalPerm σ j = totalIdx σ j := rfl

@[expose] def totalPermHom : Perm (Fin 6) →* Perm (Fin 6) where
  toFun := totalPerm
  map_one' := Perm.ext fun j => by rw [totalPerm_apply, totalIdx_one, Perm.one_apply]
  map_mul' σ τ := Perm.ext fun j => by
    rw [Perm.mul_apply, totalPerm_apply, totalPerm_apply, totalPerm_apply, totalIdx_mul]

@[expose] def rep4a : alternatingGroup (Fin 6) →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  heartHom.comp (alternatingGroup (Fin 6)).subtype

@[expose] def rep4b : alternatingGroup (Fin 6) →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  heartHom.comp (totalPermHom.comp (alternatingGroup (Fin 6)).subtype)

theorem untab_heartTab (σ : Perm (Fin 6)) : untab (heartTab (Vector.ofFn σ)) = heartHom σ := by
  have hv : (fun x => (Vector.ofFn σ)[x]) = ⇑σ := funext fun x => by simp
  simp only [heartTab, untab_tab, hv]
  rfl

theorem untab_heartTab_totalVec (σ : Perm (Fin 6)) :
    untab (heartTab (totalVec (Vector.ofFn σ))) = heartHom (totalPermHom σ) := by
  have hv : (fun x => (Vector.ofFn σ)[x]) = ⇑σ := funext fun x => by simp
  have ht : (fun x => (Vector.ofFn (totalIdx ⇑σ))[x]) = totalIdx ⇑σ := funext fun x => by simp
  simp only [heartTab, totalVec, untab_tab, hv, ht]
  rfl

theorem untab_rep4aTab (σ : alternatingGroup (Fin 6)) : untab (rep4aTab σ) = rep4a σ :=
  untab_heartTab σ

theorem untab_rep4bTab (σ : alternatingGroup (Fin 6)) : untab (rep4bTab σ) = rep4b σ :=
  untab_heartTab_totalVec σ

theorem kron16_mul (A A' B B' : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    kron16 (A * A') (B * B') = kron16 A B * kron16 A' B' := by
  simp only [kron16, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.mul_kronecker_mul]

theorem kron16_one : kron16 1 1 = 1 := by
  simp only [kron16, Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem proj8_mul_basis8 : proj8 * basis8 = 1 := by decide +kernel

@[expose] def kron16F (σ : alternatingGroup (Fin 6)) : Matrix (Fin 16) (Fin 16) FieldFour :=
  (kron16 (rep4a σ) (rep4b σ)).map ofPrime

theorem kron16F_mul (σ τ : alternatingGroup (Fin 6)) :
    kron16F (σ * τ) = kron16F σ * kron16F τ := by
  simp only [kron16F, map_mul, kron16_mul]
  exact Matrix.map_mul

theorem kron16F_one : kron16F 1 = 1 := by
  simp only [kron16F, map_one, kron16_one]
  exact Matrix.map_one ofPrime ofPrime.map_zero ofPrime.map_one

@[expose] def rep8aMat (σ : alternatingGroup (Fin 6)) : Matrix (Fin 8) (Fin 8) FieldFour :=
  proj8 * kron16F σ * basis8

theorem untab_kronOfTabs (a b : Vector (Vector (ZMod 2) 4) 4) :
    untab (kronOfTabs a b) = (kron16 (untab a) (untab b)).map ofPrime := by
  simp only [kronOfTabs, untab_tab]

theorem untab_kronTab (σ : alternatingGroup (Fin 6)) : untab (kronTab σ) = kron16F σ := by
  rw [kronTab, untab_kronOfTabs, untab_rep4aTab, untab_rep4bTab]
  rfl

theorem untab_rep8aOfKron (K : Vector (Vector FieldFour 16) 16) :
    untab (rep8aOfKron K) = proj8 * untab K * basis8 := by
  simp only [rep8aOfKron, mulBasis8, untab_tab]

theorem untab_rep8aTab (σ : alternatingGroup (Fin 6)) : untab (rep8aTab σ) = rep8aMat σ := by
  rw [rep8aTab, untab_rep8aOfKron, untab_kronTab, rep8aMat]

@[expose] def kronPerm (σ : Perm (Fin 6)) : Matrix (Fin 16) (Fin 16) FieldFour :=
  (kron16 (heartHom σ) (heartHom (totalPermHom σ))).map ofPrime

theorem kronPerm_mul (σ τ : Perm (Fin 6)) : kronPerm (σ * τ) = kronPerm σ * kronPerm τ := by
  simp only [kronPerm, map_mul, kron16_mul]
  exact Matrix.map_mul

theorem kronPerm_one : kronPerm 1 = 1 := by
  simp only [kronPerm, map_one, kron16_one]
  exact Matrix.map_one ofPrime ofPrime.map_zero ofPrime.map_one

theorem invCheckIfThreeCycle_all : ∀ σ : Perm (Fin 6), invCheckIfThreeCycle σ = true :=
  Certificates.certificate18002.1

theorem invCheckOfKron_spec (K : Vector (Vector FieldFour 16) 16) (h : invCheckOfKron K = true) :
    untab K * basis8 = basis8 * untab (rep8aOfKron K) := by
  unfold invCheckOfKron at h
  exact of_decide_eq_true h

theorem kronPerm_mul_basis8_of_isThreeCycle (σ : Perm (Fin 6)) (hσ : σ.IsThreeCycle) :
    ∃ X, kronPerm σ * basis8 = basis8 * X := by
  have h := invCheckIfThreeCycle_all σ
  have hc : σ.support.card = 3 := hσ.card_support
  simp only [invCheckIfThreeCycle, hc, ite_true, invCheckPerm] at h
  have h' := invCheckOfKron_spec _ h
  rw [untab_rep8aOfKron, untab_kronOfTabs, untab_heartTab, untab_heartTab_totalVec] at h'
  exact ⟨_, h'⟩

theorem kronPerm_mul_basis8 (σ : Perm (Fin 6)) (hσ : σ ∈ alternatingGroup (Fin 6)) :
    ∃ X, kronPerm σ * basis8 = basis8 * X := by
  rw [← Perm.closure_three_cycles_eq_alternating] at hσ
  induction hσ using Subgroup.closure_induction'' with
  | mem x hx => exact kronPerm_mul_basis8_of_isThreeCycle x hx
  | inv_mem x hx => exact kronPerm_mul_basis8_of_isThreeCycle x⁻¹ hx.inv
  | one => exact ⟨1, by rw [kronPerm_one, Matrix.one_mul, Matrix.mul_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    exact ⟨X * Y, by rw [kronPerm_mul, Matrix.mul_assoc, hY, ← Matrix.mul_assoc, hX,
      Matrix.mul_assoc]⟩

theorem kron16F_mul_basis8 (σ : alternatingGroup (Fin 6)) :
    kron16F σ * basis8 = basis8 * rep8aMat σ := by
  obtain ⟨X, hX⟩ := kronPerm_mul_basis8 σ σ.2
  have hX' : kron16F σ * basis8 = basis8 * X := hX
  have hXeq : rep8aMat σ = X := by
    rw [rep8aMat, Matrix.mul_assoc, hX', ← Matrix.mul_assoc, proj8_mul_basis8, Matrix.one_mul]
  rw [hXeq, hX']

theorem rep8aMat_mul (σ τ : alternatingGroup (Fin 6)) :
    rep8aMat (σ * τ) = rep8aMat σ * rep8aMat τ := by
  calc rep8aMat (σ * τ) = proj8 * kron16F σ * (kron16F τ * basis8) := by
        rw [rep8aMat, kron16F_mul]
        simp only [Matrix.mul_assoc]
    _ = proj8 * kron16F σ * (basis8 * rep8aMat τ) := by rw [kron16F_mul_basis8]
    _ = (proj8 * kron16F σ * basis8) * rep8aMat τ := by simp only [Matrix.mul_assoc]

theorem rep8aMat_one : rep8aMat 1 = 1 := by
  rw [rep8aMat, kron16F_one, Matrix.mul_one, proj8_mul_basis8]

@[expose] def rep8a : alternatingGroup (Fin 6) →* Matrix (Fin 8) (Fin 8) FieldFour where
  toFun := rep8aMat
  map_one' := rep8aMat_one
  map_mul' := rep8aMat_mul

@[expose] def rep8b : alternatingGroup (Fin 6) →* Matrix (Fin 8) (Fin 8) FieldFour :=
  (frob.mapMatrix : Matrix (Fin 8) (Fin 8) FieldFour →+* _).toMonoidHom.comp rep8a

theorem untab_rep8aTab' (σ : alternatingGroup (Fin 6)) : untab (rep8aTab σ) = rep8a σ :=
  untab_rep8aTab σ

@[expose] def rep1 : alternatingGroup (Fin 6) →* Matrix (Fin 1) (Fin 1) (ZMod 2) := 1

theorem cert1_check : cert1.check (fun _ => tab 1) = true := by decide +kernel

theorem cert4a_check : cert4a.check rep4aTab = true := by decide +kernel

theorem cert4b_check : cert4b.check rep4bTab = true := by decide +kernel

theorem cert8a_check : cert8a.check rep8aTab = true :=
  Certificates.certificate18002.2.1

variable {K : Type*} [Field K]

theorem isIrreducible_rep1 (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep1).IsIrreducible :=
  cert1.isIrreducible_of_check φ rep1 (fun _ => tab 1) (fun _ => by rw [untab_tab]; rfl)
    cert1_check

theorem isIrreducible_rep4a (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep4a).IsIrreducible :=
  cert4a.isIrreducible_of_check φ rep4a rep4aTab untab_rep4aTab cert4a_check

theorem isIrreducible_rep4b (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep4b).IsIrreducible :=
  cert4b.isIrreducible_of_check φ rep4b rep4bTab untab_rep4bTab cert4b_check

theorem isIrreducible_rep8a (φ : FieldFour →+* K) : (matrixBaseChange φ rep8a).IsIrreducible :=
  cert8a.isIrreducible_of_check φ rep8a rep8aTab untab_rep8aTab' cert8a_check

theorem isIrreducible_rep8b (φ : FieldFour →+* K) : (matrixBaseChange φ rep8b).IsIrreducible := by
  rw [rep8b, matrixBaseChange_comp]
  exact isIrreducible_rep8a (φ.comp frob)

theorem powImages_apply (σ : Perm (Fin 6)) (n : ℕ) (x : Fin 6) :
    (powImages (Vector.ofFn σ) n)[x] = (σ ^ n) x := by
  induction n generalizing x with
  | zero => simp [powImages]
  | succ n ih => simp [powImages, composeImages, ih, pow_succ']

theorem classCheck_eq : classCheck = true :=
  Certificates.certificate18002.2.2.1

theorem classCheckWith_spec (all : Multiset (Vector (Fin 6) 6)) (h : classCheckWith all = true) :
    ∀ v ∈ all, classCheckElem v = true := by
  unfold classCheckWith at h
  exact of_decide_eq_true h

theorem conjTestWith_spec (c v : Vector (Fin 6) 6) (j : Fin 5) (h : conjTestWith c v j = true) :
    ∀ x : Fin 6, v[c[x]] = c[classReps[j][x]] := by
  unfold conjTestWith at h
  exact of_decide_eq_true h

theorem exists_conj_classReps (g : alternatingGroup (Fin 6)) (hg : g ^ 45 = 1) :
    ∃ j : Fin 5, ∃ c : alternatingGroup (Fin 6),
      ∀ x, (g : Perm (Fin 6)) ((c : Perm (Fin 6)) x) = (c : Perm (Fin 6)) classReps[j][x] := by
  have h : ∀ v ∈ allImages, classCheckElem v = true :=
    classCheckWith_spec allImages classCheck_eq
  have hg' := h (Vector.ofFn ⇑(g : Perm (Fin 6)))
    (Multiset.mem_map.mpr ⟨g, Finset.mem_univ_val g, rfl⟩)
  rw [classCheckElem, Bool.or_eq_true] at hg'
  rcases hg' with hg' | hg'
  · exfalso
    have hid : isIdVec (powImages (Vector.ofFn ⇑(g : Perm (Fin 6))) 45) = true := by
      apply decide_eq_true
      intro x
      rw [powImages_apply, ← Subgroup.coe_pow, hg]
      rfl
    rw [hid] at hg'
    exact Bool.noConfusion hg'
  · obtain ⟨p, -, hp⟩ := List.any_eq_true.mp hg'
    refine ⟨p.1, a6OfImages p.2, fun x => ?_⟩
    have h2 := conjTestWith_spec _ _ _ hp x
    simpa using h2

theorem traceCheck_eq : traceCheck = true := by decide +kernel

theorem traceCheckWith_spec (a b : Vector (Vector (ZMod 2) 4) 4) (c : Vector (Vector FieldFour 8) 8)
    (h : traceCheckWith a b c = true) : Matrix.trace (untab a) = 1 ∧
      Matrix.trace (untab b) = 0 ∧ Matrix.trace (untab c) = ω₂ := by
  simp only [traceCheckWith, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem trace_rep4a_threeCycle : Matrix.trace (rep4a threeCycle) = 1 := by
  rw [← untab_rep4aTab]
  exact (traceCheckWith_spec _ _ _ traceCheck_eq).1

theorem trace_rep4b_threeCycle : Matrix.trace (rep4b threeCycle) = 0 := by
  rw [← untab_rep4bTab]
  exact (traceCheckWith_spec _ _ _ traceCheck_eq).2.1

theorem trace_rep8a_fiveCycle : Matrix.trace (rep8a fiveCycle) = ω₂ := by
  rw [← untab_rep8aTab']
  exact (traceCheckWith_spec _ _ _ traceCheck_eq).2.2

theorem trace_rep8b_fiveCycle : Matrix.trace (rep8b fiveCycle) = ω := by
  change Matrix.trace ((rep8a fiveCycle).map frob) = ω
  rw [← AddMonoidHom.map_trace, trace_rep8a_fiveCycle, frob_ω₂]

@[expose] noncomputable def omegaClass : Finset (alternatingGroup (Fin 6)) :=
  Finset.univ.filter fun g => (g : Perm (Fin 6)).support.card = 5 ∧ Matrix.trace (rep8a g) = ω₂

theorem classSumCheck_eq : classSumCheck = true :=
  Certificates.certificate18002.2.2.2

theorem isOmegaScalar_spec (S : Vector (Vector FieldFour 8) 8) (h : isOmegaScalar S = true) :
    untab S = ω₂ • 1 := by
  unfold isOmegaScalar at h
  exact of_decide_eq_true h

theorem untab_basisProj : untab basisProj = basis8 * proj8 := untab_tab _

theorem trace_rep8a_eq (g : alternatingGroup (Fin 6)) :
    Matrix.trace (rep8a g) = Matrix.trace (kron16F g * (basis8 * proj8)) := by
  change Matrix.trace (proj8 * kron16F g * basis8) = _
  rw [Matrix.mul_assoc proj8, Matrix.trace_mul_comm proj8, Matrix.mul_assoc]

theorem untab_addTab {m n : ℕ} {α : Type*} [Add α] (a b : Vector (Vector α n) m) :
    untab (addTab a b) = untab a + untab b := by
  ext i j
  simp [addTab, untab]

theorem untab_sumFiveCycles (s : Multiset (alternatingGroup (Fin 6))) :
    untab (sumFiveCycles s) = (s.map fun g => untab (selectFiveCycle g)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [sumFiveCycles, zeroTab16]
  | cons g s ih =>
    rw [sumFiveCycles, Multiset.foldr_cons, ← sumFiveCycles, Multiset.map_cons,
      Multiset.sum_cons, ← ih, fiveCycleStep, untab_addTab]

theorem untab_selectFiveCycle (g : alternatingGroup (Fin 6)) :
    untab (selectFiveCycle g) =
      if (g : Perm (Fin 6)).support.card = 5 ∧ Matrix.trace (rep8a g) = ω₂ then kron16F g
      else 0 := by
  have hK : Matrix.trace (untab (kronTab g) * untab basisProj) = Matrix.trace (rep8a g) := by
    rw [untab_kronTab, untab_basisProj, ← trace_rep8a_eq]
  unfold selectFiveCycle selectOmega
  rw [hK]
  by_cases h5 : (g : Perm (Fin 6)).support.card = 5 <;>
    by_cases ht : Matrix.trace (rep8a g) = ω₂ <;> simp [h5, ht, untab_kronTab, zeroTab16]

theorem sum_omegaClass_rep8a :
    ∑ g ∈ omegaClass, rep8a g = ω₂ • (1 : Matrix (Fin 8) (Fin 8) FieldFour) := by
  have h : untab (rep8aOfKron (sumFiveCycles (Finset.univ : Finset (alternatingGroup (Fin 6))).val))
      = ω₂ • 1 := isOmegaScalar_spec _ classSumCheck_eq
  rw [untab_rep8aOfKron, untab_sumFiveCycles] at h
  have hsum : ((Finset.univ : Finset (alternatingGroup (Fin 6))).val.map
      fun g => untab (selectFiveCycle g)).sum = ∑ g ∈ omegaClass, kron16F g := by
    rw [← Finset.sum_eq_multiset_sum, omegaClass, Finset.sum_filter]
    exact Finset.sum_congr rfl fun g _ => untab_selectFiveCycle g
  rw [hsum, Matrix.mul_sum, Matrix.sum_mul] at h
  exact h

end CFSG.CharacterTheory.SteinbergBY.AlternatingSix
