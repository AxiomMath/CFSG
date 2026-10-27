module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadRk
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel
open Matrix

section Norm

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def unitNorm1 (h : UnitaryFieldData ℓ f K) : Subgroup Kˣ where
  carrier := {u | h.bar (u : K) * (u : K) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    calc h.bar a * h.bar b * (a * b) = (h.bar a * a) * (h.bar b * b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
    rw [← mul_inv, ha, inv_one]

theorem mem_unitNorm1 (h : UnitaryFieldData ℓ f K) {u : Kˣ} :
    u ∈ unitNorm1 h ↔ h.bar (u : K) * (u : K) = 1 := Iff.rfl

theorem mem_unitNorm1_of_cube (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1) {a : Kˣ}
    (ha : a ^ 3 = 1) : a ∈ unitNorm1 h := by
  rw [mem_unitNorm1, UnitaryFieldData.bar_apply, ← pow_succ]
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, pow_mul]
  have : (a : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
  rw [this, one_pow]

theorem neg_one_mem_unitNorm1 (h : UnitaryFieldData ℓ f K) : (-1 : Kˣ) ∈ unitNorm1 h := by
  rw [mem_unitNorm1]
  simp

theorem tEntry_mem (N : Subgroup Kˣ) {a b c d : Kˣ} (ha : a ∈ N) (hb : b ∈ N) (hc : c ∈ N)
    (hd : d ∈ N) (k : ℕ) : tEntry a b c d k ∈ N := by
  unfold tEntry
  split_ifs
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact N.inv_mem (N.mul_mem (N.mul_mem (N.mul_mem ha hb) hc) hd)
  · exact N.one_mem

variable {n : ℕ}

theorem toGL_tDiag_mem_gramSU (h : UnitaryFieldData ℓ f K) (hn : 5 ≤ n) {a b c d : Kˣ}
    (ha : a ∈ unitNorm1 h) (hb : b ∈ unitNorm1 h) (hc : c ∈ unitNorm1 h) (hd : d ∈ unitNorm1 h) :
    (Matrix.SpecialLinearGroup.toGL (tDiag hn a b c d) : GL (Fin n) K) ∈
      gramSU h (idGram K n) := by
  rw [mem_gramSU_iff_unitary, mem_primeFormUnitary]
  refine ⟨?_, (tDiag hn a b c d).2⟩
  have hu : ∀ i : Fin n, h.bar (tEntry a b c d i : K) * (tEntry a b c d i : K) = 1 :=
    fun i => tEntry_mem (unitNorm1 h) ha hb hc hd i
  show ((diagonal fun i : Fin n => (tEntry a b c d i : K)).map h.bar)ᵀ *
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      diagonal (fun i : Fin n => (tEntry a b c d i : K)) =
    ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [Units.val_one, Matrix.diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_one,
    diagonal_mul_diagonal, show (fun i : Fin n => h.bar (tEntry a b c d i : K) *
      (tEntry a b c d i : K)) = fun _ => 1 from funext hu]
  exact diagonal_one

end Norm

section Torus

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def suTorus (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1)
    (hn : 5 ≤ n) :
    (rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K) →*
      gramSU h (idGram K n) :=
  ((Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K).comp
    (torusHom hn)).codRestrict (gramSU h (idGram K n)) fun w =>
      toGL_tDiag_mem_gramSU h hn
        (mem_unitNorm1_of_cube h hdvd ((mem_rootsOfUnity 3 _).1 w.1.2))
        (mem_unitNorm1_of_cube h hdvd ((mem_rootsOfUnity 3 _).1 w.2.1.2))
        (mem_unitNorm1_of_cube h hdvd ((mem_rootsOfUnity 3 _).1 w.2.2.1.2))
        (mem_unitNorm1_of_cube h hdvd ((mem_rootsOfUnity 3 _).1 w.2.2.2.2))

theorem suTorus_normOne (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1) (hn : 6 ≤ n)
    {w : rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K}
    (hw : suTorus h hdvd (by omega : 5 ≤ n) w ∈ normOneScalars h (gramSU h (idGram K n)) n) :
    w = 1 := by
  obtain ⟨c, -, hcn, hc⟩ := hw
  apply torusHom_scalar hn
  refine mem_scalars.2 ⟨c, hcn, ?_⟩
  have h1 : (torusHom (by omega : 5 ≤ n) w : Matrix (Fin n) (Fin n) K) =
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
  rw [GeneralLinearGroup.coe_scalar] at h1
  exact h1

theorem suTorus_injective (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1) (hn : 6 ≤ n) :
    Function.Injective (suTorus h hdvd (by omega : 5 ≤ n)) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  exact suTorus_normOne h hdvd hn (by rw [hw]; exact one_mem _)

theorem isElemAbelian_range {W G : Type*} [CommGroup W] [Group G] (φ : W →* G) {p : ℕ}
    (hW : ∀ w : W, w ^ p = 1) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨u, hu⟩ := x.2
    obtain ⟨v, hv⟩ := y.2
    apply Subtype.ext
    show (x : G) * y = y * x
    rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm u v]
  · obtain ⟨u, rfl⟩ := hx
    rw [← map_pow, hW u, map_one]

theorem pow_three_eq_one_prod
    (w : rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K) :
    w ^ 3 = 1 :=
  Prod.ext (pow_three_eq_one_roots _) (Prod.ext (pow_three_eq_one_roots _)
    (Prod.ext (pow_three_eq_one_roots _) (pow_three_eq_one_roots _)))

theorem suTorus_card [Finite K] (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1) (hn : 6 ≤ n)
    {ζ : Kˣ} (hζ : orderOf ζ = 3) :
    27 < Nat.card (suTorus h hdvd (by omega : 5 ≤ n)).range := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (suTorus_injective h hdvd hn)).toEquiv,
    Nat.card_prod, Nat.card_prod, Nat.card_prod]
  have h3 := three_le_card_roots (K := K) hζ
  have : 3 * (3 * (3 * 3)) ≤ Nat.card (rootsOfUnity 3 K) *
      (Nat.card (rootsOfUnity 3 K) * (Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K))) :=
    Nat.mul_le_mul h3 (Nat.mul_le_mul h3 (Nat.mul_le_mul h3 h3))
  omega

@[expose] noncomputable def negSU (h : UnitaryFieldData ℓ f K) (hn : 5 ≤ n) :
    gramSU h (idGram K n) :=
  ⟨Matrix.SpecialLinearGroup.toGL (negDiag hn),
    toGL_tDiag_mem_gramSU h hn (neg_one_mem_unitNorm1 h) (neg_one_mem_unitNorm1 h)
      (one_mem _) (one_mem _)⟩

theorem negSU_sq (h : UnitaryFieldData ℓ f K) (hn : 5 ≤ n) : negSU h hn ^ 2 = 1 := by
  apply Subtype.ext
  show (Matrix.SpecialLinearGroup.toGL (negDiag hn) : GL (Fin n) K) ^ 2 = 1
  rw [← map_pow, negDiag_sq, map_one]

theorem negSU_not_normOne (h : UnitaryFieldData ℓ f K) (hn : 6 ≤ n) (h2 : ringChar K ≠ 2) :
    negSU h (by omega : 5 ≤ n) ∉ normOneScalars h (gramSU h (idGram K n)) n := by
  rintro ⟨c, -, hcn, hc⟩
  refine negDiag_not_scalar hn h2 (mem_scalars.2 ⟨c, hcn, ?_⟩)
  have h1 : (negDiag (K := K) (by omega : 5 ≤ n) : Matrix (Fin n) (Fin n) K) =
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
  rw [GeneralLinearGroup.coe_scalar] at h1
  exact h1

theorem suTorus_commute_negSU (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1) (hn : 5 ≤ n)
    (w : rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K) :
    Commute (suTorus h hdvd hn w) (negSU h hn) := by
  apply Subtype.ext
  show Matrix.SpecialLinearGroup.toGL (torusHom hn w) * Matrix.SpecialLinearGroup.toGL (negDiag hn) =
    Matrix.SpecialLinearGroup.toGL (negDiag hn) * Matrix.SpecialLinearGroup.toGL (torusHom hn w)
  rw [← map_mul, ← map_mul]
  exact congrArg _ (tDiag_comm hn _ _ _ _ _ _ _ _)

end Torus

section Swap

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def swapGL (i j : Fin n) : GL (Fin n) K :=
  (Matrix.permMatrixHom (n := Fin n) (R := K)).toHomUnits (Equiv.swap i j)

theorem coe_swapGL (i j : Fin n) :
    ((swapGL i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (Equiv.swap i j).permMatrix K := by
  simp [swapGL]

theorem swap_permMatrix_apply (i j a b : Fin n) :
    (Equiv.swap i j).permMatrix K a b = if Equiv.swap i j a = b then 1 else 0 := by
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem swapGL_sq (i j : Fin n) : (swapGL i j : GL (Fin n) K) ^ 2 = 1 := by
  rw [swapGL, ← map_pow, sq, Equiv.swap_mul_self, map_one]

theorem swapGL_mem_gramSU [CharP K 2] (h : UnitaryFieldData ℓ f K) {i j : Fin n} (hij : i ≠ j) :
    (swapGL i j : GL (Fin n) K) ∈ gramSU h (idGram K n) := by
  rw [mem_gramSU_iff_unitary, mem_primeFormUnitary]
  refine ⟨?_, ?_⟩
  · rw [coe_swapGL]
    have hmap : ((Equiv.swap i j).permMatrix K).map h.bar = (Equiv.swap i j).permMatrix K := by
      ext a b
      rw [Matrix.map_apply, swap_permMatrix_apply]
      split_ifs <;> simp
    have htr : ((Equiv.swap i j).permMatrix K).transpose = (Equiv.swap i j).permMatrix K := by
      rw [Matrix.transpose_permMatrix, Equiv.swap_inv]
    have hsq : (Equiv.swap i j).permMatrix K * (Equiv.swap i j).permMatrix K = 1 := by
      rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
    show (((Equiv.swap i j).permMatrix K).map h.bar)ᵀ *
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Equiv.swap i j).permMatrix K =
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hmap, Units.val_one, Matrix.mul_one]
    exact (congrArg (· * (Equiv.swap i j).permMatrix K) htr).trans hsq
  · rw [coe_swapGL, Matrix.det_permutation, Equiv.Perm.sign_swap hij]
    simp [CharTwo.neg_eq]

theorem swapGL_not_scalar {i j : Fin n} (hij : i ≠ j) (c : Kˣ) :
    (swapGL i j : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c := by
  intro h
  have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h) i) j
  simp only [coe_swapGL, swap_permMatrix_apply, Equiv.swap_apply_left,
    GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_ne _ hij] at h1
  simp at h1

theorem diagonal_commute_swap (i j : Fin n) (d : Fin n → K) (hd : d i = d j) :
    (diagonal d : Matrix (Fin n) (Fin n) K) * (Equiv.swap i j).permMatrix K =
      (Equiv.swap i j).permMatrix K * diagonal d := by
  ext a b
  rw [diagonal_mul, mul_diagonal, swap_permMatrix_apply]
  by_cases h : Equiv.swap i j a = b
  · subst h
    rw [if_pos rfl, mul_one, one_mul]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hd]
    · rw [h2, hd]
    · rfl
  · rw [if_neg h]
    simp

end Swap

section Main

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def swapSU [CharP K 2] (h : UnitaryFieldData ℓ f K) (hn : 7 ≤ n) :
    gramSU h (idGram K n) :=
  ⟨swapGL (⟨5, by omega⟩ : Fin n) ⟨6, by omega⟩, swapGL_mem_gramSU h (by simp [Fin.ext_iff])⟩

theorem swapSU_sq [CharP K 2] (h : UnitaryFieldData ℓ f K) (hn : 7 ≤ n) : swapSU h hn ^ 2 = 1 :=
  Subtype.ext (swapGL_sq _ _)

theorem suTorus_commute_swapSU [CharP K 2] (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1)
    (hn : 7 ≤ n)
    (w : rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K) :
    Commute (suTorus h hdvd (by omega : 5 ≤ n) w) (swapSU h hn) := by
  apply Subtype.ext
  apply Units.ext
  show (diagonal fun i : Fin n => ((tEntry (w.1 : Kˣ) (w.2.1 : Kˣ) (w.2.2.1 : Kˣ) (w.2.2.2 : Kˣ) i :
      Kˣ) : K)) * ((swapGL (⟨5, by omega⟩ : Fin n) ⟨6, by omega⟩ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
    ((swapGL (⟨5, by omega⟩ : Fin n) ⟨6, by omega⟩ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      diagonal fun i : Fin n => ((tEntry (w.1 : Kˣ) (w.2.1 : Kˣ) (w.2.2.1 : Kˣ) (w.2.2.2 : Kˣ) i :
        Kˣ) : K)
  rw [coe_swapGL]
  exact diagonal_commute_swap _ _ _ (by simp [tEntry])

theorem rkY_false_su {Y : Type} [Group Y] (hRk : RkY Y) [Finite K] (h : UnitaryFieldData ℓ f K)
    (hn : 6 ≤ n) (hdvd : 3 ∣ ℓ ^ f + 1) (hodd : ringChar K ≠ 2 ∨ 7 ≤ n) {ζ : Kˣ}
    (hζ : orderOf ζ = 3) {X : Type} [Group X] (ρ : gramSU h (idGram K n) →* Y) (q : Y →* X)
    (π : gramSU h (idGram K n) →* X) (hcomp : ∀ g, q (ρ g) = π g)
    (hZ : ∀ y ∈ Subgroup.center Y, q y = 1)
    (hπ : ∀ g, π g = 1 → g ∈ normOneScalars h (gramSU h (idGram K n)) n) : False := by
  have hn5 : 5 ≤ n := by omega
  have hEπ : ∀ g ∈ (suTorus h hdvd hn5).range, π g = 1 → g = 1 := by
    rintro _ ⟨w, rfl⟩ hw
    rw [suTorus_normOne h hdvd hn (hπ _ hw), map_one]
  have hcard := suTorus_card h hdvd hn hζ
  have hE := isElemAbelian_range (suTorus h hdvd hn5) pow_three_eq_one_prod
  by_cases h2 : ringChar K = 2
  · have h7 : 7 ≤ n := hodd.resolve_left (not_not.2 h2)
    haveI : CharP K 2 := ringChar.of_eq h2
    refine rkY_false_of_cover hRk ρ q π hcomp hZ hE hcard hEπ
      (U₀ := Subgroup.zpowers (swapSU h h7))
      (isElemAbelian_zpowers (swapSU_sq h h7)).isPGroup ?_ ?_
    · refine ⟨swapSU h h7, Subgroup.mem_zpowers _, fun hπu => ?_⟩
      obtain ⟨c, -, -, hc⟩ := hπ _ hπu
      exact swapGL_not_scalar (by simp [Fin.ext_iff]) c hc
    · rintro _ ⟨w, rfl⟩ u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      have hc := suTorus_commute_swapSU h hdvd h7 w
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  · refine rkY_false_of_cover hRk ρ q π hcomp hZ hE hcard hEπ
      (U₀ := Subgroup.zpowers (negSU h hn5))
      (isElemAbelian_zpowers (negSU_sq h hn5)).isPGroup ?_ ?_
    · exact ⟨negSU h hn5, Subgroup.mem_zpowers _, fun hπu => negSU_not_normOne h hn h2 (hπ _ hπu)⟩
    · rintro _ ⟨w, rfl⟩ u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      have hc := suTorus_commute_negSU h hdvd hn5 w
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431
