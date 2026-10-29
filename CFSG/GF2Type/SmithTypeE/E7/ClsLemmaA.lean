module

public import CFSG.GF2Type.SmithTypeE.E7.UwMat
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GF2Type.SmithTypeE.E7

open scoped Matrix

@[expose] noncomputable def tau0M : M6 := 1 + Matrix.of fun i j => if i = 0 ∧ j = 5 then 1 else 0

@[expose] def InT (A : M6) : Prop := ∃ v : Fin 6 → ZMod 2, v 5 = 0 ∧
  A = 1 + Matrix.of fun i j => if j = 5 then v i else 0

@[expose] def InAltV5 (N : M6) : Prop := IsAlt N ∧ ∀ i, N i 5 = 0

@[expose] def ClsShape (a : M6) : Prop :=
  IsUT a ∧ ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → j ≠ 5 → a i j = if i = j then 1 else 0

@[expose] def clsW (j : Fin 6) : M6 :=
  Matrix.of fun a b => if (a = 0 ∧ b = j) ∨ (a = j ∧ b = 0) then 1 else 0

@[expose] def clsW5 (j : Fin 6) : M6 :=
  Matrix.of fun a b => if (a = j ∧ b = 5) ∨ (a = 5 ∧ b = j) then 1 else 0

theorem clsW5_isAlt {j : Fin 6} (hj : j ≠ 5) : IsAlt (clsW5 j) := by
  refine ⟨?_, fun i => ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, clsW5, Matrix.of_apply]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)
  · simp only [clsW5, Matrix.of_apply]
    split_ifs with h
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (h1.symm.trans h2) hj
      · exact absurd (h2.symm.trans h1) hj
    · rfl

theorem tau0_mul_clsW5 {j : Fin 6} (hj0 : j ≠ 0) (hj5 : j ≠ 5) :
    tau0M * clsW5 j * tau0Mᵀ + clsW5 j = clsW j := by
  fin_cases j <;> first | exact absurd rfl hj0 | exact absurd rfl hj5 | decide +kernel

theorem clsA1 {a : M6} (hUT : IsUT a) {j : Fin 6} (hj0 : j ≠ 0) (hj5 : j ≠ 5)
    (h : a * clsW j * aᵀ = clsW j) (i : Fin 6) (hi : i ≠ 0) :
    a i j = if i = j then 1 else 0 := by
  have h1 := congrFun (congrFun h i) 0
  have hi0 : a i 0 = 0 := by
    rw [hUT i 0 (Fin.zero_le i), if_neg hi]
  have ha00 : a 0 0 = 1 := by
    rw [hUT 0 0 le_rfl, if_pos rfl]
  fin_cases j <;> simp_all [clsW, Matrix.mul_apply, Fin.sum_univ_six, Matrix.transpose_apply]

theorem clsShape_of_wedge {a : M6} (hUT : IsUT a)
    (hw : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → a * clsW j * aᵀ = clsW j) : ClsShape a :=
  ⟨hUT, fun i j hi hj0 hj5 => clsA1 hUT hj0 hj5 (hw j hj0 hj5) i hi⟩

@[expose] def clsIx (l : Fin 4) : Fin 6 := ⟨l.val + 1, by have := l.isLt; omega⟩

theorem clsShape_col0 {a : M6} (h : ClsShape a) (i : Fin 6) :
    a i 0 = if i = 0 then 1 else 0 :=
  h.1 i 0 (Fin.zero_le i)

theorem clsShape_00 {a : M6} (h : ClsShape a) : a 0 0 = 1 := by
  rw [clsShape_col0 h 0, if_pos rfl]

theorem clsShape_55 {a : M6} (h : ClsShape a) : a 5 5 = 1 := by
  rw [h.1 5 5 (by decide), if_pos rfl]

theorem clsShape_mul_0j {a b : M6} (ha : ClsShape a) (hb : ClsShape b) {j : Fin 6}
    (hj0 : j ≠ 0) (hj5 : j ≠ 5) : (a * b) 0 j = a 0 j + b 0 j := by
  have h1 := hb.2 1 j (by decide) hj0 hj5
  have h2 := hb.2 2 j (by decide) hj0 hj5
  have h3 := hb.2 3 j (by decide) hj0 hj5
  have h4 := hb.2 4 j (by decide) hj0 hj5
  have h5 : b 5 j = 0 := by
    rw [hb.1 5 j (Fin.le_last j), if_neg (Ne.symm hj5)]
  rw [Matrix.mul_apply, Fin.sum_univ_six, clsShape_00 ha, h5, h1, h2, h3, h4]
  fin_cases j <;> first | exact absurd rfl hj0 | exact absurd rfl hj5 | (simp <;> ring)

theorem clsShape_mul_i5 {a b : M6} (ha : ClsShape a) (hb : ClsShape b) {i : Fin 6}
    (hi0 : i ≠ 0) (hi5 : i ≠ 5) : (a * b) i 5 = a i 5 + b i 5 := by
  have h0 := ha.1 i 0 (Fin.zero_le i)
  have h1 := ha.2 i 1 hi0 (by decide) (by decide)
  have h2 := ha.2 i 2 hi0 (by decide) (by decide)
  have h3 := ha.2 i 3 hi0 (by decide) (by decide)
  have h4 := ha.2 i 4 hi0 (by decide) (by decide)
  rw [Matrix.mul_apply, Fin.sum_univ_six, clsShape_55 hb, h0, h1, h2, h3, h4]
  fin_cases i <;> first | exact absurd rfl hi0 | exact absurd rfl hi5 | simp [add_comm]

theorem clsShape_mul_05 {a b : M6} (ha : ClsShape a) (hb : ClsShape b) :
    (a * b) 0 5 =
      a 0 5 + b 0 5 + (a 0 1 * b 1 5 + a 0 2 * b 2 5 + a 0 3 * b 3 5 + a 0 4 * b 4 5) := by
  rw [Matrix.mul_apply, Fin.sum_univ_six, clsShape_00 ha, clsShape_55 hb]
  ring

theorem clsExt {a b : M6} (ha : ClsShape a) (hb : ClsShape b)
    (h0 : ∀ l : Fin 4, a 0 (clsIx l) = b 0 (clsIx l))
    (hi : ∀ l : Fin 4, a (clsIx l) 5 = b (clsIx l) 5) (h05 : a 0 5 = b 0 5) : a = b := by
  have hrow : ∀ j : Fin 6, j ≠ 0 → a 0 j = b 0 j := by
    intro j hj0
    fin_cases j
    · exact absurd rfl hj0
    · exact h0 0
    · exact h0 1
    · exact h0 2
    · exact h0 3
    · exact h05
  have hcol : ∀ i : Fin 6, i ≠ 0 → i ≠ 5 → a i 5 = b i 5 := by
    intro i hi0 hi5
    fin_cases i
    · exact absurd rfl hi0
    · exact hi 0
    · exact hi 1
    · exact hi 2
    · exact hi 3
    · exact absurd rfl hi5
  ext i j
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0
      rw [clsShape_00 ha, clsShape_00 hb]
    by_cases hj5 : j = 5
    · subst hj5
      exact h05
    exact hrow j hj0
  · by_cases hj0 : j = 0
    · subst hj0
      rw [clsShape_col0 ha, clsShape_col0 hb, if_neg hi0]
    by_cases hj5 : j = 5
    · subst hj5
      by_cases hi5 : i = 5
      · subst hi5
        rw [clsShape_55 ha, clsShape_55 hb]
      · exact hcol i hi0 hi5
    · rw [ha.2 i j hi0 hj0 hj5, hb.2 i j hi0 hj0 hj5]

theorem clsN_col5 {N : M6} (h : tau0M * N * tau0Mᵀ = N) (i : Fin 6) (hi0 : i ≠ 0) :
    N i 5 = 0 := by
  have h1 := congrFun (congrFun h i) 0
  fin_cases i <;> first
    | exact absurd rfl hi0
    | (simp [tau0M, Matrix.mul_apply, Fin.sum_univ_six] at h1 ⊢; linear_combination h1)

@[expose] def clsBits (N : M6) : Fin 6 → ZMod 2 := ![N 1 2, N 1 3, N 1 4, N 2 3, N 2 4, N 3 4]

@[expose] def clsEnc (N : M6) : (Fin 4 → ZMod 2) × (Fin 6 → ZMod 2) × ZMod 2 :=
  (fun l => N 0 (clsIx l), clsBits N, N 0 5)

@[expose] def clsGam (b : Fin 6 → ZMod 2) : Fin 4 → Fin 4 → ZMod 2 :=
  ![![0, b 0, b 1, b 2], ![b 0, 0, b 3, b 4], ![b 1, b 3, 0, b 5], ![b 2, b 4, b 5, 0]]

@[expose] def ClsCons (μ v : Fin 4 → ZMod 2) (b : Fin 6 → ZMod 2) (β : ZMod 2) : Prop :=
  ∀ i : Fin 4, ∑ l : Fin 4, clsGam b i l * μ l + β * v i = 0

instance (μ v : Fin 4 → ZMod 2) (b : Fin 6 → ZMod 2) (β : ZMod 2) :
    Decidable (ClsCons μ v b β) :=
  inferInstanceAs (Decidable (∀ i : Fin 4, ∑ l : Fin 4, clsGam b i l * μ l + β * v i = 0))

theorem clsIx_zero : clsIx 0 = 1 := rfl
theorem clsIx_one : clsIx 1 = 2 := rfl
theorem clsIx_two : clsIx 2 = 3 := rfl
theorem clsIx_three : clsIx 3 = 4 := rfl

theorem clsIx_ne_zero (l : Fin 4) : clsIx l ≠ 0 := by
  fin_cases l <;> decide

theorem clsIx_ne_five (l : Fin 4) : clsIx l ≠ 5 := by
  fin_cases l <;> decide

theorem alt_symm {N : M6} (hN : IsAlt N) (i j : Fin 6) : N i j = N j i := by
  have := congrFun (congrFun hN.1 j) i
  simpa [Matrix.transpose_apply] using this

theorem clsGam_bits {N : M6} (hN : IsAlt N) (i l : Fin 4) :
    clsGam (clsBits N) i l = N (clsIx i) (clsIx l) := by
  fin_cases i <;> fin_cases l <;> simp [clsGam, clsBits, clsIx, hN.2] <;> exact alt_symm hN _ _

theorem clsFC1 : ∀ μ : Fin 4 → ZMod 2, μ ≠ 0 → ∀ v : Fin 4 → ZMod 2,
    (Finset.univ.filter (fun y : (Fin 6 → ZMod 2) × ZMod 2 => ClsCons μ v y.1 y.2)).card ≤ 16 := by
  decide +kernel

theorem clsN_row {a N : M6} (ha : ClsShape a) (hN : IsAlt N)
    (h5 : ∀ k : Fin 6, k ≠ 0 → N k 5 = 0) (h : a * N * aᵀ = N) {i : Fin 6}
    (hi0 : i ≠ 0) (hi5 : i ≠ 5) :
    ∑ m : Fin 4, N i (clsIx m) * a 0 (clsIx m) + N 0 5 * a i 5 = 0 := by
  simp only [Fin.sum_univ_four, clsIx_zero, clsIx_one, clsIx_two, clsIx_three]
  have h1 := congrFun (congrFun h i) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_six] at h1
  have e0 := ha.1 i 0 (Fin.zero_le i)
  have e1 := ha.2 i 1 hi0 (by decide) (by decide)
  have e2 := ha.2 i 2 hi0 (by decide) (by decide)
  have e3 := ha.2 i 3 hi0 (by decide) (by decide)
  have e4 := ha.2 i 4 hi0 (by decide) (by decide)
  rw [e0, e1, e2, e3, e4] at h1
  have hs0 : ∀ k : Fin 6, N k 0 = N 0 k := fun k => alt_symm hN k 0
  have hs5 : ∀ k : Fin 6, N 5 k = N k 5 := fun k => alt_symm hN 5 k
  fin_cases i <;> first | exact absurd rfl hi0 | exact absurd rfl hi5 |
    (simp only [hs0] at h1; simp [hs5, hN.2, h5, clsShape_00 ha] at h1 ⊢; linear_combination h1)

theorem clsN_cons {a N : M6} (ha : ClsShape a) (hN : IsAlt N)
    (h5 : ∀ k : Fin 6, k ≠ 0 → N k 5 = 0) (h : a * N * aᵀ = N) :
    ClsCons (fun l => a 0 (clsIx l)) (fun i => a (clsIx i) 5) (clsBits N) (N 0 5) := by
  unfold ClsCons
  intro i
  have key := clsN_row ha hN h5 h (clsIx_ne_zero i) (clsIx_ne_five i)
  simp only [clsGam_bits hN]
  exact key

theorem clsEnc_inj {N N' : M6} (hN : IsAlt N) (hN' : IsAlt N')
    (h5 : ∀ k : Fin 6, k ≠ 0 → N k 5 = 0) (h5' : ∀ k : Fin 6, k ≠ 0 → N' k 5 = 0)
    (he : clsEnc N = clsEnc N') : N = N' := by
  have e0 : ∀ l : Fin 4, N 0 (clsIx l) = N' 0 (clsIx l) :=
    fun l => congrFun (congrArg Prod.fst he) l
  have e2 : clsBits N = clsBits N' := congrArg (fun x => x.2.1) he
  have e5 : N 0 5 = N' 0 5 := congrArg (fun x => x.2.2) he
  have hb : ∀ k : Fin 6, clsBits N k = clsBits N' k := fun k => congrFun e2 k
  have a1 : N 0 1 = N' 0 1 := e0 0
  have a2 : N 0 2 = N' 0 2 := e0 1
  have a3 : N 0 3 = N' 0 3 := e0 2
  have a4 : N 0 4 = N' 0 4 := e0 3
  have b12 : N 1 2 = N' 1 2 := hb 0
  have b13 : N 1 3 = N' 1 3 := hb 1
  have b14 : N 1 4 = N' 1 4 := hb 2
  have b23 : N 2 3 = N' 2 3 := hb 3
  have b24 : N 2 4 = N' 2 4 := hb 4
  have b34 : N 3 4 = N' 3 4 := hb 5
  have z1 : N 1 5 = N' 1 5 := by rw [h5 1 (by decide), h5' 1 (by decide)]
  have z2 : N 2 5 = N' 2 5 := by rw [h5 2 (by decide), h5' 2 (by decide)]
  have z3 : N 3 5 = N' 3 5 := by rw [h5 3 (by decide), h5' 3 (by decide)]
  have z4 : N 4 5 = N' 4 5 := by rw [h5 4 (by decide), h5' 4 (by decide)]
  have key : ∀ i j : Fin 6, i ≤ j → N i j = N' i j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | rw [hN.2, hN'.2]
      | exact e5
      | exact a1 | exact a2 | exact a3 | exact a4
      | exact b12 | exact b13 | exact b14 | exact b23 | exact b24 | exact b34
      | exact z1 | exact z2 | exact z3 | exact z4
      | rw [h5 5 (by decide), h5' 5 (by decide)]
  ext i j
  rcases le_total i j with h | h
  · exact key i j h
  · calc N i j = N j i := alt_symm hN i j
      _ = N' j i := key j i h
      _ = N' i j := (alt_symm hN' i j).symm

theorem clsCard_N_le {𝒩 : AddSubgroup M6} (halt : ∀ N ∈ 𝒩, IsAlt N)
    (h5 : ∀ N ∈ 𝒩, ∀ k : Fin 6, k ≠ 0 → N k 5 = 0)
    {μ v : Fin 4 → ZMod 2} (hμ : μ ≠ 0) (hc : ∀ N ∈ 𝒩, ClsCons μ v (clsBits N) (N 0 5)) :
    Nat.card 𝒩 ≤ 256 := by
  let f : 𝒩 → (Fin 4 → ZMod 2) × {y : (Fin 6 → ZMod 2) × ZMod 2 // ClsCons μ v y.1 y.2} :=
    fun N => ((clsEnc N.1).1, ⟨((clsEnc N.1).2.1, (clsEnc N.1).2.2), hc N.1 N.2⟩)
  have hf : Function.Injective f := by
    rintro ⟨N, hN⟩ ⟨N', hN'⟩ h
    have h1 : (clsEnc N).1 = (clsEnc N').1 := congrArg (fun x => x.1) h
    have h2 := congrArg (fun x => x.2.val) h
    have h2a : (clsEnc N).2.1 = (clsEnc N').2.1 := congrArg (fun x => x.1) h2
    have h2b : (clsEnc N).2.2 = (clsEnc N').2.2 := congrArg (fun x => x.2) h2
    exact Subtype.ext (clsEnc_inj (halt N hN) (halt N' hN') (h5 N hN) (h5 N' hN')
      (Prod.ext h1 (Prod.ext h2a h2b)))
  have hcard := Nat.card_le_card_of_injective f hf
  have h16 : Nat.card {y : (Fin 6 → ZMod 2) × ZMod 2 // ClsCons μ v y.1 y.2} ≤ 16 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact clsFC1 μ hμ v
  have h16' : Nat.card (Fin 4 → ZMod 2) = 16 := by
    simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, h16'] at hcard
  calc Nat.card 𝒩 ≤ 16 * Nat.card {y : (Fin 6 → ZMod 2) × ZMod 2 // ClsCons μ v y.1 y.2} := hcard
    _ ≤ 16 * 16 := Nat.mul_le_mul_left 16 h16
    _ = 256 := by norm_num

theorem clsCard_N_le_enc {𝒩 : AddSubgroup M6} (halt : ∀ N ∈ 𝒩, IsAlt N)
    (h5 : ∀ N ∈ 𝒩, ∀ k : Fin 6, k ≠ 0 → N k 5 = 0) : Nat.card 𝒩 ≤ 16 * 64 * 2 := by
  let f : 𝒩 → (Fin 4 → ZMod 2) × (Fin 6 → ZMod 2) × ZMod 2 := fun N => clsEnc N.1
  have hf : Function.Injective f := by
    rintro ⟨N, hN⟩ ⟨N', hN'⟩ h
    exact Subtype.ext (clsEnc_inj (halt N hN) (halt N' hN') (h5 N hN) (h5 N' hN') h)
  have hcard := Nat.card_le_card_of_injective f hf
  have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by simp [Nat.card_eq_fintype_card]
  have h64 : Nat.card (Fin 6 → ZMod 2) = 64 := by simp [Nat.card_eq_fintype_card]
  have h2 : Nat.card (ZMod 2) = 2 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, Nat.card_prod, h16, h64, h2] at hcard
  exact hcard

theorem clsCard_N_le_altV5 {𝒩 : AddSubgroup M6} (halt : ∀ N ∈ 𝒩, IsAlt N)
    (h5 : ∀ N ∈ 𝒩, ∀ k : Fin 6, k ≠ 0 → N k 5 = 0) (h0 : ∀ N ∈ 𝒩, N 0 5 = 0) :
    Nat.card 𝒩 ≤ 16 * 64 := by
  let f : 𝒩 → (Fin 4 → ZMod 2) × (Fin 6 → ZMod 2) := fun N => ((clsEnc N.1).1, (clsEnc N.1).2.1)
  have hf : Function.Injective f := by
    rintro ⟨N, hN⟩ ⟨N', hN'⟩ h
    have h1 : (clsEnc N).1 = (clsEnc N').1 := congrArg (fun x => x.1) h
    have h2 : (clsEnc N).2.1 = (clsEnc N').2.1 := congrArg (fun x => x.2) h
    have h3 : (clsEnc N).2.2 = (clsEnc N').2.2 := (h0 N hN).trans (h0 N' hN').symm
    exact Subtype.ext (clsEnc_inj (halt N hN) (halt N' hN') (h5 N hN) (h5 N' hN')
      (Prod.ext h1 (Prod.ext h2 h3)))
  have hcard := Nat.card_le_card_of_injective f hf
  have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by simp [Nat.card_eq_fintype_card]
  have h64 : Nat.card (Fin 6 → ZMod 2) = 64 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, h16, h64] at hcard
  exact hcard

@[expose] def clsPar (a : M6) : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) :=
  (fun l => a 0 (clsIx l), fun l => a (clsIx l) 5)

@[expose] def clsOmega : LinearMap.BilinForm (ZMod 2) ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => x.1 ⬝ᵥ y.2 + y.1 ⬝ᵥ x.2)
    (fun m₁ m₂ n => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun c m n => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
    (fun m n₁ n₂ => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun c m n => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)

theorem clsOmega_apply (x y : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :
    clsOmega x y = x.1 ⬝ᵥ y.2 + y.1 ⬝ᵥ x.2 := rfl

theorem clsOmega_nondeg : LinearMap.Nondegenerate clsOmega := by
  have key : ∀ x : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2), (∀ y, clsOmega x y = 0) → x = 0 := by
    intro x hx
    have h1 : x.1 = 0 := funext fun l => by
      have := hx (0, Pi.single l 1)
      simpa [clsOmega_apply, dotProduct_single] using this
    have h2 : x.2 = 0 := funext fun l => by
      have := hx (Pi.single l 1, 0)
      simpa [clsOmega_apply, single_dotProduct] using this
    exact Prod.ext h1 h2
  refine ⟨key, fun y hy => ?_⟩
  have := key y (fun x => by
    have := hy x
    rw [clsOmega_apply] at this ⊢
    rw [add_comm]
    exact this)
  exact this

theorem clsOmega_par {A B : M6} (hA : ClsShape A) (hB : ClsShape B) (hc : A * B = B * A) :
    clsOmega (clsPar A) (clsPar B) = 0 := by
  have h05 := congrFun (congrFun hc 0) 5
  rw [clsShape_mul_05 hA hB, clsShape_mul_05 hB hA] at h05
  have hS : A 0 1 * B 1 5 + A 0 2 * B 2 5 + A 0 3 * B 3 5 + A 0 4 * B 4 5 =
      B 0 1 * A 1 5 + B 0 2 * A 2 5 + B 0 3 * A 3 5 + B 0 4 * A 4 5 := by
    linear_combination h05
  rw [clsOmega_apply]
  simp only [clsPar, dotProduct, Fin.sum_univ_four, clsIx_zero, clsIx_one, clsIx_two, clsIx_three]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination hS + (B 0 1 * A 1 5 + B 0 2 * A 2 5 + B 0 3 * A 3 5 + B 0 4 * A 4 5) * h2

@[expose] def clsSub (𝒜 : Subgroup GL6) (hsh : ∀ A ∈ 𝒜, ClsShape (A : M6)) :
    Submodule (ZMod 2) ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) where
  carrier := {x | ∃ A ∈ 𝒜, clsPar (A : M6) = x}
  add_mem' := by
    rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    refine ⟨A * B, 𝒜.mul_mem hA hB, ?_⟩
    refine Prod.ext (funext fun l => ?_) (funext fun l => ?_)
    · show ((A * B : GL6) : M6) 0 (clsIx l) = (A : M6) 0 (clsIx l) + (B : M6) 0 (clsIx l)
      rw [Units.val_mul]
      exact clsShape_mul_0j (hsh A hA) (hsh B hB) (clsIx_ne_zero l) (clsIx_ne_five l)
    · show ((A * B : GL6) : M6) (clsIx l) 5 = (A : M6) (clsIx l) 5 + (B : M6) (clsIx l) 5
      rw [Units.val_mul]
      exact clsShape_mul_i5 (hsh A hA) (hsh B hB) (clsIx_ne_zero l) (clsIx_ne_five l)
  zero_mem' := by
    refine ⟨1, 𝒜.one_mem, Prod.ext (funext fun l => ?_) (funext fun l => ?_)⟩
    · show ((1 : GL6) : M6) 0 (clsIx l) = 0
      rw [Units.val_one, Matrix.one_apply_ne (clsIx_ne_zero l).symm]
    · show ((1 : GL6) : M6) (clsIx l) 5 = 0
      rw [Units.val_one, Matrix.one_apply_ne (clsIx_ne_five l)]
  smul_mem' := by
    rintro c _ ⟨A, hA, rfl⟩
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 from by decide) c with h | h <;> subst h
    · refine ⟨1, 𝒜.one_mem, ?_⟩
      rw [zero_smul]
      refine Prod.ext (funext fun l => ?_) (funext fun l => ?_)
      · show ((1 : GL6) : M6) 0 (clsIx l) = 0
        rw [Units.val_one, Matrix.one_apply_ne (clsIx_ne_zero l).symm]
      · show ((1 : GL6) : M6) (clsIx l) 5 = 0
        rw [Units.val_one, Matrix.one_apply_ne (clsIx_ne_five l)]
    · rw [one_smul]
      exact ⟨A, hA, rfl⟩

theorem clsCard_A (𝒜 : Subgroup GL6) (hsh : ∀ A ∈ 𝒜, ClsShape (A : M6))
    (hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A * B = B * A) : Nat.card 𝒜 ≤ 32 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hiso : clsSub 𝒜 hsh ≤ clsOmega.orthogonal (clsSub 𝒜 hsh) := by
    rintro x ⟨A, hA, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro y ⟨B, hB, rfl⟩
    have hc := congrArg Units.val (hcomm B hB A hA)
    rw [Units.val_mul, Units.val_mul] at hc
    exact clsOmega_par (hsh B hB) (hsh A hA) hc
  have hle : Module.finrank (ZMod 2) (clsSub 𝒜 hsh) ≤
      Module.finrank (ZMod 2) (clsOmega.orthogonal (clsSub 𝒜 hsh)) :=
    Submodule.finrank_mono hiso
  have hdim := LinearMap.BilinForm.finrank_orthogonal (K := ZMod 2) clsOmega_nondeg (clsSub 𝒜 hsh)
  have htot : Module.finrank (ZMod 2) ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) = 8 := by
    simp [Module.finrank_prod, Module.finrank_fin_fun]
  have hW4 : Module.finrank (ZMod 2) (clsSub 𝒜 hsh) ≤ 4 := by omega
  have hWcard : Nat.card (clsSub 𝒜 hsh) = 2 ^ Module.finrank (ZMod 2) (clsSub 𝒜 hsh) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simp [Nat.card_eq_fintype_card]
  let f : 𝒜 → clsSub 𝒜 hsh × ZMod 2 := fun A =>
    (⟨clsPar ((A.1 : GL6) : M6), ⟨A.1, A.2, rfl⟩⟩, ((A.1 : GL6) : M6) 0 5)
  have hf : Function.Injective f := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩ h
    have hpar : clsPar (A : M6) = clsPar (B : M6) := congrArg (fun x => x.1.val) h
    have h05 : (A : M6) 0 5 = (B : M6) 0 5 := congrArg (fun x => x.2) h
    have h0 : ∀ l : Fin 4, (A : M6) 0 (clsIx l) = (B : M6) 0 (clsIx l) :=
      fun l => congrFun (congrArg Prod.fst hpar) l
    have hi : ∀ l : Fin 4, (A : M6) (clsIx l) 5 = (B : M6) (clsIx l) 5 :=
      fun l => congrFun (congrArg Prod.snd hpar) l
    exact Subtype.ext (Units.ext (clsExt (hsh A hA) (hsh B hB) h0 hi h05))
  have hcardf := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hWcard] at hcardf
  have h2 : Nat.card (ZMod 2) = 2 := by simp [Nat.card_eq_fintype_card]
  rw [h2] at hcardf
  have hpow : 2 ^ Module.finrank (ZMod 2) (clsSub 𝒜 hsh) ≤ 2 ^ 4 :=
    Nat.pow_le_pow_right (by norm_num) hW4
  calc Nat.card 𝒜 ≤ 2 ^ Module.finrank (ZMod 2) (clsSub 𝒜 hsh) * 2 := hcardf
    _ ≤ 2 ^ 4 * 2 := Nat.mul_le_mul_right 2 hpow
    _ = 32 := by norm_num

theorem clsShape_eq_T {a : M6} (ha : ClsShape a) (h0 : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → a 0 j = 0) :
    a = 1 + Matrix.of fun i j => if j = 5 then (if i = 5 then 0 else a i 5) else 0 := by
  ext i j
  by_cases hj5 : j = 5
  · subst hj5
    by_cases hi5 : i = 5
    · subst hi5
      simp [clsShape_55 ha]
    · by_cases hi0 : i = 0
      · subst hi0
        simp [clsShape_00 ha]
      · simp [hi5, hi0]
  · by_cases hj0 : j = 0
    · subst hj0
      by_cases hi0 : i = 0
      · subst hi0
        simp [clsShape_00 ha]
      · simp [hi0, clsShape_col0 ha i, Matrix.one_apply]
    · by_cases hi0 : i = 0
      · subst hi0
        simp [h0 j hj0 hj5, hj5, Matrix.one_apply, Ne.symm hj0]
      · simp [ha.2 i j hi0 hj0 hj5, hj5, Matrix.one_apply]

theorem clsCard_T : Nat.card {v : Fin 6 → ZMod 2 // v 5 = 0} = 32 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem clsCard_altV5_le : Nat.card {N : M6 // InAltV5 N} ≤ 16 * 64 := by
  let f : {N : M6 // InAltV5 N} → (Fin 4 → ZMod 2) × (Fin 6 → ZMod 2) :=
    fun N => ((clsEnc N.1).1, (clsEnc N.1).2.1)
  have hf : Function.Injective f := by
    rintro ⟨N, hN⟩ ⟨N', hN'⟩ h
    have h1 : (clsEnc N).1 = (clsEnc N').1 := congrArg (fun x => x.1) h
    have h2 : (clsEnc N).2.1 = (clsEnc N').2.1 := congrArg (fun x => x.2) h
    have h3 : (clsEnc N).2.2 = (clsEnc N').2.2 := by
      show N 0 5 = N' 0 5
      rw [hN.2 0, hN'.2 0]
    apply Subtype.ext
    exact clsEnc_inj hN.1 hN'.1 (fun k _ => hN.2 k) (fun k _ => hN'.2 k)
      (Prod.ext h1 (Prod.ext h2 h3))
  have hcard := Nat.card_le_card_of_injective f hf
  have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by simp [Nat.card_eq_fintype_card]
  have h64 : Nat.card (Fin 6 → ZMod 2) = 64 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, h16, h64] at hcard
  exact hcard

theorem lemmaA (𝒜 : Subgroup GL6) (hUT : ∀ A ∈ 𝒜, IsUT (A : M6))
    (hsq : ∀ A ∈ 𝒜, A * A = 1) (hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A * B = B * A)
    (hτ : ∃ A ∈ 𝒜, (A : M6) = tau0M)
    (𝒩 : AddSubgroup M6) (halt : ∀ N ∈ 𝒩, IsAlt N)
    (hi : ∀ A ∈ 𝒜, ∀ N ∈ 𝒩, (A : M6) * N * (A : M6)ᵀ = N)
    (hii : ∀ A ∈ 𝒜, ∀ M : M6, IsAlt M → (A : M6) * M * (A : M6)ᵀ + M ∈ 𝒩)
    (hcard : 2 ^ 15 ≤ Nat.card 𝒜 * Nat.card 𝒩) :
    (∀ A : GL6, A ∈ 𝒜 ↔ InT (A : M6)) ∧ ∀ N : M6, N ∈ 𝒩 ↔ InAltV5 N := by
  clear hsq
  obtain ⟨A₀, hA₀, hA₀eq⟩ := hτ
  have hwedge : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → clsW j ∈ 𝒩 := by
    intro j hj0 hj5
    have h := hii A₀ hA₀ (clsW5 j) (clsW5_isAlt hj5)
    rw [hA₀eq, tau0_mul_clsW5 hj0 hj5] at h
    exact h
  have hsh : ∀ A ∈ 𝒜, ClsShape (A : M6) := fun A hA =>
    clsShape_of_wedge (hUT A hA) (fun j hj0 hj5 => hi A hA (clsW j) (hwedge j hj0 hj5))
  have hcol : ∀ N ∈ 𝒩, ∀ k : Fin 6, k ≠ 0 → N k 5 = 0 := fun N hN k hk => by
    have h := hi A₀ hA₀ N hN
    rw [hA₀eq] at h
    exact clsN_col5 h k hk
  have hcons : ∀ A ∈ 𝒜, ∀ N ∈ 𝒩, ClsCons (fun l => (A : M6) 0 (clsIx l))
      (fun i => (A : M6) (clsIx i) 5) (clsBits N) (N 0 5) :=
    fun A hA N hN => clsN_cons (hsh A hA) (halt N hN) (hcol N hN) (hi A hA N hN)
  have hcardA : Nat.card 𝒜 ≤ 32 := clsCard_A 𝒜 hsh hcomm
  have hmu : ∀ A ∈ 𝒜, ∀ l : Fin 4, (A : M6) 0 (clsIx l) = 0 := by
    intro A hA l
    by_contra hne
    have hμ : (fun l => (A : M6) 0 (clsIx l)) ≠ 0 := fun h0 => hne (congrFun h0 l)
    have h256 : Nat.card 𝒩 ≤ 256 :=
      clsCard_N_le halt hcol hμ (fun N hN => hcons A hA N hN)
    have h := le_trans hcard (Nat.mul_le_mul hcardA h256)
    norm_num at h
  have hTrow : ∀ A ∈ 𝒜, ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → (A : M6) 0 j = 0 := by
    intro A hA j hj0 hj5
    fin_cases j
    · exact absurd rfl hj0
    · exact hmu A hA 0
    · exact hmu A hA 1
    · exact hmu A hA 2
    · exact hmu A hA 3
    · exact absurd rfl hj5
  by_cases hcaseA : ∃ A ∈ 𝒜, ∃ i : Fin 4, (A : M6) (clsIx i) 5 ≠ 0
  · obtain ⟨A₁, hA₁, i₁, hv⟩ := hcaseA
    have hv1 : (A₁ : M6) (clsIx i₁) 5 = 1 := by
      have h01 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact h01 _ hv
    have hN05 : ∀ N ∈ 𝒩, N 0 5 = 0 := by
      intro N hN
      have h := clsN_row (hsh A₁ hA₁) (halt N hN) (hcol N hN) (hi A₁ hA₁ N hN)
        (clsIx_ne_zero i₁) (clsIx_ne_five i₁)
      simp only [hmu A₁ hA₁, mul_zero, Finset.sum_const_zero, zero_add, hv1, mul_one] at h
      exact h
    have hN1024 : Nat.card 𝒩 ≤ 16 * 64 := clsCard_N_le_altV5 halt hcol hN05
    have hA32 : Nat.card 𝒜 = 32 := by
      by_contra hne
      have hlt : Nat.card 𝒜 ≤ 31 := by omega
      have h := le_trans hcard (Nat.mul_le_mul hlt hN1024)
      norm_num at h
    have hN1024ge : 1024 ≤ Nat.card 𝒩 := by
      have h1 : 2 ^ 15 ≤ 32 * Nat.card 𝒩 := by rw [← hA32]; exact hcard
      norm_num at h1
      omega
    let g : 𝒜 → {v : Fin 6 → ZMod 2 // v 5 = 0} := fun A =>
      ⟨fun i => if i = 5 then 0 else ((A.1 : GL6) : M6) i 5, by simp⟩
    have hg : Function.Injective g := by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ h
      have hv : ∀ i : Fin 6, i ≠ 5 → (A : M6) i 5 = (B : M6) i 5 := by
        intro i hi5
        have : (if i = 5 then 0 else ((A : GL6) : M6) i 5) =
            (if i = 5 then 0 else ((B : GL6) : M6) i 5) :=
          congrFun (congrArg Subtype.val h) i
        simpa [hi5] using this
      exact Subtype.ext (Units.ext (clsExt (hsh A hA) (hsh B hB)
        (fun l => by rw [hmu A hA l, hmu B hB l])
        (fun l => hv _ (clsIx_ne_five l))
        (hv 0 (by decide))))
    have hgbij : Function.Bijective g := by
      rw [Nat.bijective_iff_injective_and_card]
      exact ⟨hg, by rw [hA32, clsCard_T]⟩
    have hmemT : ∀ A : GL6, A ∈ 𝒜 ↔ InT (A : M6) := by
      intro A
      constructor
      · intro hA
        exact ⟨fun i => if i = 5 then 0 else (A : M6) i 5, by simp,
          clsShape_eq_T (hsh A hA) (fun j hj0 hj5 => hTrow A hA j hj0 hj5)⟩
      · rintro ⟨v, hv5, hAv⟩
        obtain ⟨B, hB⟩ := hgbij.2 ⟨v, hv5⟩
        have hfun : (fun i => if i = 5 then 0 else ((B.1 : GL6) : M6) i 5) = v :=
          congrArg Subtype.val hB
        have hv_i : ∀ i : Fin 6, (if i = 5 then 0 else ((B.1 : GL6) : M6) i 5) = v i :=
          fun i => congrFun hfun i
        have hBv : ((B.1 : GL6) : M6) = (A : M6) := by
          have key := clsShape_eq_T (hsh B.1 B.2) (fun j hj0 hj5 => hTrow B.1 B.2 j hj0 hj5)
          rw [key, hAv]
          congr 1
          ext i j
          simp only [Matrix.of_apply, hv_i]
        exact (Units.ext hBv) ▸ B.2
    have hsub : ((𝒩 : AddSubgroup M6) : Set M6) ⊆ {N : M6 | InAltV5 N} := fun N hN =>
      ⟨halt N hN, fun i => by
        by_cases hi0 : i = 0
        · subst hi0
          exact hN05 N hN
        · exact hcol N hN i hi0⟩
    have heq : ((𝒩 : AddSubgroup M6) : Set M6) = {N : M6 | InAltV5 N} := by
      apply Set.eq_of_subset_of_ncard_le hsub
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      have h1 : Nat.card ↥({N : M6 | InAltV5 N} : Set M6) ≤ 16 * 64 := clsCard_altV5_le
      have h2 : 1024 ≤ Nat.card ↥((𝒩 : AddSubgroup M6) : Set M6) := hN1024ge
      omega
    refine ⟨hmemT, fun N => ?_⟩
    exact Set.ext_iff.mp heq N
  · push Not at hcaseA
    have hA2 : Nat.card 𝒜 ≤ 2 := by
      let g : 𝒜 → ZMod 2 := fun A => ((A.1 : GL6) : M6) 0 5
      have hg : Function.Injective g := by
        rintro ⟨A, hA⟩ ⟨B, hB⟩ h
        have hAB : (A : M6) = (B : M6) := clsExt (hsh A hA) (hsh B hB)
          (fun l => by rw [hmu A hA l, hmu B hB l])
          (fun l => by rw [hcaseA A hA l, hcaseA B hB l]) h
        exact Subtype.ext (Units.ext hAB)
      have h2 := Nat.card_le_card_of_injective g hg
      have hz : Nat.card (ZMod 2) = 2 := by simp [Nat.card_eq_fintype_card]
      rw [hz] at h2
      exact h2
    have hN2048 := clsCard_N_le_enc halt hcol
    have h := le_trans hcard (Nat.mul_le_mul hA2 hN2048)
    norm_num at h

end CFSG.GF2Type.SmithTypeE.E7
