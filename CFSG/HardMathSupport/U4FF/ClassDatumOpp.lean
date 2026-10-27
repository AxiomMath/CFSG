module

public import CFSG.HardMathSupport.U4FF.ClassDatumNorm

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)

namespace Datum

section Jconj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def Jconj (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (S : Subgroup (G4 K n)) :
    Subgroup (G4 K n) :=
  S.map (MulAut.conj (jSU K n)).toMonoidHom

theorem mem_Jconj {S : Subgroup (G4 K n)} {y : G4 K n} :
    y ∈ Jconj K n S ↔ jSU K n * y * jSU K n ∈ S := by
  have hJ := jSU_mul_self (K := K) (n := n)
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : jSU K n * (MulAut.conj (jSU K n)).toMonoidHom x * jSU K n = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, jSU_inv]
      calc jSU K n * (jSU K n * x * jSU K n) * jSU K n
          = (jSU K n * jSU K n) * x * (jSU K n * jSU K n) := by group
        _ = x := by rw [hJ, one_mul, mul_one]
    rw [this]
    exact hx
  · intro h
    refine ⟨jSU K n * y * jSU K n, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, jSU_inv]
    calc jSU K n * (jSU K n * y * jSU K n) * jSU K n
        = (jSU K n * jSU K n) * y * (jSU K n * jSU K n) := by group
      _ = y := by rw [hJ, one_mul, mul_one]

theorem jconj_jconj (g : G4 K n) : jSU K n * (jSU K n * g * jSU K n) * jSU K n = g := by
  calc jSU K n * (jSU K n * g * jSU K n) * jSU K n
      = (jSU K n * jSU K n) * g * (jSU K n * jSU K n) := by group
    _ = g := by rw [jSU_mul_self, one_mul, mul_one]

theorem Jconj_le_L {S : Subgroup (G4 K n)} (hS : S ≤ UpperU K n) : Jconj K n S ≤ LowerU K n := by
  intro y hy
  have h := hS (mem_Jconj.mp hy)
  refine mem_LowerU_of_conj_mem_UpperU ?_
  rw [jSU_inv]
  exact h

theorem jSU_comm_nHom (w : WB) : jSU K n * nHom K n w = nHom K n w * jSU K n := by
  apply eq_of_gm_eq
  rw [gm_mul, gm_mul, gm_nHom, gm_jSU, antidiag_eq_pmat, pmat_mul, pmat_mul]
  congr 1
  ext i
  simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply]
  exact congrArg Fin.val (permOf_comm_rev w i).symm

theorem jconj_mem_U {l : G4 K n} (hl : l ∈ LowerU K n) : jSU K n * l * jSU K n ∈ UpperU K n := by
  have := conj_mem_UpperU_of_mem_LowerU hl
  rwa [jSU_inv] at this

theorem gm_entry_via_J (y : G4 K n) (a b : Fin 4) :
    gm y a b = gm (jSU K n * y * jSU K n) (Fin.rev a) (Fin.rev b) := by
  rw [gm_jconj, Fin.rev_rev, Fin.rev_rev]

theorem conj_comm_J {m : G4 K n} (hJm : jSU K n * m = m * jSU K n) (q : G4 K n) :
    jSU K n * (m * q * m⁻¹) * jSU K n = m * (jSU K n * q * jSU K n) * m⁻¹ := by
  have h1 : jSU K n * m = m * jSU K n := hJm
  have h2 : m⁻¹ * jSU K n = jSU K n * m⁻¹ := by
    have := (Commute.inv_right (show Commute (jSU K n) m from h1)).eq
    exact this.symm
  calc jSU K n * (m * q * m⁻¹) * jSU K n
      = (jSU K n * m) * q * (m⁻¹ * jSU K n) := by group
    _ = (m * jSU K n) * q * (jSU K n * m⁻¹) := by rw [h1, h2]
    _ = m * (jSU K n * q * jSU K n) * m⁻¹ := by group

end Jconj

section YQ

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem L_le_Jconj_sup {X Us : Subgroup (G4 K n)}
    (hU : ∀ u ∈ UpperU K n, ∃ x ∈ X, ∃ v ∈ Us, u = x * v) :
    LowerU K n ≤ Jconj K n X ⊔ Jconj K n Us := by
  intro l hl
  obtain ⟨x, hx, v, hv, e⟩ := hU _ (jconj_mem_U hl)
  have hl' : l = (jSU K n * x * jSU K n) * (jSU K n * v * jSU K n) := by
    calc l = jSU K n * (jSU K n * l * jSU K n) * jSU K n := (jconj_jconj l).symm
      _ = jSU K n * (x * v) * jSU K n := by rw [← e]
      _ = (jSU K n * x * jSU K n) * (jSU K n * v * jSU K n) := by
        calc jSU K n * (x * v) * jSU K n
            = jSU K n * x * (jSU K n * jSU K n) * v * jSU K n := by rw [jSU_mul_self]; group
          _ = _ := by group
  rw [hl']
  refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
  · rw [mem_Jconj, jconj_jconj]
    exact hx
  · rw [mem_Jconj, jconj_jconj]
    exact hv

theorem X_normJconj {X Us : Subgroup (G4 K n)} {m : G4 K n}
    (hA : ∀ x ∈ X, ∀ v ∈ Us, x * v * x⁻¹ ∈ Us)
    (hC : ∀ v ∈ Us, m * v * m⁻¹ ∈ Us) (hC' : ∀ v ∈ Us, m⁻¹ * v * m ∈ Us)
    (hY : ∀ y ∈ Jconj K n X, m * y * m⁻¹ ∈ X) :
    ∀ x ∈ X, ∀ q ∈ Jconj K n Us, x * q * x⁻¹ ∈ Jconj K n Us := by
  intro x hx q hq
  rw [mem_Jconj] at hq ⊢
  have hy : jSU K n * x * jSU K n ∈ Jconj K n X := by
    rw [mem_Jconj, jconj_jconj]
    exact hx
  set y := jSU K n * x * jSU K n with hydef
  have hx' := hY y hy
  have hyq : jSU K n * (x * q * x⁻¹) * jSU K n = y * (jSU K n * q * jSU K n) * y⁻¹ := by
    rw [hydef]
    have hJ := jSU_mul_self (K := K) (n := n)
    calc jSU K n * (x * q * x⁻¹) * jSU K n
        = jSU K n * x * (jSU K n * jSU K n) * q * (jSU K n * jSU K n) * x⁻¹ * jSU K n := by
          rw [hJ]; group
      _ = _ := by
          simp only [_root_.mul_inv_rev, inv_inv, jSU_inv]
          group
  rw [hyq]
  have e : y = m⁻¹ * (m * y * m⁻¹) * m := by group
  rw [e]
  have h1 := hC _ hq
  have h2 := hA _ hx' _ h1
  have h3 := hC' _ h2
  convert h3 using 1
  group

theorem Jconj_normJconj {X Us : Subgroup (G4 K n)}
    (hA : ∀ x ∈ X, ∀ v ∈ Us, x * v * x⁻¹ ∈ Us) :
    ∀ y ∈ Jconj K n X, ∀ q ∈ Jconj K n Us, y * q * y⁻¹ ∈ Jconj K n Us := by
  intro y hy q hq
  rw [mem_Jconj] at hy hq ⊢
  have hJ := jSU_mul_self (K := K) (n := n)
  have e : jSU K n * (y * q * y⁻¹) * jSU K n =
      (jSU K n * y * jSU K n) * (jSU K n * q * jSU K n) * (jSU K n * y * jSU K n)⁻¹ := by
    simp only [_root_.mul_inv_rev, inv_inv, jSU_inv]
    calc jSU K n * (y * q * y⁻¹) * jSU K n
        = jSU K n * y * (jSU K n * jSU K n) * q * (jSU K n * jSU K n) * y⁻¹ * jSU K n := by
          rw [hJ]; group
      _ = _ := by group
  rw [e]
  exact hA _ hy _ hq

theorem n_normJconj {Us : Subgroup (G4 K n)} {m : G4 K n}
    (hJm : jSU K n * m = m * jSU K n) (hC : ∀ v ∈ Us, m * v * m⁻¹ ∈ Us) :
    ∀ q ∈ Jconj K n Us, m * q * m⁻¹ ∈ Jconj K n Us := by
  intro q hq
  rw [mem_Jconj] at hq ⊢
  rw [conj_comm_J hJm]
  exact hC _ hq

theorem n_conjX_of {X : Subgroup (G4 K n)} {m : G4 K n}
    (hJm : jSU K n * m = m * jSU K n) (hY : ∀ y ∈ Jconj K n X, m * y * m⁻¹ ∈ X) :
    ∀ x ∈ X, m * x * m⁻¹ ∈ Jconj K n X := by
  intro x hx
  rw [mem_Jconj, conj_comm_J hJm]
  apply hY
  rw [mem_Jconj, jconj_jconj]
  exact hx

theorem H_normJconj {Us : Subgroup (G4 K n)}
    (hH : ∀ h ∈ Hd K n, ∀ v ∈ Us, h * v * h⁻¹ ∈ Us) :
    ∀ h ∈ Hd K n, ∀ q ∈ Jconj K n Us, h * q * h⁻¹ ∈ Jconj K n Us := by
  intro h hh q hq
  rw [mem_Jconj] at hq ⊢
  have hJ := jSU_mul_self (K := K) (n := n)
  have e : jSU K n * (h * q * h⁻¹) * jSU K n =
      (jSU K n * h * jSU K n) * (jSU K n * q * jSU K n) * (jSU K n * h * jSU K n)⁻¹ := by
    simp only [_root_.mul_inv_rev, inv_inv, jSU_inv]
    calc jSU K n * (h * q * h⁻¹) * jSU K n
        = jSU K n * h * (jSU K n * jSU K n) * q * (jSU K n * jSU K n) * h⁻¹ * jSU K n := by
          rw [hJ]; group
      _ = _ := by group
  rw [e]
  exact hH _ (jconj_mem_Hd hh) _ hq

end YQ

section Families

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def Xs (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Fin 2 → Subgroup (G4 K n)
  | 0 => X0 K n
  | 1 => X1 K n

@[expose] def Uss (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    Fin 2 → Subgroup (G4 K n)
  | 0 => Us0 K n
  | 1 => Us1 K n

@[expose] noncomputable def nSimple (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ)
    (s : Fin 2) : G4 K n :=
  nHom K n (csB.simple s)

end Families

section ConjY

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem n0_conjY0 (hK : Nat.card K = (2 ^ n) ^ 2) {y : G4 K n} (hy : y ∈ Jconj K n (X0 K n)) :
    nHom K n s0 * y * (nHom K n s0)⁻¹ ∈ X0 K n := by
  obtain ⟨c, hc⟩ := mem_X0.mp (mem_Jconj.mp hy)
  refine mem_X0.mpr ⟨c ^ 2 ^ n, ?_⟩
  ext i j
  rw [gm_conj_s0, gm_entry_via_J, hc]
  fin_cases i <;> fin_cases j <;>
    simp [x0Mat, pA_zero, pA_one, pA_two, pA_three, rev0, rev1, rev2, rev3, pow_pow_of_card hK]

theorem n1_conjY1 {y : G4 K n} (hy : y ∈ Jconj K n (X1 K n)) :
    nHom K n s1 * y * (nHom K n s1)⁻¹ ∈ X1 K n := by
  obtain ⟨c, hcq, hc⟩ := mem_X1.mp (mem_Jconj.mp hy)
  refine mem_X1.mpr ⟨c, hcq, ?_⟩
  ext i j
  rw [gm_conj_s1, gm_entry_via_J, hc]
  fin_cases i <;> fin_cases j <;>
    simp [x1Mat, pB_zero, pB_one, pB_two, pB_three, rev0, rev1, rev2, rev3]

end ConjY

section NWConj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem x0Mat_apply_of_ne (c : K) (a b : Fin 4) (hab : a ≠ b) (h1 : ¬(a = 0 ∧ b = 1))
    (h2 : ¬(a = 2 ∧ b = 3)) : x0Mat n c a b = 0 := by
  revert hab h1 h2
  fin_cases a <;> fin_cases b <;> simp [x0Mat]

theorem x1Mat_apply_of_ne (c : K) (a b : Fin 4) (hab : a ≠ b) (h1 : ¬(a = 1 ∧ b = 2)) :
    x1Mat c a b = 0 := by
  revert hab h1
  fin_cases a <;> fin_cases b <;> simp [x1Mat]

theorem x0Mat_diag (c : K) (a : Fin 4) : x0Mat n c a a = 1 := by
  fin_cases a <;> simp [x0Mat]

theorem x1Mat_diag (c : K) (a : Fin 4) : x1Mat c a a = 1 := by
  fin_cases a <;> simp [x1Mat]

theorem inv_lt_supp0 : ∀ t : Fin 8, permInvLt 0 (permTab t) →
    ∀ i k : Fin 4, k < i →
      ¬(permTab t i = 0 ∧ permTab t k = 1) ∧ ¬(permTab t i = 2 ∧ permTab t k = 3) := by
  decide

theorem inv_lt_supp1 : ∀ t : Fin 8, permInvLt 1 (permTab t) →
    ∀ i k : Fin 4, k < i → ¬(permTab t i = 1 ∧ permTab t k = 2) := by
  decide

theorem nW_conj0 (w : WB) (hw : permInvLt 0 (permOf w)) {x : G4 K n} (hx : x ∈ X0 K n) :
    (nHom K n w)⁻¹ * x * nHom K n w ∈ UpperU K n := by
  obtain ⟨c, hc⟩ := mem_X0.mp hx
  obtain ⟨t, rfl⟩ := exists_wTab w
  rw [permOf_wTab] at hw
  have hs := inv_lt_supp0 t hw
  refine mem_UpperU'.mpr ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [gm_nHom_conj_inv, hc, permOf_wTab]
    have hne : permTab t i ≠ permTab t j := fun h => (ne_of_gt hji) ((permTab t).injective h)
    exact x0Mat_apply_of_ne c _ _ hne (hs i j hji).1 (hs i j hji).2
  · rw [gm_nHom_conj_inv, hc]
    exact x0Mat_diag c _

theorem nW_conj1 (w : WB) (hw : permInvLt 1 (permOf w)) {x : G4 K n} (hx : x ∈ X1 K n) :
    (nHom K n w)⁻¹ * x * nHom K n w ∈ UpperU K n := by
  obtain ⟨c, -, hc⟩ := mem_X1.mp hx
  obtain ⟨t, rfl⟩ := exists_wTab w
  rw [permOf_wTab] at hw
  have hs := inv_lt_supp1 t hw
  refine mem_UpperU'.mpr ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [gm_nHom_conj_inv, hc, permOf_wTab]
    have hne : permTab t i ≠ permTab t j := fun h => (ne_of_gt hji) ((permTab t).injective h)
    exact x1Mat_apply_of_ne c _ _ hne (hs i j hji)
  · rw [gm_nHom_conj_inv, hc]
    exact x1Mat_diag c _

theorem nW_conj_all (w : WB) (s : Fin 2)
    (h : csB.length (csB.simple s * w) = csB.length w + 1) :
    ∀ x ∈ Xs K n s, (nHom K n w)⁻¹ * x * nHom K n w ∈ UpperU K n := by
  have hp := (length_simple_mul_iff s w).mp h
  fin_cases s
  · exact fun x hx => nW_conj0 w (by simpa using hp) hx
  · exact fun x hx => nW_conj1 w (by simpa using hp) hx

end NWConj

end Datum

end CFSG.HardMathSupport.U4FF
