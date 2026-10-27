module

public import CFSG.CGT.Stroth77.Extension22FourClassify

public section

namespace CFSG.CGT.Stroth77

open scoped IsMulCommutative

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

@[expose] noncomputable def conjByMulEquiv {H : Subgroup S} {g : S}
    (hg : g ∈ Subgroup.normalizer H) : H ≃* H where
  toFun := conjBy hg
  invFun := conjBy (Subgroup.inv_mem _ hg)
  left_inv x := conjBy_inv_conjBy hg x
  right_inv x := by
    apply Subtype.ext
    simp only [conjBy_val, inv_inv, Subgroup.coe_mk]
    group
  map_mul' := conjBy_mul hg

@[expose] noncomputable def conjByAddEquiv {H : Subgroup S} {g : S}
    (hg : g ∈ Subgroup.normalizer H) : Additive H ≃+ Additive H :=
  MulEquiv.toAdditive (conjByMulEquiv hg)

@[simp]
theorem conjByAddEquiv_apply {H : Subgroup S} {g : S}
    (hg : g ∈ Subgroup.normalizer H) (x : Additive H) :
    conjByAddEquiv hg x = Additive.ofMul (conjBy hg (Additive.toMul x)) := rfl

@[expose] noncomputable def conjTorusFour
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {e f : C} (E : TorusBasisEquivFour D hBC e f) {g : S}
    (hg : g ∈ Subgroup.normalizer C) : Torus (Type200.k m) ≃+ Torus (Type200.k m) :=
  E.E.trans ((conjByAddEquiv hg).trans E.E.symm)

@[simp]
theorem conjTorusFour_apply
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {e f : C} (E : TorusBasisEquivFour D hBC e f) {g : S}
    (hg : g ∈ Subgroup.normalizer C) (x : Torus (Type200.k m)) :
    conjTorusFour D hBC E hg x =
      E.E.symm (Additive.ofMul (conjBy hg (Additive.toMul (E.E x)))) := rfl


@[expose] noncomputable def doubleGens (m : ℕ) : (i : Fin 3) → Torus (Type200.k m) :=
  ![gen (Type200.k m) 0, (2 : ℕ) • gen (Type200.k m) 1,
    (2 : ℕ) • gen (Type200.k m) 2]

theorem doubleGens_smul (m : ℕ) (i : Fin 3) :
    (2 ^ Type100.k m i) • doubleGens m i = 0 := by
  fin_cases i
  · have h := addOrderOf_nsmul_eq_zero (gen (Type200.k m) 0)
    rw [addOrderOf_gen] at h
    simpa [doubleGens, Type100.k, Type200.k] using h
  · have h := addOrderOf_nsmul_eq_zero (gen (Type200.k m) 1)
    rw [addOrderOf_gen] at h
    change (2 ^ (m + 1)) • ((2 : ℕ) • gen (Type200.k m) 1) = 0
    calc 2 ^ (m + 1) • ((2 : ℕ) • gen (Type200.k m) 1)
        = (2 ^ (m + 1) * 2) • gen (Type200.k m) 1 := by rw [smul_smul]
      _ = 2 ^ (m + 2) • gen (Type200.k m) 1 := by
          rw [show (2 : ℕ) ^ (m + 1) * 2 = 2 ^ (m + 2) by ring]
      _ = 0 := h
  · have h := addOrderOf_nsmul_eq_zero (gen (Type200.k m) 2)
    rw [addOrderOf_gen] at h
    change (2 ^ (m + 1)) • ((2 : ℕ) • gen (Type200.k m) 2) = 0
    calc 2 ^ (m + 1) • ((2 : ℕ) • gen (Type200.k m) 2)
        = (2 ^ (m + 1) * 2) • gen (Type200.k m) 2 := by rw [smul_smul]
      _ = 2 ^ (m + 2) • gen (Type200.k m) 2 := by
          rw [show (2 : ℕ) ^ (m + 1) * 2 = 2 ^ (m + 2) by ring]
      _ = 0 := h

@[expose] noncomputable def doubleHom (m : ℕ) :
    Torus (Type100.k m) →+ Torus (Type200.k m) :=
  torusHomOfGens (Type100.k m) (doubleGens m) (doubleGens_smul m)

@[simp]
theorem doubleHom_gen (m : ℕ) (j : Fin 3) :
    doubleHom m (gen (Type100.k m) j) = doubleGens m j := by
  have h := torusHomOfGens_gen (k := Type100.k m) (x := doubleGens m)
    (hx := doubleGens_smul m) j
  simpa [doubleHom] using h

theorem doubleHom_gen_zero (m : ℕ) :
    doubleHom m (gen (Type100.k m) 0) = gen (Type200.k m) 0 := by
  simpa [doubleGens] using doubleHom_gen m 0

theorem doubleHom_gen_one (m : ℕ) :
    doubleHom m (gen (Type100.k m) 1) = (2 : ℕ) • gen (Type200.k m) 1 := by
  simpa [doubleGens] using doubleHom_gen m 1

theorem doubleHom_gen_two (m : ℕ) :
    doubleHom m (gen (Type100.k m) 2) = (2 : ℕ) • gen (Type200.k m) 2 := by
  simpa [doubleGens] using doubleHom_gen m 2


namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

theorem symm_a (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) :
    E.E.symm (Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C)) =
      (2 : ℤ) • gen (Type200.k m) 1 := by
  have h : Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C) =
      E.E ((2 : ℤ) • gen (Type200.k m) 1) := by
    rw [map_zsmul, E.E_gen1]
    show Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C) = (2 : ℤ) • Additive.ofMul e
    rw [two_zsmul, ← ofMul_mul, he]
  rw [h, AddEquiv.symm_apply_apply]

theorem symm_b (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) :
    E.E.symm (Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C)) =
      (2 : ℤ) • gen (Type200.k m) 2 := by
  have h : Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C) =
      E.E ((2 : ℤ) • gen (Type200.k m) 2) := by
    rw [map_zsmul, E.E_gen2]
    show Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C) = (2 : ℤ) • Additive.ofMul f
    rw [two_zsmul, ← ofMul_mul, hf]
  rw [h, AddEquiv.symm_apply_apply]

theorem symm_c (E : TorusBasisEquivFour D hBC e f) :
    E.E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = gen (Type200.k m) 0 := by
  rw [← E.E_gen0, AddEquiv.symm_apply_apply]

theorem symm_inclusion (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (β : B) {i j l : ℤ}
    (hβ : D.ec β = i • gen (StrothTypeIndex.t100 m).k 0 +
      j • gen (StrothTypeIndex.t100 m).k 1 +
      l • gen (StrothTypeIndex.t100 m).k 2) :
    E.E.symm (Additive.ofMul (⟨β, hBC β.2⟩ : C)) =
      i • gen (Type200.k m) 0 + (j * 2) • gen (Type200.k m) 1 +
        (l * 2) • gen (Type200.k m) 2 := by
  have hβ' : β = D.c ^ i * D.a ^ j * D.b ^ l := eq_c_zpow_mul_a_b D hβ
  have hci : ∀ n : ℤ,
      E.E.symm (Additive.ofMul (⟨D.c ^ n, hBC (D.c ^ n).2⟩ : C)) =
        n • gen (Type200.k m) 0 := by
    intro n
    have hsub : (⟨D.c ^ n, hBC (D.c ^ n).2⟩ : C) =
        (⟨D.c, hBC D.c.2⟩ : C) ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, symm_c E]
  have hai : ∀ n : ℤ,
      E.E.symm (Additive.ofMul (⟨D.a ^ n, hBC (D.a ^ n).2⟩ : C)) =
        (n * 2) • gen (Type200.k m) 1 := by
    intro n
    have hsub : (⟨D.a ^ n, hBC (D.a ^ n).2⟩ : C) =
        (⟨D.a, hBC D.a.2⟩ : C) ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, symm_a he E, smul_smul]
  have hbi : ∀ n : ℤ,
      E.E.symm (Additive.ofMul (⟨D.b ^ n, hBC (D.b ^ n).2⟩ : C)) =
        (n * 2) • gen (Type200.k m) 2 := by
    intro n
    have hsub : (⟨D.b ^ n, hBC (D.b ^ n).2⟩ : C) =
        (⟨D.b, hBC D.b.2⟩ : C) ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, symm_b hf E, smul_smul]
  have hprod : (⟨β, hBC β.2⟩ : C) =
      (⟨D.c ^ i, hBC (D.c ^ i).2⟩ : C) *
        (⟨D.a ^ j, hBC (D.a ^ j).2⟩ : C) *
        (⟨D.b ^ l, hBC (D.b ^ l).2⟩ : C) := by
    apply Subtype.ext
    simp [hβ']
  rw [hprod]
  rw [show Additive.ofMul ((⟨D.c ^ i, hBC (D.c ^ i).2⟩ : C) *
      (⟨D.a ^ j, hBC (D.a ^ j).2⟩ : C) *
      (⟨D.b ^ l, hBC (D.b ^ l).2⟩ : C)) =
      Additive.ofMul ⟨D.c ^ i, hBC (D.c ^ i).2⟩ +
        Additive.ofMul ⟨D.a ^ j, hBC (D.a ^ j).2⟩ +
        Additive.ofMul ⟨D.b ^ l, hBC (D.b ^ l).2⟩ by
    rw [ofMul_mul, ofMul_mul, add_assoc]]
  rw [map_add, map_add, hci, hai, hbi]

end TorusBasisEquivFour


theorem doubleHom_gen_one_int (m : ℕ) :
    doubleHom m (gen (Type100.k m) 1) = (2 : ℤ) • gen (Type200.k m) 1 := by
  rw [doubleHom_gen_one, two_nsmul, two_zsmul]

theorem doubleHom_gen_two_int (m : ℕ) :
    doubleHom m (gen (Type100.k m) 2) = (2 : ℤ) • gen (Type200.k m) 2 := by
  rw [doubleHom_gen_two, two_nsmul, two_zsmul]

theorem doubleHom_lin (m : ℕ) (i j l : ℤ) :
    doubleHom m (i • gen (Type100.k m) 0 + j • gen (Type100.k m) 1 +
        l • gen (Type100.k m) 2) =
      i • gen (Type200.k m) 0 + (j * 2) • gen (Type200.k m) 1 +
        (l * 2) • gen (Type200.k m) 2 := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
    doubleHom_gen_zero, doubleHom_gen_one_int, doubleHom_gen_two_int, smul_smul, smul_smul]

theorem doubleHom_uv_gen (m : ℕ) (j : Fin 3) :
    doubleHom m ((Type100.action m).φuv (gen (Type100.k m) j)) =
      (Type200.action m).φuv (doubleHom m (gen (Type100.k m) j)) := by
  fin_cases j
  · change doubleHom m ((Type100.action m).φuv (gen (Type100.k m) 0)) =
      (Type200.action m).φuv (doubleHom m (gen (Type100.k m) 0))
    rw [show gen (Type100.k m) 0 = Torus.c from rfl, Type100.uv_c,
      doubleHom_gen_zero,
      show (Type200.action m).φuv (gen (Type200.k m) 0) =
        (Type200.action m).φuv Torus.c from rfl, Type200.uv_c, doubleHom_lin]
    module
  · change doubleHom m ((Type100.action m).φuv (gen (Type100.k m) 1)) =
      (Type200.action m).φuv (doubleHom m (gen (Type100.k m) 1))
    rw [show gen (Type100.k m) 1 = Torus.a from rfl, Type100.uv_a,
      doubleHom_gen_one_int,
      show (Type200.action m).φuv ((2 : ℤ) • gen (Type200.k m) 1) =
        (2 : ℤ) • (Type200.action m).φuv Torus.a from by
        rw [map_zsmul],
      Type200.uv_a, doubleHom_lin, smul_add, smul_add]
    module
  · change doubleHom m ((Type100.action m).φuv (gen (Type100.k m) 2)) =
      (Type200.action m).φuv (doubleHom m (gen (Type100.k m) 2))
    rw [show gen (Type100.k m) 2 = Torus.b from rfl, Type100.uv_b,
      doubleHom_gen_two_int,
      show (Type200.action m).φuv ((2 : ℤ) • gen (Type200.k m) 2) =
        (2 : ℤ) • (Type200.action m).φuv Torus.b from by
        rw [map_zsmul],
      Type200.uv_b, doubleHom_lin, smul_add, smul_add]
    module

theorem doubleHom_uv (m : ℕ) (x : Torus (Type100.k m)) :
    doubleHom m ((Type100.action m).φuv x) =
      (Type200.action m).φuv (doubleHom m x) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type100.k m) x
  simp only [map_add, map_zsmul, doubleHom_uv_gen]


theorem doubleHom_t_gen (m : ℕ) (j : Fin 3) :
    doubleHom m ((Type100.action m).φt (gen (Type100.k m) j)) =
      (Type200.action m).φt (doubleHom m (gen (Type100.k m) j)) := by
  fin_cases j
  · change doubleHom m ((Type100.action m).φt (gen (Type100.k m) 0)) =
      (Type200.action m).φt (doubleHom m (gen (Type100.k m) 0))
    rw [doubleHom_gen_zero,
      show gen (Type100.k m) 0 = Torus.c from rfl, Type100.t_c,
      show (Type200.action m).φt (gen (Type200.k m) 0) =
        (Type200.action m).φt Torus.c from rfl, Type200.t_c]
    simp only [map_add, map_zsmul, doubleHom_gen_zero, doubleHom_gen_one_int,
      doubleHom_gen_two_int, smul_add, smul_smul, zero_smul, add_zero, zero_add]
    module
  · change doubleHom m ((Type100.action m).φt (gen (Type100.k m) 1)) =
      (Type200.action m).φt (doubleHom m (gen (Type100.k m) 1))
    rw [doubleHom_gen_one_int,
      show gen (Type100.k m) 1 = Torus.a from rfl, Type100.t_a,
      show (Type200.action m).φt ((2 : ℤ) • gen (Type200.k m) 1) =
        (2 : ℤ) • (Type200.action m).φt Torus.a from by
        rw [map_zsmul],
      Type200.t_a]
    simp only [map_add, map_zsmul, doubleHom_gen_zero, doubleHom_gen_one_int,
      doubleHom_gen_two_int, smul_add, smul_smul, zero_smul, add_zero, zero_add]
    module
  · change doubleHom m ((Type100.action m).φt (gen (Type100.k m) 2)) =
      (Type200.action m).φt (doubleHom m (gen (Type100.k m) 2))
    rw [doubleHom_gen_two_int,
      show gen (Type100.k m) 2 = Torus.b from rfl, Type100.t_b,
      show (Type200.action m).φt ((2 : ℤ) • gen (Type200.k m) 2) =
        (2 : ℤ) • (Type200.action m).φt Torus.b from by
        rw [map_zsmul],
      Type200.t_b]
    simp only [map_add, map_zsmul, doubleHom_gen_zero, doubleHom_gen_one_int,
      doubleHom_gen_two_int, smul_add, smul_smul, zero_smul, add_zero, zero_add]
    module

theorem doubleHom_t (m : ℕ) (x : Torus (Type100.k m)) :
    doubleHom m ((Type100.action m).φt x) =
      (Type200.action m).φt (doubleHom m x) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type100.k m) x
  simp only [map_add, map_zsmul, doubleHom_t_gen]

theorem doubleHom_u_gen (m : ℕ) (j : Fin 3) :
    doubleHom m ((Type100.action m).φu (gen (Type100.k m) j)) =
      (Type200.action m).φu (doubleHom m (gen (Type100.k m) j)) := by
  fin_cases j
  · change doubleHom m ((Type100.action m).φu (gen (Type100.k m) 0)) =
      (Type200.action m).φu (doubleHom m (gen (Type100.k m) 0))
    rw [doubleHom_gen_zero,
      show gen (Type100.k m) 0 = Torus.c from rfl, Type100.u_c,
      show (Type200.action m).φu (gen (Type200.k m) 0) =
        (Type200.action m).φu Torus.c from rfl, Type200.u_c]
    simp only [map_add, map_zsmul, doubleHom_gen_zero, doubleHom_gen_one_int,
      doubleHom_gen_two_int, smul_add, smul_smul, zero_smul, add_zero, zero_add]
  · change doubleHom m ((Type100.action m).φu (gen (Type100.k m) 1)) =
      (Type200.action m).φu (doubleHom m (gen (Type100.k m) 1))
    rw [doubleHom_gen_one_int,
      show gen (Type100.k m) 1 = Torus.a from rfl, Type100.u_a,
      show (Type200.action m).φu ((2 : ℤ) • gen (Type200.k m) 1) =
        (2 : ℤ) • (Type200.action m).φu Torus.a from by
        rw [map_zsmul],
      Type200.u_a]
    simp only [map_add, map_zsmul, doubleHom_gen_zero, doubleHom_gen_one_int,
      doubleHom_gen_two_int, smul_add, smul_smul, zero_smul, add_zero, zero_add]
    module
  · change doubleHom m ((Type100.action m).φu (gen (Type100.k m) 2)) =
      (Type200.action m).φu (doubleHom m (gen (Type100.k m) 2))
    rw [doubleHom_gen_two_int,
      show gen (Type100.k m) 2 = Torus.b from rfl, Type100.u_b,
      show (Type200.action m).φu ((2 : ℤ) • gen (Type200.k m) 2) =
        (2 : ℤ) • (Type200.action m).φu Torus.b from by
        rw [map_zsmul],
      Type200.u_b]
    simp only [map_add, map_zsmul, doubleHom_gen_zero, doubleHom_gen_one_int,
      doubleHom_gen_two_int, smul_add, smul_smul, zero_smul, add_zero, zero_add]
    module

theorem doubleHom_u (m : ℕ) (x : Torus (Type100.k m)) :
    doubleHom m ((Type100.action m).φu x) =
      (Type200.action m).φu (doubleHom m x) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type100.k m) x
  simp only [map_add, map_zsmul, doubleHom_u_gen]

theorem doubleHom_rho_gen (m : ℕ) (j : Fin 3) :
    doubleHom m ((Type100.action m).φρ (gen (Type100.k m) j)) =
      (Type200.action m).φρ (doubleHom m (gen (Type100.k m) j)) := by
  fin_cases j
  · change doubleHom m ((Type100.action m).φρ (gen (Type100.k m) 0)) =
      (Type200.action m).φρ (doubleHom m (gen (Type100.k m) 0))
    rw [doubleHom_gen_zero,
      show gen (Type100.k m) 0 = Torus.c from rfl, Type100.rho_c,
      show (Type200.action m).φρ (gen (Type200.k m) 0) =
        (Type200.action m).φρ Torus.c from rfl, Type200.rho_c]
    simp only [map_add, map_zsmul, doubleHom_gen_zero, doubleHom_gen_one_int,
      doubleHom_gen_two_int, smul_add, smul_smul, zero_smul, add_zero, zero_add]
  · change doubleHom m ((Type100.action m).φρ (gen (Type100.k m) 1)) =
      (Type200.action m).φρ (doubleHom m (gen (Type100.k m) 1))
    rw [doubleHom_gen_one_int,
      show gen (Type100.k m) 1 = Torus.a from rfl, Type100.rho_a,
      show (Type200.action m).φρ ((2 : ℤ) • gen (Type200.k m) 1) =
        (2 : ℤ) • (Type200.action m).φρ Torus.a from by
        rw [map_zsmul],
      Type200.rho_a]
    simp only [map_add, map_zsmul, doubleHom_gen_zero, doubleHom_gen_one_int,
      doubleHom_gen_two_int, smul_add, smul_smul, zero_smul, add_zero, zero_add]
    module
  · change doubleHom m ((Type100.action m).φρ (gen (Type100.k m) 2)) =
      (Type200.action m).φρ (doubleHom m (gen (Type100.k m) 2))
    rw [doubleHom_gen_two_int,
      show gen (Type100.k m) 2 = Torus.b from rfl, Type100.rho_b,
      show (Type200.action m).φρ ((2 : ℤ) • gen (Type200.k m) 2) =
        (2 : ℤ) • (Type200.action m).φρ Torus.b from by
        rw [map_zsmul],
      Type200.rho_b]
    simp only [map_add, map_zsmul, doubleHom_gen_zero, doubleHom_gen_one_int,
      doubleHom_gen_two_int, smul_add, smul_smul, zero_smul, add_zero, zero_add]
    module

theorem doubleHom_rho (m : ℕ) (x : Torus (Type100.k m)) :
    doubleHom m ((Type100.action m).φρ x) =
      (Type200.action m).φρ (doubleHom m x) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type100.k m) x
  simp only [map_add, map_zsmul, doubleHom_rho_gen]


namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

theorem symm_inclusion_eq (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (y : B) :
    E.E.symm (Additive.ofMul (⟨y, hBC y.2⟩ : C)) = doubleHom m (D.ec y) := by
  obtain ⟨i, j, l, h⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t100 m).k (D.ec y)
  have h' : D.ec y = i • gen (Type100.k m) 0 + j • gen (Type100.k m) 1 +
      l • gen (Type100.k m) 2 := h
  rw [symm_inclusion he hf E y h, h', doubleHom_lin]

theorem symm_conj_inclusion
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    (φ₁ : Torus (Type100.k m) →+ Torus (Type100.k m))
    (φ₂ : Torus (Type200.k m) →+ Torus (Type200.k m))
    (hcomp : ∀ x : Torus (Type100.k m), doubleHom m (φ₁ x) = φ₂ (doubleHom m x))
    (hφ₁ : ∀ y : B, D.ec (conjBy hgB y) = φ₁ (D.ec y))
    (y : B) :
    E.E.symm (Additive.ofMul (conjBy hgC (⟨y, hBC y.2⟩ : C))) =
      φ₂ (E.E.symm (Additive.ofMul (⟨y, hBC y.2⟩ : C))) := by
  have hconj : conjBy hgC (⟨y, hBC y.2⟩ : C) =
      (⟨conjBy hgB y, hBC (conjBy hgB y).2⟩ : C) := Subtype.ext rfl
  rw [hconj, symm_inclusion_eq he hf E (conjBy hgB y), hφ₁ y,
    hcomp (D.ec y), ← symm_inclusion_eq he hf E y]

theorem symm_conj_uv
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C) (y : B) :
    E.E.symm (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨y, hBC y.2⟩ : C))) =
      (Type200.action m).φuv (E.E.symm (Additive.ofMul (⟨y, hBC y.2⟩ : C))) :=
  symm_conj_inclusion he hf E (hL D.uv_mem_L) D.uv_mem
    ((Type100.action m).φuv) ((Type200.action m).φuv)
    (doubleHom_uv m) (fun y => D.uv_conj y) y

theorem symm_conj_t
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C) (y : B) :
    E.E.symm (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨y, hBC y.2⟩ : C))) =
      (Type200.action m).φt (E.E.symm (Additive.ofMul (⟨y, hBC y.2⟩ : C))) :=
  symm_conj_inclusion he hf E (hL D.t_mem_L) D.t_mem
    ((Type100.action m).φt) ((Type200.action m).φt)
    (doubleHom_t m) (fun y => D.t_conj y) y

theorem symm_conj_u
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C) (y : B) :
    E.E.symm (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨y, hBC y.2⟩ : C))) =
      (Type200.action m).φu (E.E.symm (Additive.ofMul (⟨y, hBC y.2⟩ : C))) :=
  symm_conj_inclusion he hf E (hL D.u_mem_L) D.u_mem
    ((Type100.action m).φu) ((Type200.action m).φu)
    (doubleHom_u m) (fun y => D.u_conj y) y

theorem symm_conj_ρ
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C) (y : B) :
    E.E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨y, hBC y.2⟩ : C))) =
      (Type200.action m).φρ (E.E.symm (Additive.ofMul (⟨y, hBC y.2⟩ : C))) :=
  symm_conj_inclusion he hf E (hL D.ρ_mem_L) D.ρ_mem
    ((Type100.action m).φρ) ((Type200.action m).φρ)
    (doubleHom_rho m) (fun y => D.ρ_conj y) y

end TorusBasisEquivFour


namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C} {g : S}

theorem conjTorusFour_two_gen1 (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hgC : g ∈ Subgroup.normalizer C) :
    conjTorusFour D hBC E hgC ((2 : ℤ) • gen (Type200.k m) 1) =
      E.E.symm (Additive.ofMul (conjBy hgC (⟨D.a, hBC D.a.2⟩ : C))) := by
  rw [map_zsmul]
  rw [conjTorusFour_apply, E.E_gen1, toMul_ofMul]
  rw [← map_zsmul]
  congr 1
  rw [two_zsmul, ← ofMul_mul,
    show conjBy hgC e * conjBy hgC e = conjBy hgC (e * e) from (conjBy_mul hgC e e).symm, he]

theorem conjTorusFour_two_gen2 (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hgC : g ∈ Subgroup.normalizer C) :
    conjTorusFour D hBC E hgC ((2 : ℤ) • gen (Type200.k m) 2) =
      E.E.symm (Additive.ofMul (conjBy hgC (⟨D.b, hBC D.b.2⟩ : C))) := by
  rw [map_zsmul]
  rw [conjTorusFour_apply, E.E_gen2, toMul_ofMul]
  rw [← map_zsmul]
  congr 1
  rw [two_zsmul, ← ofMul_mul,
    show conjBy hgC f * conjBy hgC f = conjBy hgC (f * f) from (conjBy_mul hgC f f).symm, hf]

@[expose] noncomputable def cocycle (φ : Torus (Type200.k m) →+ Torus (Type200.k m))
    (E : TorusBasisEquivFour D hBC e f) (hgC : g ∈ Subgroup.normalizer C) :
    Torus (Type200.k m) →+ Torus (Type200.k m) :=
  (conjTorusFour D hBC E hgC).toAddMonoidHom - φ

@[simp]
theorem cocycle_apply (φ : Torus (Type200.k m) →+ Torus (Type200.k m))
    (E : TorusBasisEquivFour D hBC e f) (hgC : g ∈ Subgroup.normalizer C)
    (x : Torus (Type200.k m)) :
    cocycle (D := D) (hBC := hBC) (e := e) (f := f) φ E hgC x =
      conjTorusFour D hBC E hgC x - φ x := rfl

theorem cocycle_gen0_eq_zero (φ : Torus (Type200.k m) →+ Torus (Type200.k m))
    (E : TorusBasisEquivFour D hBC e f) (hgC : g ∈ Subgroup.normalizer C)
    (h0 : conjTorusFour D hBC E hgC (gen (Type200.k m) 0) =
      φ (gen (Type200.k m) 0)) :
    cocycle (D := D) (hBC := hBC) (e := e) (f := f) φ E hgC
      (gen (Type200.k m) 0) = 0 := by
  rw [cocycle_apply, h0, sub_self]

theorem cocycle_two_gen1 (φ : Torus (Type200.k m) →+ Torus (Type200.k m))
    (E : TorusBasisEquivFour D hBC e f) (hgC : g ∈ Subgroup.normalizer C)
    (h2 : conjTorusFour D hBC E hgC ((2 : ℤ) • gen (Type200.k m) 1) =
      φ ((2 : ℤ) • gen (Type200.k m) 1)) :
    (2 : ℤ) • cocycle (D := D) (hBC := hBC) (e := e) (f := f) φ E hgC
      (gen (Type200.k m) 1) = 0 := by
  rw [← map_zsmul, cocycle_apply, h2, sub_self]

theorem cocycle_two_gen2 (φ : Torus (Type200.k m) →+ Torus (Type200.k m))
    (E : TorusBasisEquivFour D hBC e f) (hgC : g ∈ Subgroup.normalizer C)
    (h2 : conjTorusFour D hBC E hgC ((2 : ℤ) • gen (Type200.k m) 2) =
      φ ((2 : ℤ) • gen (Type200.k m) 2)) :
    (2 : ℤ) • cocycle (D := D) (hBC := hBC) (e := e) (f := f) φ E hgC
      (gen (Type200.k m) 2) = 0 := by
  rw [← map_zsmul, cocycle_apply, h2, sub_self]

end TorusBasisEquivFour

namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

theorem conjTorusFour_uv_two_gen1
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    conjTorusFour D hBC E (hL D.uv_mem_L) ((2 : ℤ) • gen (Type200.k m) 1) =
      (Type200.action m).φuv ((2 : ℤ) • gen (Type200.k m) 1) := by
  rw [conjTorusFour_two_gen1 he E (hL D.uv_mem_L),
    symm_conj_uv he hf E hL D.a, symm_a he E]

theorem conjTorusFour_uv_two_gen2
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    conjTorusFour D hBC E (hL D.uv_mem_L) ((2 : ℤ) • gen (Type200.k m) 2) =
      (Type200.action m).φuv ((2 : ℤ) • gen (Type200.k m) 2) := by
  rw [conjTorusFour_two_gen2 hf E (hL D.uv_mem_L),
    symm_conj_uv he hf E hL D.b, symm_b hf E]

theorem conjTorusFour_t_two_gen1
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    conjTorusFour D hBC E (hL D.t_mem_L) ((2 : ℤ) • gen (Type200.k m) 1) =
      (Type200.action m).φt ((2 : ℤ) • gen (Type200.k m) 1) := by
  rw [conjTorusFour_two_gen1 he E (hL D.t_mem_L),
    symm_conj_t he hf E hL D.a, symm_a he E]

theorem conjTorusFour_t_two_gen2
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    conjTorusFour D hBC E (hL D.t_mem_L) ((2 : ℤ) • gen (Type200.k m) 2) =
      (Type200.action m).φt ((2 : ℤ) • gen (Type200.k m) 2) := by
  rw [conjTorusFour_two_gen2 hf E (hL D.t_mem_L),
    symm_conj_t he hf E hL D.b, symm_b hf E]

theorem conjTorusFour_u_two_gen1
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    conjTorusFour D hBC E (hL D.u_mem_L) ((2 : ℤ) • gen (Type200.k m) 1) =
      (Type200.action m).φu ((2 : ℤ) • gen (Type200.k m) 1) := by
  rw [conjTorusFour_two_gen1 he E (hL D.u_mem_L),
    symm_conj_u he hf E hL D.a, symm_a he E]

theorem conjTorusFour_u_two_gen2
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    conjTorusFour D hBC E (hL D.u_mem_L) ((2 : ℤ) • gen (Type200.k m) 2) =
      (Type200.action m).φu ((2 : ℤ) • gen (Type200.k m) 2) := by
  rw [conjTorusFour_two_gen2 hf E (hL D.u_mem_L),
    symm_conj_u he hf E hL D.b, symm_b hf E]

theorem conjTorusFour_ρ_two_gen1
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    conjTorusFour D hBC E (hL D.ρ_mem_L) ((2 : ℤ) • gen (Type200.k m) 1) =
      (Type200.action m).φρ ((2 : ℤ) • gen (Type200.k m) 1) := by
  rw [conjTorusFour_two_gen1 he E (hL D.ρ_mem_L),
    symm_conj_ρ he hf E hL D.a, symm_a he E]

theorem conjTorusFour_ρ_two_gen2
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    conjTorusFour D hBC E (hL D.ρ_mem_L) ((2 : ℤ) • gen (Type200.k m) 2) =
      (Type200.action m).φρ ((2 : ℤ) • gen (Type200.k m) 2) := by
  rw [conjTorusFour_two_gen2 hf E (hL D.ρ_mem_L),
    symm_conj_ρ he hf E hL D.b, symm_b hf E]

end TorusBasisEquivFour

namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

@[expose] noncomputable def cocycleUV
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type200.k m) →+ Torus (Type200.k m) :=
  cocycle (D := D) (hBC := hBC) (e := e) (f := f)
    ((Type200.action m).φuv) E (hL D.uv_mem_L)

@[expose] noncomputable def cocycleT
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type200.k m) →+ Torus (Type200.k m) :=
  cocycle (D := D) (hBC := hBC) (e := e) (f := f)
    ((Type200.action m).φt) E (hL D.t_mem_L)

@[expose] noncomputable def cocycleU
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type200.k m) →+ Torus (Type200.k m) :=
  cocycle (D := D) (hBC := hBC) (e := e) (f := f)
    ((Type200.action m).φu) E (hL D.u_mem_L)

@[expose] noncomputable def cocycleR
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type200.k m) →+ Torus (Type200.k m) :=
  cocycle (D := D) (hBC := hBC) (e := e) (f := f)
    ((Type200.action m).φρ) E (hL D.ρ_mem_L)


theorem cocycleUV_gen0
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 0) = 0 :=
  cocycle_gen0_eq_zero _ _ _ (by
    rw [conjTorusFour_apply, E.E_gen0, toMul_ofMul,
      symm_conj_uv he hf E hL D.c, symm_c E])

theorem cocycleUV_two_gen1
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 :=
  cocycle_two_gen1 _ _ _
    (conjTorusFour_uv_two_gen1 he hf E hL)

theorem cocycleUV_two_gen2
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 :=
  cocycle_two_gen2 _ _ _
    (conjTorusFour_uv_two_gen2 he hf E hL)

theorem cocycleT_gen0
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 0) = 0 :=
  cocycle_gen0_eq_zero _ _ _ (by
    rw [conjTorusFour_apply, E.E_gen0, toMul_ofMul,
      symm_conj_t he hf E hL D.c, symm_c E])

theorem cocycleT_two_gen1
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 :=
  cocycle_two_gen1 _ _ _
    (conjTorusFour_t_two_gen1 he hf E hL)

theorem cocycleT_two_gen2
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 :=
  cocycle_two_gen2 _ _ _
    (conjTorusFour_t_two_gen2 he hf E hL)

theorem cocycleU_gen0
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 0) = 0 :=
  cocycle_gen0_eq_zero _ _ _ (by
    rw [conjTorusFour_apply, E.E_gen0, toMul_ofMul,
      symm_conj_u he hf E hL D.c, symm_c E])

theorem cocycleU_two_gen1
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 :=
  cocycle_two_gen1 _ _ _
    (conjTorusFour_u_two_gen1 he hf E hL)

theorem cocycleU_two_gen2
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 :=
  cocycle_two_gen2 _ _ _
    (conjTorusFour_u_two_gen2 he hf E hL)

theorem cocycleR_gen0
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 0) = 0 :=
  cocycle_gen0_eq_zero _ _ _ (by
    rw [conjTorusFour_apply, E.E_gen0, toMul_ofMul,
      symm_conj_ρ he hf E hL D.c, symm_c E])

theorem cocycleR_two_gen1
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 :=
  cocycle_two_gen1 _ _ _
    (conjTorusFour_ρ_two_gen1 he hf E hL)

theorem cocycleR_two_gen2
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 :=
  cocycle_two_gen2 _ _ _
    (conjTorusFour_ρ_two_gen2 he hf E hL)

end TorusBasisEquivFour

namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

theorem conjTorusFour_basis
    (E : TorusBasisEquivFour D hBC e f) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (j : Fin 3) :
    conjTorusFour D hBC E hgC (gen (Type200.k m) j) =
      E.symm (Additive.ofMul (conjBy hgC (basisElemsFour D hBC e f j))) := by
  fin_cases j
  · change conjTorusFour D hBC E hgC (gen (Type200.k m) 0) =
      E.symm (Additive.ofMul (conjBy hgC (basisElemsFour D hBC e f 0)))
    rw [conjTorusFour_apply, E.E_gen0, toMul_ofMul]
    rfl
  · change conjTorusFour D hBC E hgC (gen (Type200.k m) 1) =
      E.symm (Additive.ofMul (conjBy hgC (basisElemsFour D hBC e f 1)))
    rw [conjTorusFour_apply, E.E_gen1, toMul_ofMul]
    rfl
  · change conjTorusFour D hBC E hgC (gen (Type200.k m) 2) =
      E.symm (Additive.ofMul (conjBy hgC (basisElemsFour D hBC e f 2)))
    rw [conjTorusFour_apply, E.E_gen2, toMul_ofMul]
    rfl

theorem conjTorusFour_gen_eq_of_cocycle_eq_zero
    (E : TorusBasisEquivFour D hBC e f) {g : S}
    (hgC : g ∈ Subgroup.normalizer C)
    (φ : Torus (Type200.k m) →+ Torus (Type200.k m))
    (h : cocycle (D := D) (hBC := hBC) (e := e) (f := f) φ E hgC = 0)
    (j : Fin 3) :
    conjTorusFour D hBC E hgC (gen (Type200.k m) j) = φ (gen (Type200.k m) j) := by
  have h0 : cocycle (D := D) (hBC := hBC) (e := e) (f := f) φ E hgC
      (gen (Type200.k m) j) = 0 := by
    rw [h]
    rfl
  rw [cocycle_apply] at h0
  exact sub_eq_zero.mp h0

theorem type200Images_of_cocycle_eq_zero
    (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C)
    (huv : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (ht : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) :
    Type200Images D hBC hL e f E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    rw [← conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E) (hgC := hL D.uv_mem_L) (j := j)]
    exact conjTorusFour_gen_eq_of_cocycle_eq_zero E (hL D.uv_mem_L) _ huv j
  · intro j
    rw [← conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E) (hgC := hL D.t_mem_L) (j := j)]
    exact conjTorusFour_gen_eq_of_cocycle_eq_zero E (hL D.t_mem_L) _ ht j
  · intro j
    rw [← conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E) (hgC := hL D.u_mem_L) (j := j)]
    exact conjTorusFour_gen_eq_of_cocycle_eq_zero E (hL D.u_mem_L) _ hu j
  · intro j
    rw [← conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E) (hgC := hL D.ρ_mem_L) (j := j)]
    exact conjTorusFour_gen_eq_of_cocycle_eq_zero E (hL D.ρ_mem_L) _ hρ j

end TorusBasisEquivFour

namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

theorem action_eq_printed_add_cocycle
    (E : TorusBasisEquivFour D hBC e f) {g : S}
    (hgC : g ∈ Subgroup.normalizer C)
    (φ : Torus (Type200.k m) →+ Torus (Type200.k m)) (x : Torus (Type200.k m)) :
    conjTorusFour D hBC E hgC x =
      φ x + cocycle (D := D) (hBC := hBC) (e := e) (f := f) φ E hgC x := by
  rw [cocycle_apply]
  abel

theorem action_reduction_uv
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (∀ x, conjTorusFour D hBC E (hL D.uv_mem_L) x =
      (Type200.action m).φuv x + cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x) ∧
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL (gen (Type200.k m) 0) = 0 ∧
      (2 : ℤ) • cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) = 0 ∧
      (2 : ℤ) • cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) = 0 :=
  ⟨fun _ => action_eq_printed_add_cocycle E (hL D.uv_mem_L) _ _,
    cocycleUV_gen0 he hf E hL, cocycleUV_two_gen1 he hf E hL, cocycleUV_two_gen2 he hf E hL⟩

theorem action_reduction_t
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (∀ x, conjTorusFour D hBC E (hL D.t_mem_L) x =
      (Type200.action m).φt x + cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL x) ∧
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL (gen (Type200.k m) 0) = 0 ∧
      (2 : ℤ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) = 0 ∧
      (2 : ℤ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) = 0 :=
  ⟨fun _ => action_eq_printed_add_cocycle E (hL D.t_mem_L) _ _,
    cocycleT_gen0 he hf E hL, cocycleT_two_gen1 he hf E hL, cocycleT_two_gen2 he hf E hL⟩

theorem action_reduction_u
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (∀ x, conjTorusFour D hBC E (hL D.u_mem_L) x =
      (Type200.action m).φu x + cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL x) ∧
      cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL (gen (Type200.k m) 0) = 0 ∧
      (2 : ℤ) • cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) = 0 ∧
      (2 : ℤ) • cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) = 0 :=
  ⟨fun _ => action_eq_printed_add_cocycle E (hL D.u_mem_L) _ _,
    cocycleU_gen0 he hf E hL, cocycleU_two_gen1 he hf E hL, cocycleU_two_gen2 he hf E hL⟩

theorem action_reduction_ρ
    (he : e * e = (⟨D.a, hBC D.a.2⟩ : C))
    (hf : f * f = (⟨D.b, hBC D.b.2⟩ : C))
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    (∀ x, conjTorusFour D hBC E (hL D.ρ_mem_L) x =
      (Type200.action m).φρ x + cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL x) ∧
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL (gen (Type200.k m) 0) = 0 ∧
      (2 : ℤ) • cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) = 0 ∧
      (2 : ℤ) • cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) = 0 :=
  ⟨fun _ => action_eq_printed_add_cocycle E (hL D.ρ_mem_L) _ _,
    cocycleR_gen0 he hf E hL, cocycleR_two_gen1 he hf E hL, cocycleR_two_gen2 he hf E hL⟩

end TorusBasisEquivFour

namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

theorem cocycle_eq_zero_of_gen_eq_zero
    (E : TorusBasisEquivFour D hBC e f) {g : S}
    (hgC : g ∈ Subgroup.normalizer C)
    (φ : Torus (Type200.k m) →+ Torus (Type200.k m))
    (h : ∀ j : Fin 3, cocycle (D := D) (hBC := hBC) (e := e) (f := f) φ E hgC
      (gen (Type200.k m) j) = 0) :
    cocycle (D := D) (hBC := hBC) (e := e) (f := f) φ E hgC = 0 := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type200.k m) x
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h 0, h 1, h 2]
  simp

theorem cocycleUV_eq_zero_iff
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0 ↔
      ∀ j : Fin 3, E.symm (Additive.ofMul (conjBy (hL D.uv_mem_L)
        (basisElemsFour D hBC e f j))) =
        (Type200.action m).φuv (gen (Type200.k m) j) := by
  constructor
  · intro h j
    have h0 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) j) = 0 := by rw [h]; rfl
    change cocycle (D := D) (hBC := hBC) (e := e) (f := f)
      ((Type200.action m).φuv) E (hL D.uv_mem_L) (gen (Type200.k m) j) = 0 at h0
    rw [cocycle_apply] at h0
    rw [conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
      (hgC := hL D.uv_mem_L) (j := j)] at h0
    exact sub_eq_zero.mp h0
  · intro h
    apply cocycle_eq_zero_of_gen_eq_zero E (hL D.uv_mem_L)
    intro j
    have hc : conjTorusFour D hBC E (hL D.uv_mem_L) (gen (Type200.k m) j) =
        (Type200.action m).φuv (gen (Type200.k m) j) := by
      rw [conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
        (hgC := hL D.uv_mem_L) (j := j)]
      exact h j
    change cocycle (D := D) (hBC := hBC) (e := e) (f := f)
      ((Type200.action m).φuv) E (hL D.uv_mem_L) (gen (Type200.k m) j) = 0
    rw [cocycle_apply, hc, sub_self]

theorem cocycleT_eq_zero_iff
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0 ↔
      ∀ j : Fin 3, E.symm (Additive.ofMul (conjBy (hL D.t_mem_L)
        (basisElemsFour D hBC e f j))) =
        (Type200.action m).φt (gen (Type200.k m) j) := by
  constructor
  · intro h j
    have h0 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) j) = 0 := by rw [h]; rfl
    change cocycle (D := D) (hBC := hBC) (e := e) (f := f)
      ((Type200.action m).φt) E (hL D.t_mem_L) (gen (Type200.k m) j) = 0 at h0
    rw [cocycle_apply] at h0
    rw [conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
      (hgC := hL D.t_mem_L) (j := j)] at h0
    exact sub_eq_zero.mp h0
  · intro h
    apply cocycle_eq_zero_of_gen_eq_zero E (hL D.t_mem_L)
    intro j
    have hc : conjTorusFour D hBC E (hL D.t_mem_L) (gen (Type200.k m) j) =
        (Type200.action m).φt (gen (Type200.k m) j) := by
      rw [conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
        (hgC := hL D.t_mem_L) (j := j)]
      exact h j
    change cocycle (D := D) (hBC := hBC) (e := e) (f := f)
      ((Type200.action m).φt) E (hL D.t_mem_L) (gen (Type200.k m) j) = 0
    rw [cocycle_apply, hc, sub_self]

theorem cocycleU_eq_zero_iff
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0 ↔
      ∀ j : Fin 3, E.symm (Additive.ofMul (conjBy (hL D.u_mem_L)
        (basisElemsFour D hBC e f j))) =
        (Type200.action m).φu (gen (Type200.k m) j) := by
  constructor
  · intro h j
    have h0 : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) j) = 0 := by rw [h]; rfl
    change cocycle (D := D) (hBC := hBC) (e := e) (f := f)
      ((Type200.action m).φu) E (hL D.u_mem_L) (gen (Type200.k m) j) = 0 at h0
    rw [cocycle_apply] at h0
    rw [conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
      (hgC := hL D.u_mem_L) (j := j)] at h0
    exact sub_eq_zero.mp h0
  · intro h
    apply cocycle_eq_zero_of_gen_eq_zero E (hL D.u_mem_L)
    intro j
    have hc : conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) j) =
        (Type200.action m).φu (gen (Type200.k m) j) := by
      rw [conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
        (hgC := hL D.u_mem_L) (j := j)]
      exact h j
    change cocycle (D := D) (hBC := hBC) (e := e) (f := f)
      ((Type200.action m).φu) E (hL D.u_mem_L) (gen (Type200.k m) j) = 0
    rw [cocycle_apply, hc, sub_self]

theorem cocycleR_eq_zero_iff
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0 ↔
      ∀ j : Fin 3, E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L)
        (basisElemsFour D hBC e f j))) =
        (Type200.action m).φρ (gen (Type200.k m) j) := by
  constructor
  · intro h j
    have h0 : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) j) = 0 := by rw [h]; rfl
    change cocycle (D := D) (hBC := hBC) (e := e) (f := f)
      ((Type200.action m).φρ) E (hL D.ρ_mem_L) (gen (Type200.k m) j) = 0 at h0
    rw [cocycle_apply] at h0
    rw [conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
      (hgC := hL D.ρ_mem_L) (j := j)] at h0
    exact sub_eq_zero.mp h0
  · intro h
    apply cocycle_eq_zero_of_gen_eq_zero E (hL D.ρ_mem_L)
    intro j
    have hc : conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) j) =
        (Type200.action m).φρ (gen (Type200.k m) j) := by
      rw [conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
        (hgC := hL D.ρ_mem_L) (j := j)]
      exact h j
    change cocycle (D := D) (hBC := hBC) (e := e) (f := f)
      ((Type200.action m).φρ) E (hL D.ρ_mem_L) (gen (Type200.k m) j) = 0
    rw [cocycle_apply, hc, sub_self]

end TorusBasisEquivFour

namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

theorem type200Images_iff_cocycle_eq_zero
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C) :
    Type200Images D hBC hL e f E ↔
      (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0 ∧
        cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0 ∧
        cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0 ∧
        cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) := by
  constructor
  · intro h
    exact ⟨(cocycleUV_eq_zero_iff E hL).mpr h.uv,
      (cocycleT_eq_zero_iff E hL).mpr h.t,
      (cocycleU_eq_zero_iff E hL).mpr h.u,
      (cocycleR_eq_zero_iff E hL).mpr h.ρ⟩
  · rintro ⟨huv, ht, hu, hρ⟩
    exact type200Images_of_cocycle_eq_zero E hL huv ht hu hρ

end TorusBasisEquivFour

end CFSG.CGT.Stroth77
