module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldAutPSL
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldPSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.GH74.GLS.IVK Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped commutatorElement

section Diag

variable {F : Type} [Field F]

@[expose] def l3bDiag (x y z : F) (h : x * y * z = 1) : SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![x, y, z], by
    rw [det_diagonal]
    simp [Fin.prod_univ_three, h]⟩

theorem coe_toGL_l3bDiag (x y z : F) (h : x * y * z = 1) :
    ((SpecialLinearGroup.toGL (l3bDiag x y z h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![x, y, z] := rfl

theorem l3bDiag_mem {p f₀ : ℕ} (hp : p ^ f₀ ≠ 0) {x y z : F} (h : x * y * z = 1)
    (hx : x ^ (p ^ f₀) * x = 1) (hy : y ^ (p ^ f₀) * y = 1) (hz : z ^ (p ^ f₀) * z = 1) :
    SpecialLinearGroup.toGL (l3bDiag x y z h) ∈ unitarySU p f₀ F 3 := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [coe_toGL_l3bDiag, det_diagonal]
    simp [Fin.prod_univ_three, h]
  · rw [coe_toGL_l3bDiag]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.mul_apply, hx, hy, hz, zero_pow hp]

theorem l3bf_exists_zeta {F₀ : Type} [Field F₀] [Finite F₀] {q : ℕ} (hcard : Nat.card F₀ = q ^ 2)
    (hq : 2 ≤ q) : ∃ ζ : F₀, orderOf ζ = q + 1 := by
  have : Fintype F₀ := Fintype.ofFinite F₀
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F₀ˣ)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have hdvd : q - 1 ∣ orderOf g := by
    rw [hord]
    exact ⟨q + 1, by
      have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        have : 1 ≤ q := by omega
        zify [this, show 1 ≤ q ^ 2 by nlinarith]
        ring
      exact this⟩
  have h1 : orderOf (g ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord]
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have : 1 ≤ q := by omega
      zify [this, show 1 ≤ q ^ 2 by nlinarith]
      ring
    rw [this, Nat.mul_div_cancel_left _ (by omega)]
  exact ⟨((g ^ (q - 1) : F₀ˣ) : F₀), by rw [orderOf_units, h1]⟩

theorem l3bf_fixed_of_zeta {K : Type} [Field K] [Finite K] (F₀ : Subfield K) {q : ℕ} (hq : 2 ≤ q)
    (hcard : Nat.card F₀ = q ^ 2) (τ : K ≃+* K) {ζ : F₀} (hζ : orderOf ζ = q + 1)
    (hτ : τ (ζ : K) = ζ) : ∀ x : F₀, τ (x : K) = x := by
  let E : Subfield F₀ := (τ.toRingHom.comp F₀.subtype).eqLocusField F₀.subtype
  have hmem : ∀ x : F₀, x ∈ E ↔ τ (x : K) = x := fun x => by
    rw [RingHom.mem_eqLocusField]
    rfl
  have hζE : ζ ∈ E := (hmem ζ).2 hτ
  have : Fintype F₀ := Fintype.ofFinite F₀
  have : Fintype E := Fintype.ofFinite E
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hζ
    omega
  have hE2 : q + 1 ∣ Nat.card E - 1 := by
    let u : Eˣ := Units.mk0 ⟨ζ, hζE⟩ (fun h => hζ0 (congrArg Subtype.val h))
    have hu : orderOf u = q + 1 := by
      rw [← orderOf_units] 
      have : ((u : Eˣ) : E) = ⟨ζ, hζE⟩ := rfl
      rw [this, ← orderOf_injective (E.subtype : E →+* F₀).toMonoidHom Subtype.val_injective
        (⟨ζ, hζE⟩ : E)]
      exact hζ
    rw [← hu, ← Nat.card_units]
    exact orderOf_dvd_natCard u
  have hE1 : 2 ≤ Nat.card E := Finite.one_lt_card
  have hEge : q + 2 ≤ Nat.card E := by
    have := Nat.le_of_dvd (by omega) hE2
    omega
  have hd := Module.natCard_eq_pow_finrank (K := E) (V := F₀)
  rw [hcard] at hd
  have hfr : Module.finrank E F₀ = 1 := by
    by_contra hne
    rcases Nat.lt_or_ge (Module.finrank E F₀) 1 with h0 | h2
    · have h00 : Module.finrank E F₀ = 0 := by omega
      rw [h00, pow_zero] at hd
      nlinarith
    · have h2' : 2 ≤ Module.finrank E F₀ := by omega
      have : Nat.card E ^ 2 ≤ Nat.card E ^ Module.finrank E F₀ :=
        Nat.pow_le_pow_right (by omega) h2'
      rw [← hd] at this
      nlinarith
  have hone := (finrank_eq_one_iff_of_nonzero' (K := E) (V := F₀) (1 : F₀) one_ne_zero).1 hfr
  intro x
  obtain ⟨c, hc⟩ := hone x
  have hcx : x = (c : F₀) := by
    rw [← hc, Algebra.smul_def, mul_one]
    rfl
  rw [hcx]
  exact (hmem c).1 c.2
end Diag

section Rigid

variable {p f f₀ : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {σ : K ≃+* K}
  (hf : f = 3 * f₀) (h₀ : UnitaryFieldData p f₀ (fixedField σ))

theorem coe_suIncl_eq_map (g : unitarySU p f₀ (fixedField σ) 3) :
    ((suIncl h h₀ (bar_coe_fixedField h hf h₀) g : unitarySU p f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ)) := by
  apply GeneralLinearGroup.ext
  intro i j
  rw [coe_suIncl_apply]
  simp [GeneralLinearGroup.map_apply]

include hf h₀ in
theorem l3bf_psu_conj_eq (hq₀ : p ^ f₀ ≠ 2)
    (ρ : MulAut (unitaryPSU h 3))
    (hρ : ∀ g, ρ (l3bUG h hf h₀ g) = l3bUG h hf h₀ g) (A : unitaryIsom3 h) (τ : K ≃+* K)
    (hρe : ρ = psuConj h A * psuField h τ) (g : unitarySU p f₀ (fixedField σ) 3) :
    (A : GL (Fin 3) K) * glAut τ (GeneralLinearGroup.map (fixedField σ).subtype
        (g : GL (Fin 3) (fixedField σ))) * (A : GL (Fin 3) K)⁻¹ =
      GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ)) := by
  have := h.finite
  have := h₀.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card (fixedField σ) = (p ^ f₀) ^ 2 := by
    rw [h₀.card, ← pow_mul, mul_comm]
  have hperf : commutator (unitarySU p f₀ (fixedField σ) 3) = ⊤ :=
    (Group.isPerfect_def (G := unitarySU p f₀ (fixedField σ) 3)).1
      (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF le_rfl (fun h3 => hq₀ (by simpa using h3)))
  let φ₁ : unitarySU p f₀ (fixedField σ) 3 →* unitarySU p f K 3 :=
    ((suConj h A : MulAut (unitarySU p f K 3)) : unitarySU p f K 3 →* unitarySU p f K 3).comp
      (((suField h τ : MulAut (unitarySU p f K 3)) : unitarySU p f K 3 →* unitarySU p f K 3).comp
        (suIncl h h₀ (bar_coe_fixedField h hf h₀)))
  have hφ : φ₁ = suIncl h h₀ (bar_coe_fixedField h hf h₀) := by
    apply l3bf_eq_of_perfect hperf
    intro g'
    have h1 := hρ g'
    rw [hρe] at h1
    change (psuConj h A * psuField h τ) (unitaryProj h 3 (suIncl h h₀ (bar_coe_fixedField h hf h₀) g')) =
      unitaryProj h 3 (suIncl h h₀ (bar_coe_fixedField h hf h₀) g') at h1
    rw [MulAut.mul_apply] at h1
    have h2 : unitaryProj h 3 (φ₁ g') = unitaryProj h 3 (suIncl h h₀ (bar_coe_fixedField h hf h₀) g') :=
      h1
    have h3 : (suIncl h h₀ (bar_coe_fixedField h hf h₀) g')⁻¹ * φ₁ g' ∈ (unitaryProj h 3).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
    rw [ker_unitaryProj] at h3
    exact unitaryScalars_le_center h 3 h3
  have h4 := congrArg (fun φ : unitarySU p f₀ (fixedField σ) 3 →* unitarySU p f K 3 =>
    ((φ g : unitarySU p f K 3) : GL (Fin 3) K)) hφ
  simp only [φ₁, MonoidHom.comp_apply] at h4
  change ((suConj h A (suField h τ (suIncl h h₀ (bar_coe_fixedField h hf h₀) g)) :
    unitarySU p f K 3) : GL (Fin 3) K) = _ at h4
  rw [coe_suConj, coe_suField, coe_suIncl_eq_map h hf h₀] at h4
  simpa using h4

theorem l3bf_map_diag3 (f : K → K) (h0 : f 0 = 0) (a b c : K) :
    (Matrix.diagonal ![a, b, c] : Matrix (Fin 3) (Fin 3) K).map f =
      Matrix.diagonal ![f a, f b, f c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0]

theorem l3bf_diag_entry {A : Matrix (Fin 3) (Fin 3) K} {n d : Fin 3 → K}
    (h : A * Matrix.diagonal n = Matrix.diagonal d * A) (i j : Fin 3) :
    A i j * n j = d i * A i j := by
  have := congrFun (congrFun h i) j
  simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this

theorem l3bf_psu_diag_eq (hp : p ^ f₀ ≠ 0) (A : GL (Fin 3) K) (τ : K ≃+* K)
    (H : ∀ g : unitarySU p f₀ (fixedField σ) 3,
      A * glAut τ (GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ))) *
        A⁻¹ = GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ)))
    {x y z : fixedField σ} (hxyz : x * y * z = 1) (hx : x ^ (p ^ f₀) * x = 1)
    (hy : y ^ (p ^ f₀) * y = 1) (hz : z ^ (p ^ f₀) * z = 1) :
    A.val * Matrix.diagonal ![τ (x : K), τ (y : K), τ (z : K)] =
      Matrix.diagonal ![(x : K), (y : K), (z : K)] * A.val := by
  have h1 := H ⟨SpecialLinearGroup.toGL (l3bDiag x y z hxyz), l3bDiag_mem hp hxyz hx hy hz⟩
  have h2 := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) h1
  have hmap : ((GeneralLinearGroup.map (fixedField σ).subtype
      (SpecialLinearGroup.toGL (l3bDiag x y z hxyz) : GL (Fin 3) (fixedField σ)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![(x : K), (y : K), (z : K)] := by
    ext i j
    show (fixedField σ).subtype (((SpecialLinearGroup.toGL (l3bDiag x y z hxyz) :
      GL (Fin 3) (fixedField σ)) : Matrix (Fin 3) (Fin 3) (fixedField σ)) i j) = _
    rw [coe_toGL_l3bDiag]
    fin_cases i <;> fin_cases j <;> simp
  simp only [Units.val_mul, coe_glAut, hmap] at h2
  rw [l3bf_map_diag3 τ (map_zero τ)] at h2
  have h3 : (A⁻¹ : GL (Fin 3) K).val * A.val = 1 := Units.inv_mul A
  calc A.val * Matrix.diagonal ![τ (x : K), τ (y : K), τ (z : K)]
      = A.val * Matrix.diagonal ![τ (x : K), τ (y : K), τ (z : K)] * ((A⁻¹ : GL (Fin 3) K).val * A.val) := by
        rw [h3, mul_one]
    _ = (A.val * Matrix.diagonal ![τ (x : K), τ (y : K), τ (z : K)] * (A⁻¹ : GL (Fin 3) K).val) * A.val := by
        simp only [mul_assoc]
    _ = _ := by rw [h2]

theorem l3bf_det_ne_zero (A : GL (Fin 3) K) : A.val.det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact (Matrix.GeneralLinearGroup.det A).ne_zero

theorem l3bf_psu_tau_zeta (hp : p ^ f₀ ≠ 0) (A : GL (Fin 3) K) (τ : K ≃+* K)
    (H : ∀ g : unitarySU p f₀ (fixedField σ) 3,
      A * glAut τ (GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ))) *
        A⁻¹ = GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ)))
    {ζ : fixedField σ} (hζ0 : ζ ≠ 0) (hζ : ζ ^ (p ^ f₀) * ζ = 1) : τ (ζ : K) = ζ := by
  by_contra hne
  have hxyz : ζ * ζ * (ζ ^ 2)⁻¹ = 1 := by field_simp
  have hz : ((ζ ^ 2)⁻¹) ^ (p ^ f₀) * (ζ ^ 2)⁻¹ = 1 := by
    have : (ζ ^ 2) ^ (p ^ f₀) * ζ ^ 2 = 1 := by
      calc (ζ ^ 2) ^ (p ^ f₀) * ζ ^ 2 = (ζ ^ (p ^ f₀) * ζ) ^ 2 := by ring
        _ = 1 := by rw [hζ]; norm_num
    rw [inv_pow, ← mul_inv, this, inv_one]
  have h := l3bf_psu_diag_eq hp A τ H hxyz hζ hζ hz
  have hent := l3bf_diag_entry h
  have hne' : τ (ζ : K) - ζ ≠ 0 := sub_ne_zero.2 hne
  have hz0 : ∀ i j : Fin 3, i.val < 2 → j.val < 2 → A.val i j = 0 := by
    intro i j hi hj
    have h1 := hent i j
    have h2 : A.val i j * (τ (ζ : K) - ζ) = 0 := by
      have : (![τ (ζ : K), τ (ζ : K), τ ((ζ ^ 2)⁻¹ : fixedField σ)] j) = τ (ζ : K) := by
        fin_cases j <;> simp at hj ⊢
      have h3 : (![(ζ : K), (ζ : K), (((ζ ^ 2)⁻¹ : fixedField σ) : K)] i) = ζ := by
        fin_cases i <;> simp at hi ⊢
      rw [this, h3] at h1
      linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_right hne'
  apply l3bf_det_ne_zero A
  rw [Matrix.det_fin_three]
  have e00 := hz0 0 0 (by decide) (by decide)
  have e01 := hz0 0 1 (by decide) (by decide)
  have e10 := hz0 1 0 (by decide) (by decide)
  have e11 := hz0 1 1 (by decide) (by decide)
  rw [e00, e01, e10, e11]
  ring

theorem l3bf_psu_cyc_eq (hp : p ^ f₀ ≠ 0) (A : GL (Fin 3) K) (τ : K ≃+* K)
    (H : ∀ g : unitarySU p f₀ (fixedField σ) 3,
      A * glAut τ (GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ))) *
        A⁻¹ = GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ))) :
    A.val * !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] = !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] * A.val := by
  have h1 := H ⟨SpecialLinearGroup.toGL (l3bCyc (fixedField σ)), l3bUCyc_mem hp⟩
  have h2 := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) h1
  have hmap : ((GeneralLinearGroup.map (fixedField σ).subtype
      (SpecialLinearGroup.toGL (l3bCyc (fixedField σ)) : GL (Fin 3) (fixedField σ)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] := by
    ext i j
    show (fixedField σ).subtype (((SpecialLinearGroup.toGL (l3bCyc (fixedField σ)) :
      GL (Fin 3) (fixedField σ)) : Matrix (Fin 3) (Fin 3) (fixedField σ)) i j) = _
    rw [coe_toGL_l3bCyc]
    fin_cases i <;> fin_cases j <;> simp
  have hτ : (!![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0]).map τ = !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  simp only [Units.val_mul, coe_glAut, hmap, hτ] at h2
  have h3 : (A⁻¹ : GL (Fin 3) K).val * A.val = 1 := Units.inv_mul A
  calc A.val * !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0]
      = A.val * !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] * ((A⁻¹ : GL (Fin 3) K).val * A.val) := by
        rw [h3, mul_one]
    _ = (A.val * !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] * (A⁻¹ : GL (Fin 3) K).val) * A.val := by
        simp only [mul_assoc]
    _ = _ := by rw [h2]

theorem l3bf_psu_scalar (hp : p ^ f₀ ≠ 0) (A : GL (Fin 3) K) (τ : K ≃+* K)
    (H : ∀ g : unitarySU p f₀ (fixedField σ) 3,
      A * glAut τ (GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ))) *
        A⁻¹ = GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ)))
    (hτ : ∀ x : fixedField σ, τ (x : K) = x)
    {ζ : fixedField σ} (hζ0 : ζ ≠ 0) (hζ : ζ ^ (p ^ f₀) * ζ = 1) (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1) :
    ∃ a : K, A.val = Matrix.scalar (Fin 3) a := by
  have hxyz : ζ * ζ⁻¹ * 1 = 1 := by field_simp
  have hy : ζ⁻¹ ^ (p ^ f₀) * ζ⁻¹ = 1 := by
    rw [inv_pow, ← mul_inv, hζ, inv_one]
  have hone : (1 : fixedField σ) ^ (p ^ f₀) * 1 = 1 := by simp
  have h := l3bf_psu_diag_eq hp A τ H hxyz hζ hy hone
  rw [hτ, hτ, hτ] at h
  have hent := l3bf_diag_entry h
  have hcyc := l3bf_psu_cyc_eq hp A τ H
  have hne01 : ((ζ : fixedField σ) : K) ≠ ((ζ : fixedField σ) : K)⁻¹ := by
    intro he
    apply hζ2
    have hζK : ((ζ : fixedField σ) : K) ≠ 0 := fun h0 => hζ0 (Subtype.ext h0)
    have : ((ζ ^ 2 : fixedField σ) : K) = 1 := by
      push_cast
      calc ((ζ : fixedField σ) : K) ^ 2 = ((ζ : fixedField σ) : K) * ((ζ : fixedField σ) : K) := by ring
        _ = ((ζ : fixedField σ) : K) * ((ζ : fixedField σ) : K)⁻¹ := by rw [← he]
        _ = 1 := mul_inv_cancel₀ hζK
    exact Subtype.ext this
  have hne02 : ((ζ : fixedField σ) : K) ≠ 1 := fun he => hζ1 (Subtype.ext he)
  have hne12 : ((ζ : fixedField σ) : K)⁻¹ ≠ 1 := by
    intro he
    apply hζ1
    exact Subtype.ext (inv_eq_one.1 he)
  have aux : ∀ {x y u : K}, u * y = x * u → x ≠ y → u = 0 := by
    intro x y u h hxy
    have : u * (y - x) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.1 h0).symm hxy
  have hoff : ∀ i j : Fin 3, i ≠ j → A.val i j = 0 := by
    intro i j hij
    have h1 := hent i j
    fin_cases i <;> fin_cases j <;> simp at hij h1 ⊢
    · exact aux (by linear_combination h1) hne01
    · exact aux (by linear_combination h1) hne02
    · exact aux (by linear_combination h1) hne01.symm
    · exact aux (by linear_combination h1) hne12
    · exact aux (by linear_combination h1) hne02.symm
    · exact aux (by linear_combination h1) hne12.symm
  have hc1 := congrFun (congrFun hcyc 0) 2
  have hc2 := congrFun (congrFun hcyc 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hc1 hc2
  refine ⟨A.val 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  all_goals first | rfl | exact hoff _ _ (by decide) | exact hc1.symm | exact hc2

include h₀ in
theorem l3bf_psu_tau_scalar [Finite K] (A : GL (Fin 3) K) (τ : K ≃+* K)
    (H : ∀ g : unitarySU p f₀ (fixedField σ) 3,
      A * glAut τ (GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ))) *
        A⁻¹ = GeneralLinearGroup.map (fixedField σ).subtype (g : GL (Fin 3) (fixedField σ))) :
    (∀ x : fixedField σ, τ (x : K) = x) ∧ ∃ a : K, A.val = Matrix.scalar (Fin 3) a := by
  have := h₀.finite
  have hp : p ^ f₀ ≠ 0 := pow_ne_zero _ h₀.prime.ne_zero
  have h2 : 2 ≤ p ^ f₀ :=
    h₀.prime.two_le.trans (Nat.le_self_pow (by have := h₀.one_le; omega) p)
  have hcard : Nat.card (fixedField σ) = (p ^ f₀) ^ 2 := by
    rw [h₀.card, ← pow_mul, mul_comm]
  obtain ⟨ζ, hord⟩ := l3bf_exists_zeta hcard h2
  have hζn : ζ ^ (p ^ f₀) * ζ = 1 := by
    rw [← pow_succ, ← hord]
    exact pow_orderOf_eq_one ζ
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hord
    omega
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hord
    omega
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2'
    have := orderOf_dvd_of_pow_eq_one h2'
    rw [hord] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hτζ := l3bf_psu_tau_zeta hp A τ H hζ0 hζn
  have hall := l3bf_fixed_of_zeta (fixedField σ) h2 hcard τ hord hτζ
  exact ⟨hall, l3bf_psu_scalar hp A τ H hall hζ0 hζn hζ1 hζ2⟩

theorem l3bf_psuConj_one_of_scalar (A : unitaryIsom3 h) {a : K}
    (ha : (A : GL (Fin 3) K).val = Matrix.scalar (Fin 3) a) : psuConj h A = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuConj_mk]
    have : suConj h A g = g := by
      apply Subtype.ext
      rw [coe_suConj]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      have hcomm : (A : GL (Fin 3) K).val * ((g : unitarySU p f K 3) : GL (Fin 3) K).val =
          ((g : unitarySU p f K 3) : GL (Fin 3) K).val * (A : GL (Fin 3) K).val := by
        rw [ha]
        exact (Matrix.scalar_commute a (fun _ => Commute.all _ _) _).eq
      rw [hcomm, mul_assoc, Subgroup.coe_inv, Units.mul_inv, mul_one]
    rw [this]
    rfl

include hf h₀ in
theorem l3bf_rigid_psu (hq : 2 < p ^ f) (hq₀ : p ^ f₀ ≠ 2) (ρ : MulAut (unitaryPSU h 3))
    (hρ : ∀ g, ρ (l3bUG h hf h₀ g) = l3bUG h hf h₀ g) :
    ρ ∈ Subgroup.zpowers (psuField h σ) := by
  have := h.finite
  obtain ⟨A, τ, hρe⟩ := exists_psuConj_mul_psuField hq ρ
  have H := l3bf_psu_conj_eq h hf h₀ hq₀ ρ hρ A τ hρe
  obtain ⟨hall, a, ha⟩ := l3bf_psu_tau_scalar h₀ A τ H
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (l3bf_mem_zpowers_of_fixes σ τ
    (fun t ht => hall ⟨t, (mem_fixedField_iff σ t).2 ht⟩))
  rw [hρe, l3bf_psuConj_one_of_scalar h A ha, one_mul, ← hk, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ _

end Rigid

end CFSG.HardMathSupport.Solomon.Coordinator
