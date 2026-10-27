module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellOffender

public section

namespace CFSG.CGT.PushingUpLit.BHS

open Matrix CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender
open CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization

variable {k : Type} [Field k]

@[expose] def sl2QuarterTurn : SpecialLinearGroup (Fin 2) k :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

theorem sl2QuarterTurn_mulVec (v : Fin 2 → k) :
    ((sl2QuarterTurn : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec v =
      ![v 1, -v 0] := by
  ext i; fin_cases i <;> simp [sl2QuarterTurn, mulVec, dotProduct, Fin.sum_univ_two]

theorem unipotent_mulVec (t : k) (v : Fin 2 → k) :
    ((unipotent t : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec v =
      ![v 0 + t * v 1, v 1] :=
  smul_unipotent_vec t v

omit [Field k] in
theorem planeVec_ext {v w : Fin 2 → k} (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
  ext i; fin_cases i <;> assumption

theorem exists_scalar_of_commutes_sl2 (c : (Fin 2 → k) →+ (Fin 2 → k))
    (hc : ∀ (g : SpecialLinearGroup (Fin 2) k) (v : Fin 2 → k),
      c ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) = (g : Matrix (Fin 2) (Fin 2) k).mulVec (c v)) :
    ∃ a : k, ∀ v, c v = a • v := by
  set x := c ![1, 0] with hx
  have h1 : c ![1, 0] = ![x 0, 0] := by
    have h := congrFun (hc (unipotent 1) ![1, 0]) 0
    rw [unipotent_mulVec, unipotent_mulVec] at h
    exact planeVec_ext rfl (by simpa [← hx] using h)
  have h2 : c ![0, 1] = ![0, x 0] := by
    have h := hc sl2QuarterTurn ![1, 0]
    rw [sl2QuarterTurn_mulVec, sl2QuarterTurn_mulVec, h1] at h
    have h' : c (-![![1, 0] 1, -![1, 0] 0]) = -![![x 0, 0] 1, -![x 0, 0] 0] := by
      rw [map_neg, h]
    have e : (-![![1, 0] 1, -![1, 0] 0] : Fin 2 → k) = ![0, 1] :=
      planeVec_ext (by simp) (by simp)
    rw [e] at h'
    rw [h']
    exact planeVec_ext (by simp) (by simp)
  have h3 : ∀ t : k, c ![t, 0] = ![x 0 * t, 0] := by
    intro t
    have h := hc (unipotent t) ![0, 1]
    rw [unipotent_mulVec, unipotent_mulVec, h2] at h
    have e : (![t, 0] : Fin 2 → k) =
        ![![0, 1] 0 + t * ![0, 1] 1, ![0, 1] 1] - ![0, 1] := planeVec_ext (by simp) (by simp)
    rw [e, map_sub, h, h2]
    exact planeVec_ext (by simp [mul_comm]) (by simp)
  have h4 : ∀ t : k, c ![0, t] = ![0, x 0 * t] := by
    intro t
    have h := hc sl2QuarterTurn ![-t, 0]
    rw [sl2QuarterTurn_mulVec, sl2QuarterTurn_mulVec, h3] at h
    have e : (![0, t] : Fin 2 → k) = ![![-t, 0] 1, -![-t, 0] 0] :=
      planeVec_ext (by simp) (by simp)
    rw [e, h]
    exact planeVec_ext (by simp) (by simp)
  refine ⟨x 0, fun v => ?_⟩
  have hv : v = ![v 0, 0] + ![0, v 1] := planeVec_ext (by simp) (by simp)
  rw [hv, map_add, h3, h4]
  exact planeVec_ext (by simp) (by simp)

theorem exists_isSemilinearWith_of_normalizes [Finite k] (b : Equiv.Perm (Fin 2 → k))
    (hadd : ∀ w w' : Fin 2 → k, b (w + w') = b w + b w')
    (hnorm : ∀ g : SpecialLinearGroup (Fin 2) k,
      ∃ g' : SpecialLinearGroup (Fin 2) k, b⁻¹ * slPerm k g * b = slPerm k g') :
    ∃ σ : k ≃+* k, IsSemilinearWith b σ := by
  have hadd' : ∀ w w' : Fin 2 → k, b⁻¹ (w + w') = b⁻¹ w + b⁻¹ w' := fun w w' =>
    b.injective (by simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, hadd])
  let cl : k → (Fin 2 → k) →+ (Fin 2 → k) := fun l =>
    AddMonoidHom.mk' (fun w => b (l • b⁻¹ w)) (fun w w' => by rw [hadd', smul_add, hadd])
  have hcl : ∀ l (g : SpecialLinearGroup (Fin 2) k) (v : Fin 2 → k),
      cl l ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) =
        (g : Matrix (Fin 2) (Fin 2) k).mulVec (cl l v) := by
    intro l g v
    obtain ⟨g', hg'⟩ := hnorm g
    have e1 : ∀ y, b⁻¹ ((g : Matrix (Fin 2) (Fin 2) k).mulVec (b y)) =
        (g' : Matrix (Fin 2) (Fin 2) k).mulVec y := fun y =>
      congrArg (fun e : Equiv.Perm (Fin 2 → k) => e y) hg'
    have e2 : b⁻¹ ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) =
        (g' : Matrix (Fin 2) (Fin 2) k).mulVec (b⁻¹ v) := by
      simp only [← e1, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
    have e3 : ∀ y, b ((g' : Matrix (Fin 2) (Fin 2) k).mulVec y) =
        (g : Matrix (Fin 2) (Fin 2) k).mulVec (b y) := fun y => by
      simp only [← e1, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
    show b (l • b⁻¹ _) = _ *ᵥ b (l • b⁻¹ v)
    rw [e2, ← mulVec_smul, e3]
  choose μ hμ using fun l => exists_scalar_of_commutes_sl2 (cl l) (hcl l)
  have key : ∀ l (v : Fin 2 → k), b (l • v) = μ l • b v := fun l v => by
    have := hμ l (b v)
    simpa [cl] using this
  have uniq : ∀ s t : k, (∀ v, s • b v = t • b v) → s = t := fun s t h => by
    simpa using congrFun (h (b⁻¹ (Pi.single 0 1))) 0
  have hb0 : b 0 = 0 := by
    have := hadd 0 0
    simpa using this
  let φ : k →+* k :=
    { toFun := μ
      map_one' := uniq _ _ fun v => by rw [← key, one_smul, one_smul]
      map_mul' := fun s t => uniq _ _ fun v => by rw [← key, mul_smul, key, key, mul_smul]
      map_zero' := uniq _ _ fun v => by rw [← key, zero_smul, zero_smul, hb0]
      map_add' := fun s t => uniq _ _ fun v => by rw [← key, add_smul, hadd, key, key, add_smul] }
  refine ⟨RingEquiv.ofBijective φ ⟨φ.injective, Finite.surjective_of_injective φ.injective⟩, ?_⟩
  intro l w
  exact key l w

@[expose] def columnDet (b : Equiv.Perm (Fin 2 → k)) : k :=
  b (Pi.single 0 1) 0 * b (Pi.single 1 1) 1 - b (Pi.single 0 1) 1 * b (Pi.single 1 1) 0

@[expose] def columnMat (b : Equiv.Perm (Fin 2 → k)) : Matrix (Fin 2) (Fin 2) k :=
  Matrix.of fun i j => b (Pi.single j 1) i

theorem apply_eq_of_isSemilinearWith {b : Equiv.Perm (Fin 2 → k)} {σ : k ≃+* k}
    (hadd : ∀ w w' : Fin 2 → k, b (w + w') = b w + b w') (hσ : IsSemilinearWith b σ)
    (w : Fin 2 → k) :
    b w = σ (w 0) • b (Pi.single 0 1) + σ (w 1) • b (Pi.single 1 1) := by
  have hw : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 := planeVec_ext (by simp) (by simp)
  conv_lhs => rw [hw]
  rw [hadd, hσ, hσ]

theorem columnDet_mul {a : Equiv.Perm (Fin 2 → k)} {σ : k ≃+* k}
    (hadd : ∀ w w' : Fin 2 → k, a (w + w') = a w + a w') (hσ : IsSemilinearWith a σ)
    (b : Equiv.Perm (Fin 2 → k)) : columnDet (a * b) = columnDet a * σ (columnDet b) := by
  simp only [columnDet, Equiv.Perm.mul_apply]
  rw [apply_eq_of_isSemilinearWith hadd hσ (b (Pi.single 0 1)),
    apply_eq_of_isSemilinearWith hadd hσ (b (Pi.single 1 1))]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
  ring

theorem columnDet_one : columnDet (1 : Equiv.Perm (Fin 2 → k)) = 1 := by simp [columnDet]

theorem det_columnMat (b : Equiv.Perm (Fin 2 → k)) : (columnMat b).det = columnDet b := by
  rw [det_fin_two]; simp [columnMat, columnDet]; ring

theorem columnMat_mulVec {b : Equiv.Perm (Fin 2 → k)} {σ : k ≃+* k}
    (hadd : ∀ w w' : Fin 2 → k, b (w + w') = b w + b w') (hσ : IsSemilinearWith b σ)
    (w : Fin 2 → k) : (columnMat b).mulVec (fun i => σ (w i)) = b w := by
  rw [apply_eq_of_isSemilinearWith hadd hσ w]
  ext i; fin_cases i <;> simp [columnMat, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem conj_scalar_mem_Gamma {b : Equiv.Perm (Fin 2 → k)} {σ : k ≃+* k}
    (hadd : ∀ w w' : Fin 2 → k, b (w + w') = b w + b w') (hσ : IsSemilinearWith b σ) (u : kˣ)
    (hu : ((u⁻¹ : kˣ) * σ u : k) ^ 2 * columnDet b = 1) :
    (MulAction.toPermHom kˣ (Fin 2 → k) u)⁻¹ * b * MulAction.toPermHom kˣ (Fin 2 → k) u ∈
      Gamma k := by
  set s : k := (u⁻¹ : kˣ) * σ u with hs
  have hdet : (s • columnMat b).det = 1 := by
    rw [det_smul, det_columnMat]; simpa using hu
  let A : SpecialLinearGroup (Fin 2) k := ⟨s • columnMat b, hdet⟩
  refine ⟨A, σ, ?_⟩
  ext w : 1
  show _ = (A : Matrix (Fin 2) (Fin 2) k).mulVec (fun i => σ (w i))
  rw [← map_inv]
  simp only [Equiv.Perm.mul_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Units.smul_def]
  rw [hσ, smul_smul]
  show _ = (s • columnMat b).mulVec _
  rw [smul_mulVec, columnMat_mulVec hadd hσ]

section CharTwo

variable [Finite k] [CharP k 2]

theorem exists_unit_sq_mul_eq_one (σ : k ≃+* k) {δ : k} (hδ : δ * σ δ = 1) :
    ∃ u : kˣ, ((u⁻¹ : kˣ) * σ u : k) ^ 2 * δ = 1 := by
  obtain ⟨ν, hν0, hν⟩ : ∃ ν : k, ν ≠ 0 ∧ σ ν * δ = ν := by
    by_cases h1 : δ = 1
    · exact ⟨1, one_ne_zero, by simp [h1]⟩
    · refine ⟨1 + δ, fun h => h1 ?_, ?_⟩
      · linear_combination add_self_eq_zero_of_char_two δ - h
      · rw [map_add, map_one, add_mul, one_mul, mul_comm (σ δ), hδ, add_comm]
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' ν
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hν0 (by simpa using hr)
  refine ⟨Units.mk0 r hr0, ?_⟩
  have key : σ r * σ r * δ = r * r := by rw [← map_mul, ← hr, hν]
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
  field_simp
  linear_combination key

theorem exists_unit_conj_mem_Gamma (B : Subgroup (Equiv.Perm (Fin 2 → k)))
    (hadd : ∀ b ∈ B, ∀ w w' : Fin 2 → k, b (w + w') = b w + b w')
    (hsq : ∀ a ∈ B, a * a = 1) :
    ∃ u : kˣ, ∀ b ∈ B, ∀ σ : k ≃+* k, IsSemilinearWith b σ →
      ((u⁻¹ : kˣ) * σ u : k) ^ 2 * columnDet b = 1 := by
  have hdet1 : ∀ b ∈ B, ∀ σ : k ≃+* k, IsSemilinearWith b σ →
      columnDet b * σ (columnDet b) = 1 := by
    intro b hb σ hσ
    rw [← columnDet_mul (hadd b hb) hσ, hsq b hb, columnDet_one]
  have hlin : ∀ b ∈ B, IsSemilinearWith b (1 : k ≃+* k) → columnDet b = 1 := by
    intro b hb hσ
    have h := hdet1 b hb 1 hσ
    exact CharTwo.sq_inj.1 (by rw [one_pow, sq]; simpa using h)
  by_cases hex : ∃ b ∈ B, ∃ σ : k ≃+* k, IsSemilinearWith b σ ∧ σ ≠ 1
  · obtain ⟨b₀, hb₀, σ₀, hσ₀, hne₀⟩ := hex
    have hσ₀2 : σ₀ * σ₀ = 1 := sq_eq_one_of_semilinear (hsq b₀ hb₀) hσ₀
    obtain ⟨u, hu⟩ := exists_unit_sq_mul_eq_one σ₀ (hdet1 b₀ hb₀ σ₀ hσ₀)
    refine ⟨u, fun b hb σ hσ => ?_⟩
    by_cases h1 : σ = 1
    · subst h1
      simp [hlin b hb hσ]
    · have hσ2 : σ * σ = 1 := sq_eq_one_of_semilinear (hsq b hb) hσ
      obtain rfl : σ = σ₀ := aut_involution_unique σ σ₀ hσ2 hσ₀2 h1 hne₀
      have h3 := hlin _ (mul_mem hb hb₀) (hσ2 ▸ hσ.mul hσ₀)
      rw [columnDet_mul (hadd b hb) hσ] at h3
      have h4 := hdet1 b₀ hb₀ σ hσ₀
      have hne : σ (columnDet b₀) ≠ 0 := fun h => by
        rw [h, mul_zero] at h4
        exact zero_ne_one h4
      rw [mul_right_cancel₀ hne (h3.trans h4.symm)]
      exact hu
  · push Not at hex
    refine ⟨1, fun b hb σ hσ => ?_⟩
    obtain rfl := hex b hb σ hσ
    simp [hlin b hb hσ]

theorem eq_rootPerm_of_offender_normalizer (B : Subgroup (Equiv.Perm (Fin 2 → k)))
    (hadd : ∀ b ∈ B, ∀ w w' : Fin 2 → k, b (w + w') = b w + b w')
    (hnorm : ∀ b ∈ B, ∀ g : SpecialLinearGroup (Fin 2) k,
      ∃ g' : SpecialLinearGroup (Fin 2) k, b * slPerm k g * b⁻¹ = slPerm k g')
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hsq : ∀ a ∈ B, a * a = 1) (hne : B ≠ ⊥)
    (hge : Nat.card k ^ 2 ≤ Nat.card B * Nat.card (fixSet B)) :
    ∃ ℓ : ℙ k (Fin 2 → k), B = rootPerm ℓ := by
  have hsemi : ∀ b ∈ B, ∃ σ : k ≃+* k, IsSemilinearWith b σ := fun b hb =>
    exists_isSemilinearWith_of_normalizes b (hadd b hb) fun g => by
      simpa using hnorm b⁻¹ (inv_mem hb) g
  obtain ⟨u, hu⟩ := exists_unit_conj_mem_Gamma B hadd hsq
  set c := MulAction.toPermHom kˣ (Fin 2 → k) u with hc
  have hcsl : ∀ g : SpecialLinearGroup (Fin 2) k, c * slPerm k g = slPerm k g * c := by
    intro g
    ext w : 1
    simp only [Equiv.Perm.mul_apply, hc, MulAction.toPermHom_apply, MulAction.toPerm_apply,
      Units.smul_def, slPerm_apply]
    show (u : k) • ((g : Matrix (Fin 2) (Fin 2) k) *ᵥ w) =
      (g : Matrix (Fin 2) (Fin 2) k) *ᵥ ((u : k) • w)
    rw [mulVec_smul]
  set f := (MulAut.conj c⁻¹).toMonoidHom with hf
  have hfx : ∀ x, f x = c⁻¹ * x * c := fun x => by simp [hf]
  have hfinj : Function.Injective f := (MulAut.conj c⁻¹).injective
  set B' := B.map f with hB'
  have hB'Γ : B' ≤ Gamma k := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨σ, hσ⟩ := hsemi b hb
    rw [hfx]
    exact conj_scalar_mem_Gamma (hadd b hb) hσ u (hu b hb σ hσ)
  have hcomm' : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hsq' : ∀ a ∈ B', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  have hne' : B' ≠ ⊥ := by
    rwa [hB', Ne, Subgroup.map_eq_bot_iff_of_injective _ hfinj]
  have hcard : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective hfinj
  have hfix : Nat.card (fixSet B') = Nat.card (fixSet B) := card_fixSet_map_conj B c⁻¹
  obtain ⟨hle, heq⟩ := offender_dichotomy B' hB'Γ hcomm' hsq' hne'
  obtain ⟨ℓ, hℓ⟩ := heq (le_antisymm hle (by rw [hcard, hfix]; exact hge))
  refine ⟨ℓ, ?_⟩
  have hfix_el : ∀ x ∈ B, f x = x := by
    intro x hx
    have hx' : f x ∈ rootPerm ℓ := hℓ ▸ ⟨x, hx, rfl⟩
    obtain ⟨g, -, hg⟩ := hx'
    have h := hcsl g
    rw [hg] at h
    have e : c * f x = x * c := by rw [hfx]; group
    exact mul_right_cancel (h.symm.trans e)
  rw [← hℓ]
  ext x
  constructor
  · intro hx
    exact ⟨x, hx, hfix_el x hx⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [hfix_el y hy]

end CharTwo

end CFSG.CGT.PushingUpLit.BHS
