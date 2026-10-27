module

public import CFSG.LieType.SpecialLinear.EndNode.Radicals

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Universal.SpecialLinear

noncomputable section

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

@[expose] def endSwap : Equiv.Perm (Fin (m+2)) :=
  Equiv.swap 0 (Fin.last (m+1))

@[expose] def endSigns : Fin (m+2) → F :=
  fun i => if i = 0 then -1 else 1

omit [Finite F] in
private theorem endSigns_sq (i : Fin (m+2)) : endSigns m F i * endSigns m F i = 1 := by
  unfold endSigns
  split_ifs <;> ring

omit [Finite F] in
private theorem prod_endSigns : (∏ i : Fin (m+2), endSigns m F i) = -1 := by
  rw [Fintype.prod_eq_single (0 : Fin (m+2))]
  · simp [endSigns]
  · intro b hb
    simp [endSigns, hb]

omit [Finite F] in
private theorem signedPerm_endSigns_eq_permMatrix_mul_diagonal :
    signedPerm (endSwap m) (endSigns m F) =
      ((endSwap m)⁻¹).permMatrix F * diagonal (endSigns m F) := by
  ext a b
  rw [Matrix.mul_diagonal, signedPerm_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, Equiv.Perm.inv_eq_iff_eq]
  split_ifs <;> simp

omit [Finite F] in
theorem det_endSigns : (signedPerm (endSwap m) (endSigns m F)).det = 1 := by
  rw [signedPerm_endSigns_eq_permMatrix_mul_diagonal, Matrix.det_mul,
    Matrix.det_permutation, Matrix.det_diagonal, Equiv.Perm.sign_inv]
  unfold endSwap
  rw [Equiv.Perm.sign_swap (by simp)]
  rw [prod_endSigns]
  norm_num

@[expose] def endMonomial : SLm2 m F :=
  ⟨signedPerm (endSwap m) (endSigns m F), det_endSigns m F⟩

omit [Finite F] in
@[simp] theorem coe_endMonomial :
    (endMonomial m F : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      signedPerm (endSwap m) (endSigns m F) := rfl

omit [Finite F] in
private theorem coe_inv_endMonomial :
    (((endMonomial m F)⁻¹ : SLm2 m F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      signedPerm (endSwap m)⁻¹ (fun s => endSigns m F ((endSwap m)⁻¹ s)) := by
  apply inv_coe_signedPerm (n := m+2) (g := endMonomial m F)
    (π := endSwap m) (ε := endSigns m F) (by rfl)
  exact endSigns_sq m F

omit [Finite F] in
omit [Finite F] in
private theorem map_conj_signedPerm_colRadical_le {b : Fin (m+2)}
    {π : Equiv.Perm (Fin (m+2))} {ε : Fin (m+2) → F} {g : SLm2 m F}
    (hg : (g : Matrix (Fin (m+2)) (Fin (m+2)) F) = signedPerm π ε)
    (hε : ∀ i, ε i * ε i = 1) :
    (colRadical m F b).map (MulAut.conj g).toMonoidHom ≤
      colRadical m F (π b) := by
  rintro x ⟨a, ha, rfl⟩
  change (g * a * g⁻¹ : SLm2 m F) ∈ colRadical m F (π b)
  rw [mem_colRadical]
  constructor
  · have h := conj_signedPerm_coe (m := m+1) (F := F) (π := π) (ε := ε)
      (g := g) (by simpa using hg) (by simpa using hε) a (π b) (π b)
    rw [h]
    change ε (π.symm (π b)) *
      (a : Matrix (Fin (m+2)) (Fin (m+2)) F) (π.symm (π b)) (π.symm (π b)) *
      ε (π.symm (π b)) = 1
    rw [Equiv.symm_apply_apply]
    rw [ha.1, mul_one, hε]
  · intro i j hj
    have h := conj_signedPerm_coe (m := m+1) (F := F) (π := π) (ε := ε)
      (g := g) (by simpa using hg) (by simpa using hε) a i j
    rw [h]
    change ε (π.symm i) * (a : Matrix (Fin (m+2)) (Fin (m+2)) F) (π.symm i)
        (π.symm j) * ε (π.symm j) =
      (1 : Matrix (Fin (m+2)) (Fin (m+2)) F) i j
    have hj' : π.symm j ≠ b := by
      intro hbij
      apply hj
      rw [← hbij, Equiv.apply_symm_apply]
    by_cases hij : i = j
    · subst hij
      rw [ha.2 (π.symm i) (π.symm i) hj']
      simp [Matrix.one_apply_eq, hε]
    · have hne : π.symm i ≠ π.symm j := fun h' => hij (π.symm.injective h')
      rw [ha.2 (π.symm i) (π.symm j) hj']
      simp [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]

omit [Finite F] in
private theorem map_conj_signedPerm_colRadical {b : Fin (m+2)}
    {π : Equiv.Perm (Fin (m+2))} {ε : Fin (m+2) → F} {g : SLm2 m F}
    (hg : (g : Matrix (Fin (m+2)) (Fin (m+2)) F) = signedPerm π ε)
    (hε : ∀ i, ε i * ε i = 1) :
    (colRadical m F b).map (MulAut.conj g).toMonoidHom =
      colRadical m F (π b) := by
  refine le_antisymm (map_conj_signedPerm_colRadical_le m F hg hε) ?_
  intro x hx
  have hg_inv : ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      signedPerm π⁻¹ (fun s => ε (π⁻¹ s)) :=
    inv_coe_signedPerm (n := m+2) (g := g) (π := π) (ε := ε) hg hε
  have hε_inv : ∀ s, ε (π⁻¹ s) * ε (π⁻¹ s) = 1 := fun s => hε _
  have hle := map_conj_signedPerm_colRadical_le (m := m) (F := F)
    (b := π b) (π := π⁻¹) (ε := fun s => ε (π⁻¹ s)) (g := g⁻¹)
    (by simpa using hg_inv) (by simpa using hε_inv)
  have hle' : (colRadical m F (π b)).map
      (MulAut.conj g⁻¹).toMonoidHom ≤ colRadical m F b := by
    simpa [Equiv.symm_apply_apply] using hle
  have ha : g⁻¹ * x * g ∈ colRadical m F b := by
    apply hle'
    have hx' := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx
    change (MulAut.conj g⁻¹) x ∈
      (colRadical m F (π b)).map (MulAut.conj g⁻¹).toMonoidHom at hx'
    simpa [MulAut.conj_apply] using hx' 
  exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ha, by
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group⟩

theorem endSwap_zero : endSwap m (0 : Fin (m+2)) = Fin.last (m+1) := by
  simp [endSwap]

omit [Finite F] in
theorem map_conj_endMonomial_firstCol :
    (firstColRadical m F).map
      (MulAut.conj (endMonomial m F)).toMonoidHom = lastColRadical m F := by
  change (colRadical m F 0).map
      (MulAut.conj (endMonomial m F)).toMonoidHom =
    colRadical m F (Fin.last (m+1))
  rw [← endSwap_zero m]
  exact map_conj_signedPerm_colRadical (m := m) (F := F) (b := 0)
    (π := endSwap m) (ε := endSigns m F) (g := endMonomial m F)
    (by rfl) (endSigns_sq m F)


end

end CFSG.LieType.SpecialLinear
