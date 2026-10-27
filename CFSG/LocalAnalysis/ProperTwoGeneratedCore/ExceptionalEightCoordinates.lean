module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCharacterFamily

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

abbrev Coords : Type := Multiplicative (Fin 3 → ZMod 2)

theorem card_coords : Nat.card Coords = 8 := by
  rw [Nat.card_eq_fintype_card]
  rfl

section Basic

variable {U : Type*} [Group U]

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

@[simp] theorem zmod_two_val_one : (1 : ZMod 2).val = 1 := rfl

theorem pow_val_add_of_sq_eq_one {g : U} (hg : g ^ 2 = 1) (a b : ZMod 2) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 + 1 : ZMod 2) = 0 by decide, ZMod.val_zero, pow_zero, ZMod.val_one, pow_one,
      ← pow_two, hg]

theorem sq_eq_one_of_isElementaryAbelian [IsElementaryAbelian 2 U] (g : U) : g ^ 2 = 1 :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 U) g

theorem inv_eq_self_of_isElementaryAbelian [IsElementaryAbelian 2 U] (g : U) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, sq_eq_one_of_isElementaryAbelian])

theorem mul_comm_of_isElementaryAbelian [IsElementaryAbelian 2 U] (g h : U) : g * h = h * g :=
  (IsMulCommutative.is_comm (M := U)).comm g h

@[expose] def Independent (x : Fin 3 → U) : Prop :=
  ∀ a b c : ZMod 2, x 0 ^ a.val * x 1 ^ b.val * x 2 ^ c.val = 1 → a = 0 ∧ b = 0 ∧ c = 0

variable [IsElementaryAbelian 2 U]

@[expose] def coordHom (x : Fin 3 → U) : Coords →* U where
  toFun v := x 0 ^ (v.toAdd 0).val * x 1 ^ (v.toAdd 1).val * x 2 ^ (v.toAdd 2).val
  map_one' := by simp
  map_mul' v w := by
    let _ : CommGroup U := IsMulCommutative.instCommGroup
    simp only [toAdd_mul, Pi.add_apply,
      pow_val_add_of_sq_eq_one (sq_eq_one_of_isElementaryAbelian _)]
    ac_rfl

theorem coordHom_apply (x : Fin 3 → U) (v : Coords) :
    coordHom x v = x 0 ^ (v.toAdd 0).val * x 1 ^ (v.toAdd 1).val * x 2 ^ (v.toAdd 2).val := rfl

theorem coordHom_single (x : Fin 3 → U) (i : Fin 3) :
    coordHom x (Multiplicative.ofAdd (Pi.single i 1)) = x i := by
  fin_cases i <;> simp [coordHom_apply]

theorem coordHom_injective {x : Fin 3 → U} (hx : Independent x) :
    Function.Injective (coordHom x) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  obtain ⟨h0, h1, h2⟩ := hx _ _ _ hv
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

@[expose] noncomputable def coordEquiv {x : Fin 3 → U} (hx : Independent x) (hcard : Nat.card U = 8) :
    Coords ≃* U :=
  MulEquiv.ofBijective (coordHom x) <| by
    have : Finite U := Nat.finite_of_card_ne_zero (by omega)
    exact (Function.Injective.bijective_of_nat_card_le (coordHom_injective hx)
      (by rw [card_coords, hcard]))

theorem coordEquiv_apply {x : Fin 3 → U} (hx : Independent x) (hcard : Nat.card U = 8)
    (v : Coords) : coordEquiv hx hcard v = coordHom x v := rfl

theorem coordEquiv_single {x : Fin 3 → U} (hx : Independent x) (hcard : Nat.card U = 8)
    (i : Fin 3) : coordEquiv hx hcard (Multiplicative.ofAdd (Pi.single i 1)) = x i :=
  coordHom_single x i

theorem exists_coords {x : Fin 3 → U} (hx : Independent x) (hcard : Nat.card U = 8) (g : U) :
    ∃ a b c : ZMod 2, x 0 ^ a.val * x 1 ^ b.val * x 2 ^ c.val = g := by
  obtain ⟨v, rfl⟩ := (coordEquiv hx hcard).surjective g
  exact ⟨_, _, _, rfl⟩

theorem hom_ext_of_independent {V : Type*} [Group V] {x : Fin 3 → U} (hx : Independent x)
    (hcard : Nat.card U = 8) {f g : U →* V} (h : ∀ i, f (x i) = g (x i)) : f = g := by
  ext u
  obtain ⟨a, b, c, rfl⟩ := exists_coords hx hcard u
  simp only [map_mul, map_pow, h]

theorem mulAut_ext_of_independent {x : Fin 3 → U} (hx : Independent x) (hcard : Nat.card U = 8)
    {σ τ : MulAut U} (h : ∀ i, σ (x i) = τ (x i)) : σ = τ := by
  have hhom := hom_ext_of_independent hx hcard (f := σ.toMonoidHom) (g := τ.toMonoidHom) h
  ext u
  exact DFunLike.congr_fun hhom u

@[expose] noncomputable def basisAut {x y : Fin 3 → U} (hx : Independent x) (hy : Independent y)
    (hcard : Nat.card U = 8) : MulAut U :=
  (coordEquiv hx hcard).symm.trans (coordEquiv hy hcard)

theorem basisAut_apply {x y : Fin 3 → U} (hx : Independent x) (hy : Independent y)
    (hcard : Nat.card U = 8) (i : Fin 3) : basisAut hx hy hcard (x i) = y i := by
  change coordEquiv hy hcard ((coordEquiv hx hcard).symm (x i)) = y i
  rw [← coordEquiv_single hx hcard i, MulEquiv.symm_apply_apply, coordEquiv_single]

theorem independent_of_ne {x : Fin 3 → U} (h0 : x 0 ≠ 1) (h1 : x 1 ≠ 1) (h10 : x 1 ≠ x 0)
    (h2 : x 2 ≠ 1) (h20 : x 2 ≠ x 0) (h21 : x 2 ≠ x 1) (h201 : x 2 ≠ x 0 * x 1) :
    Independent x := by
  have hinv : ∀ g : U, g⁻¹ = g := inv_eq_self_of_isElementaryAbelian
  intro a b c habc
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    rcases zmod_two_cases c with rfl | rfl <;>
    simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul, mul_one] at habc
  · exact ⟨rfl, rfl, rfl⟩
  · exact absurd habc h2
  · exact absurd habc h1
  · exact absurd ((eq_inv_of_mul_eq_one_right habc).trans (hinv _)) h21
  · exact absurd habc h0
  · exact absurd ((eq_inv_of_mul_eq_one_right habc).trans (hinv _)) h20
  · exact absurd ((eq_inv_of_mul_eq_one_right habc).trans (hinv _)) h10
  · exact absurd ((eq_inv_of_mul_eq_one_right habc).trans (hinv _)) h201

end Basic

section Automorphisms

theorem nonempty_mulAut_mulEquiv_GL {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    {n : ℕ} (hcard : Nat.card A = 2 ^ n) : Nonempty (MulAut A ≃* GL (Fin n) (ZMod 2)) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  let Q := Additive A
  let _ : AddCommGroup Q := Additive.addCommGroup
  let _ : Module (ZMod 2) Q := inferInstance
  let _ : Finite Q := inferInstance
  let _ : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  let eAdd : MulAut A ≃* Multiplicative (AddAut Q) :=
    (AddAutAdditive A).toMultiplicative.symm
  let eAddLin : Multiplicative (AddAut Q) ≃* (Q ≃ₗ[ZMod 2] Q) :=
    { toFun := fun a =>
        (a : AddAut Q).toLinearEquiv (fun c x => by
          change (a : AddAut Q).toAddMonoidHom (c • x) =
            c • (a : AddAut Q).toAddMonoidHom x
          exact ZMod.map_smul (a : AddAut Q).toAddMonoidHom c x)
      invFun := fun a => Multiplicative.ofAdd a.toAddEquiv
      left_inv := by
        intro a
        apply Multiplicative.toAdd.injective
        ext x
        rfl
      right_inv := by
        intro a
        ext x
        rfl
      map_mul' := by
        intro a b
        ext x
        rfl }
  let eLin : MulAut A ≃* LinearMap.GeneralLinearGroup (ZMod 2) Q :=
    (eAdd.trans eAddLin).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Q).symm
  let m := Module.finrank (ZMod 2) Q
  let basis : Module.Basis (Fin m) (ZMod 2) Q := Module.finBasis (ZMod 2) Q
  let eMatrix : MulAut A ≃* GL (Fin m) (ZMod 2) :=
    eLin.trans (Matrix.GeneralLinearGroup.toLin' basis).symm
  have hcardQ : Nat.card Q = 2 ^ m := by
    simpa [Q, m, ZMod.card] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Q))
  have hm : m = n := by
    have hpow : 2 ^ m = 2 ^ n := hcardQ.symm.trans (by
      simpa [Q] using (Nat.card_congr (Additive.ofMul (α := A))).symm.trans hcard)
    exact Nat.pow_right_injective (le_refl 2) hpow
  exact ⟨hm ▸ eMatrix⟩

theorem card_mulAut_eq_168 {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 8) : Nat.card (MulAut A) = 168 := by
  obtain ⟨e⟩ := nonempty_mulAut_mulEquiv_GL (A := A) (n := 3) (by rw [hcard]; norm_num)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_succ]

end Automorphisms

section Existence

variable {U : Type*} [Group U] [IsElementaryAbelian 2 U]

theorem exists_not_mem_finset_of_card_lt {V : Type*} [Finite V] (s : Finset V)
    (h : s.card < Nat.card V) : ∃ x : V, x ∉ s := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s) (t := Finset.univ)
    (by rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
  exact ⟨e, he⟩

theorem exists_independent (hcard : Nat.card U = 8) : ∃ x : Fin 3 → U, Independent x := by
  classical
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨x0, hx0⟩ := exists_not_mem_finset_of_card_lt ({1} : Finset U) (by
    rw [hcard, Finset.card_singleton]; omega)
  obtain ⟨x1, hx1⟩ := exists_not_mem_finset_of_card_lt ({1, x0} : Finset U) (by
    rw [hcard]; exact (Finset.card_le_two).trans_lt (by omega))
  obtain ⟨x2, hx2⟩ := exists_not_mem_finset_of_card_lt ({1, x0, x1, x0 * x1} : Finset U) (by
    rw [hcard]; exact (Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx0 hx1 hx2
  refine ⟨![x0, x1, x2], independent_of_ne ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> tauto

end Existence

section Dihedral

@[expose] def coordsInvolution (f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (hadd : ∀ v w, f (v + w) = f v + f w) (hinv : ∀ v, f (f v) = v) : MulAut Coords where
  toFun v := Multiplicative.ofAdd (f v.toAdd)
  invFun v := Multiplicative.ofAdd (f v.toAdd)
  left_inv v := by simp [hinv]
  right_inv v := by simp [hinv]
  map_mul' v w := by simp [hadd]

@[expose] def coordsS : MulAut Coords :=
  coordsInvolution (fun v => ![v 0 + v 1, v 1, v 2]) (by decide) (by decide)

@[expose] def coordsT : MulAut Coords :=
  coordsInvolution (fun v => ![v 0, v 1 + v 2, v 2]) (by decide) (by decide)

theorem coordsST_pow_four : (coordsS * coordsT) ^ 4 = 1 :=
  MulEquiv.ext (by decide)

theorem coordsS_mul_self : coordsS * coordsS = 1 :=
  MulEquiv.ext (by decide)

theorem coordsS_conj : coordsS * (coordsS * coordsT) * coordsS = (coordsS * coordsT)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  exact MulEquiv.ext (by decide)

@[expose] def dihedralCoords : DihedralGroup 4 →* MulAut Coords :=
  CFSG.Semidihedral.Principal.dihedralWordHom (coordsS * coordsT) coordsS 4 coordsST_pow_four
    coordsS_mul_self coordsS_conj

theorem dihedralCoords_injective : Function.Injective dihedralCoords := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have key : ∀ x : DihedralGroup 4, (∀ v : Coords, dihedralCoords x v = v) → x = 1 := by
    decide
  exact key x (fun v => by rw [hx]; rfl)

theorem exists_dihedral_subgroup_mulAut {U : Type*} [Group U] [IsElementaryAbelian 2 U]
    (hcard : Nat.card U = 8) : ∃ P : Subgroup (MulAut U), Nonempty (P ≃* DihedralGroup 4) := by
  obtain ⟨x, hx⟩ := exists_independent hcard
  let φ : DihedralGroup 4 →* MulAut U :=
    (MulAut.congr (coordEquiv hx hcard)).toMonoidHom.comp dihedralCoords
  have hφ : Function.Injective φ :=
    (MulAut.congr (coordEquiv hx hcard)).injective.comp dihedralCoords_injective
  exact ⟨φ.range, ⟨(MonoidHom.ofInjective hφ).symm⟩⟩

end Dihedral

section Transvection

variable {U : Type*} [Group U] [IsElementaryAbelian 2 U]

theorem exists_transvection_basis (hcard : Nat.card U = 8) {a : MulAut U} (ha1 : a ≠ 1)
    (ha2 : a * a = 1) :
    ∃ x : Fin 3 → U, Independent x ∧ a (x 0) = x 0 ∧ a (x 1) = x 0 * x 1 ∧ a (x 2) = x 2 := by
  classical
  let _ : CommGroup U := IsMulCommutative.instCommGroup
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have hinv : ∀ g : U, g⁻¹ = g := inv_eq_self_of_isElementaryAbelian
  have hsq : ∀ g : U, g * g = 1 := fun g => by rw [← pow_two, sq_eq_one_of_isElementaryAbelian]
  have haa : ∀ z, a (a z) = z := fun z => by
    have h := congrArg (fun σ : MulAut U => σ z) ha2
    simpa using h
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : U, a w₀ ≠ w₀ := by
    by_contra h
    push Not at h
    exact ha1 (MulEquiv.ext h)
  set e₀ := w₀⁻¹ * a w₀ with he₀
  have hae₀ : a e₀ = e₀ := by
    rw [he₀, map_mul, map_inv, haa, hinv, hinv, mul_comm]
  have haw₀ : a w₀ = e₀ * w₀ := by
    rw [he₀, hinv, mul_comm w₀, mul_assoc, hsq, mul_one]
  have he₀1 : e₀ ≠ 1 := by
    intro h
    apply hw₀
    rw [haw₀, h, one_mul]
  have hw₀1 : w₀ ≠ 1 := by
    rintro rfl
    exact hw₀ (map_one a)
  have hw₀e₀ : w₀ ≠ e₀ := by
    rintro h
    apply hw₀
    rw [h, hae₀]
  have he₀w₀ : a (e₀ * w₀) ≠ e₀ * w₀ := by
    rw [map_mul, hae₀, haw₀, ← mul_assoc, hsq, one_mul]
    intro h
    apply he₀1
    calc e₀ = e₀ * w₀ * w₀ := by rw [mul_assoc, hsq, mul_one]
      _ = w₀ * w₀ := by rw [← h]
      _ = 1 := hsq w₀
  obtain ⟨z₁, hz₁⟩ := exists_not_mem_finset_of_card_lt ({1, e₀, w₀, e₀ * w₀} : Finset U) (by
    rw [hcard]; exact (Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz₁
  obtain ⟨hz1, hz0, hzw, hz0w⟩ := hz₁
  obtain ⟨e₂, hae₂, he₂1, he₂0⟩ : ∃ e₂ : U, a e₂ = e₂ ∧ e₂ ≠ 1 ∧ e₂ ≠ e₀ := by
    set g := z₁⁻¹ * a z₁ with hg
    have hag : a g = g := by
      rw [hg, map_mul, map_inv, haa, hinv, hinv, mul_comm]
    by_cases hg1 : g = 1
    · refine ⟨z₁, ?_, hz1, hz0⟩
      rw [hg, hinv] at hg1
      calc a z₁ = z₁ * (z₁ * a z₁) := by rw [← mul_assoc, hsq, one_mul]
        _ = z₁ := by rw [hg1, mul_one]
    by_cases hg0 : g = e₀
    · refine ⟨w₀ * z₁, ?_, ?_, ?_⟩
      · have haz : a z₁ = z₁ * e₀ := by
          rw [← hg0, hg, hinv, ← mul_assoc, hsq, one_mul]
        rw [map_mul, haw₀, haz]
        calc e₀ * w₀ * (z₁ * e₀) = w₀ * z₁ * (e₀ * e₀) := by ac_rfl
          _ = w₀ * z₁ := by rw [hsq, mul_one]
      · intro h
        apply hzw
        calc z₁ = w₀ * (w₀ * z₁) := by rw [← mul_assoc, hsq, one_mul]
          _ = w₀ := by rw [h, mul_one]
      · intro h
        apply hz0w
        calc z₁ = w₀ * (w₀ * z₁) := by rw [← mul_assoc, hsq, one_mul]
          _ = e₀ * w₀ := by rw [h, mul_comm]
    · exact ⟨g, hag, hg1, hg0⟩
  refine ⟨![e₀, w₀, e₂], independent_of_ne ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · exact he₀1
  · exact hw₀1
  · exact hw₀e₀
  · exact he₂1
  · exact he₂0
  · intro h
    apply hw₀
    change e₂ = w₀ at h
    rw [← h, hae₂]
  · intro h
    apply he₀w₀
    change e₂ = e₀ * w₀ at h
    rw [← h, hae₂]
  · exact hae₀
  · exact haw₀
  · exact hae₂

end Transvection

section OrderFour

@[expose] def coordsAut (f g : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (hadd : ∀ v w, f (v + w) = f v + f w) (hfg : ∀ v, f (g v) = v) (hgf : ∀ v, g (f v) = v) :
    MulAut Coords where
  toFun v := Multiplicative.ofAdd (f v.toAdd)
  invFun v := Multiplicative.ofAdd (g v.toAdd)
  left_inv v := by simp [hgf]
  right_inv v := by simp [hfg]
  map_mul' v w := by simp [hadd]

@[expose] def coordsB : MulAut Coords :=
  coordsAut (fun v => ![v 0 + v 2, v 1, v 1 + v 2]) (fun v => ![v 0 + v 1 + v 2, v 1, v 1 + v 2])
    (by decide) (by decide) (by decide)

theorem coordsB_mul_self : coordsB * coordsB = coordsS :=
  MulEquiv.ext (by decide)

@[expose] def coordsCorrection (v : Coords) : Coords :=
  Multiplicative.ofAdd ![0, v.toAdd 2, 0]

theorem coordsCorrection_spec :
    ∀ v : Coords, coordsS v = v → v * coordsS (coordsCorrection v) = coordsCorrection v * coordsB v := by
  decide

theorem coordsB_square_norm :
    ∀ v : Coords, v * coordsB v * coordsS (v * coordsB v) = 1 := by
  decide

end OrderFour

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
