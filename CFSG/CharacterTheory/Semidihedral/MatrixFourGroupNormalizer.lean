module

public import CFSG.CharacterTheory.Semidihedral.MatrixTorus

public section

namespace CFSG.Semidihedral.MatrixFourGroupNormalizer

noncomputable section

open Matrix
open CFSG.Semidihedral.MatrixCoverData
open CFSG.Semidihedral.MatrixCover

universe u v

variable (F : Type u) [Field F]

@[expose] def fixedCoefficient (A : Subgroup (F ≃+* F)) (a : Fˣ)
    (ha : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) : (FixedField F A)ˣ :=
  Units.mk0 (⟨(a : F), ha⟩ : FixedField F A) (by
    intro h
    exact a.ne_zero (congrArg Subtype.val h))

theorem fixedCoefficient_literal (A : Subgroup (F ≃+* F)) (a : Fˣ)
    (ha : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) :
    fixedUnit F A (fixedCoefficient F A a ha) = a := Units.ext rfl

theorem scaled_two_squares [Finite F] (hodd : Odd (Nat.card F))
    (a : F) (ha : a ≠ 0) (c : F) : ∃ x y : F, x ^ 2 + a * y ^ 2 = c := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let f : Polynomial F := Polynomial.X ^ 2 - Polynomial.C c
  let g : Polynomial F := Polynomial.C a * Polynomial.X ^ 2
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := f) (g := g) (Polynomial.degree_X_pow_sub_C (by decide) c)
    (Polynomial.degree_C_mul_X_pow 2 ha)
    (Nat.odd_iff.mp (by simpa only [Nat.card_eq_fintype_card] using hodd))
  refine ⟨x, y, ?_⟩
  have h : x ^ 2 - c + a * y ^ 2 = 0 := by
    simpa only [f, g, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_mul] using hxy
  linear_combination h

theorem fixed_field_odd [Finite F] (A : Subgroup (F ≃+* F))
    (hF : Odd (Nat.card F)) (hA : Odd (Nat.card A)) :
    Odd (Nat.card (FixedField F A)) := by
  apply (Nat.odd_pow_iff hA.pos.ne').mp
  rw [← FixedFieldData.nat_card_eq_fixedSubfield_card_pow F A]
  exact hF

theorem exists_fixed_pair [Finite F] (A : Subgroup (F ≃+* F))
    (hF : Odd (Nat.card F)) (hA : Odd (Nat.card A)) (a : (FixedField F A)ˣ) :
    ∃ x y : FixedField F A, x ^ 2 + (a : FixedField F A) * y ^ 2 = -1 :=
  scaled_two_squares (FixedField F A) (fixed_field_odd F A hF hA) a a.ne_zero (-1)

@[expose] def xMatrix (a : Fˣ) (x y : F) : Matrix (Fin 2) (Fin 2) F :=
  !![x, (a : F) * y; y, -x]

theorem xMatrix_det (a : Fˣ) (x y : F) :
    (xMatrix F a x y).det = -(x ^ 2 + (a : F) * y ^ 2) := by
  simp [xMatrix, Matrix.det_fin_two]
  ring

@[expose] def nativeX (a : Fˣ) (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    SL F := ⟨xMatrix F a x y, by rw [xMatrix_det, hxy, neg_neg]⟩

theorem nativeX_matrix (a : Fˣ) (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    (nativeX F a x y hxy : Matrix (Fin 2) (Fin 2) F) =
      !![x, (a : F) * y; y, -x] := rfl

theorem nativeX_square (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    nativeX F a x y hxy ^ 2 = OddFieldSL2.minusIdentity F := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((nativeX F a x y hxy ^ 2 : SL F) : Matrix (Fin 2) (Fin 2) F) i j =
    (OddFieldSL2.minusIdentity F : Matrix (Fin 2) (Fin 2) F) i j
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
  fin_cases i <;> fin_cases j <;>
    simp [nativeX, xMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      OddFieldSL2.minusIdentity] <;>
      first | (solve | convert hxy using 1 <;> ring) | ring

theorem nativeX_anticommutes (a : Fˣ) (x y : F) :
    xMatrix F a x y * (J F a : Matrix (Fin 2) (Fin 2) F) =
      -(J F a : Matrix (Fin 2) (Fin 2) F) * xMatrix F a x y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMatrix, J_matrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem nativeX_inv (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    (nativeX F a x y hxy)⁻¹ = OddFieldSL2.minusIdentity F * nativeX F a x y hxy := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [mul_assoc, ← pow_two, nativeX_square, ← pow_two]
  exact OddFieldSL2.minusIdentity_square F

theorem nativeX_order [Finite F] (hF : Odd (Nat.card F)) (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : orderOf (nativeX F a x y hxy) = 4 := by
  have hfour : nativeX F a x y hxy ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, nativeX_square]
    exact OddFieldSL2.minusIdentity_square F
  have htwo : nativeX F a x y hxy ^ 2 ≠ 1 := by
    rw [nativeX_square]
    exact OddFieldSL2.minusIdentity_ne_one F (OddFieldSL2.two_ne_zero_of_odd_card F hF)
  have hdvd := orderOf_dvd_of_pow_eq_one hfour
  have hp := (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by decide, hfour⟩).orderOf_pos
  have hlt : orderOf (nativeX F a x y hxy) ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hcases : orderOf (nativeX F a x y hxy) = 1 ∨
      orderOf (nativeX F a x y hxy) = 2 ∨ orderOf (nativeX F a x y hxy) = 4 := by
    interval_cases h : orderOf (nativeX F a x y hxy) <;> simp_all
  rcases hcases with h | h | h
  · have hx := pow_orderOf_eq_one (nativeX F a x y hxy)
    rw [h, pow_one] at hx
    exact False.elim (htwo (by rw [hx, one_pow]))
  · have hx := pow_orderOf_eq_one (nativeX F a x y hxy)
    rw [h] at hx
    exact False.elim (htwo hx)
  · exact h


theorem beta_nativeX (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    beta F a (nativeX F a x y hxy) = (nativeX F a x y hxy)⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [beta, slConjugation_toGL]
  have hInv : (((nativeX F a x y hxy)⁻¹ : SL F) : Matrix (Fin 2) (Fin 2) F) =
      !![-x, -(a : F) * y; -y, x] := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nativeX, xMatrix]
  have hmat : (MatrixCoverData.J F a : Matrix (Fin 2) (Fin 2) F) *
      (nativeX F a x y hxy : Matrix (Fin 2) (Fin 2) F) =
      (((nativeX F a x y hxy)⁻¹ : SL F) : Matrix (Fin 2) (Fin 2) F) *
        (MatrixCoverData.J F a : Matrix (Fin 2) (Fin 2) F) := by
    rw [hInv, nativeX_matrix, MatrixCoverData.J_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have h : MatrixCoverData.J F a * Matrix.SpecialLinearGroup.toGL (nativeX F a x y hxy) =
      Matrix.SpecialLinearGroup.toGL ((nativeX F a x y hxy)⁻¹) * MatrixCoverData.J F a :=
    Units.ext hmat

  rw [h]
  group

theorem nativeX_field_fixed (sigma : F ≃+* F) (a : Fˣ) (x y : F)
    (ha : sigma (a : F) = a) (hx : sigma x = x) (hy : sigma y = y)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    Matrix.SpecialLinearGroup.map sigma.toRingHom (nativeX F a x y hxy) =
      nativeX F a x y hxy := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((Matrix.SpecialLinearGroup.map sigma.toRingHom (nativeX F a x y hxy) : SL F) :
    Matrix (Fin 2) (Fin 2) F) i j = (nativeX F a x y hxy : Matrix (Fin 2) (Fin 2) F) i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [nativeX, xMatrix, ha, hx, hy]

@[expose] def xInM (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : M F a :=
  inclusion F a (nativeX F a x y hxy)

@[expose] def zInM (a : Fˣ) : M F a := inclusion F a (OddFieldSL2.minusIdentity F)

theorem xInM_square (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : xInM F a x y hxy ^ 2 = zInM F a := by
  rw [xInM, ← map_pow, nativeX_square]
  rfl

theorem u_inverts_xInM (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    u F a * xInM F a x y hxy * (u F a)⁻¹ = (xInM F a x y hxy)⁻¹ := by
  change SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) *
    SemidirectProduct.inl (nativeX F a x y hxy) *
    (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) : M F a)⁻¹ = _
  rw [← map_inv, ← SemidirectProduct.inl_aut, MatrixCoverData.action_one, beta_nativeX]
  exact map_inv (inclusion F a) (nativeX F a x y hxy)

theorem xInM_conjugates_u (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    xInM F a x y hxy * u F a * (xInM F a x y hxy)⁻¹ = zInM F a * u F a := by
  have h := u_inverts_xInM F a x y hxy
  have h' : u F a * (xInM F a x y hxy)⁻¹ = xInM F a x y hxy * u F a := by
    have hc := congrArg (fun g : M F a => g⁻¹ * u F a) h
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel, mul_one] using hc
  calc
    xInM F a x y hxy * u F a * (xInM F a x y hxy)⁻¹ =
        (xInM F a x y hxy) ^ 2 * u F a := by
      rw [mul_assoc, h', pow_two]
      group
    _ = zInM F a * u F a := by rw [xInM_square]

@[expose] def generatedDihedral {G : Type u} [Group G] (r s : G) : Subgroup G :=
  Subgroup.zpowers r ⊔ Subgroup.zpowers s

theorem generatedDihedral_equiv {G : Type u} [Group G] [Finite G]
    (r s : G) (hr : orderOf r = 4) (hs : s ^ 2 = 1)
    (hrel : s * r * s⁻¹ = r⁻¹) (hnot : s ∉ Subgroup.zpowers r) :
    Nonempty (generatedDihedral r s ≃* DihedralGroup 4) := by
  let D := generatedDihedral r s
  let r0 : D := ⟨r, Subgroup.mem_sup_left (Subgroup.mem_zpowers r)⟩
  let s0 : D := ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩
  have hgen : (⊤ : Subgroup D) = Subgroup.zpowers r0 ⊔ Subgroup.zpowers s0 := by
    apply le_antisymm
    · intro d _
      have hm : (d : G) ∈ (Subgroup.zpowers r0 ⊔ Subgroup.zpowers s0).map D.subtype := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        change (d : G) ∈ Subgroup.zpowers r ⊔ Subgroup.zpowers s
        exact d.property
      obtain ⟨k, hk, hkd⟩ := Subgroup.mem_map.mp hm
      exact (Subtype.ext hkd : k = d) ▸ hk
    · exact le_top
  have hr0 : orderOf r0 = 4 := by
    rw [← orderOf_injective D.subtype D.subtype_injective r0]
    exact hr
  have hs0 : s0 ^ 2 = 1 := Subtype.ext hs
  have hrel0 : s0 * r0 * s0⁻¹ = r0⁻¹ := Subtype.ext hrel
  have hnot0 : s0 ∉ Subgroup.zpowers r0 := by
    intro h
    apply hnot
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, congrArg Subtype.val hi⟩
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem r0 s0 hgen hs0 hrel0 hnot0
  rw [hr0] at h
  exact h

theorem xInM_order [Finite F] (hF : Odd (Nat.card F)) (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : orderOf (xInM F a x y hxy) = 4 := by
  exact (orderOf_injective (inclusion F a) (inclusion_injective F a) _).trans
    (nativeX_order F hF a x y hxy)

theorem u_not_mem_xInM_zpowers (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    u F a ∉ Subgroup.zpowers (xInM F a x y hxy) := by
  intro h
  have hx : xInM F a x y hxy ∈ (SemidirectProduct.rightHom : M F a →* C2).ker := rfl
  have hz : Subgroup.zpowers (xInM F a x y hxy) ≤
      (SemidirectProduct.rightHom : M F a →* C2).ker := Subgroup.zpowers_le_of_mem hx
  have hc : (Multiplicative.ofAdd (1 : ZMod 2) : C2) = 1 := hz h
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2) : C2) ≠ 1) hc

theorem matrix_dihedral_eight [Finite F] (hF : Odd (Nat.card F)) (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    Nonempty (generatedDihedral (xInM F a x y hxy) (u F a) ≃* DihedralGroup 4) ∧
    Nat.card (generatedDihedral (xInM F a x y hxy) (u F a)) = 8 := by
  let : Finite (M F a) := Finite.of_equiv (SL F × C2)
    SemidirectProduct.equivProd.symm
  have he := generatedDihedral_equiv (xInM F a x y hxy) (u F a)
    (xInM_order F hF a x y hxy) (u_square F a) (u_inverts_xInM F a x y hxy)
    (u_not_mem_xInM_zpowers F a x y hxy)
  refine ⟨he, ?_⟩
  obtain ⟨e⟩ := he
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem nativeX_inverts_coordinates (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) (Y : SL F)
    (h01 : (Y : Matrix (Fin 2) (Fin 2) F) 0 1 = -(a : F) * Y 1 0)
    (h11 : (Y : Matrix (Fin 2) (Fin 2) F) 1 1 = Y 0 0) :
    nativeX F a x y hxy * Y * (nativeX F a x y hxy)⁻¹ = Y⁻¹ := by
  have hYinv : ((Y⁻¹ : SL F) : Matrix (Fin 2) (Fin 2) F) =
      !![Y 0 0, (a : F) * Y 1 0; -Y 1 0, Y 0 0] := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h11]
  have hm : (nativeX F a x y hxy : Matrix (Fin 2) (Fin 2) F) *
      (Y : Matrix (Fin 2) (Fin 2) F) =
      ((Y⁻¹ : SL F) : Matrix (Fin 2) (Fin 2) F) * nativeX F a x y hxy := by
    rw [hYinv, nativeX_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h11] <;> ring
  have h : nativeX F a x y hxy * Y = Y⁻¹ * nativeX F a x y hxy :=
    Subtype.ext hm

  rw [h]
  group



section

variable {G : Type u} [Group G]

@[expose] def kleinGenerated (z u : G) : Subgroup G :=
  Subgroup.zpowers z ⊔ Subgroup.zpowers u

theorem mem_zpowers_of_square (v : G) (hv : v ^ 2 = 1) (g : G) :
    g ∈ Subgroup.zpowers v ↔ g = 1 ∨ g = v := by
  classical
  constructor
  · intro hg
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hm : v ^ i = v ^ (i % 2) := by
      rw [← Int.emod_add_mul_ediv i 2, _root_.zpow_add, _root_.zpow_mul, zpow_ofNat, hv]
      simp
    rcases Int.emod_two_eq_zero_or_one i with h0 | h1
    · left
      rw [← hi, hm, h0, zpow_zero]
    · right
      rw [← hi, hm, h1, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem mem_kleinGenerated (z u : G) (hz : z ∈ Subgroup.center G)
    (hz2 : z ^ 2 = 1) (hu2 : u ^ 2 = 1) (g : G) :
    g ∈ kleinGenerated z u ↔ g = 1 ∨ g = z ∨ g = u ∨ g = z * u := by
  have hzcomm : ∀ g : G, g * z = z * g := (Subgroup.mem_center_iff.mp hz)
  let : (Subgroup.zpowers z).Normal := ⟨by
    intro n hn g
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have h : Commute g z := hzcomm g
    rw [show g * z ^ i * g⁻¹ = z ^ i by rw [h.zpow_right i]; group]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _⟩
  rw [kleinGenerated, Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨s, hs, t, ht, hst⟩
    rcases (mem_zpowers_of_square z hz2 s).mp hs with rfl | rfl <;>
    rcases (mem_zpowers_of_square u hu2 t).mp ht with rfl | rfl <;> simp_all
  · rintro (h | h | h | h)
    all_goals rw [h]
    · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, one_mul _⟩
    · exact ⟨z, Subgroup.mem_zpowers _, 1, Subgroup.one_mem _, mul_one _⟩
    · exact ⟨1, Subgroup.one_mem _, u, Subgroup.mem_zpowers _, one_mul _⟩
    · exact ⟨z, Subgroup.mem_zpowers _, u, Subgroup.mem_zpowers _, rfl⟩

theorem centralizer_kleinGenerated (z u : G) (hz : z ∈ Subgroup.center G) :
    Subgroup.centralizer (kleinGenerated z u : Set G) = Subgroup.centralizer {u} := by
  have hclosure : kleinGenerated z u = Subgroup.closure ({z, u} : Set G) := by
    rw [kleinGenerated, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    congr 1
  rw [hclosure, Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hzcomm := Subgroup.mem_center_iff.mp hz g
  constructor
  · intro h k hk
    subst k
    exact h u (Or.inr rfl)
  · intro h k hk
    rcases hk with hk | hk
    · rw [hk]
      exact hzcomm.symm
    · rw [hk]
      exact h u rfl

theorem normalizer_conjugates_u (z u : G) (hz : z ∈ Subgroup.center G)
    (hz2 : z ^ 2 = 1) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (g : G) (hg : g ∈ Subgroup.normalizer (kleinGenerated z u : Set G)) :
    g * u * g⁻¹ = u ∨ g * u * g⁻¹ = z * u := by
  have huV : u ∈ kleinGenerated z u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hmem := (Subgroup.mem_normalizer_iff.mp hg u).mp huV
  rcases (mem_kleinGenerated z u hz hz2 hu2 _).mp hmem with h | h | h | h
  · have h' := congrArg (fun x : G => g⁻¹ * x * g) h
    exact False.elim (hu1 (by simpa only [mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel, mul_one] using h'))
  · have h' := congrArg (fun x : G => g⁻¹ * x * g) h
    have hzcomm := Subgroup.mem_center_iff.mp hz g
    have hzconj : g⁻¹ * z * g = z := by rw [mul_assoc, ← hzcomm]; group
    exact False.elim (huz (by simpa only [mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel, hzconj, mul_one] using h'))
  · exact Or.inl h
  · exact Or.inr h

theorem swap_mem_normalizer [Finite G] (z u X : G) (hz : z ∈ Subgroup.center G)
    (hz2 : z ^ 2 = 1) (hu2 : u ^ 2 = 1) (hswap : X * u * X⁻¹ = z * u) :
    X ∈ Subgroup.normalizer (kleinGenerated z u : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro v hv
  rcases (mem_kleinGenerated z u hz hz2 hu2 v).mp hv with hv | hv | hv | hv
  all_goals rw [hv]
  · simp
  · have hc := Subgroup.mem_center_iff.mp hz X
    have h : X * z * X⁻¹ = z := by rw [hc]; group
    rw [h]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  · rw [hswap]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers z) (Subgroup.mem_zpowers u)
  · have hc := Subgroup.mem_center_iff.mp hz X
    have h : X * z * X⁻¹ = z := by rw [hc]; group
    rw [show X * (z * u) * X⁻¹ = (X * z * X⁻¹) * (X * u * X⁻¹) by group,
      h, hswap, ← mul_assoc, ← pow_two, hz2, one_mul]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)

theorem normalizer_eq_centralizer_sup [Finite G] (z u X : G)
    (hz : z ∈ Subgroup.center G) (hz2 : z ^ 2 = 1) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) (hswap : X * u * X⁻¹ = z * u) :
    Subgroup.normalizer (kleinGenerated z u : Set G) =
      Subgroup.centralizer {u} ⊔ Subgroup.zpowers X := by
  have hXN := swap_mem_normalizer z u X hz hz2 hu2 hswap
  apply le_antisymm
  · intro g hg
    rcases normalizer_conjugates_u z u hz hz2 hu2 hu1 huz g hg with h | h
    · apply Subgroup.mem_sup_left
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h' := congrArg (fun x : G => x * g) h
      simpa [mul_assoc] using h'
    · have hc : X⁻¹ * g ∈ Subgroup.centralizer {u} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hfix : (X⁻¹ * g) * u * (X⁻¹ * g)⁻¹ = u := by
          calc
            (X⁻¹ * g) * u * (X⁻¹ * g)⁻¹ = X⁻¹ * (g * u * g⁻¹) * X := by group
            _ = X⁻¹ * (z * u) * X := by rw [h]
            _ = X⁻¹ * (X * u * X⁻¹) * X := by rw [hswap]
            _ = u := by group
        have h' := congrArg (fun x : G => x * (X⁻¹ * g)) hfix
        simpa [mul_assoc] using h'
      have hm := Subgroup.mul_mem (Subgroup.centralizer {u} ⊔ Subgroup.zpowers X)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers X)) (Subgroup.mem_sup_left hc)
      simpa only [mul_inv_cancel_left] using hm
  · apply sup_le
    · rw [← centralizer_kleinGenerated z u hz]
      exact Subgroup.centralizer_le_normalizer _
    · exact Subgroup.zpowers_le_of_mem hXN
end


section

variable {G : Type u} [Group G]

@[expose] def commutingProduct (S B : Subgroup G)
    (hc : ∀ s : S, ∀ b : B, Commute (S.subtype s) (B.subtype b)) : S × B →* G :=
  S.subtype.noncommCoprod B.subtype hc

theorem commutingProduct_range (S B : Subgroup G)
    (hc : ∀ s : S, ∀ b : B, Commute (S.subtype s) (B.subtype b)) :
    (commutingProduct S B hc).range = S ⊔ B := by
  exact (MonoidHom.noncommCoprod_range S.subtype B.subtype hc).trans (by
    rw [Subgroup.range_subtype, Subgroup.range_subtype])

theorem commutingProduct_injective (S B : Subgroup G)
    (hc : ∀ s : S, ∀ b : B, Commute (S.subtype s) (B.subtype b)) (hd : Disjoint S B) :
    Function.Injective (commutingProduct S B hc) := by
  apply (MonoidHom.noncommCoprod_injective _ _ hc).mpr
  simpa only [Subgroup.range_subtype] using
    (show Function.Injective S.subtype ∧ Function.Injective B.subtype ∧ Disjoint S B from
      ⟨S.subtype_injective, B.subtype_injective, hd⟩)

@[expose] def commutingProductEquiv (S B : Subgroup G)
    (hc : ∀ s : S, ∀ b : B, Commute (S.subtype s) (B.subtype b)) (hd : Disjoint S B) :
    S × B ≃* ↥(S ⊔ B) := by
  let f : S × B →* ↥(S ⊔ B) := (commutingProduct S B hc).codRestrict _ (by
    intro p
    exact Subgroup.mul_mem_sup p.1.property p.2.property)
  apply MulEquiv.ofBijective f
  constructor
  · intro p q hpq
    exact commutingProduct_injective S B hc hd (congrArg Subtype.val hpq)
  · intro k
    have hk : (k : G) ∈ (commutingProduct S B hc).range := by
      rw [commutingProduct_range]
      exact k.property
    obtain ⟨p, hp⟩ := hk
    exact ⟨p, Subtype.ext hp⟩

theorem commutingProductEquiv_coe (S B : Subgroup G)
    (hc : ∀ s : S, ∀ b : B, Commute (S.subtype s) (B.subtype b)) (hd : Disjoint S B)
    (p : S × B) : (commutingProductEquiv S B hc hd p : G) = (p.1 : G) * p.2 := rfl

theorem disjoint_commutingProduct_of_projection {Q : Type v} [Group Q]
    (W S B : Subgroup G) (pr : G →* Q)
    (hW : W ≤ pr.ker) (hS : S ≤ pr.ker)
    (hB : Function.Injective (pr.comp B.subtype))
    (hc : ∀ s : S, ∀ b : B, Commute (S.subtype s) (B.subtype b)) (hd : Disjoint W S) :
    Disjoint W (S ⊔ B) := by
  apply Subgroup.disjoint_def.mpr
  intro g hgW hgK
  have hk : g ∈ (commutingProduct S B hc).range := by
    rw [commutingProduct_range]
    exact hgK
  obtain ⟨p, hp⟩ := hk
  have hpg : pr g = 1 := hW hgW
  have hps : pr (p.1 : G) = 1 := hS p.1.property
  have hpb : pr (p.2 : G) = 1 := by
    have hproduct : (commutingProduct S B hc) p = (p.1 : G) * p.2 := rfl
    rw [← hp, hproduct, map_mul, hps, one_mul] at hpg
    exact hpg
  have hb : p.2 = 1 := hB (by
    change pr (p.2 : G) = pr 1
    rw [hpb, map_one])
  have hgS : g ∈ S := by
    have hproduct : (commutingProduct S B hc) p = (p.1 : G) * p.2 := rfl
    rw [← hp, hproduct, hb, Subgroup.coe_one, mul_one]
    exact p.1.property
  exact Subgroup.disjoint_def.mp hd hgW hgS

@[expose] def subgroupAction (W K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (W : Set G)) : K →* MulAut W :=
  W.normalizerMonoidHom.comp (Subgroup.inclusion hK)

@[expose] def subgroupSemidirectMap (W K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (W : Set G)) :
    SemidirectProduct W K (subgroupAction W K hK) →* G :=
  SemidirectProduct.monoidHomSubgroup hK

theorem subgroupSemidirectMap_range (W K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (W : Set G)) :
    (subgroupSemidirectMap W K hK).range = W ⊔ K := by
  apply le_antisymm
  · rintro g ⟨p, rfl⟩
    exact Subgroup.mul_mem_sup p.left.property p.right.property
  · apply sup_le
    · intro w hw
      exact ⟨SemidirectProduct.inl ⟨w, hw⟩, by
        change (w : G) * 1 = w
        exact mul_one _⟩
    · intro k hk
      exact ⟨SemidirectProduct.inr ⟨k, hk⟩, by
        change (1 : G) * k = k
        exact one_mul _⟩

theorem subgroupSemidirectMap_injective (W K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (W : Set G)) (hd : Disjoint W K) :
    Function.Injective (subgroupSemidirectMap W K hK) := by
  intro p q hpq
  have heq : (q.left : G)⁻¹ * p.left = (q.right : G) * (p.right : G)⁻¹ := by
    change (p.left : G) * p.right = (q.left : G) * q.right at hpq
    calc
      (q.left : G)⁻¹ * p.left = (q.left : G)⁻¹ * ((p.left : G) * p.right) * (p.right : G)⁻¹ := by group
      _ = (q.left : G)⁻¹ * ((q.left : G) * q.right) * (p.right : G)⁻¹ := by rw [hpq]
      _ = (q.right : G) * (p.right : G)⁻¹ := by group
  have hW : (q.left : G)⁻¹ * p.left ∈ W := W.mul_mem (W.inv_mem q.left.property) p.left.property
  have hK' : (q.left : G)⁻¹ * p.left ∈ K := by
    rw [heq]
    exact K.mul_mem q.right.property (K.inv_mem p.right.property)
  have h1 := Subgroup.disjoint_def.mp hd hW hK'
  have hl : p.left = q.left := Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hr : p.right = q.right := by
    apply Subtype.ext
    apply mul_right_cancel (b := (p.right : G)⁻¹)
    rw [mul_inv_cancel, ← heq, h1]
  exact SemidirectProduct.ext hl hr

@[expose] def subgroupSemidirectEquiv (W K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (W : Set G)) (hd : Disjoint W K) :
    SemidirectProduct W K (subgroupAction W K hK) ≃* ↥(W ⊔ K) := by
  let f : SemidirectProduct W K (subgroupAction W K hK) →* ↥(W ⊔ K) :=
    (subgroupSemidirectMap W K hK).codRestrict _ (by
      intro p
      exact Subgroup.mul_mem_sup p.left.property p.right.property)
  apply MulEquiv.ofBijective f
  constructor
  · intro p q hpq
    exact subgroupSemidirectMap_injective W K hK hd (congrArg Subtype.val hpq)
  · intro n
    have hn : (n : G) ∈ (subgroupSemidirectMap W K hK).range := by
      rw [subgroupSemidirectMap_range]
      exact n.property
    obtain ⟨p, hp⟩ := hn
    exact ⟨p, Subtype.ext hp⟩

theorem subgroupSemidirectEquiv_coe (W K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (W : Set G)) (hd : Disjoint W K)
    (p : SemidirectProduct W K (subgroupAction W K hK)) :
    (subgroupSemidirectEquiv W K hK hd p : G) = (p.left : G) * p.right := rfl


theorem subgroup_internal_complement (W K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (W : Set G)) (hd : Disjoint W K) :
    (W.subgroupOf (W ⊔ K)).IsComplement' (K.subgroupOf (W ⊔ K)) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro g hgW hgK
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hd hgW hgK
  · apply Set.eq_univ_of_forall
    intro g
    obtain ⟨p, hp⟩ := (subgroupSemidirectEquiv W K hK hd).surjective g
    refine ⟨⟨p.left.val, (show W ≤ W ⊔ K from le_sup_left) p.left.property⟩, p.left.property,
      ⟨p.right.val, (show K ≤ W ⊔ K from le_sup_right) p.right.property⟩, p.right.property, ?_⟩
    apply Subtype.ext
    exact (subgroupSemidirectEquiv_coe W K hK hd p).symm.trans (congrArg Subtype.val hp)

theorem sylow_two_of_card_eight (P : Subgroup G) (k : ℕ)
    (hP : Nat.card P = 8) (hG : Nat.card G = 8 * k) (hk : Odd k) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = P := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by simpa using hP)
  have hindex : P.index = k := by
    have hc := P.index_mul_card
    rw [hP, hG] at hc
    omega
  have hnot : ¬2 ∣ P.index := by
    rw [hindex]
    exact fun h => Nat.not_even_iff_odd.mpr hk (even_iff_two_dvd.mpr h)
  exact ⟨hpg.toSylow hnot, hpg.toSylow_coe hnot⟩

end


section OriginalNormalizer

variable (F : Type u) [Field F] (a : Fˣ)
variable (A : Subgroup (F ≃+* F))
variable (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)

theorem nativeX_inverts_torus (a : Fˣ) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) (Y : MatrixTorus.Torus F a) :
    nativeX F a x y hxy * Y.val * (nativeX F a x y hxy)⁻¹ = Y.val⁻¹ := by
  obtain ⟨h01, h11⟩ := (MatrixTorus.mem_torus_iff F a Y.val).mp Y.property
  exact nativeX_inverts_coordinates F a x y hxy Y.val h01 h11

abbrev H := MatrixTorus.OriginalH F a A hfix

noncomputable instance finiteOriginalH [Finite F] : Finite (H F a A hfix) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun sigma : F ≃+* F => (sigma : F → F)) DFunLike.coe_injective
  let : Finite (M F a) := Finite.of_equiv (SL F × C2) SemidirectProduct.equivProd.symm
  exact Finite.of_equiv (M F a × A) SemidirectProduct.equivProd.symm

@[expose] def X (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : H F a A hfix :=
  MatrixTorus.originalSlInH F a A hfix (nativeX F a x y hxy)

@[expose] def S0 (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : Subgroup (H F a A hfix) :=
  Subgroup.zpowers (X F a A hfix x y hxy) ⊔
    Subgroup.zpowers (MatrixTorus.originalU F a A hfix)

@[expose] def WInH : MatrixTorus.W F a →* H F a A hfix :=
  (MatrixTorus.originalSlInH F a A hfix).comp
    ((MatrixTorus.Torus F a).subtype.comp (MatrixTorus.W F a).subtype)

@[expose] def WGroup : Subgroup (H F a A hfix) := (WInH F a A hfix).range

@[expose] def FieldGroup : Subgroup (H F a A hfix) :=
  (MatrixTorus.originalFieldInH F a A hfix).range

@[expose] def Complement (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : Subgroup (H F a A hfix) :=
  S0 F a A hfix x y hxy ⊔ FieldGroup F a A hfix

@[expose] def Normalizer : Subgroup (H F a A hfix) :=
  Subgroup.normalizer (MatrixTorus.originalV0 F a A hfix : Set (H F a A hfix))

theorem originalSlInH_injective : Function.Injective (MatrixTorus.originalSlInH F a A hfix) :=
  SemidirectProduct.inl_injective.comp (inclusion_injective F a)

theorem WInH_injective : Function.Injective (WInH F a A hfix) :=
  (originalSlInH_injective F a A hfix).comp
    ((MatrixTorus.Torus F a).subtype_injective.comp (MatrixTorus.W F a).subtype_injective)

@[expose] def WGroupEquiv : MatrixTorus.W F a ≃* WGroup F a A hfix :=
  MonoidHom.ofInjective (WInH_injective F a A hfix)

@[expose] def FieldGroupEquiv : A ≃* FieldGroup F a A hfix :=
  MonoidHom.ofInjective SemidirectProduct.inr_injective

@[expose] def residueProjection : H F a A hfix →* C2 where
  toFun g := g.left.right
  map_one' := rfl
  map_mul' _ _ := rfl

theorem X_square (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    X F a A hfix x y hxy ^ 2 = MatrixTorus.originalZ F a A hfix := by
  rw [X, ← map_pow, nativeX_square]
  rfl

theorem X_order [Finite F] (hF : Odd (Nat.card F)) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : orderOf (X F a A hfix x y hxy) = 4 :=
  (orderOf_injective (MatrixTorus.originalSlInH F a A hfix)
    (originalSlInH_injective F a A hfix) _).trans (nativeX_order F hF a x y hxy)

theorem U_square : MatrixTorus.originalU F a A hfix ^ 2 = 1 := by
  change (SemidirectProduct.inl (u F a) : H F a A hfix) ^ 2 = 1
  rw [← map_pow, u_square, map_one]

theorem U_ne_one : MatrixTorus.originalU F a A hfix ≠ 1 := by
  intro h
  have hc := congrArg (residueProjection F a A hfix) h
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2) : C2) ≠ 1) hc

theorem U_ne_Z : MatrixTorus.originalU F a A hfix ≠ MatrixTorus.originalZ F a A hfix := by
  intro h
  have hc := congrArg (residueProjection F a A hfix) h
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2) : C2) ≠ 1) hc

theorem Z_square : MatrixTorus.originalZ F a A hfix ^ 2 = 1 := by
  change MatrixTorus.originalSlInH F a A hfix (OddFieldSL2.minusIdentity F) ^ 2 = 1
  rw [← map_pow, OddFieldSL2.minusIdentity_square, map_one]

theorem Z_central : MatrixTorus.originalZ F a A hfix ∈ Subgroup.center (H F a A hfix) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  obtain ⟨k, rfl⟩ := (MatrixTorus.originalModelEquiv F a A hfix).surjective g
  rw [← MatrixTorus.originalModelEquiv_z, ← map_mul, ← map_mul]
  exact congrArg (MatrixTorus.originalModelEquiv F a A hfix)
    (Subgroup.mem_center_iff.mp (MatrixTorus.zInH_mem_center F A
      (MatrixTorus.originalCoefficient F a A hfix)) k)



theorem U_inverts_X (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    MatrixTorus.originalU F a A hfix * X F a A hfix x y hxy *
      (MatrixTorus.originalU F a A hfix)⁻¹ = (X F a A hfix x y hxy)⁻¹ := by
  have he := congrArg (SemidirectProduct.inl : M F a →* H F a A hfix)
    (u_inverts_xInM F a x y hxy)
  simpa only [map_mul, map_inv, X, MatrixTorus.originalSlInH,
    MatrixTorus.originalU, MatrixTorus.originalZ, xInM, zInM, MonoidHom.comp_apply] using he

theorem X_conjugates_U (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    X F a A hfix x y hxy * MatrixTorus.originalU F a A hfix *
      (X F a A hfix x y hxy)⁻¹ =
      MatrixTorus.originalZ F a A hfix * MatrixTorus.originalU F a A hfix := by
  have he := congrArg (SemidirectProduct.inl : M F a →* H F a A hfix)
    (xInM_conjugates_u F a x y hxy)
  simpa only [map_mul, map_inv, X, MatrixTorus.originalSlInH,
    MatrixTorus.originalU, MatrixTorus.originalZ, xInM, zInM, MonoidHom.comp_apply] using he

theorem U_not_mem_X_zpowers (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    MatrixTorus.originalU F a A hfix ∉ Subgroup.zpowers (X F a A hfix x y hxy) := by
  intro h
  have hx : X F a A hfix x y hxy ∈ (residueProjection F a A hfix).ker := rfl
  have hle := Subgroup.zpowers_le_of_mem hx
  have hc : (Multiplicative.ofAdd (1 : ZMod 2) : C2) = 1 := hle h
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2) : C2) ≠ 1) hc

@[expose] def S0Equiv [Finite F] (hF : Odd (Nat.card F)) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : S0 F a A hfix x y hxy ≃* DihedralGroup 4 :=
  Classical.choice (generatedDihedral_equiv (X F a A hfix x y hxy)
    (MatrixTorus.originalU F a A hfix) (X_order F a A hfix hF x y hxy)
    (U_square F a A hfix) (U_inverts_X F a A hfix x y hxy)
    (U_not_mem_X_zpowers F a A hfix x y hxy))

theorem S0_card [Finite F] (hF : Odd (Nat.card F)) (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : Nat.card (S0 F a A hfix x y hxy) = 8 := by
  rw [Nat.card_congr (S0Equiv F a A hfix hF x y hxy).toEquiv, DihedralGroup.nat_card]

theorem V0_le_S0 (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    MatrixTorus.originalV0 F a A hfix ≤ S0 F a A hfix x y hxy := by
  apply sup_le
  · apply Subgroup.zpowers_le_of_mem
    rw [← X_square F a A hfix x y hxy]
    exact (S0 F a A hfix x y hxy).pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) 2
  · exact le_sup_right

theorem X_inverts_T (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1)
    (w : MatrixTorus.Torus F a) :
    X F a A hfix x y hxy * MatrixTorus.originalSlInH F a A hfix w.val *
      (X F a A hfix x y hxy)⁻¹ = MatrixTorus.originalSlInH F a A hfix w.val⁻¹ := by
  have he := congrArg (MatrixTorus.originalSlInH F a A hfix)
    (nativeX_inverts_torus F a x y hxy w)
  simpa only [map_mul, map_inv, X, MatrixTorus.originalSlInH,
    MatrixTorus.originalU, MatrixTorus.originalZ, xInM, zInM, MonoidHom.comp_apply] using he

theorem U_trivial_T (w : MatrixTorus.Torus F a) :
    MatrixTorus.originalU F a A hfix * MatrixTorus.originalSlInH F a A hfix w.val *
      (MatrixTorus.originalU F a A hfix)⁻¹ = MatrixTorus.originalSlInH F a A hfix w.val := by
  change (SemidirectProduct.inl (u F a) : H F a A hfix) *
    SemidirectProduct.inl (inclusion F a w.val) * (SemidirectProduct.inl (u F a))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  change SemidirectProduct.inl (u F a * inclusion F a w.val * (u F a)⁻¹) =
    SemidirectProduct.inl (inclusion F a w.val)
  apply congrArg SemidirectProduct.inl
  change SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) *
    SemidirectProduct.inl w.val * (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) : M F a)⁻¹ = _
  rw [← map_inv, ← SemidirectProduct.inl_aut, MatrixTorus.action_torus_trivial]
  rfl


theorem originalCentralizer_le_product [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    Subgroup.centralizer {MatrixTorus.originalU F a A hfix} ≤
      WGroup F a A hfix ⊔ Complement F a A hfix x y hxy := by
  intro g hg
  let b := MatrixTorus.originalCoefficient F a A hfix
  let e := MatrixTorus.originalModelEquiv F a A hfix
  have hge : e.symm g ∈ Subgroup.centralizer {MatrixTorus.uInH F A b} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply, e, b, MatrixTorus.originalModelEquiv_u] using
      Subgroup.mem_centralizer_singleton_iff.mp hg
  have hb : ¬IsSquare (fixedUnit F A b) := by
    rw [MatrixTorus.originalCoefficient_literal]
    exact ha
  obtain ⟨w, v, sigma, he⟩ := (MatrixTorus.centralizer_factorization_iff F A b hF hb _).mp hge
  have hval := congrArg e he
  have hsl : e (MatrixTorus.slInH F A b w.val.val) ∈ WGroup F a A hfix := by
    change MatrixTorus.originalSlInH F a A hfix w.val.val ∈ WGroup F a A hfix
    have hw : w.val.val ∈ MatrixTorus.Torus F a := by
      rw [← MatrixTorus.originalCoefficient_literal F a A hfix]
      exact w.val.property
    have hwW : (⟨w.val.val, hw⟩ : MatrixTorus.Torus F a) ∈ MatrixTorus.W F a := by
      apply (MatrixTorus.mem_W_iff F a _).mpr
      apply Subtype.ext
      have heq := congrArg (fun t : MatrixTorus.Torus F (fixedUnit F A b) => t.val)
        ((MatrixTorus.mem_W_iff F (fixedUnit F A b) w.val).mp w.property)
      exact heq
    exact ⟨⟨⟨w.val.val, hw⟩, hwW⟩, rfl⟩
  have hv : e v.val ∈ MatrixTorus.originalV0 F a A hfix := by
    rw [← MatrixTorus.originalV0_map]
    exact ⟨v.val, v.property, rfl⟩
  have hs := V0_le_S0 F a A hfix x y hxy hv
  have hf : e (MatrixTorus.fieldInH F A b sigma) ∈ FieldGroup F a A hfix := ⟨sigma, rfl⟩
  rw [MulEquiv.apply_symm_apply, map_mul, map_mul] at hval
  rw [hval]
  rw [mul_assoc]
  exact Subgroup.mul_mem_sup hsl
    ((Complement F a A hfix x y hxy).mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hf))



theorem field_fixes_X (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) (sigma : A) :
    MatrixTorus.originalFieldAction F a A hfix sigma (xInM F a x y hxy) =
      xInM F a x y hxy := by
  apply SemidirectProduct.ext
  · exact nativeX_field_fixed F sigma a x y (hfix sigma) (x.property sigma) (y.property sigma) hxy
  · rfl

theorem field_commutes_X (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) (sigma : A) :
    Commute (MatrixTorus.originalFieldInH F a A hfix sigma) (X F a A hfix x y hxy) := by
  change SemidirectProduct.inr sigma * SemidirectProduct.inl (xInM F a x y hxy) =
    SemidirectProduct.inl (xInM F a x y hxy) * SemidirectProduct.inr sigma
  apply mul_right_cancel (b := SemidirectProduct.inr sigma⁻¹)
  rw [← SemidirectProduct.inl_aut, field_fixes_X]
  simp [mul_assoc]

theorem field_commutes_U (sigma : A) :
    Commute (MatrixTorus.originalFieldInH F a A hfix sigma) (MatrixTorus.originalU F a A hfix) := by
  change SemidirectProduct.inr sigma * SemidirectProduct.inl (u F a) =
    SemidirectProduct.inl (u F a) * SemidirectProduct.inr sigma
  apply mul_right_cancel (b := SemidirectProduct.inr sigma⁻¹)
  rw [← SemidirectProduct.inl_aut]
  have hu : MatrixTorus.originalFieldAction F a A hfix sigma (u F a) = u F a := by
    apply SemidirectProduct.ext
    · exact map_one _
    · rfl
  rw [hu]
  simp [mul_assoc]

theorem S0_field_commute (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    ∀ s : S0 F a A hfix x y hxy, ∀ f : FieldGroup F a A hfix,
      Commute ((S0 F a A hfix x y hxy).subtype s) ((FieldGroup F a A hfix).subtype f) := by
  intro s f
  obtain ⟨sigma, hsigma⟩ := f.property
  have hle : S0 F a A hfix x y hxy ≤
      Subgroup.centralizer {MatrixTorus.originalFieldInH F a A hfix sigma} := by
    apply sup_le <;> apply Subgroup.zpowers_le_of_mem <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact (field_commutes_X F a A hfix x y hxy sigma).symm
    · exact (field_commutes_U F a A hfix sigma).symm
  change Commute s.val f.val
  rw [← hsigma]
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle s.property)

theorem W_field_action (w : MatrixTorus.W F a) (sigma : A) :
    MatrixTorus.originalFieldInH F a A hfix sigma * WInH F a A hfix w *
      (MatrixTorus.originalFieldInH F a A hfix sigma)⁻¹ =
      WInH F a A hfix (MatrixTorus.WFieldEquiv F a sigma (hfix sigma) w) := by
  change SemidirectProduct.inr sigma * SemidirectProduct.inl (inclusion F a w.val.val) *
    (SemidirectProduct.inr sigma : H F a A hfix)⁻¹ = _
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

theorem W_X_action (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) (w : MatrixTorus.W F a) :
    X F a A hfix x y hxy * WInH F a A hfix w * (X F a A hfix x y hxy)⁻¹ =
      WInH F a A hfix w⁻¹ := by
  change X F a A hfix x y hxy * MatrixTorus.originalSlInH F a A hfix w.val.val *
    (X F a A hfix x y hxy)⁻¹ = MatrixTorus.originalSlInH F a A hfix (w.val.val)⁻¹
  exact X_inverts_T F a A hfix x y hxy w.val

theorem W_U_action (w : MatrixTorus.W F a) :
    MatrixTorus.originalU F a A hfix * WInH F a A hfix w *
      (MatrixTorus.originalU F a A hfix)⁻¹ = WInH F a A hfix w :=
  U_trivial_T F a A hfix w.val

theorem Complement_normalizes_W [Finite F] (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    Complement F a A hfix x y hxy ≤ Subgroup.normalizer (WGroup F a A hfix : Set (H F a A hfix)) := by
  apply sup_le
  · apply sup_le <;> apply Subgroup.zpowers_le_of_mem <;> apply Subgroup.mem_normalizer_fintype
    · rintro w ⟨t, rfl⟩
      rw [W_X_action]
      exact ⟨t⁻¹, rfl⟩
    · rintro w ⟨t, rfl⟩
      rw [W_U_action]
      exact ⟨t, rfl⟩
  · rintro f ⟨sigma, rfl⟩
    apply Subgroup.mem_normalizer_fintype
    rintro w ⟨t, rfl⟩
    rw [W_field_action]
    exact ⟨MatrixTorus.WFieldEquiv F a sigma (hfix sigma) t, rfl⟩



theorem normalizer_centralizer_X [Finite F] (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    Normalizer F a A hfix = Subgroup.centralizer {MatrixTorus.originalU F a A hfix} ⊔
      Subgroup.zpowers (X F a A hfix x y hxy) :=
  normalizer_eq_centralizer_sup (MatrixTorus.originalZ F a A hfix)
    (MatrixTorus.originalU F a A hfix) (X F a A hfix x y hxy)
    (Z_central F a A hfix) (Z_square F a A hfix) (U_square F a A hfix)
    (U_ne_one F a A hfix) (U_ne_Z F a A hfix) (X_conjugates_U F a A hfix x y hxy)

theorem centralizer_le_normalizer_original :
    Subgroup.centralizer {MatrixTorus.originalU F a A hfix} ≤ Normalizer F a A hfix := by
  rw [Normalizer, ← centralizer_kleinGenerated _ _ (Z_central F a A hfix)]
  exact Subgroup.centralizer_le_normalizer _

theorem W_le_normalizer : WGroup F a A hfix ≤ Normalizer F a A hfix := by
  apply le_trans _ (centralizer_le_normalizer_original F a A hfix)
  rintro w ⟨t, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc := congrArg (fun v : H F a A hfix => v * MatrixTorus.originalU F a A hfix)
    (W_U_action F a A hfix t)
  have he : WInH F a A hfix t * MatrixTorus.originalU F a A hfix =
      MatrixTorus.originalU F a A hfix * WInH F a A hfix t := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hc.symm
  exact he

theorem field_le_normalizer : FieldGroup F a A hfix ≤ Normalizer F a A hfix := by
  apply le_trans _ (centralizer_le_normalizer_original F a A hfix)
  rintro f ⟨sigma, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact field_commutes_U F a A hfix sigma

theorem S0_le_normalizer [Finite F] (x y : F)
    (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) : S0 F a A hfix x y hxy ≤ Normalizer F a A hfix := by
  rw [normalizer_centralizer_X F a A hfix x y hxy]
  apply sup_le
  · exact le_sup_right
  · apply Subgroup.zpowers_le_of_mem
    apply Subgroup.mem_sup_left
    rw [Subgroup.mem_centralizer_singleton_iff]

theorem normalizer_eq_product [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    Normalizer F a A hfix = WGroup F a A hfix ⊔ Complement F a A hfix x y hxy := by
  apply le_antisymm
  · rw [normalizer_centralizer_X F a A hfix x y hxy]
    apply sup_le
    · exact originalCentralizer_le_product F a A hfix hF ha x y hxy
    · apply Subgroup.zpowers_le_of_mem
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_left
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  · apply sup_le
    · exact W_le_normalizer F a A hfix
    · exact sup_le (S0_le_normalizer F a A hfix x y hxy) (field_le_normalizer F a A hfix)

theorem S0_field_projection (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    S0 F a A hfix x y hxy ≤ (SemidirectProduct.rightHom : H F a A hfix →* A).ker := by
  apply sup_le <;> apply Subgroup.zpowers_le_of_mem <;> rfl

theorem W_field_projection :
    WGroup F a A hfix ≤ (SemidirectProduct.rightHom : H F a A hfix →* A).ker := by
  rintro w ⟨t, rfl⟩
  rfl

theorem field_projection_injective : Function.Injective
    ((SemidirectProduct.rightHom : H F a A hfix →* A).comp
      (FieldGroup F a A hfix).subtype) := by
  intro f g h
  obtain ⟨sigma, hs⟩ := f.property
  obtain ⟨tau, ht⟩ := g.property
  apply Subtype.ext
  have he : sigma = tau := by
    change (f.val).right = (g.val).right at h
    rw [← hs, ← ht] at h
    exact h
  rw [← hs, ← ht, he]

theorem S0_field_disjoint (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    Disjoint (S0 F a A hfix x y hxy) (FieldGroup F a A hfix) := by
  apply Subgroup.disjoint_def.mpr
  intro g hgS hgF
  obtain ⟨sigma, hsigma⟩ := hgF
  have hs := S0_field_projection F a A hfix x y hxy hgS
  rw [← hsigma] at hs
  have he : sigma = 1 := hs
  rw [← hsigma, he, map_one]

theorem WGroup_card [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    Nat.card (WGroup F a A hfix) = MatrixTorus.torusSize (Nat.card F) / 2 := by
  rw [← Nat.card_congr (WGroupEquiv F a A hfix).toEquiv]
  exact MatrixTorus.W_card F a hF ha

theorem W_S0_disjoint [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    Disjoint (WGroup F a A hfix) (S0 F a A hfix x y hxy) := by
  apply Subgroup.disjoint_of_coprime_natCard
  rw [WGroup_card F a A hfix hF ha, S0_card F a A hfix hF x y hxy]
  have ho := MatrixTorus.torusSize_half_odd hF
  exact (Nat.coprime_two_right.mpr ho).pow_right 3

theorem W_complement_disjoint [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A) (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    Disjoint (WGroup F a A hfix) (Complement F a A hfix x y hxy) :=
  disjoint_commutingProduct_of_projection (WGroup F a A hfix) (S0 F a A hfix x y hxy)
    (FieldGroup F a A hfix) SemidirectProduct.rightHom
    (W_field_projection F a A hfix) (S0_field_projection F a A hfix x y hxy)
    (field_projection_injective F a A hfix) (S0_field_commute F a A hfix x y hxy)
    (W_S0_disjoint F a A hfix hF ha x y hxy)

@[expose] def ComplementEquiv (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    S0 F a A hfix x y hxy × A ≃* Complement F a A hfix x y hxy :=
  (MulEquiv.prodCongr (MulEquiv.refl _) (FieldGroupEquiv F a A hfix)).trans
    (commutingProductEquiv (S0 F a A hfix x y hxy) (FieldGroup F a A hfix)
      (S0_field_commute F a A hfix x y hxy) (S0_field_disjoint F a A hfix x y hxy))

theorem ComplementEquiv_coe (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1)
    (p : S0 F a A hfix x y hxy × A) :
    (ComplementEquiv F a A hfix x y hxy p : H F a A hfix) =
      p.1.val * MatrixTorus.originalFieldInH F a A hfix p.2 := rfl

@[expose] def normalizerAction [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    S0 F a A hfix x y hxy × A →* MulAut (MatrixTorus.W F a) :=
  (MulAut.congr (WGroupEquiv F a A hfix).symm).toMonoidHom.comp
    ((subgroupAction (WGroup F a A hfix) (Complement F a A hfix x y hxy)
      (Complement_normalizes_W F a A hfix x y hxy)).comp
        (ComplementEquiv F a A hfix x y hxy).toMonoidHom)

theorem normalizerAction_coe [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1)
    (p : S0 F a A hfix x y hxy × A) (w : MatrixTorus.W F a) :
    WInH F a A hfix (normalizerAction F a A hfix x y hxy p w) =
      (p.1.val * MatrixTorus.originalFieldInH F a A hfix p.2) *
        WInH F a A hfix w *
        (p.1.val * MatrixTorus.originalFieldInH F a A hfix p.2)⁻¹ := by
  have he := (WGroupEquiv F a A hfix).apply_symm_apply
    (subgroupAction (WGroup F a A hfix) (Complement F a A hfix x y hxy)
      (Complement_normalizes_W F a A hfix x y hxy)
      (ComplementEquiv F a A hfix x y hxy p) (WGroupEquiv F a A hfix w))
  have hv := congrArg Subtype.val he
  exact hv

@[expose] def NormalizerEquiv [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    SemidirectProduct (MatrixTorus.W F a) (S0 F a A hfix x y hxy × A)
      (normalizerAction F a A hfix x y hxy) ≃* Normalizer F a A hfix :=
  (SemidirectProduct.congr' (WGroupEquiv F a A hfix).symm
    (ComplementEquiv F a A hfix x y hxy).symm).symm.trans
      ((subgroupSemidirectEquiv (WGroup F a A hfix) (Complement F a A hfix x y hxy)
        (Complement_normalizes_W F a A hfix x y hxy)
        (W_complement_disjoint F a A hfix hF ha x y hxy)).trans
          (MulEquiv.subgroupCongr (normalizer_eq_product F a A hfix hF ha x y hxy).symm))

theorem NormalizerEquiv_coe [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1)
    (p : SemidirectProduct (MatrixTorus.W F a) (S0 F a A hfix x y hxy × A)
      (normalizerAction F a A hfix x y hxy)) :
    (NormalizerEquiv F a A hfix hF ha x y hxy p : H F a A hfix) =
      WInH F a A hfix p.left * p.right.1.val *
        MatrixTorus.originalFieldInH F a A hfix p.right.2 := by
  change WInH F a A hfix p.left *
    (p.right.1.val * MatrixTorus.originalFieldInH F a A hfix p.right.2) = _
  exact (mul_assoc _ _ _).symm

theorem normalizer_internal_complement [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    ((WGroup F a A hfix).subgroupOf (Normalizer F a A hfix)).IsComplement'
      ((Complement F a A hfix x y hxy).subgroupOf (Normalizer F a A hfix)) := by
  rw [normalizer_eq_product F a A hfix hF ha x y hxy]
  exact subgroup_internal_complement (WGroup F a A hfix) (Complement F a A hfix x y hxy)
    (Complement_normalizes_W F a A hfix x y hxy)
    (W_complement_disjoint F a A hfix hF ha x y hxy)

theorem W_normal_in_normalizer [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    ((WGroup F a A hfix).subgroupOf (Normalizer F a A hfix)).Normal := by
  rw [normalizer_eq_product F a A hfix hF ha x y hxy, sup_comm]
  exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
    (Complement_normalizes_W F a A hfix x y hxy)

theorem Normalizer_card [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    Nat.card (Normalizer F a A hfix) =
      4 * Nat.card A * MatrixTorus.torusSize (Nat.card F) := by
  rw [← Nat.card_congr (NormalizerEquiv F a A hfix hF ha x y hxy).toEquiv,
    Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, Nat.card_prod,
    MatrixTorus.W_card F a hF ha, S0_card F a A hfix hF x y hxy]
  have htwo := MatrixTorus.torusSize_two_mul_half hF
  nlinarith

theorem S0_sylow [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (hA : Odd (Nat.card A)) (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    ∃ S : Sylow 2 (Normalizer F a A hfix), (S : Subgroup (Normalizer F a A hfix)) =
      (S0 F a A hfix x y hxy).subgroupOf (Normalizer F a A hfix) := by
  apply sylow_two_of_card_eight _
    (Nat.card A * (MatrixTorus.torusSize (Nat.card F) / 2))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (S0_le_normalizer F a A hfix x y hxy)).toEquiv]
    exact S0_card F a A hfix hF x y hxy
  · rw [Normalizer_card F a A hfix hF ha x y hxy]
    have htwo := MatrixTorus.torusSize_two_mul_half hF
    nlinarith
  · exact hA.mul (MatrixTorus.torusSize_half_odd hF)

@[expose] def XInS0 (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    S0 F a A hfix x y hxy :=
  ⟨X F a A hfix x y hxy, Subgroup.mem_sup_left (Subgroup.mem_zpowers _)⟩

@[expose] def UInS0 (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    S0 F a A hfix x y hxy :=
  ⟨MatrixTorus.originalU F a A hfix, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩

theorem normalizerAction_X [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) (w : MatrixTorus.W F a) :
    normalizerAction F a A hfix x y hxy (XInS0 F a A hfix x y hxy, 1) w = w⁻¹ := by
  apply WInH_injective F a A hfix
  rw [normalizerAction_coe, map_one, mul_one]
  exact W_X_action F a A hfix x y hxy w

theorem normalizerAction_U [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) (w : MatrixTorus.W F a) :
    normalizerAction F a A hfix x y hxy (UInS0 F a A hfix x y hxy, 1) w = w := by
  apply WInH_injective F a A hfix
  rw [normalizerAction_coe, map_one, mul_one]
  exact W_U_action F a A hfix w

theorem normalizerAction_field [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) (sigma : A) (w : MatrixTorus.W F a) :
    normalizerAction F a A hfix x y hxy (1, sigma) w =
      MatrixTorus.WFieldEquiv F a sigma (hfix sigma) w := by
  apply WInH_injective F a A hfix
  rw [normalizerAction_coe, Subgroup.coe_one, one_mul]
  exact W_field_action F a A hfix w sigma

theorem normalizerAction_field_entries [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) (sigma : A) (w : MatrixTorus.W F a) :
    ((normalizerAction F a A hfix x y hxy (1, sigma) w).val.val : Matrix (Fin 2) (Fin 2) F) =
      (sigma : F ≃+* F).toRingHom.mapMatrix (w.val.val : Matrix (Fin 2) (Fin 2) F) := by
  rw [normalizerAction_field]
  rfl

include hfix in
theorem original_fixed_pair_exists [Finite F] (hF : Odd (Nat.card F))
    (hA : Odd (Nat.card A)) :
    ∃ x y : FixedField F A, (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1 := by
  obtain ⟨x, y, hxy⟩ := exists_fixed_pair F A hF hA (fixedCoefficient F A a hfix)
  refine ⟨x, y, ?_⟩
  exact congrArg (fun t : FixedField F A => (t : F)) hxy

theorem WGroup_odd [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    Odd (Nat.card (WGroup F a A hfix)) := by
  rw [WGroup_card F a A hfix hF ha]
  exact MatrixTorus.torusSize_half_odd hF

theorem Complement_card [Finite F] (hF : Odd (Nat.card F)) (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    Nat.card (Complement F a A hfix x y hxy) = 8 * Nat.card A := by
  rw [← Nat.card_congr (ComplementEquiv F a A hfix x y hxy).toEquiv, Nat.card_prod,
    S0_card F a A hfix hF x y hxy]

@[expose] def WInNormalizer : MatrixTorus.W F a →* Normalizer F a A hfix :=
  (WInH F a A hfix).codRestrict _ (by
    intro w
    exact W_le_normalizer F a A hfix ⟨w, rfl⟩)

@[expose] def ComplementInNormalizer [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    S0 F a A hfix x y hxy × A →* Normalizer F a A hfix :=
  ((Complement F a A hfix x y hxy).subtype.comp
    (ComplementEquiv F a A hfix x y hxy).toMonoidHom).codRestrict _ (by
      intro p
      exact (sup_le (S0_le_normalizer F a A hfix x y hxy)
        (field_le_normalizer F a A hfix)) (ComplementEquiv F a A hfix x y hxy p).property)

theorem WInNormalizer_coe (w : MatrixTorus.W F a) :
    (WInNormalizer F a A hfix w : H F a A hfix) = WInH F a A hfix w := rfl

theorem ComplementInNormalizer_coe [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1)
    (p : S0 F a A hfix x y hxy × A) :
    (ComplementInNormalizer F a A hfix x y hxy p : H F a A hfix) =
      p.1.val * MatrixTorus.originalFieldInH F a A hfix p.2 := rfl

theorem NormalizerEquiv_inl [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A) (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1)
    (w : MatrixTorus.W F a) :
    NormalizerEquiv F a A hfix hF ha x y hxy (SemidirectProduct.inl w) =
      WInNormalizer F a A hfix w := by
  apply Subtype.ext
  rw [NormalizerEquiv_coe, WInNormalizer_coe]
  simp

theorem NormalizerEquiv_inr [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A) (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1)
    (p : S0 F a A hfix x y hxy × A) :
    NormalizerEquiv F a A hfix hF ha x y hxy (SemidirectProduct.inr p) =
      ComplementInNormalizer F a A hfix x y hxy p := by
  apply Subtype.ext
  rw [NormalizerEquiv_coe, ComplementInNormalizer_coe]
  simp

theorem normalizer_unique_presentation [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A) (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1)
    (g : H F a A hfix) :
    g ∈ Normalizer F a A hfix ↔ ∃! p : MatrixTorus.W F a × (S0 F a A hfix x y hxy × A),
      g = WInH F a A hfix p.1 * p.2.1.val * MatrixTorus.originalFieldInH F a A hfix p.2.2 := by
  constructor
  · intro hg
    let e := NormalizerEquiv F a A hfix hF ha x y hxy
    let t := e.symm ⟨g, hg⟩
    refine ⟨(t.left, t.right), ?_, ?_⟩
    · exact (congrArg Subtype.val (e.apply_symm_apply ⟨g, hg⟩)).symm.trans
        (NormalizerEquiv_coe F a A hfix hF ha x y hxy t)
    · intro p hp
      have he : e (SemidirectProduct.mk p.1 p.2) = ⟨g, hg⟩ := by
        apply Subtype.ext
        exact (NormalizerEquiv_coe F a A hfix hF ha x y hxy _).trans hp.symm
      have ht : SemidirectProduct.mk p.1 p.2 = t := e.injective (he.trans (e.apply_symm_apply ⟨g, hg⟩).symm)
      exact congrArg (fun v => (v.left, v.right)) ht
  · rintro ⟨p, hp, _⟩
    rw [hp]
    exact (Normalizer F a A hfix).mul_mem
      ((Normalizer F a A hfix).mul_mem (W_le_normalizer F a A hfix ⟨p.1, rfl⟩)
        (S0_le_normalizer F a A hfix x y hxy p.2.1.property))
      (field_le_normalizer F a A hfix ⟨p.2.2, rfl⟩)


theorem WInNormalizer_injective : Function.Injective (WInNormalizer F a A hfix) := by
  intro w v h
  exact WInH_injective F a A hfix (congrArg Subtype.val h)

theorem ComplementInNormalizer_injective [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    Function.Injective (ComplementInNormalizer F a A hfix x y hxy) := by
  intro p q h
  apply (ComplementEquiv F a A hfix x y hxy).injective
  have he : (ComplementEquiv F a A hfix x y hxy p).val =
      (ComplementEquiv F a A hfix x y hxy q).val := congrArg
        (fun n : Normalizer F a A hfix => n.val) h
  exact Subtype.ext he

theorem WInNormalizer_range :
    (WInNormalizer F a A hfix).range =
      (WGroup F a A hfix).subgroupOf (Normalizer F a A hfix) := by
  ext g
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Subtype.ext hw⟩

theorem ComplementInNormalizer_range [Finite F] (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    (ComplementInNormalizer F a A hfix x y hxy).range =
      (Complement F a A hfix x y hxy).subgroupOf (Normalizer F a A hfix) := by
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    exact (ComplementEquiv F a A hfix x y hxy p).property
  · intro hg
    obtain ⟨p, hp⟩ := (ComplementEquiv F a A hfix x y hxy).surjective ⟨g.val, hg⟩
    have he : (ComplementInNormalizer F a A hfix x y hxy p).val = g.val :=
      congrArg (fun n : Complement F a A hfix x y hxy => n.val) hp
    exact ⟨p, Subtype.ext he⟩

theorem S0_field_internal_direct (x y : FixedField F A)
    (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    ((S0 F a A hfix x y hxy).subgroupOf (Complement F a A hfix x y hxy)).IsComplement'
      ((FieldGroup F a A hfix).subgroupOf (Complement F a A hfix x y hxy)) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro g hgS hgF
    exact Subtype.ext (Subgroup.disjoint_def.mp
      (S0_field_disjoint F a A hfix x y hxy) hgS hgF)
  · apply Set.eq_univ_of_forall
    intro g
    obtain ⟨p, hp⟩ := (ComplementEquiv F a A hfix x y hxy).surjective g
    refine ⟨⟨p.1.val, Subgroup.mem_sup_left p.1.property⟩, p.1.property,
      ⟨MatrixTorus.originalFieldInH F a A hfix p.2, Subgroup.mem_sup_right ⟨p.2, rfl⟩⟩,
      ⟨p.2, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (ComplementEquiv_coe F a A hfix x y hxy p).symm.trans (congrArg Subtype.val hp)

theorem originalV0_card [Finite F] (hF : Odd (Nat.card F)) :
    Nat.card (MatrixTorus.originalV0 F a A hfix) = 4 := by
  rw [← Nat.card_congr (MatrixTorus.originalFourEquiv F a A hfix).toEquiv]
  exact MatrixTorus.V0_card F A (MatrixTorus.originalCoefficient F a A hfix) hF

theorem X_coordinates (x y : F) (hxy : x ^ 2 + (a : F) * y ^ 2 = -1) :
    ((X F a A hfix x y hxy).left.left : Matrix (Fin 2) (Fin 2) F) =
      !![x, (a : F) * y; y, -x] ∧
    (X F a A hfix x y hxy).left.right = 1 ∧
    (X F a A hfix x y hxy).right = 1 := ⟨rfl, rfl, rfl⟩

theorem originalSlInH_coordinates (Y : SL F) :
    (MatrixTorus.originalSlInH F a A hfix Y).left.left = Y ∧
    (MatrixTorus.originalSlInH F a A hfix Y).left.right = 1 ∧
    (MatrixTorus.originalSlInH F a A hfix Y).right = 1 := ⟨rfl, rfl, rfl⟩

theorem originalFieldInH_coordinates (sigma : A) :
    (MatrixTorus.originalFieldInH F a A hfix sigma).left = 1 ∧
    (MatrixTorus.originalFieldInH F a A hfix sigma).right = sigma := ⟨rfl, rfl⟩

@[expose] def fourGroupSign (q : ℕ) : ℤ := if q % 4 = 1 then 1 else -1

theorem torusSize_eq_signed {q : ℕ} (hq : Odd q) :
    (MatrixTorus.torusSize q : ℤ) = (q : ℤ) + fourGroupSign q := by
  by_cases h : q % 4 = 1
  · simp [MatrixTorus.torusSize, fourGroupSign, h]
  · simp only [MatrixTorus.torusSize, fourGroupSign, ite_eq_right h]
    have hpos := hq.pos
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    simp only [Nat.cast_one]
    ring

theorem fourGroupSign_mod_four {q : ℕ} (hq : Odd q) :
    (q % 4 = 1 ∨ q % 4 = 3) ∧
    (fourGroupSign q = 1 ↔ q % 4 = 1) ∧
    (fourGroupSign q = -1 ↔ q % 4 = 3) := by
  have htwo := Nat.odd_iff.mp hq
  have hlt := Nat.mod_lt q (by decide : 0 < 4)
  have hm : (q % 4) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd q (by decide : 2 ∣ 4)]
    exact htwo
  have hor : q % 4 = 1 ∨ q % 4 = 3 := by omega
  refine ⟨hor, ?_, ?_⟩
  · simp [fourGroupSign]
  · rcases hor with h | h <;> simp [fourGroupSign, h]

theorem Normalizer_card_signed [Finite F] (hF : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (x y : FixedField F A) (hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1) :
    (Nat.card (Normalizer F a A hfix) : ℤ) =
      4 * (Nat.card A : ℤ) * ((Nat.card F : ℤ) + fourGroupSign (Nat.card F)) := by
  rw [Normalizer_card F a A hfix hF ha x y hxy, Nat.cast_mul, Nat.cast_mul,
    torusSize_eq_signed hF]
  norm_num


theorem fixed_field_literal : FixedField F A = FixedPoints.subfield A F := rfl

theorem fixed_pair_equation_iff (x y : FixedField F A) :
    x ^ 2 + (fixedCoefficient F A a hfix : FixedField F A) * y ^ 2 = -1 ↔
      (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1 := by
  constructor
  · intro h
    exact congrArg (fun t : FixedField F A => (t : F)) h
  · intro h
    exact Subtype.ext h

theorem originalH_multiplication (g k : H F a A hfix) :
    (g * k).left.left = g.left.left * MatrixCoverData.action F a g.left.right
      (MatrixCover.slFieldEquiv F g.right k.left.left) ∧
    (g * k).left.right = g.left.right * k.left.right ∧
    (g * k).right = g.right * k.right := ⟨rfl, rfl, rfl⟩

theorem nonsquare_matrix_four_group_normalizer_action [Finite F]
    (hF : Odd (Nat.card F)) (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) :
    fixedUnit F A (fixedCoefficient F A a hfix) = a ∧
    FixedField F A = FixedPoints.subfield A F ∧
    Odd (Nat.card (FixedPoints.subfield A F)) ∧
    (∃ x y : FixedPoints.subfield A F,
      x ^ 2 + (fixedCoefficient F A a hfix : FixedPoints.subfield A F) * y ^ 2 = -1) ∧
    (∀ g k : H F a A hfix,
      (g * k).left.left = g.left.left * MatrixCoverData.action F a g.left.right
        (MatrixCover.slFieldEquiv F g.right k.left.left) ∧
      (g * k).left.right = g.left.right * k.left.right ∧
      (g * k).right = g.right * k.right) ∧
    (∀ sigma : A, ∀ Y : M F a, MatrixTorus.originalFieldAction F a A hfix sigma Y =
      ⟨Matrix.SpecialLinearGroup.map (sigma : F ≃+* F).toRingHom Y.left, Y.right⟩) ∧
    (∀ Y : SL F, (MatrixTorus.originalSlInH F a A hfix Y).left.left = Y ∧
      (MatrixTorus.originalSlInH F a A hfix Y).left.right = 1 ∧
      (MatrixTorus.originalSlInH F a A hfix Y).right = 1) ∧
    (∀ sigma : A, (MatrixTorus.originalFieldInH F a A hfix sigma).left = 1 ∧
      (MatrixTorus.originalFieldInH F a A hfix sigma).right = sigma) ∧
    IsCyclic (MatrixTorus.Torus F a) ∧
    Nat.card (MatrixTorus.Torus F a) = MatrixTorus.torusSize (Nat.card F) ∧
    IsCyclic (MatrixTorus.W F a) ∧
    (∀ w : MatrixTorus.Torus F a, w ∈ MatrixTorus.W F a ↔ Odd (orderOf w)) ∧
    Nat.card (MatrixTorus.W F a) = MatrixTorus.torusSize (Nat.card F) / 2 ∧
    Odd (Nat.card (MatrixTorus.W F a)) ∧
    Nat.card (MatrixTorus.originalV0 F a A hfix) = 4 ∧
    (Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3) ∧
    (fourGroupSign (Nat.card F) = 1 ↔ Nat.card F % 4 = 1) ∧
    (fourGroupSign (Nat.card F) = -1 ↔ Nat.card F % 4 = 3) ∧
    ∀ x y : FixedPoints.subfield A F,
      ∀ hxy : (x : F) ^ 2 + (a : F) * (y : F) ^ 2 = -1,
      (nativeX F a x y hxy : Matrix (Fin 2) (Fin 2) F) =
        !![(x : F), (a : F) * (y : F); (y : F), -(x : F)] ∧
      (xMatrix F a x y).det = 1 ∧
      nativeX F a x y hxy ^ 2 = OddFieldSL2.minusIdentity F ∧
      orderOf (nativeX F a x y hxy) = 4 ∧
      (((X F a A hfix x y hxy).left.left : Matrix (Fin 2) (Fin 2) F) =
        !![(x : F), (a : F) * (y : F); (y : F), -(x : F)] ∧
        (X F a A hfix x y hxy).left.right = 1 ∧
        (X F a A hfix x y hxy).right = 1) ∧
      X F a A hfix x y hxy ^ 2 = MatrixTorus.originalZ F a A hfix ∧
      orderOf (X F a A hfix x y hxy) = 4 ∧
      X F a A hfix x y hxy * MatrixTorus.originalU F a A hfix *
        (X F a A hfix x y hxy)⁻¹ = MatrixTorus.originalZ F a A hfix *
          MatrixTorus.originalU F a A hfix ∧
      MatrixTorus.originalU F a A hfix * X F a A hfix x y hxy *
        (MatrixTorus.originalU F a A hfix)⁻¹ = (X F a A hfix x y hxy)⁻¹ ∧
      Nonempty (S0 F a A hfix x y hxy ≃* DihedralGroup 4) ∧
      Nat.card (S0 F a A hfix x y hxy) = 8 ∧
      MatrixTorus.originalV0 F a A hfix ≤ S0 F a A hfix x y hxy ∧
      (∀ sigma : A, Matrix.SpecialLinearGroup.map (sigma : F ≃+* F).toRingHom
        (nativeX F a x y hxy) = nativeX F a x y hxy) ∧
      (∀ t : MatrixTorus.Torus F a, X F a A hfix x y hxy *
        MatrixTorus.originalSlInH F a A hfix t.val * (X F a A hfix x y hxy)⁻¹ =
          MatrixTorus.originalSlInH F a A hfix t.val⁻¹) ∧
      (∀ t : MatrixTorus.Torus F a, MatrixTorus.originalU F a A hfix *
        MatrixTorus.originalSlInH F a A hfix t.val * (MatrixTorus.originalU F a A hfix)⁻¹ =
          MatrixTorus.originalSlInH F a A hfix t.val) ∧
      (∀ s : S0 F a A hfix x y hxy, ∀ sigma : A,
        Commute s.val (MatrixTorus.originalFieldInH F a A hfix sigma)) ∧
      Disjoint (S0 F a A hfix x y hxy) (FieldGroup F a A hfix) ∧
      ((S0 F a A hfix x y hxy).subgroupOf (Complement F a A hfix x y hxy)).IsComplement'
        ((FieldGroup F a A hfix).subgroupOf (Complement F a A hfix x y hxy)) ∧
      (∀ p : S0 F a A hfix x y hxy × A,
        (ComplementEquiv F a A hfix x y hxy p : H F a A hfix) =
          p.1.val * MatrixTorus.originalFieldInH F a A hfix p.2) ∧
      Normalizer F a A hfix = WGroup F a A hfix ⊔ Complement F a A hfix x y hxy ∧
      Disjoint (WGroup F a A hfix) (Complement F a A hfix x y hxy) ∧
      ((WGroup F a A hfix).subgroupOf (Normalizer F a A hfix)).Normal ∧
      ((WGroup F a A hfix).subgroupOf (Normalizer F a A hfix)).IsComplement'
        ((Complement F a A hfix x y hxy).subgroupOf (Normalizer F a A hfix)) ∧
      Function.Injective (WInNormalizer F a A hfix) ∧
      (WInNormalizer F a A hfix).range =
        (WGroup F a A hfix).subgroupOf (Normalizer F a A hfix) ∧
      Function.Injective (ComplementInNormalizer F a A hfix x y hxy) ∧
      (ComplementInNormalizer F a A hfix x y hxy).range =
        (Complement F a A hfix x y hxy).subgroupOf (Normalizer F a A hfix) ∧
      (∀ p : SemidirectProduct (MatrixTorus.W F a) (S0 F a A hfix x y hxy × A)
          (normalizerAction F a A hfix x y hxy),
        (NormalizerEquiv F a A hfix hF ha x y hxy p : H F a A hfix) =
          WInH F a A hfix p.left * p.right.1.val *
            MatrixTorus.originalFieldInH F a A hfix p.right.2) ∧
      (∀ g : H F a A hfix, g ∈ Normalizer F a A hfix ↔
        ∃! p : MatrixTorus.W F a × (S0 F a A hfix x y hxy × A),
          g = WInH F a A hfix p.1 * p.2.1.val *
            MatrixTorus.originalFieldInH F a A hfix p.2.2) ∧
      (∀ w : MatrixTorus.W F a,
        normalizerAction F a A hfix x y hxy (XInS0 F a A hfix x y hxy, 1) w = w⁻¹) ∧
      (∀ w : MatrixTorus.W F a,
        normalizerAction F a A hfix x y hxy (UInS0 F a A hfix x y hxy, 1) w = w) ∧
      (∀ sigma : A, ∀ w : MatrixTorus.W F a,
        normalizerAction F a A hfix x y hxy (1, sigma) w =
          MatrixTorus.WFieldEquiv F a sigma (hfix sigma) w) ∧
      (∀ sigma : A, ∀ w : MatrixTorus.W F a,
        ((normalizerAction F a A hfix x y hxy (1, sigma) w).val.val :
            Matrix (Fin 2) (Fin 2) F) =
          (sigma : F ≃+* F).toRingHom.mapMatrix (w.val.val : Matrix (Fin 2) (Fin 2) F)) ∧
      Nat.card (Normalizer F a A hfix) =
        4 * Nat.card A * MatrixTorus.torusSize (Nat.card F) ∧
      (Nat.card (Normalizer F a A hfix) : ℤ) =
        4 * (Nat.card A : ℤ) * ((Nat.card F : ℤ) + fourGroupSign (Nat.card F)) ∧
      ∃ S : Sylow 2 (Normalizer F a A hfix), (S : Subgroup (Normalizer F a A hfix)) =
        (S0 F a A hfix x y hxy).subgroupOf (Normalizer F a A hfix) := by
  have hsign := fourGroupSign_mod_four hF
  refine ⟨fixedCoefficient_literal F A a hfix, fixed_field_literal F A,
    fixed_field_odd F A hF hA, exists_fixed_pair F A hF hA _,
    originalH_multiplication F a A hfix, MatrixTorus.originalFieldAction_pair F a A hfix,
    originalSlInH_coordinates F a A hfix, originalFieldInH_coordinates F a A hfix,
    MatrixTorus.torus_cyclic F a hF ha, MatrixTorus.torus_card F a hF ha,
    MatrixTorus.W_cyclic F a hF ha, MatrixTorus.mem_W_iff_odd_order F a hF ha,
    MatrixTorus.W_card F a hF ha, ?_, originalV0_card F a A hfix hF,
    hsign.1, hsign.2.1, hsign.2.2, ?_⟩
  · rw [MatrixTorus.W_card F a hF ha]
    exact MatrixTorus.torusSize_half_odd hF
  · intro x y hxy
    refine ⟨nativeX_matrix F a x y hxy, ?_, nativeX_square F a x y hxy,
      nativeX_order F hF a x y hxy, X_coordinates F a A hfix x y hxy,
      X_square F a A hfix x y hxy, X_order F a A hfix hF x y hxy,
      X_conjugates_U F a A hfix x y hxy, U_inverts_X F a A hfix x y hxy,
      ⟨S0Equiv F a A hfix hF x y hxy⟩, S0_card F a A hfix hF x y hxy,
      V0_le_S0 F a A hfix x y hxy, ?_, X_inverts_T F a A hfix x y hxy,
      U_trivial_T F a A hfix, ?_, S0_field_disjoint F a A hfix x y hxy,
      S0_field_internal_direct F a A hfix x y hxy, ComplementEquiv_coe F a A hfix x y hxy,
      normalizer_eq_product F a A hfix hF ha x y hxy,
      W_complement_disjoint F a A hfix hF ha x y hxy,
      W_normal_in_normalizer F a A hfix hF ha x y hxy,
      normalizer_internal_complement F a A hfix hF ha x y hxy,
      WInNormalizer_injective F a A hfix, WInNormalizer_range F a A hfix,
      ComplementInNormalizer_injective F a A hfix x y hxy,
      ComplementInNormalizer_range F a A hfix x y hxy,
      NormalizerEquiv_coe F a A hfix hF ha x y hxy,
      normalizer_unique_presentation F a A hfix hF ha x y hxy,
      normalizerAction_X F a A hfix x y hxy, normalizerAction_U F a A hfix x y hxy,
      normalizerAction_field F a A hfix x y hxy,
      normalizerAction_field_entries F a A hfix x y hxy,
      Normalizer_card F a A hfix hF ha x y hxy,
      Normalizer_card_signed F a A hfix hF ha x y hxy,
      S0_sylow F a A hfix hF ha hA x y hxy⟩
    · rw [xMatrix_det, hxy, neg_neg]
    · intro sigma
      exact nativeX_field_fixed F sigma a x y (hfix sigma)
        (x.property sigma) (y.property sigma) hxy
    · intro s sigma
      exact S0_field_commute F a A hfix x y hxy s ⟨_, ⟨sigma, rfl⟩⟩


end OriginalNormalizer

end

end CFSG.Semidihedral.MatrixFourGroupNormalizer
