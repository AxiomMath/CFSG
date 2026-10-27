module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.L2.TorusCentralizer

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.Assembly.LowTwoRank
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_toGL)



section Aut

theorem five_le_card_of_odd_gt3 {n : ℕ} (hodd : Odd n) (h3 : 3 < n) : 5 ≤ n := by
  obtain ⟨k, hk⟩ := hodd
  omega

variable {F : Type} [Field F] [Finite F]

theorem pPrimeCore_eq_bot_of_equiv {Q : Type} [Group Q] (e : Q ≃* SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) : pPrimeCore 2 Q = ⊥ := by
  have hmap := pPrimeCore_map_iso 2 e
  rw [pPrimeCore_two_sl2_five hodd (five_le_card_of_odd_gt3 hodd h3)] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 Q) e.injective).1 hmap

omit [Finite F] in
theorem mem_center_equiv_iff {Q : Type} [Group Q] (e : Q ≃* SpecialLinearGroup (Fin 2) F)
    (x : SpecialLinearGroup (Fin 2) F) : x ∈ center (SpecialLinearGroup (Fin 2) F) ↔ e.symm x ∈ center Q := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h (e g)
  · intro h g
    have := h (e.symm g)
    have := congrArg e this
    simpa using this

theorem sq_eq_minusIdentity {Q : Type} [Group Q] (e : Q ≃* SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) {a : Q} (ha : a * a ∈ center Q) (hna : a ∉ center Q) :
    e a * e a = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hc : e (a * a) ∈ center (SpecialLinearGroup (Fin 2) F) := by
    rw [mem_center_equiv_iff e]; simpa using ha
  have hcna : e a ∉ center (SpecialLinearGroup (Fin 2) F) := by
    rw [mem_center_equiv_iff e]; simpa using hna
  obtain ⟨r, hr, hrm⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  rw [Fintype.card_fin] at hr
  have hr' : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.1 hr' with h1 | h1
  · exfalso
    have hr1 : r = 1 := sub_eq_zero.1 h1
    have hsq : e a * e a = 1 := by
      have h5 : e (a * a) = 1 := by
        apply Subtype.ext
        rw [← hrm, hr1]; simp
      rwa [map_mul] at h5
    have hinv : (e a)⁻¹ = e a := by
      rw [inv_eq_iff_mul_eq_one]; exact hsq
    rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 (e a) hinv with h | h
    · exact hcna (by rw [h]; exact Subgroup.one_mem _)
    · exact hcna (by rw [h]; exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F)
  · have hr1 : r = -1 := eq_neg_of_add_eq_zero_left h1
    have h3 : (e (a * a) : Matrix (Fin 2) (Fin 2) F) =
        (CFSG.Semidihedral.OddFieldSL2.minusIdentity F : Matrix (Fin 2) (Fin 2) F) := by
      rw [← hrm, hr1, CFSG.Semidihedral.OddFieldSL2.minusIdentity_matrix]
    have h4 : e (a * a) = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := Subtype.ext h3
    rwa [map_mul] at h4

theorem card_centralizer_equiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (a : Q) :
    Nat.card ↥(centralizer ({a} : Set Q)) = Nat.card ↥(centralizer ({e a} : Set Q')) := by
  have h : (centralizer ({a} : Set Q)).map e.toMonoidHom = centralizer ({e a} : Set Q') := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      show e y * e a = e a * e y
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
  rw [← h]
  exact (Subgroup.card_map_of_injective e.injective).symm

theorem card_centralizer_of_sq_mem_center {Q : Type} [Group Q] (e : Q ≃* SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) {a : Q} (ha : a * a ∈ center Q) (hna : a ∉ center Q) :
    Nat.card ↥(centralizer ({a} : Set Q)) =
      if Nat.card F % 4 = 1 then Nat.card F - 1 else Nat.card F + 1 := by
  have hea := sq_eq_minusIdentity e hodd ha hna
  rw [card_centralizer_equiv e a]
  obtain ⟨hcyc, hsq, hnsq⟩ := L2Torus.centralizer_cyclic_card hodd (e a) hea
  have hsqiff : IsSquare (-1 : F) ↔ Nat.card F % 4 ≠ 3 := by
    have := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, Nat.card_eq_fintype_card]
  have hmod : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hmod with h1 | h3
  · simp only [h1, ↓reduceIte]
    exact hsq (hsqiff.2 (by omega))
  · simp only [show ¬ (Nat.card F % 4 = 1) by omega, ↓reduceIte]
    exact hnsq (fun h => (hsqiff.1 h) h3)

end Aut



section Outer

variable {F : Type} [Field F] [Finite F]

theorem gammaOf_slConjugation (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (c : GL (Fin 2) F) :
    gammaOf hodd h3 (slConjugation F c) = SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk c) := by
  apply (thetaEquiv hodd h3).injective
  rw [thetaEquiv_gammaOf, psl2MulAutOf_slConjugation hodd h3]

theorem slConjugation_mem_inn_iff (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (c : GL (Fin 2) F) :
    slConjugation F c ∈ (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range ↔
      IsSquare ((c : Matrix (Fin 2) (Fin 2) F).det) := by
  rw [mem_inn_iff hodd h3, gammaOf_slConjugation]
  simp only [SemidirectProduct.right_inl, SemidirectProduct.left_inl, true_and]
  exact CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare c

end Outer



section Outer

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem sq_scalar_of_conj_sq_one (c : GL (Fin 2) F)
    (h : slConjugation F c * slConjugation F c = 1) :
    ∃ μ : F, (c : Matrix (Fin 2) (Fin 2) F) * c = μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hcc : slConjugation F (c * c) = 1 := by rw [map_mul]; exact h
  have hfix : ∀ X : SpecialLinearGroup (Fin 2) F,
      (c : Matrix (Fin 2) (Fin 2) F) * c * (X : Matrix (Fin 2) (Fin 2) F) =
        (X : Matrix (Fin 2) (Fin 2) F) * ((c : Matrix (Fin 2) (Fin 2) F) * c) := by
    intro X
    have h1 := slConjugation_toGL F (c * c) X
    rw [hcc] at h1
    have h2 : SpecialLinearGroup.toGL X = c * c * SpecialLinearGroup.toGL X * (c * c)⁻¹ := h1
    have h3 : c * c * SpecialLinearGroup.toGL X = SpecialLinearGroup.toGL X * (c * c) := by
      calc c * c * SpecialLinearGroup.toGL X
          = (c * c * SpecialLinearGroup.toGL X * (c * c)⁻¹) * (c * c) := by group
        _ = SpecialLinearGroup.toGL X * (c * c) := by rw [← h2]
    have h4 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h3
    simpa using h4
  let u : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let v : SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  exact exists_smul_one_of_commute_uv _ (hfix u) (hfix v)

omit [Finite F] in
theorem isSquare_det_of_scalar (c : GL (Fin 2) F) (s : F)
    (hs : (c : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F)) :
    IsSquare ((c : Matrix (Fin 2) (Fin 2) F).det) := by
  refine ⟨s, ?_⟩
  rw [hs, Matrix.det_smul, Matrix.det_one]
  simp [sq]

omit [Finite F] in
theorem mem_fixedSubgroup_slConjugation (G : GL (Fin 2) F) (x : SpecialLinearGroup (Fin 2) F) :
    x ∈ fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slConjugation F G) ↔
      SpecialLinearGroup.toGL x ∈ centralizer ({G} : Set (GL (Fin 2) F)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  show slConjugation F G x = x ↔ _
  constructor
  · intro h
    have h1 := slConjugation_toGL F G x
    rw [h] at h1
    calc SpecialLinearGroup.toGL x * G = (G * SpecialLinearGroup.toGL x * G⁻¹) * G := by rw [← h1]
      _ = G * SpecialLinearGroup.toGL x := by group
  · intro h
    apply SpecialLinearGroup.toGL_injective
    rw [slConjugation_toGL]
    calc G * SpecialLinearGroup.toGL x * G⁻¹ = (SpecialLinearGroup.toGL x * G) * G⁻¹ := by rw [h]
      _ = SpecialLinearGroup.toGL x := by group

omit [Finite F] in
theorem slCentralizer_eq_map (G : GL (Fin 2) F) :
    slCentralizer G = (fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slConjugation F G)).map
      (specialLinearGroupEquivStatedSL 2 F).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv]
  obtain ⟨x, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective y
  rw [MulEquiv.symm_apply_apply, mem_fixedSubgroup_slConjugation]
  rfl

end Outer



section Fixed

noncomputable def fixedEquivCongr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (φ : MulAut Q) :
    ↥(fixedSubgroup Q φ) ≃* ↥(fixedSubgroup Q' (MulAut.congr e φ)) :=
  (MulEquiv.subgroupMap e _).trans
    (MulEquiv.subgroupCongr (CFSG.GH74.GLS.Stage1.Thm3.Sec5.fixedSubgroup_congr e φ).symm)

theorem pPrimeCore_fixed_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (φ : MulAut Q) :
    pPrimeCore 2 ↥(fixedSubgroup Q φ) = ⊥ ↔
      pPrimeCore 2 ↥(fixedSubgroup Q' (MulAut.congr e φ)) = ⊥ := by
  have hmap := pPrimeCore_map_iso 2 (fixedEquivCongr e φ)
  rw [← hmap]
  exact (Subgroup.map_eq_bot_iff_of_injective _ (fixedEquivCongr e φ).injective).symm

theorem card_fixed_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (φ : MulAut Q) :
    Nat.card ↥(fixedSubgroup Q φ) = Nat.card ↥(fixedSubgroup Q' (MulAut.congr e φ)) :=
  Nat.card_congr (fixedEquivCongr e φ).toEquiv

end Fixed



section OuterMain

variable {F : Type} [Field F] [Finite F]

theorem pPrimeCore_fixed_slFieldAut (hodd : Odd (Nat.card F)) (σ : F ≃+* F) :
    pPrimeCore 2 ↥(fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slFieldAut σ)) = ⊥ := by
  have hq₀odd : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hodd
  have hq₀gt : 1 < Nat.card ↥(fixedField σ) := one_lt_card_fixedField σ
  have hmap := pPrimeCore_map_iso 2 (fixedEquivSL σ)
  have hbot : pPrimeCore 2 (SpecialLinearGroup (Fin 2) ↥(fixedField σ)) = ⊥ := by
    by_cases h3 : Nat.card ↥(fixedField σ) = 3
    · exact pPrimeCore_two_sl2_three h3
    · have h5 : 5 ≤ Nat.card ↥(fixedField σ) := by
        obtain ⟨k, hk⟩ := hq₀odd
        omega
      exact pPrimeCore_two_sl2_five hq₀odd h5
  rw [hbot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ (fixedEquivSL σ).injective).1 hmap

theorem pPrimeCore_fixed_of_field_part (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα2 : α * α = 1)
    (hσ : (gammaOf hodd h3 α).right ≠ 1) :
    pPrimeCore 2 ↥(fixedSubgroup (SpecialLinearGroup (Fin 2) F) α) = ⊥ := by
  obtain ⟨β, hβ⟩ := exists_conj_slFieldAut hodd h3 α hα2 hσ
  have hγ2 : gammaOf hodd h3 α * gammaOf hodd h3 α = 1 := by
    rw [← map_mul, hα2, map_one]
  have hσσ : (gammaOf hodd h3 α).right * (gammaOf hodd h3 α).right = 1 := by
    have := congrArg SemidirectProduct.right hγ2
    simpa using this
  have hαeq : α = MulAut.congr β (slFieldAut (gammaOf hodd h3 α).right) := by
    rw [← hβ]
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  have h0 := pPrimeCore_fixed_slFieldAut hodd (gammaOf hodd h3 α).right
  have h1 := (pPrimeCore_fixed_congr β (slFieldAut (gammaOf hodd h3 α).right)).1 h0
  rwa [← hαeq] at h1

omit [Finite F] in
theorem inn_of_congr_inn {Q : Type} [Group Q] (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ : MulAut Q)
    (h : MulAut.congr e φ ∈
      (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range) :
    φ ∈ (MulAut.conj : Q →* MulAut Q).range := by
  obtain ⟨s, hs⟩ := h
  refine ⟨e.symm s, ?_⟩
  apply (MulAut.congr e).injective
  rw [congr_conj, MulEquiv.apply_symm_apply, hs]

theorem fixed_outer {Q : Type} [Group Q] (e : Q ≃* SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (φ : MulAut Q) (hφ2 : φ * φ = 1)
    (hout : φ ∉ (MulAut.conj : Q →* MulAut Q).range) :
    pPrimeCore 2 ↥(fixedSubgroup Q φ) = ⊥ ∨
      Nat.card ↥(fixedSubgroup Q φ) = if Nat.card F % 4 = 1 then Nat.card F + 1 else Nat.card F - 1 := by
  have hα2 : MulAut.congr e φ * MulAut.congr e φ = 1 := by rw [← map_mul, hφ2, map_one]
  by_cases hσ : (gammaOf hodd h3 (MulAut.congr e φ)).right = 1
  · right
    obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
    have hsq := sq_scalar_of_conj_sq_one G (by rw [← hG]; exact hα2)
    have hdet : ¬ IsSquare ((G : Matrix (Fin 2) (Fin 2) F).det) := by
      intro hsqr
      apply hout
      apply inn_of_congr_inn e
      rw [hG]
      exact (slConjugation_mem_inn_iff hodd h3 G).2 hsqr
    have hns : ¬ ∃ s : F, (G : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rintro ⟨s, hs⟩
      exact hdet (isSquare_det_of_scalar G s hs)
    have hF : L2Field F := ⟨hodd, h3⟩
    have hcard : Nat.card ↥(fixedSubgroup Q φ) = Nat.card ↥(slCentralizer G) := by
      rw [card_fixed_congr e φ, hG, slCentralizer_eq_map]
      exact (Subgroup.card_map_of_injective (specialLinearGroupEquivStatedSL 2 F).injective).symm
    rw [hcard]
    have hmod : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hqpos : 0 < Nat.card F := Nat.card_pos
    rcases hmod with h1 | h3'
    · simp only [h1, ↓reduceIte]
      refine (slCentralizer_outer_involution hF 1 (Or.inl rfl) ?_ (Nat.card F + 1) ?_ G ⟨hsq.choose, hsq.choose_spec⟩ hns hdet).2
      · rw [Int.ModEq]; omega
      · push_cast; ring
    · simp only [show ¬ (Nat.card F % 4 = 1) by omega, ↓reduceIte]
      refine (slCentralizer_outer_involution hF (-1) (Or.inr rfl) ?_ (Nat.card F - 1) ?_ G ⟨hsq.choose, hsq.choose_spec⟩ hns hdet).2
      · rw [Int.ModEq]; omega
      · rw [Nat.cast_sub (by omega)]; push_cast; ring
  · left
    have h1 := pPrimeCore_fixed_of_field_part hodd h3 _ hα2 hσ
    exact (pPrimeCore_fixed_congr e φ).2 h1

end OuterMain

end CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound
