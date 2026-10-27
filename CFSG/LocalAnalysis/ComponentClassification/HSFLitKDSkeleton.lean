module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Skeleton

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup CFSG.CosetTable GorensteinWalter Blueprint

structure GHRel {G : Type*} [Group G] (z l α₁ α₂ α₃ α₄ x y a : G) : Prop where
  l_sq : l ^ 2 = z
  α₁_sq : α₁ ^ 2 = z
  α₂_sq : α₂ ^ 2 = z
  α₃_sq : α₃ ^ 2 = z
  α₄_sq : α₄ ^ 2 = z
  z_sq : z ^ 2 = 1
  x_sq : x ^ 2 = 1
  y_sq : y ^ 2 = 1
  a_sq : a ^ 2 = 1
  c_a1_a3 : α₁⁻¹ * α₃⁻¹ * α₁ * α₃ = z
  c_a2_a4 : α₂⁻¹ * α₄⁻¹ * α₂ * α₄ = z
  c_x_a1 : x⁻¹ * α₁⁻¹ * x * α₁ = z
  c_x_a2 : x⁻¹ * α₂⁻¹ * x * α₂ = z
  c_y_a2 : y⁻¹ * α₂⁻¹ * y * α₂ = z
  c_a_l : a⁻¹ * l⁻¹ * a * l = z
  c_x_a3 : x⁻¹ * α₃⁻¹ * x * α₃ = α₁
  c_x_a4 : x⁻¹ * α₄⁻¹ * x * α₄ = α₂
  c_y_a3 : y⁻¹ * α₃⁻¹ * y * α₃ = α₁ * α₂ * l
  c_y_a4 : y⁻¹ * α₄⁻¹ * y * α₄ = α₁ * l * z
  c_a_a1 : a⁻¹ * α₁⁻¹ * a * α₁ = α₁ * α₂ * z
  c_a_a2 : a⁻¹ * α₂⁻¹ * a * α₂ = α₁ * α₂ * z
  c_a_a3 : a⁻¹ * α₃⁻¹ * a * α₃ = α₃ * α₄ * z
  c_a_a4 : a⁻¹ * α₄⁻¹ * a * α₄ = α₃ * α₄ * z
  c_a_y : a⁻¹ * y⁻¹ * a * y = x * α₁ * α₂ * l * z
  comm_z_l : z * l = l * z
  comm_z_a1 : z * α₁ = α₁ * z
  comm_z_a2 : z * α₂ = α₂ * z
  comm_z_a3 : z * α₃ = α₃ * z
  comm_z_a4 : z * α₄ = α₄ * z
  comm_z_x : z * x = x * z
  comm_z_y : z * y = y * z
  comm_z_a : z * a = a * z
  comm_l_a1 : l * α₁ = α₁ * l
  comm_l_a2 : l * α₂ = α₂ * l
  comm_l_a3 : l * α₃ = α₃ * l
  comm_l_a4 : l * α₄ = α₄ * l
  comm_l_x : l * x = x * l
  comm_l_y : l * y = y * l
  comm_a1_a2 : α₁ * α₂ = α₂ * α₁
  comm_a1_a4 : α₁ * α₄ = α₄ * α₁
  comm_a1_y : α₁ * y = y * α₁
  comm_a2_a3 : α₂ * α₃ = α₃ * α₂
  comm_a3_a4 : α₃ * α₄ = α₄ * α₃
  comm_x_y : x * y = y * x
  comm_x_a : x * a = a * x

@[expose] def ghWords : List (List (Fin 9 × Bool)) :=
  [[(1, true), (1, true), (0, false)],
    [(2, true), (2, true), (0, false)],
    [(3, true), (3, true), (0, false)],
    [(4, true), (4, true), (0, false)],
    [(5, true), (5, true), (0, false)],
    [(0, true), (0, true)],
    [(6, true), (6, true)],
    [(7, true), (7, true)],
    [(8, true), (8, true)],
    [(2, false), (4, false), (2, true), (4, true), (0, false)],
    [(3, false), (5, false), (3, true), (5, true), (0, false)],
    [(6, false), (2, false), (6, true), (2, true), (0, false)],
    [(6, false), (3, false), (6, true), (3, true), (0, false)],
    [(7, false), (3, false), (7, true), (3, true), (0, false)],
    [(8, false), (1, false), (8, true), (1, true), (0, false)],
    [(6, false), (4, false), (6, true), (4, true), (2, false)],
    [(6, false), (5, false), (6, true), (5, true), (3, false)],
    [(7, false), (4, false), (7, true), (4, true), (1, false), (3, false), (2, false)],
    [(7, false), (5, false), (7, true), (5, true), (0, false), (1, false), (2, false)],
    [(8, false), (2, false), (8, true), (2, true), (0, false), (3, false), (2, false)],
    [(8, false), (3, false), (8, true), (3, true), (0, false), (3, false), (2, false)],
    [(8, false), (4, false), (8, true), (4, true), (0, false), (5, false), (4, false)],
    [(8, false), (5, false), (8, true), (5, true), (0, false), (5, false), (4, false)],
    [(8, false), (7, false), (8, true), (7, true), (0, false), (1, false), (3, false), (2, false),
      (6, false)],
    [(0, true), (1, true), (0, false), (1, false)],
    [(0, true), (2, true), (0, false), (2, false)],
    [(0, true), (3, true), (0, false), (3, false)],
    [(0, true), (4, true), (0, false), (4, false)],
    [(0, true), (5, true), (0, false), (5, false)],
    [(0, true), (6, true), (0, false), (6, false)],
    [(0, true), (7, true), (0, false), (7, false)],
    [(0, true), (8, true), (0, false), (8, false)],
    [(1, true), (2, true), (1, false), (2, false)],
    [(1, true), (3, true), (1, false), (3, false)],
    [(1, true), (4, true), (1, false), (4, false)],
    [(1, true), (5, true), (1, false), (5, false)],
    [(1, true), (6, true), (1, false), (6, false)],
    [(1, true), (7, true), (1, false), (7, false)],
    [(2, true), (3, true), (2, false), (3, false)],
    [(2, true), (5, true), (2, false), (5, false)],
    [(2, true), (7, true), (2, false), (7, false)],
    [(3, true), (4, true), (3, false), (4, false)],
    [(4, true), (5, true), (4, false), (5, false)],
    [(6, true), (7, true), (6, false), (7, false)],
    [(6, true), (8, true), (6, false), (8, false)]]

abbrev GHGroup : Type := PG 9 ghWords

@[expose] def ghFam {G : Type*} (z l α₁ α₂ α₃ α₄ x y a : G) : Fin 9 → G
  | 0 => z
  | 1 => l
  | 2 => α₁
  | 3 => α₂
  | 4 => α₃
  | 5 => α₄
  | 6 => x
  | 7 => y
  | 8 => a

theorem range_ghFam {G : Type*} (z l α₁ α₂ α₃ α₄ x y a : G) :
    Set.range (ghFam z l α₁ α₂ α₃ α₄ x y a) = {z, l, α₁, α₂, α₃, α₄, x, y, a} := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [ghFam]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩, ⟨7, rfl⟩,
      ⟨8, rfl⟩]

namespace GHRel

variable {G : Type*} [Group G] {z l α₁ α₂ α₃ α₄ x y a : G}

theorem lift_eq_one (h : GHRel z l α₁ α₂ α₃ α₄ x y a) :
    ∀ r ∈ {r : FreeGroup (Fin 9) | r ∈ ghWords.map FreeGroup.mk},
      FreeGroup.lift (ghFam z l α₁ α₂ α₃ α₄ x y a) r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  simp only [ghWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
  all_goals simp only [FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Bool.cond_true, Bool.cond_false, ghFam, mul_one]
  · have e := h.l_sq
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.α₁_sq
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.α₂_sq
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.α₃_sq
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.α₄_sq
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.z_sq
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.x_sq
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.y_sq
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.a_sq
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_a1_a3
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_a2_a4
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_x_a1
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_x_a2
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_y_a2
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_a_l
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_x_a3
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_x_a4
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_y_a3
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_y_a4
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_a_a1
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_a_a2
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_a_a3
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_a_a4
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.c_a_y
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_z_l
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_z_a1
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_z_a2
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_z_a3
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_z_a4
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_z_x
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_z_y
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_z_a
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_l_a1
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_l_a2
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_l_a3
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_l_a4
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_l_x
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_l_y
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_a1_a2
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_a1_a4
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_a1_y
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_a2_a3
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_a3_a4
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_x_y
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e
  · have e := h.comm_x_a
    rw [← mul_inv_eq_one] at e
    simpa only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one] using e

@[expose] noncomputable def hom (h : GHRel z l α₁ α₂ α₃ α₄ x y a) : GHGroup →* G :=
  PresentedGroup.toGroup h.lift_eq_one

theorem range_hom (h : GHRel z l α₁ α₂ α₃ α₄ x y a) :
    h.hom.range = Subgroup.closure {z, l, α₁, α₂, α₃, α₄, x, y, a} := by
  rw [hom, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp, ← range_ghFam]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, PresentedGroup.toGroup.of]

end GHRel

@[expose] def GHPresentationBound : Prop := Finite GHGroup ∧ Nat.card GHGroup ≤ 512

@[expose] def GHRelInHS : Prop :=
  ∃ z l α₁ α₂ α₃ α₄ x y a : NativeSporadic.HS, GHRel z l α₁ α₂ α₃ α₄ x y a ∧
    Nat.card (Subgroup.closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set NativeSporadic.HS)) = 512

theorem nonempty_equiv_of_ghRel (hB : GHPresentationBound) {G : Type*} [Group G]
    {z l α₁ α₂ α₃ α₄ x y a : G} (h : GHRel z l α₁ α₂ α₃ α₄ x y a)
    (hcard : Nat.card (Subgroup.closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set G)) = 512) :
    Nonempty (GHGroup ≃* Subgroup.closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set G)) := by
  obtain ⟨hfin, hle⟩ := hB
  have hsurj := h.hom.rangeRestrict_surjective
  have hr : Nat.card h.hom.range = 512 := by rw [h.range_hom, hcard]
  have hbij : Function.Bijective h.hom.rangeRestrict :=
    hsurj.bijective_of_nat_card_le (by omega)
  exact ⟨(MulEquiv.ofBijective _ hbij).trans (MulEquiv.subgroupCongr h.range_hom)⟩

theorem isTypeHS_of_ghRel (hB : GHPresentationBound) (hM : GHRelInHS) {X : Type} [Group X]
    [Finite X] (S : Sylow 2 X) {z l α₁ α₂ α₃ α₄ x y a : X} (h : GHRel z l α₁ α₂ α₃ α₄ x y a)
    (hgen : Subgroup.closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set X) = S)
    (hcard : Nat.card (S : Subgroup X) = 512) : IsTypeHS X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite NativeSporadic.HS := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.HS.card_HS]; norm_num)
  obtain ⟨z', l', α₁', α₂', α₃', α₄', x', y', a', h', hcard'⟩ := hM
  obtain ⟨e⟩ := nonempty_equiv_of_ghRel hB h (by rw [hgen, hcard])
  obtain ⟨e'⟩ := nonempty_equiv_of_ghRel hB h' hcard'
  set Q : Sylow 2 NativeSporadic.HS :=
    Sylow.ofCard (Subgroup.closure
      ({z', l', α₁', α₂', α₃', α₄', x', y', a'} : Set NativeSporadic.HS)) (by
      rw [hcard', CFSG.Sporadic.HS.card_HS, show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 86625)]
      norm_num)
  refine ⟨S, Q, ⟨?_⟩⟩
  exact ((MulEquiv.subgroupCongr hgen).symm.trans e.symm).trans
    (e'.trans (MulEquiv.subgroupCongr (Sylow.coe_ofCard _ _).symm))

@[expose] def FritzKDSylow : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (F : Type) [Field F] [Finite F],
      Nonempty (L ⧸ pPrimeCore 2 L ≃* PSL2 F) → ∀ A : L2Data t L, A.CaseKD →
        ∃ (S : Sylow 2 X) (z l α₁ α₂ α₃ α₄ x y a : X), GHRel z l α₁ α₂ α₃ α₄ x y a ∧
          Subgroup.closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set X) = S ∧
          Nat.card (S : Subgroup X) = 512

@[expose] def HSQuotA6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X) (L : Subgroup X), Config t L →
    Nonempty (X ≃* NativeSporadic.HS) → Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 6))

theorem fritzL2CaseKD_of_parts (hB : GHPresentationBound) (hM : GHRelInHS)
    (hKD : FritzKDSylow) (hA6 : HSQuotA6) : FritzL2CaseKD := by
  intro hH hGH X _ _ _ hnonab hnot t L F _ _ he A C
  obtain ⟨S, z, l, α₁, α₂, α₃, α₄, x, y, a, h, hgen, hcard⟩ :=
    hKD hH X hnonab hnot t L F he A C
  have hX : Nonempty (X ≃* NativeSporadic.HS) :=
    gorensteinHarris_corollaryA hGH (isTypeHS_of_ghRel hB hM S h hgen hcard)
  exact ⟨hA6 X t L A.config hX, hX⟩

end CFSG.ComponentClassification.HSFLit
