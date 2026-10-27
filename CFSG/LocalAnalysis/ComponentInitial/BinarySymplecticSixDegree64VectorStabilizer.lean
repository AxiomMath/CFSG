module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixPointRadicalCoordinates
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Matrix

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (ZMod 2)

@[expose] def glX : GL (Fin 2) (ZMod 2) :=
  ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> decide,
    by ext i j; fin_cases i <;> fin_cases j <;> decide⟩

@[expose] def glY : GL (Fin 2) (ZMod 2) :=
  ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by ext i j; fin_cases i <;> fin_cases j <;> decide,
    by ext i j; fin_cases i <;> fin_cases j <;> decide⟩

theorem zmod_two_comm_XY : ∀ a b c d : ZMod 2,
    !![(1 : ZMod 2), 1; 0, 1] * !![a, b; c, d] = !![a, b; c, d] * !![(1 : ZMod 2), 1; 0, 1] →
    !![(1 : ZMod 2), 0; 1, 1] * !![a, b; c, d] = !![a, b; c, d] * !![(1 : ZMod 2), 0; 1, 1] →
    a * d - b * c ≠ 0 → !![a, b; c, d] = 1 := by
  decide

theorem eq_one_of_comm_GL_two {t : GL (Fin 2) (ZMod 2)} (hX : glX * t = t * glX)
    (hY : glY * t = t * glY) : t = 1 := by
  have hX' : (!![1, 1; 0, 1] : M₂) * (t : M₂) = (t : M₂) * !![1, 1; 0, 1] := by
    rw [← show ((glX : GL (Fin 2) (ZMod 2)) : M₂) = !![1, 1; 0, 1] from rfl, ← Units.val_mul,
      hX, Units.val_mul]
  have hY' : (!![1, 0; 1, 1] : M₂) * (t : M₂) = (t : M₂) * !![1, 0; 1, 1] := by
    rw [← show ((glY : GL (Fin 2) (ZMod 2)) : M₂) = !![1, 0; 1, 1] from rfl, ← Units.val_mul,
      hY, Units.val_mul]
  have hdet : (t : M₂).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 t.isUnit).ne_zero
  apply Units.ext
  rw [Units.val_one]
  rw [Matrix.eta_fin_two (t : M₂)] at hX' hY' hdet ⊢
  rw [Matrix.det_fin_two_of] at hdet
  exact zmod_two_comm_XY _ _ _ _ hX' hY' hdet

theorem card_GL_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  norm_num

theorem eq_bot_of_normal_GL_two {N : Subgroup (GL (Fin 2) (ZMod 2))} (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hdvd : Nat.card N ∣ 6 := card_GL_two ▸ Subgroup.card_subgroup_dvd_card N
  rw [hk] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := Nat.dvd_trans h4 hdvd
    norm_num at this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with rfl | rfl
  · rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq N hk
  · exfalso
    rw [pow_one] at hk
    have hne : N ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hk
      norm_num at hk
    obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have h3 : ∀ x ∈ N, x = 1 ∨ x = t := by
      intro x hx
      by_contra hne'
      push Not at hne'
      have hsub : ({(1 : GL (Fin 2) (ZMod 2)), t, x} : Set _) ⊆ N := by
        intro y hy
        rcases hy with rfl | rfl | rfl
        · exact N.one_mem
        · exact ht
        · exact hx
      have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hn1 : (1 : GL (Fin 2) (ZMod 2)) ∉ ({t, x} : Set _) := by
        rintro (h | h)
        · exact ht1' h.symm
        · exact hne'.1 h.symm
      rw [Set.ncard_insert_of_notMem hn1, Set.ncard_pair (fun h => hne'.2 h.symm),
        ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hk] at hcard
      omega
    have hcen : ∀ g : GL (Fin 2) (ZMod 2), g * t = t * g := by
      intro g
      rcases h3 _ (hN.conj_mem t ht g) with h | h
      · exfalso
        apply ht1'
        have := congrArg (fun y => g⁻¹ * y * g) h
        simpa [mul_assoc] using this
      · calc g * t = g * t * g⁻¹ * g := by group
          _ = t * g := by rw [h]
    exact ht1' (eq_one_of_comm_GL_two (hcen glX) (hcen glY))

@[expose] def vecStabGL : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {g | (g : M₃) 0 0 = 1 ∧ (g : M₃) 1 0 = 0 ∧ (g : M₃) 2 0 = 0}
  mul_mem' := by
    rintro g h ⟨g0, g1, g2⟩ ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, g0, g1, g2,
        mul_one, mul_zero, add_zero]
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> simp
  inv_mem' := by
    rintro g ⟨g0, g1, g2⟩
    have hinv : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) * (g : M₃) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e := fun i => congrFun (congrFun hinv i) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, g0, g1, g2, mul_one, mul_zero,
      add_zero] at e
    exact ⟨by simpa using e 0, by simpa using e 1, by simpa using e 2⟩

theorem mem_vecStabGL {g : GL (Fin 3) (ZMod 2)} :
    g ∈ vecStabGL ↔ (g : M₃) 0 0 = 1 ∧ (g : M₃) 1 0 = 0 ∧ (g : M₃) 2 0 = 0 :=
  Iff.rfl

theorem lagrangianT0_le_vecStabGL : lagrangianT0 ≤ vecStabGL := by
  rintro _ ⟨⟨a, a'⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp [coe_t0Unit, t0Mat]

@[expose] def blk (M : M₃) : M₂ :=
  !![M 1 1, M 1 2; M 2 1, M 2 2]

theorem blk_mul {M N : M₃} (h1 : M 1 0 = 0) (h2 : M 2 0 = 0) : blk (M * N) = blk M * blk N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h1, h2]

theorem blk_one : blk (1 : M₃) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

@[expose] def blkHom : vecStabGL →* GL (Fin 2) (ZMod 2) where
  toFun g := ⟨blk ((g : GL (Fin 3) (ZMod 2)) : M₃), blk (((g : GL (Fin 3) (ZMod 2))⁻¹ :
      GL (Fin 3) (ZMod 2)) : M₃), by
    rw [← blk_mul g.2.2.1 g.2.2.2, ← Units.val_mul, mul_inv_cancel, Units.val_one, blk_one], by
    rw [← blk_mul (vecStabGL.inv_mem g.2).2.1 (vecStabGL.inv_mem g.2).2.2, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, blk_one]⟩
  map_one' := Units.ext (by
    change blk ((1 : GL (Fin 3) (ZMod 2)) : M₃) = 1
    rw [Units.val_one, blk_one])
  map_mul' g h := Units.ext (by
    change blk (((g : GL (Fin 3) (ZMod 2)) * (h : GL (Fin 3) (ZMod 2)) : GL (Fin 3) (ZMod 2)) :
      M₃) = blk ((g : GL (Fin 3) (ZMod 2)) : M₃) * blk ((h : GL (Fin 3) (ZMod 2)) : M₃)
    rw [Units.val_mul, blk_mul g.2.2.1 g.2.2.2])

theorem coe_blkHom (g : vecStabGL) :
    ((blkHom g : GL (Fin 2) (ZMod 2)) : M₂) = blk ((g : GL (Fin 3) (ZMod 2)) : M₃) :=
  rfl

@[expose] def extMat (M : M₂) : M₃ :=
  !![1, 0, 0; 0, M 0 0, M 0 1; 0, M 1 0, M 1 1]

theorem extMat_mul (M N : M₂) : extMat M * extMat N = extMat (M * N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem extMat_one : extMat (1 : M₂) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [extMat]

theorem blkHom_surjective : Function.Surjective blkHom := by
  intro M
  let g : GL (Fin 3) (ZMod 2) := ⟨extMat (M : M₂), extMat ((M⁻¹ : GL (Fin 2) (ZMod 2)) : M₂), by
    rw [extMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, extMat_one], by
    rw [extMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, extMat_one]⟩
  have hg : g ∈ vecStabGL := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [g, extMat]
  refine ⟨⟨g, hg⟩, Units.ext ?_⟩
  rw [coe_blkHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g, blk, extMat]

theorem t0Mat_eq_of_blk {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ vecStabGL)
    (h : blk (g : M₃) = 1) : g = t0Unit ((g : M₃) 0 1) ((g : M₃) 0 2) := by
  obtain ⟨g0, g1, g2⟩ := hg
  have e := fun i j => congrFun (congrFun h i) j
  apply Units.ext
  rw [coe_t0Unit]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [t0Mat] using g0
  · simp [t0Mat]
  · simp [t0Mat]
  · simpa [t0Mat] using g1
  · simpa [blk, t0Mat] using e 0 0
  · simpa [blk, t0Mat] using e 0 1
  · simpa [t0Mat] using g2
  · simpa [blk, t0Mat] using e 1 0
  · simpa [blk, t0Mat] using e 1 1

theorem ker_blkHom : blkHom.ker = lagrangianT0.subgroupOf vecStabGL := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h' : blk ((g : GL (Fin 3) (ZMod 2)) : M₃) = 1 := by
      have := congrArg (fun x : GL (Fin 2) (ZMod 2) => (x : M₂)) h
      simpa [coe_blkHom] using this
    rw [t0Mat_eq_of_blk g.2 h']
    exact ⟨(_, _), rfl⟩
  · rintro ⟨⟨a, a'⟩, ha⟩
    apply Units.ext
    rw [coe_blkHom, ← ha, coe_t0Unit, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk, t0Mat]

theorem card_vecStabGL : Nat.card vecStabGL = 24 := by
  have h1 := Subgroup.card_mul_index blkHom.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 blkHom_surjective, Subgroup.card_top,
    card_GL_two] at h1
  have h3 : Nat.card blkHom.ker = 4 := by
    rw [ker_blkHom, ← card_lagrangianT0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe lagrangianT0_le_vecStabGL).toEquiv
  rw [← h1, h3]

theorem le_lagrangianT0_of_normal {P : Subgroup (GL (Fin 3) (ZMod 2))} (hPS : P ≤ vecStabGL)
    (hn : ∀ g ∈ vecStabGL, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (h2 : IsPGroup 2 P) : P ≤ lagrangianT0 := by
  have hP'n : (P.subgroupOf vecStabGL).Normal := ⟨fun p hp g => by
    rw [Subgroup.mem_subgroupOf] at hp ⊢
    exact hn g g.2 p hp⟩
  have hP'2 : IsPGroup 2 (P.subgroupOf vecStabGL) :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm
  have hbot := eq_bot_of_normal_GL_two (hP'n.map blkHom blkHom_surjective)
    (hP'2.map blkHom)
  intro p hp
  have h1 : blkHom ⟨p, hPS hp⟩ ∈ (P.subgroupOf vecStabGL).map blkHom :=
    ⟨⟨p, hPS hp⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
  rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_blkHom, Subgroup.mem_subgroupOf] at h1
  exact h1

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
