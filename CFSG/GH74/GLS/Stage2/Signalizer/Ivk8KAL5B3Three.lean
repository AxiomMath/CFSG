module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL5Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.LieType.HighestRoot (three_eq_zero card_eq_24 eight_le_card_of_normal
  mem_center_iff_of_mulEquiv slEquivSL23 closure_orderOf_three_eq_top
  exists_mul_of_mem_sup_of_commute conj_mul_commutator)
open scoped MatrixGroups

section Field

variable {F : Type} [Field F] [Finite F]

theorem kaL5B3T_two_ne_zero (hK : Nat.card F = 3) : (2 : F) ≠ 0 := by
  intro h2
  have h3 := three_eq_zero hK
  have : (1 : F) = 0 := by linear_combination h3 - h2
  exact one_ne_zero this

theorem kaL5B3T_ringChar_ne_two (hK : Nat.card F = 3) : ringChar F ≠ 2 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).2 (by rw [h])
  exact kaL5B3T_two_ne_zero hK (by exact_mod_cast h')

theorem kaL5B3T_sq_eq_one (hK : Nat.card F = 3) {a : F} (ha : a ≠ 0) : a * a = 1 := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.card_eq_fintype_card, hK] at h
  simpa [sq] using h

end Field

section Defs

variable {F : Type} [Field F]

@[expose] def kaL5B3TMat (F : Type) [Field F] : Matrix (Fin 5) (Fin 5) F :=
  Matrix.diagonal fun i : Fin 5 => if (i : ℕ) < 3 then (1 : F) else -1

theorem kaL5B3TMat_mul_self : kaL5B3TMat F * kaL5B3TMat F = 1 := by
  rw [kaL5B3TMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

@[expose] def kaL5B3TGL (F : Type) [Field F] : GL (Fin 5) F :=
  ⟨kaL5B3TMat F, kaL5B3TMat F, kaL5B3TMat_mul_self, kaL5B3TMat_mul_self⟩

theorem coe_kaL5B3TGL :
    ((kaL5B3TGL F : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = kaL5B3TMat F :=
  rfl

theorem kaL5B3TGL_mul_self : kaL5B3TGL F * kaL5B3TGL F = 1 :=
  Units.ext (by rw [Units.val_mul, coe_kaL5B3TGL, kaL5B3TMat_mul_self, Units.val_one])

theorem kaL5B3TGL_inv : (kaL5B3TGL F)⁻¹ = kaL5B3TGL F :=
  inv_eq_of_mul_eq_one_right kaL5B3TGL_mul_self

theorem kaL5B3T_exists_frame (hK : ringChar F ≠ 2) {B : GL (Fin 5) F} (hB : B * B = 1)
    (h3 : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 3) :
    ∃ P : GL (Fin 5) F, B = P * kaL5B3TGL F * P⁻¹ := by
  have hBm : (B : Matrix (Fin 5) (Fin 5) F) * B = 1 := by
    rw [← Units.val_mul, hB, Units.val_one]
  obtain ⟨b, hb⟩ := exists_eigenbasis hK hBm
  obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B
  have hDd : (D : Matrix (Fin 5) (Fin 5) F) = kaL5B3TMat F := by
    rw [hD, kaL5B3TMat]
    ext a c
    rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, h3, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
    by_cases hac : a = c
    · subst hac
      simp
    · simp [hac, Ne.symm hac]
  refine ⟨P, ?_⟩
  have hDe : D = kaL5B3TGL F := Units.ext hDd
  rw [← hDe, ← hPD]
  group

end Defs

section Blocks

variable {F : Type} [Field F]

theorem kaL5B3T_det_diagBlock (X : Matrix (Fin 3) (Fin 3) F) (Y : Matrix (Fin 2) (Fin 2) F) :
    (diagBlock X Y).det = X.det * Y.det := by
  rw [diagBlock, det_reindex_self, det_fromBlocks_zero₁₂]

@[expose] def kaL5B3THom (F : Type) [Field F] : SL(3, F) × SL(2, F) →* SL(5, F) where
  toFun p := ⟨diagBlock (p.1 : Matrix (Fin 3) (Fin 3) F) (p.2 : Matrix (Fin 2) (Fin 2) F), by
    rw [kaL5B3T_det_diagBlock, p.1.2, p.2.2, one_mul]⟩
  map_one' := Subtype.ext (by
    simp only [Prod.fst_one, Prod.snd_one, Matrix.SpecialLinearGroup.coe_one]
    exact diagBlock_one)
  map_mul' p q := Subtype.ext (by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact (diagBlock_mul _ _ _ _).symm)

theorem coe_kaL5B3THom (p : SL(3, F) × SL(2, F)) :
    ((kaL5B3THom F p : SL(5, F)) : Matrix (Fin 5) (Fin 5) F) =
      diagBlock (p.1 : Matrix (Fin 3) (Fin 3) F) (p.2 : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem kaL5B3T_diagBlock_inj {X X' : Matrix (Fin 3) (Fin 3) F} {Y Y' : Matrix (Fin 2) (Fin 2) F}
    (h : diagBlock X Y = diagBlock X' Y') : X = X' ∧ Y = Y' := by
  have h1 : fromBlocks X 0 0 Y = fromBlocks X' 0 0 Y' :=
    (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h
  have h2 := Matrix.fromBlocks_inj.1 h1
  exact ⟨h2.1, h2.2.2.2⟩

theorem kaL5B3THom_injective : Function.Injective (kaL5B3THom F) := by
  intro p q h
  have h1 := kaL5B3T_diagBlock_inj (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext h1.1) (Subtype.ext h1.2)

theorem kaL5B3T_val_inl (i : Fin 3) :
    (finSumFinEquiv (Sum.inl i : Fin 3 ⊕ Fin 2) : Fin 5).val = i.val :=
  rfl

theorem kaL5B3T_val_inr (j : Fin 2) :
    (finSumFinEquiv (Sum.inr j : Fin 3 ⊕ Fin 2) : Fin 5).val = 3 + j.val :=
  rfl

theorem kaL5B3T_exists_blk (h2 : (2 : F) ≠ 0) {g : Matrix (Fin 5) (Fin 5) F}
    (hg : g * kaL5B3TMat F = kaL5B3TMat F * g) :
    ∃ (A : Matrix (Fin 3) (Fin 3) F) (D : Matrix (Fin 2) (Fin 2) F), g = diagBlock A D := by
  have key : ∀ x : F, -x = x → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.1 this).resolve_left h2
  refine ⟨Matrix.of fun i j => g (finSumFinEquiv (Sum.inl i : Fin 3 ⊕ Fin 2))
      (finSumFinEquiv (Sum.inl j : Fin 3 ⊕ Fin 2)),
    Matrix.of fun i j => g (finSumFinEquiv (Sum.inr i : Fin 3 ⊕ Fin 2))
      (finSumFinEquiv (Sum.inr j : Fin 3 ⊕ Fin 2)), ?_⟩
  ext a b
  obtain ⟨a, rfl⟩ := (finSumFinEquiv (m := 3) (n := 2)).surjective a
  obtain ⟨b, rfl⟩ := (finSumFinEquiv (m := 3) (n := 2)).surjective b
  have hab := congrFun (congrFun hg (finSumFinEquiv (m := 3) (n := 2) a))
    (finSumFinEquiv (m := 3) (n := 2) b)
  rw [kaL5B3TMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at hab
  rw [diagBlock, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases a with i | i <;> rcases b with j | j
  · rw [fromBlocks_apply₁₁]
    rfl
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    simp [kaL5B3T_val_inl, kaL5B3T_val_inr] at hab
    exact key _ hab
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    simp [kaL5B3T_val_inl, kaL5B3T_val_inr] at hab
    exact key _ hab.symm
  · rw [fromBlocks_apply₂₂]
    rfl

theorem kaL5B3T_blk_comm (A : Matrix (Fin 3) (Fin 3) F) (D : Matrix (Fin 2) (Fin 2) F) :
    diagBlock A D * kaL5B3TMat F = kaL5B3TMat F * diagBlock A D := by
  ext a b
  obtain ⟨a, rfl⟩ := (finSumFinEquiv (m := 3) (n := 2)).surjective a
  obtain ⟨b, rfl⟩ := (finSumFinEquiv (m := 3) (n := 2)).surjective b
  rw [kaL5B3TMat, Matrix.mul_diagonal, Matrix.diagonal_mul, diagBlock, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a with i | i <;> rcases b with j | j
  · simp [kaL5B3T_val_inl, mul_comm]
  · simp [kaL5B3T_val_inl, kaL5B3T_val_inr]
  · simp [kaL5B3T_val_inl, kaL5B3T_val_inr]
  · simp [kaL5B3T_val_inr, mul_comm]

end Blocks

section Cent

variable {F : Type} [Field F]

theorem kaL5B3T_mem_cent {g : SL(5, F)} :
    g ∈ kaSlCent5 (kaL5B3TGL F) ↔
      (g : Matrix (Fin 5) (Fin 5) F) * kaL5B3TMat F = kaL5B3TMat F * g := by
  rw [kaSlCent5, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h1 := congrArg (fun u : GL (Fin 5) F => (u : Matrix (Fin 5) (Fin 5) F))
      (h (kaL5B3TGL F) (Set.mem_singleton _))
    simp only [Units.val_mul, coe_kaL5B3TGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h1
    exact h1.symm
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    apply Units.ext
    simp only [Units.val_mul, coe_kaL5B3TGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact h.symm

theorem kaL5B3T_blk_mem_cent (p : SL(3, F) × SL(2, F)) :
    kaL5B3THom F p ∈ kaSlCent5 (kaL5B3TGL F) := by
  rw [kaL5B3T_mem_cent, coe_kaL5B3THom]
  exact kaL5B3T_blk_comm _ _

theorem kaL5B3T_map_le_fix {x : projectiveSL 5 F}
    (hx : x ∈ (kaSlCent5 (kaL5B3TGL F)).map (proj 5 F)) :
    conjAut 5 F (kaL5B3TGL F) x = x := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hc := kaL5B3T_mem_cent.1 hg
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, kaL5B3TGL_inv, coe_kaL5B3TGL, ← hc, Matrix.mul_assoc,
    kaL5B3TMat_mul_self, Matrix.mul_one]

@[expose] noncomputable def kaL5B3TPhi (F : Type) [Field F] :
    SL(3, F) × SL(2, F) →* projectiveSL 5 F :=
  (proj 5 F).comp (kaL5B3THom F)

@[expose] noncomputable def kaL5B3TInl (F : Type) [Field F] : SL(3, F) →* projectiveSL 5 F :=
  (kaL5B3TPhi F).comp (MonoidHom.inl _ _)

@[expose] noncomputable def kaL5B3TInr (F : Type) [Field F] : SL(2, F) →* projectiveSL 5 F :=
  (kaL5B3TPhi F).comp (MonoidHom.inr _ _)

@[expose] noncomputable def kaL5B3TL (F : Type) [Field F] : Subgroup (projectiveSL 5 F) :=
  (kaL5B3TPhi F).range

theorem kaL5B3T_phi (s : SL(3, F)) (t : SL(2, F)) :
    kaL5B3TPhi F (s, t) = kaL5B3TInl F s * kaL5B3TInr F t := by
  show kaL5B3TPhi F (s, t) = kaL5B3TPhi F (s, 1) * kaL5B3TPhi F (1, t)
  rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem kaL5B3T_comm (s : SL(3, F)) (t : SL(2, F)) :
    kaL5B3TInl F s * kaL5B3TInr F t = kaL5B3TInr F t * kaL5B3TInl F s := by
  have h2 : kaL5B3TPhi F (s, t) = kaL5B3TInr F t * kaL5B3TInl F s := by
    show kaL5B3TPhi F (s, t) = kaL5B3TPhi F (1, t) * kaL5B3TPhi F (s, 1)
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [← kaL5B3T_phi, h2]

theorem kaL5B3T_inl_mem (s : SL(3, F)) : kaL5B3TInl F s ∈ kaL5B3TL F := ⟨(s, 1), rfl⟩

theorem kaL5B3T_inr_mem (t : SL(2, F)) : kaL5B3TInr F t ∈ kaL5B3TL F := ⟨(1, t), rfl⟩

theorem kaL5B3T_L_le_sup : kaL5B3TL F ≤ (kaL5B3TInl F).range ⊔ (kaL5B3TInr F).range := by
  rintro _ ⟨⟨s, t⟩, rfl⟩
  change kaL5B3TPhi F (s, t) ∈ _
  rw [kaL5B3T_phi]
  exact mul_mem (Subgroup.mem_sup_left ⟨s, rfl⟩) (Subgroup.mem_sup_right ⟨t, rfl⟩)

theorem kaL5B3T_L_le_fix : kaL5B3TL F ≤ fixSub (conjAut 5 F (kaL5B3TGL F)) := by
  rintro _ ⟨p, rfl⟩
  exact mem_fixSub.2 (kaL5B3T_map_le_fix ⟨kaL5B3THom F p, kaL5B3T_blk_mem_cent p, rfl⟩)

end Cent

section Odd

variable {F : Type} [Field F] [Finite F]

theorem kaL5B3T_sq_mem (hK : Nat.card F = 3) {g : SL(5, F)}
    (hg : g ∈ kaSlCent5 (kaL5B3TGL F)) :
    ∃ p : SL(3, F) × SL(2, F), g * g = kaL5B3THom F p := by
  obtain ⟨A, D, hAD⟩ := kaL5B3T_exists_blk (kaL5B3T_two_ne_zero hK) (kaL5B3T_mem_cent.1 hg)
  have hdet : A.det * D.det = 1 := by
    rw [← kaL5B3T_det_diagBlock, ← hAD]
    exact g.2
  refine ⟨(⟨A * A, ?_⟩, ⟨D * D, ?_⟩), ?_⟩
  · rw [Matrix.det_mul]
    exact kaL5B3T_sq_eq_one hK (left_ne_zero_of_mul_eq_one hdet)
  · rw [Matrix.det_mul]
    exact kaL5B3T_sq_eq_one hK (right_ne_zero_of_mul_eq_one hdet)
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hAD, coe_kaL5B3THom]
    exact diagBlock_mul _ _ _ _

theorem kaL5B3T_odd_mem (hK : Nat.card F = 3) {y : projectiveSL 5 F}
    (hy : y ∈ (kaSlCent5 (kaL5B3TGL F)).map (proj 5 F)) (ho : Odd (orderOf y)) :
    y ∈ kaL5B3TL F := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨p, hp⟩ := kaL5B3T_sq_mem hK hg
  refine ka_odd_mem_of_sq_mem ?_ ho
  rw [← map_mul, hp]
  exact ⟨p, rfl⟩

theorem kaL5B3T_closure_odd_sl2 (hK : Nat.card F = 3) :
    Subgroup.closure {y : SL(2, F) | Odd (orderOf y)} = ⊤ := by
  rw [eq_top_iff, ← closure_orderOf_three_eq_top hK]
  refine Subgroup.closure_mono fun y hy => ?_
  have hy3 : orderOf y = 3 := hy
  show Odd (orderOf y)
  rw [hy3]
  decide

theorem kaL5B3T_closure_odd_sl3 :
    Subgroup.closure {y : SL(3, F) | Odd (orderOf y)} = ⊤ := by
  have hperf : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  exact ka_perfect_closure_odd hperf.commutator_eq_top

omit [Finite F] in
theorem kaL5B3T_mem_closure_odd {G : Type*} [Group G]
    (hG : Subgroup.closure {y : G | Odd (orderOf y)} = ⊤) (f : G →* projectiveSL 5 F)
    (hf : ∀ g, f g ∈ kaL5B3TL F) (g : G) :
    f g ∈ Subgroup.closure {x : projectiveSL 5 F | x ∈ kaL5B3TL F ∧ Odd (orderOf x)} := by
  have hg : g ∈ Subgroup.closure {y : G | Odd (orderOf y)} := by
    rw [hG]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ⟨hf y, ?_⟩
    exact Odd.of_dvd_nat hy (orderOf_map_dvd f y)
  | one =>
    rw [map_one]
    exact one_mem _
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact inv_mem ha

theorem kaL5B3T_gen (hK : Nat.card F = 3) :
    Subgroup.closure {x : projectiveSL 5 F | x ∈ kaL5B3TL F ∧ Odd (orderOf x)} =
      kaL5B3TL F := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
  rintro _ ⟨⟨s, t⟩, rfl⟩
  change kaL5B3TPhi F (s, t) ∈ _
  rw [kaL5B3T_phi]
  exact mul_mem (kaL5B3T_mem_closure_odd kaL5B3T_closure_odd_sl3 (kaL5B3TInl F)
      kaL5B3T_inl_mem s)
    (kaL5B3T_mem_closure_odd (kaL5B3T_closure_odd_sl2 hK) (kaL5B3TInr F) kaL5B3T_inr_mem t)

end Odd

section CentralProduct

variable {F : Type} [Field F] [Finite F]

theorem kaL5B3T_proj_injective (hK : Nat.card F = 3) : Function.Injective (proj 5 F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker, proj_eq_one_iff] at hg
  obtain ⟨c, hc, hgc⟩ := mem_scalars.1 hg
  have hc5 : (c : F) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have hc2 : (c : F) * c = 1 := kaL5B3T_sq_eq_one hK c.ne_zero
  have hc1 : (c : F) = 1 := by
    linear_combination hc5 - (c : F) * ((c : F) * c + 1) * hc2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hgc, hc1, map_one]
  rfl

theorem kaL5B3T_inl_injective (hK : Nat.card F = 3) : Function.Injective (kaL5B3TInl F) := by
  intro s s' h
  have h1 := kaL5B3THom_injective (kaL5B3T_proj_injective hK h)
  exact (Prod.mk.inj h1).1

theorem kaL5B3T_inr_injective (hK : Nat.card F = 3) : Function.Injective (kaL5B3TInr F) := by
  intro t t' h
  have h1 := kaL5B3THom_injective (kaL5B3T_proj_injective hK h)
  exact (Prod.mk.inj h1).2

theorem kaL5B3T_sq_eq_one_of_mem_center (hK : Nat.card F = 3) {J : Type*} [Group J]
    (e : J ≃* SL(2, F)) {z : J} (hz : z ∈ Subgroup.center J) : z * z = 1 := by
  rw [mem_center_iff_of_mulEquiv hK e] at hz
  apply (e.trans (slEquivSL23 hK)).injective
  rcases hz with h | h <;> simp [map_mul, h]

theorem kaL5B3T_normal_odd_eq_bot (hK : Nat.card F = 3) {J : Type*} [Group J]
    (e : J ≃* SL(2, F)) (N : Subgroup J) [N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  by_cases hNZ : N ≤ Subgroup.center J
  · rw [eq_bot_iff]
    intro z hz
    have hsq := kaL5B3T_sq_eq_one_of_mem_center hK e (hNZ hz)
    exact ka_odd_mem_of_sq_mem (R := ⊥) (by rw [hsq]; exact one_mem _)
      (hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hz))
  · exfalso
    have h8 := eight_le_card_of_normal hK e N hNZ
    have h24 := card_eq_24 hK e
    have hdvd : Nat.card N ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card N
    have hle : Nat.card N ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := hodd
    generalize Nat.card N = n at hdvd h8 hk hle
    interval_cases n <;> omega

theorem kaL5B3T_inf_eq_bot (hK : Nat.card F = 3) {Y : Type} [Group Y] [Finite Y]
    {A : Subgroup Y} (e : A ≃* SL(2, F)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup Y} (hX : IsPGroup p ↥X) (hAX : ∀ a ∈ A, a ∈ normalizer (X : Set Y)) :
    X ⊓ A = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  let N : Subgroup ↥A := (X ⊓ A).subgroupOf A
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    refine ⟨?_, (g * n * g⁻¹ : ↥A).2⟩
    have := (Subgroup.mem_normalizer_iff.1 (hAX g g.2) n).1 hn.1
    simpa using this
  have hodd : Odd (Nat.card N) := by
    have h1 : Nat.card N = Nat.card ↥(X ⊓ A) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : X ⊓ A ≤ A)).toEquiv
    have h2 : IsPGroup p ↥(X ⊓ A) := hX.to_le inf_le_left
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    rw [h1, hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hbot : N = ⊥ := kaL5B3T_normal_odd_eq_bot hK e N hodd
  rw [eq_bot_iff]
  intro y hy
  have hyN : (⟨y, hy.2⟩ : ↥A) ∈ N := Subgroup.mem_subgroupOf.mpr hy
  rw [hbot, Subgroup.mem_bot] at hyN
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hyN)

theorem kaL5B3T_center_sl3 (hK : Nat.card F = 3) {s : SL(3, F)}
    (hs : s ∈ Subgroup.center SL(3, F)) : s = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hs
  obtain ⟨r, hr, hrs⟩ := hs
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hr
    exact zero_ne_one hr
  have hr2 : r * r = 1 := kaL5B3T_sq_eq_one hK hr0
  have hr1 : r = 1 := by linear_combination hr - r * hr2
  apply Subtype.ext
  rw [← hrs, hr1, map_one]
  rfl

omit [Finite F] in
theorem kaL5B3T_quasisimple : CFSG.IsQuasisimple SL(3, F) := by
  have hperf : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega)
      (Or.inl (by norm_num))
  refine ⟨hperf, hsimple, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (SL(3, F) ⧸ Subgroup.center SL(3, F)) := ⟨⟨h⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (SL(3, F) ⧸ Subgroup.center SL(3, F)) this

theorem kaL5B3T_eq_bot_of_hom (hK : Nat.card F = 3) {Y : Type} [Group Y] [Finite Y]
    (f : SL(3, F) →* Y) (g : SL(2, F) →* Y) (hf : Function.Injective f)
    (hg : Function.Injective g) (hcomm : ∀ s t, f s * g t = g t * f s) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup Y} (hX : IsPGroup p ↥X) (hXle : X ≤ f.range ⊔ g.range)
    (hXf : ∀ a ∈ f.range, a ∈ normalizer (X : Set Y))
    (hXg : ∀ a ∈ g.range, a ∈ normalizer (X : Set Y)) : X = ⊥ := by
  have hL : X ⊓ g.range = ⊥ :=
    kaL5B3T_inf_eq_bot hK (MonoidHom.ofInjective hg).symm hp hp2 hX hXg
  have hMc := ka_central_of_quasisimple_image f kaL5B3T_quasisimple hp (X ⊓ f.range)
    inf_le_right (hX.to_le inf_le_left) (fun l hl => by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := Subgroup.mem_normalizer_iff.1 (hXf l hl) h
      have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) h
      simp only [Subgroup.mem_inf]
      rw [h1, h2])
  have hZ : ∀ j ∈ f.range, (∀ a ∈ f.range, a * j = j * a) → j = 1 := by
    rintro _ ⟨s, rfl⟩ hc
    have hs : s ∈ Subgroup.center SL(3, F) := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply hf
      rw [map_mul, map_mul]
      exact hc (f t) ⟨t, rfl⟩
    rw [kaL5B3T_center_sl3 hK hs, map_one]
  have hJ : X ⊓ f.range = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    exact Subgroup.mem_bot.2 (hZ m hm.2 fun a ha => (hMc m hm a ha).symm)
  have hcomm' : ∀ a ∈ f.range, ∀ b ∈ g.range, a * b = b * a := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact hcomm s t
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨j, hj, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm' (hXle hx)
  have hjc : ∀ a ∈ f.range, a * j = j * a := by
    intro a ha
    have h1 : a * (j * l) * a⁻¹ * (j * l)⁻¹ ∈ X :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (hXf a ha) _).1 hx) (inv_mem hx)
    rw [conj_mul_commutator (hcomm' a ha l hl)] at h1
    have h3 : a * j * a⁻¹ * j⁻¹ ∈ f.range :=
      mul_mem (mul_mem (mul_mem ha hj) (inv_mem ha)) (inv_mem hj)
    have h2 : a * j * a⁻¹ * j⁻¹ ∈ X ⊓ f.range := ⟨h1, h3⟩
    rw [hJ, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hj1 : j = 1 := hZ j hj hjc
  rw [hj1, one_mul] at hx ⊢
  have hlb : l ∈ X ⊓ g.range := ⟨hx, hl⟩
  rw [hL] at hlb
  exact hlb

theorem kaL5B3T_hRp (hK : Nat.card F = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (projectiveSL 5 F)} (hX : IsPGroup p ↥X) (hXle : X ≤ kaL5B3TL F)
    (hnorm : ∀ r ∈ kaL5B3TL F, r ∈ normalizer (X : Set (projectiveSL 5 F))) : X = ⊥ := by
  refine kaL5B3T_eq_bot_of_hom hK (kaL5B3TInl F) (kaL5B3TInr F) (kaL5B3T_inl_injective hK)
    (kaL5B3T_inr_injective hK) kaL5B3T_comm hp hp2 hX (hXle.trans kaL5B3T_L_le_sup)
    (fun a ha => ?_) (fun a ha => ?_)
  · obtain ⟨s, rfl⟩ := ha
    exact hnorm _ (kaL5B3T_inl_mem s)
  · obtain ⟨t, rfl⟩ := ha
    exact hnorm _ (kaL5B3T_inr_mem t)

end CentralProduct

section Class

variable {F : Type} [Field F] [Finite F]

theorem kaL5B3T_congr_eq_mul {Y : Type} [Group Y] (e α : MulAut Y) :
    MulAut.congr e α = e * α * e⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

theorem kaL5B3T_main (hK : Nat.card F = 3) : KAAll (conjAut 5 F (kaL5B3TGL F)) := by
  have hodd : ringChar F ≠ 2 := kaL5B3T_ringChar_ne_two hK
  refine ka_all_of_oddcore (ka_conj_inj_pl5 hodd) (kaL5B3TL F) kaL5B3T_L_le_fix
    (kaL5B3T_gen hK) ?_ ?_ (ka_outCyc_pl5_three hK)
    (ka_outCentral_pl5 hodd (kaL5B3TGL F) kaL5B3TGL_mul_self)
  · intro c hc ho
    exact kaL5B3T_odd_mem hK (ka_odd_mem_map_cent_pl5 (kaL5B3TGL F) kaL5B3TGL_mul_self
      (mem_fixSub.1 hc) ho) ho
  · intro p hp hp2 X hX hXle hnorm
    exact kaL5B3T_hRp hK hp hp2 hX hXle hnorm

end Class

theorem kaL5B3Three_thm : KAL5B3Three := by
  intro F _ _ hK B hB h3
  obtain ⟨P, rfl⟩ := kaL5B3T_exists_frame (kaL5B3T_ringChar_ne_two hK) hB h3
  have h := KAAll.of_mulEquiv (conjAut 5 F P : projectiveSL 5 F ≃* projectiveSL 5 F)
    (kaL5B3T_main hK)
  have e : MulAut.congr (conjAut 5 F P : projectiveSL 5 F ≃* projectiveSL 5 F)
      (conjAut 5 F (kaL5B3TGL F)) = conjAut 5 F (P * kaL5B3TGL F * P⁻¹) := by
    rw [kaL5B3T_congr_eq_mul, map_mul, map_mul, map_inv]
  rwa [e] at h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
