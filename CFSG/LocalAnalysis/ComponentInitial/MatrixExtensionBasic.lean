module

public import CFSG.LocalAnalysis.ComponentInitial.GroupBinaryPolar
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace MatrixExtension

open Matrix
open scoped commutatorElement

section Congruence

variable {n : ℕ}

theorem mul_vecMulVec_mul_transpose {R : Type*} [CommRing R] {m : Type*} [Fintype m]
    (g : Matrix m m R) (u v : m → R) : g * vecMulVec u v * gᵀ = vecMulVec (g *ᵥ u) (g *ᵥ v) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, transpose_apply, mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem binaryTransvection_coe {a b : Fin n} (h : a ≠ b) :
    (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + single a b 1 :=
  rfl

theorem one_add_single_mulVec {a b : Fin n} (v : Fin n → ZMod 2) :
    (1 + single a b (1 : ZMod 2)) *ᵥ v = v + Pi.single a (v b) := by
  rw [add_mulVec, one_mulVec, single_mulVec, one_mul]
  rfl

theorem pi_single_eq_smul (a : Fin n) (c : ZMod 2) :
    Pi.single a c = c • Pi.single a (1 : ZMod 2) := by
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

theorem one_add_single_congr_polar (a b : Fin n) (u v : Fin n → ZMod 2) :
    (1 + single a b (1 : ZMod 2)) * (vecMulVec u v + vecMulVec v u) *
        (1 + single a b (1 : ZMod 2))ᵀ =
      vecMulVec u v + vecMulVec v u +
        u b • (vecMulVec (Pi.single a 1) v + vecMulVec v (Pi.single a 1)) +
        v b • (vecMulVec u (Pi.single a 1) + vecMulVec (Pi.single a 1) u) := by
  rw [Matrix.mul_add, Matrix.add_mul, mul_vecMulVec_mul_transpose, mul_vecMulVec_mul_transpose,
    one_add_single_mulVec, one_add_single_mulVec, pi_single_eq_smul a (u b),
    pi_single_eq_smul a (v b)]
  simp only [add_vecMulVec, vecMulVec_add, smul_vecMulVec, vecMulVec_smul, smul_add, smul_smul]
  have h2 : (v b * u b) • vecMulVec (Pi.single a (1 : ZMod 2)) (Pi.single a 1) +
      (u b * v b) • vecMulVec (Pi.single a (1 : ZMod 2)) (Pi.single a 1) = 0 := by
    rw [mul_comm, ← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  linear_combination (norm := abel) h2

theorem one_add_single_congr_sq (a b : Fin n) (v : Fin n → ZMod 2) :
    (1 + single a b (1 : ZMod 2)) * vecMulVec v v * (1 + single a b (1 : ZMod 2))ᵀ =
      vecMulVec v v + v b • (vecMulVec (Pi.single a 1) v + vecMulVec v (Pi.single a 1) +
        vecMulVec (Pi.single a 1) (Pi.single a 1)) := by
  rw [mul_vecMulVec_mul_transpose, one_add_single_mulVec, pi_single_eq_smul a (v b)]
  simp only [add_vecMulVec, vecMulVec_add, smul_vecMulVec, vecMulVec_smul, smul_add, smul_smul]
  have h2 : v b * v b = v b := by
    have : ∀ c : ZMod 2, c * c = c := by decide
    exact this _
  rw [h2]
  abel

@[expose] def binaryOff (i j : Fin n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  single i j 1 + single j i 1

theorem binaryOff_comm (i j : Fin n) : binaryOff i j = binaryOff j i :=
  add_comm _ _

theorem binaryOff_self (i : Fin n) : binaryOff i i = 0 :=
  binary_add_self _

theorem binaryOff_eq_vecMulVec (i j : Fin n) :
    binaryOff i j = vecMulVec (Pi.single i 1) (Pi.single j 1) +
      vecMulVec (Pi.single j 1) (Pi.single i 1) := by
  rw [vecMulVec_single_single, vecMulVec_single_single]
  rfl

theorem binaryOff_mem_binaryAltMatrices (i j : Fin n) : binaryOff i j ∈ binaryAltMatrices n := by
  refine ⟨?_, fun k => ?_⟩
  · rw [binaryOff, transpose_add, transpose_single, transpose_single, add_comm]
  · simp only [binaryOff, Matrix.add_apply, single_apply]
    split_ifs <;> simp_all [CharTwo.add_self_eq_zero]

theorem binaryTransvection_congr_binaryOff {a b : Fin n} (h : a ≠ b) (i j : Fin n) :
    (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2)) * binaryOff i j *
        (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      binaryOff i j + (if i = b then binaryOff a j else 0) +
        (if j = b then binaryOff i a else 0) := by
  rw [binaryTransvection_coe, binaryOff_eq_vecMulVec, one_add_single_congr_polar,
    ← binaryOff_eq_vecMulVec, ← binaryOff_eq_vecMulVec, ← binaryOff_eq_vecMulVec,
    Pi.single_apply, Pi.single_apply]
  by_cases hi : i = b <;> by_cases hj : j = b
  · simp [hi, hj]
  · simp [hi, hj, Ne.symm hj]
  · simp [hi, hj, Ne.symm hi]
  · simp [hi, hj, Ne.symm hi, Ne.symm hj]

theorem binaryTransvection_congr_diag {a b : Fin n} (h : a ≠ b) (k : Fin n) :
    (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2)) * single k k 1 *
        (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      single k k 1 + (if k = b then binaryOff a k + single a a 1 else 0) := by
  rw [binaryTransvection_coe, show single k k (1 : ZMod 2) =
      vecMulVec (Pi.single k 1) (Pi.single k 1) from (vecMulVec_single_single k k).symm,
    one_add_single_congr_sq, ← binaryOff_eq_vecMulVec, vecMulVec_single_single,
    vecMulVec_single_single, Pi.single_apply]
  by_cases hk : k = b
  · simp [hk]
  · simp [hk, Ne.symm hk]

end Congruence

section Relations

variable {n : ℕ}

theorem binaryTransvection_mul_self {a b : Fin n} (h : a ≠ b) :
    binaryTransvection h * binaryTransvection h = 1 := by
  apply Units.ext
  change transvection a b (1 : ZMod 2) * transvection a b 1 = 1
  rw [transvection_mul_transvection_same _ _ h, show (1 : ZMod 2) + 1 = 0 from rfl,
    transvection_zero]

theorem binaryTransvection_inv {a b : Fin n} (h : a ≠ b) :
    (binaryTransvection h)⁻¹ = binaryTransvection h :=
  inv_eq_of_mul_eq_one_right (binaryTransvection_mul_self h)

theorem commutatorElement_binaryTransvection {a k i : Fin n} (hak : a ≠ k) (hki : k ≠ i)
    (hai : a ≠ i) :
    ⁅binaryTransvection hak, binaryTransvection hki⁆ = binaryTransvection hai := by
  rw [commutatorElement_def, binaryTransvection_inv, binaryTransvection_inv]
  apply Units.ext
  simp only [Units.val_mul, binaryTransvection_coe]
  have h := CFSG.LinearGroups.elementary_three_index_commutator hai hak hki.symm
    (1 : ZMod 2) 1
  rw [(CFSG.LinearGroups.elementary_matrix_identities hak).2.2.1,
    (CFSG.LinearGroups.elementary_matrix_identities hki).2.2.1, mul_one,
    ZMod.neg_eq_self_mod_two] at h
  exact h

theorem binaryTransvection_commute {a i b j : Fin n} (hai : a ≠ i) (hbj : b ≠ j) (hib : i ≠ b)
    (hja : j ≠ a) :
    binaryTransvection hai * binaryTransvection hbj =
      binaryTransvection hbj * binaryTransvection hai := by
  apply Units.ext
  simp only [Units.val_mul, binaryTransvection_coe, add_mul, mul_add, one_mul, mul_one,
    single_mul_single_of_ne _ _ _ _ hib, single_mul_single_of_ne _ _ _ _ hja, add_zero]
  abel

theorem closure_binaryTransvection :
    Subgroup.closure {g : GL (Fin n) (ZMod 2) | ∃ (a b : Fin n) (h : a ≠ b),
      binaryTransvection h = g} = ⊤ := by
  have hsurj : Function.Surjective (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2)) := by
    intro g
    have hdet : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
      have hu : IsUnit (g : Matrix (Fin n) (Fin n) (ZMod 2)).det := by
        simpa using (Matrix.GeneralLinearGroup.det g).isUnit
      generalize (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = d at hu
      revert d
      decide
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨A, rfl⟩ := hsurj g
  have hA : A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet n (ZMod 2)) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top A
  have h := Subgroup.mem_map_of_mem SpecialLinearGroup.toGL hA
  rw [MonoidHom.map_closure] at h
  refine (Subgroup.closure_le _).mpr ?_ h
  rintro _ ⟨B, ⟨i, j, hij, c, rfl⟩, rfl⟩
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · have h1 : SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (0 : ZMod 2)) = 1 :=
      Units.ext (by
        change (1 + single i j (0 : ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1
        rw [single_zero, add_zero])
    rw [h1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨i, j, hij, Units.ext rfl⟩

end Relations

section Actions

variable {G M : Type*} [Group G] [AddCommGroup M]

theorem act_mul_apply (act : G →* AddMonoid.End M) (g h : G) (x : M) :
    act (g * h) x = act g (act h x) := by
  rw [map_mul]
  rfl

theorem act_one_apply (act : G →* AddMonoid.End M) (x : M) : act 1 x = x := by
  rw [map_one]
  rfl

theorem act_inv_apply_act (act : G →* AddMonoid.End M) (g : G) (x : M) :
    act g⁻¹ (act g x) = x := by
  rw [← act_mul_apply, inv_mul_cancel, act_one_apply]

theorem act_apply_act_inv (act : G →* AddMonoid.End M) (g : G) (x : M) :
    act g (act g⁻¹ x) = x := by
  rw [← act_mul_apply, mul_inv_cancel, act_one_apply]

theorem act_commutatorElement_apply_eq (act : G →* AddMonoid.End M) {C : AddSubgroup M}
    (hC : ∀ g, ∀ c ∈ C, act g c = c) {g₁ g₂ : G} {x : M} (h₁ : act g₁ x - x ∈ C)
    (h₂ : act g₂ x - x ∈ C) : act ⁅g₁, g₂⁆ x = x := by
  obtain ⟨c₁, hc₁, e₁⟩ : ∃ c ∈ C, act g₁ x = x + c := ⟨_, h₁, by abel⟩
  obtain ⟨c₂, hc₂, e₂⟩ : ∃ c ∈ C, act g₂ x = x + c := ⟨_, h₂, by abel⟩
  have hinv : ∀ {g : G} {c : M}, c ∈ C → act g x = x + c → act g⁻¹ x = x - c := by
    intro g c hc e
    rw [← act_inv_apply_act act g (x - c), map_sub, e, hC g c hc, add_sub_cancel_right]
  have f₁ := hinv hc₁ e₁
  have f₂ := hinv hc₂ e₂
  have k₁ : ∀ g, act g c₁ = c₁ := fun g => hC g _ hc₁
  have k₂ : ∀ g, act g c₂ = c₂ := fun g => hC g _ hc₂
  simp only [commutatorElement_def, act_mul_apply, f₂, map_sub, f₁, k₁, k₂, e₂, map_add, e₁]
  abel

theorem act_mem_of_closure_eq_top (act : G →* AddMonoid.End M) {S : AddSubgroup M} {T : Set G}
    (hT : Subgroup.closure T = ⊤) (hTinv : ∀ t ∈ T, t⁻¹ ∈ T)
    (h : ∀ t ∈ T, ∀ x ∈ S, act t x ∈ S) (g : G) : ∀ x ∈ S, act g x ∈ S := by
  have hg : g ∈ (Subgroup.closure T).toSubmonoid := by
    rw [hT]
    exact Subgroup.mem_top g
  rw [Subgroup.closure_toSubmonoid] at hg
  induction hg using Submonoid.closure_induction with
  | mem t ht =>
    rcases ht with ht | ht
    · exact h t ht
    · exact h _ (by simpa using hTinv _ ht)
  | one => intro x hx; rwa [act_one_apply]
  | mul g₁ g₂ _ _ h₁ h₂ =>
    intro x hx
    rw [act_mul_apply]
    exact h₁ _ (h₂ x hx)

end Actions

section AltSection

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem zmod_two_smul_mem (S : AddSubgroup M) (c : ZMod 2) {x : M} (hx : x ∈ S) : c • x ∈ S := by
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem S hx _

@[expose] def altSection (o : Fin n → Fin n → M) : Matrix (Fin n) (Fin n) (ZMod 2) →+ M where
  toFun X := ∑ p ∈ binaryUpperPairs n, X p.1 p.2 • o p.1 p.2
  map_zero' := by simp
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]

theorem altSection_apply (o : Fin n → Fin n → M) (X : Matrix (Fin n) (Fin n) (ZMod 2)) :
    altSection o X = ∑ p ∈ binaryUpperPairs n, X p.1 p.2 • o p.1 p.2 :=
  rfl

theorem altSection_single (o : Fin n → Fin n → M) {i j : Fin n} (hij : i < j) :
    altSection o (single i j 1) = o i j := by
  rw [altSection_apply, Finset.sum_eq_single (i, j)]
  · rw [single_apply, ite_eq_left ⟨rfl, rfl⟩, one_smul]
  · intro p _ hp
    rw [single_apply, ite_eq_right fun h => hp (Prod.ext h.1.symm h.2.symm), zero_smul]
  · intro h
    exact absurd (show (i, j) ∈ binaryUpperPairs n from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩) h

theorem zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem map_zmod_two_smul (f : M →+ Matrix (Fin n) (Fin n) (ZMod 2)) (c : ZMod 2) (x : M) :
    f (c • x) = c • f x := by
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, map_zero, zero_smul]
  · rw [one_smul, one_smul]

theorem altSection_closure_spec (o : Fin n → Fin n → M) (hdiag : ∀ i, o i i = 0)
    (hsymm : ∀ i j, o i j = o j i) (π : M →+ Matrix (Fin n) (Fin n) (ZMod 2))
    (hπ : ∀ i j, π (o i j) = binaryOff i j) :
    (∀ x ∈ AddSubgroup.closure (Set.range fun p : Fin n × Fin n => o p.1 p.2), π x = 0 →
      x = 0) ∧
    ∀ X ∈ binaryAltMatrices n,
      ∃ x ∈ AddSubgroup.closure (Set.range fun p : Fin n × Fin n => o p.1 p.2), π x = X := by
  set S := AddSubgroup.closure (Set.range fun p : Fin n × Fin n => o p.1 p.2) with hS
  have hπσ : ∀ X, π (altSection o X) = ∑ p ∈ binaryUpperPairs n,
      X p.1 p.2 • (single p.1 p.2 (1 : ZMod 2) + single p.2 p.1 1) := by
    intro X
    rw [altSection_apply, map_sum]
    exact Finset.sum_congr rfl fun p _ =>
      (map_zmod_two_smul π (X p.1 p.2) (o p.1 p.2)).trans (congrArg _ (hπ _ _))
  have hSσ : S ≤ (altSection o).range := by
    rw [hS, AddSubgroup.closure_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    rcases lt_trichotomy i j with h | rfl | h
    · exact ⟨single i j 1, altSection_single o h⟩
    · exact ⟨0, by rw [map_zero]; exact (hdiag i).symm⟩
    · exact ⟨single j i 1, by rw [altSection_single o h, hsymm]⟩
  have hσS : ∀ X, altSection o X ∈ S := fun X => by
    rw [altSection_apply]
    exact AddSubgroup.sum_mem _ fun p _ =>
      zmod_two_smul_mem S _ (AddSubgroup.subset_closure ⟨p, rfl⟩)
  refine ⟨fun x hx hπx => ?_, fun X hX => ⟨altSection o X, hσS X, ?_⟩⟩
  · obtain ⟨Y, rfl⟩ := hSσ hx
    have hzero : ∀ p ∈ binaryUpperPairs n, Y p.1 p.2 = 0 := by
      intro p hp
      have h := congrFun₂ ((hπσ Y).symm.trans hπx) p.1 p.2
      rw [binaryUpperSum_apply, ite_eq_left (Finset.mem_filter.mp hp).2] at h
      exact h
    rw [altSection_apply]
    exact Finset.sum_eq_zero fun p hp => by rw [hzero p hp, zero_smul]
  · rw [hπσ]
    ext a b
    rw [binaryUpperSum_apply]
    obtain ⟨hXt, hXd⟩ := hX
    split_ifs with hab hba
    · rfl
    · exact congrFun₂ hXt a b
    · rw [le_antisymm (not_lt.mp hba) (not_lt.mp hab), hXd]

end AltSection

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_eq (a a' b : G) :
    ⁅a * a', b⁆ = a * ⁅a', b⁆ * a⁻¹ * ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right_eq (a b b' : G) :
    ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_eq_one_of_mem_center_left {a : G} (ha : a ∈ Subgroup.center G)
    (b : G) : ⁅a, b⁆ = 1 := by
  rw [commutatorElement_def, (Subgroup.mem_center_iff.mp ha b).symm]
  group

theorem commutatorElement_eq_one_of_mem_center_right (a : G) {b : G}
    (hb : b ∈ Subgroup.center G) : ⁅a, b⁆ = 1 := by
  rw [← commutatorElement_inv, commutatorElement_eq_one_of_mem_center_left hb, inv_one]

theorem conj_eq_self_of_mem_center (g : G) {a : G} (ha : a ∈ Subgroup.center G) :
    g * a * g⁻¹ = a := by
  rw [Subgroup.mem_center_iff.mp ha g, mul_inv_cancel_right]

variable {H : Type*} [Group H] (π : G →* H) (hH : ∀ a b : H, a * b = b * a)
include hH

theorem commutatorElement_mem_ker (x y : G) : ⁅x, y⁆ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hH _ _

omit hH in
theorem commutatorElement_eq_of_map_eq (hC : π.ker ≤ Subgroup.center G) {x x' y y' : G}
    (hx : π x = π x') (hy : π y = π y') : ⁅x, y⁆ = ⁅x', y'⁆ := by
  obtain ⟨k, hk, rfl⟩ : ∃ k ∈ π.ker, x' = x * k :=
    ⟨x⁻¹ * x', by rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel], by group⟩
  obtain ⟨l, hl, rfl⟩ : ∃ l ∈ π.ker, y' = y * l :=
    ⟨y⁻¹ * y', by rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel], by group⟩
  rw [commutatorElement_mul_left_eq, commutatorElement_eq_one_of_mem_center_left (hC hk),
    mul_one, mul_inv_cancel, one_mul, commutatorElement_mul_right_eq,
    commutatorElement_eq_one_of_mem_center_right _ (hC hl), mul_one, mul_inv_cancel, mul_one]

theorem commutatorElement_mul_right_of_ker (hC : π.ker ≤ Subgroup.center G) (x y y' : G) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  rw [commutatorElement_mul_right_eq,
    conj_eq_self_of_mem_center _ (hC (commutatorElement_mem_ker π hH x y'))]

end Commutators

end MatrixExtension

end CFSG.LocalAnalysis.ComponentInitial
