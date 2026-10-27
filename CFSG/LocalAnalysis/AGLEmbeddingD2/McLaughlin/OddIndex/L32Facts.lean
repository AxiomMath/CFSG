module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrobPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.L32Mat

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem det_ne_zero_GL (g : GL (Fin 3) (ZMod 2)) : (g : Mat3).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

theorem card_GL32_subtype (P : Mat3 → Prop) [DecidablePred P] (hdet : ∀ m : Mat3, P m → m.det ≠ 0) :
    Nat.card {g : GL (Fin 3) (ZMod 2) // P (g : Mat3)} = (Finset.univ.filter P).card := by
  let e : {g : GL (Fin 3) (ZMod 2) // P (g : Mat3)} ≃ {m : Mat3 // P m} :=
    { toFun := fun x => ⟨((x : GL (Fin 3) (ZMod 2)) : Mat3), x.2⟩
      invFun := fun m => ⟨GeneralLinearGroup.mkOfDetNeZero m.1 (hdet m.1 m.2), by simpa using m.2⟩
      left_inv := fun x => Subtype.ext (Units.ext rfl)
      right_inv := fun m => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

section Norm

variable {G : Type} [Group G]

theorem mem_normalizer_zpowers_iff {a : G} (ha : orderOf a = 3) {x : G} :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) ↔
      x * a = a * x ∨ x * a = a * a * x := by
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num at ha
  have hmem : ∀ y : G, y ∈ Subgroup.zpowers a ↔ y = 1 ∨ y = a ∨ y = a * a := by
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk : a ^ k = a ^ (k % 3) := by
        rw [← zpow_mod_orderOf a k, ha]
        rfl
      rw [hk]
      have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
      have h3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
      interval_cases (k % 3)
      · left; simp
      · right; left; simp
      · right; right; exact zpow_two a
    · rintro (h | h | h) <;> rw [h]
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers a
      · exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
  constructor
  · intro hx
    have h := (Subgroup.mem_normalizer_iff.mp hx a).mp (Subgroup.mem_zpowers a)
    rcases (hmem _).mp h with h1 | h1 | h1
    · exfalso; apply ha1
      have : x * a * x⁻¹ * x = x := by rw [h1, one_mul]
      have : x * a = x := by simpa [mul_assoc] using this
      exact mul_eq_left.mp this
    · left
      calc x * a = x * a * x⁻¹ * x := by group
        _ = a * x := by rw [h1]
    · right
      calc x * a = x * a * x⁻¹ * x := by group
        _ = a * a * x := by rw [h1]
  · intro hx
    have hc : x * a * x⁻¹ ∈ Subgroup.zpowers a := by
      rcases hx with h | h
      · rw [h, mul_inv_cancel_right]; exact Subgroup.mem_zpowers a
      · rw [h, mul_inv_cancel_right]
        exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
    have hc' : x⁻¹ * a * x ∈ Subgroup.zpowers a := by
      rcases hx with h | h
      · have : x⁻¹ * a * x = a := by
          calc x⁻¹ * a * x = x⁻¹ * (a * x) := by group
            _ = x⁻¹ * (x * a) := by rw [h]
            _ = a := by group
        rw [this]; exact Subgroup.mem_zpowers a
      ·
        set w := x⁻¹ * a * x with hw
        have hw3 : w ^ 3 = 1 := by
          rw [hw]
          have : (x⁻¹ * a * x) ^ 3 = x⁻¹ * a ^ 3 * x := by
            rw [show x⁻¹ * a * x = x⁻¹ * a * x⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
          rw [this, ha3]; group
        have hwa : w * w = a := by
          rw [hw]
          calc x⁻¹ * a * x * (x⁻¹ * a * x) = x⁻¹ * (a * a * x) := by group
            _ = x⁻¹ * (x * a) := by rw [← h]
            _ = a := by group
        have : w = a * a := by
          calc w = w ^ 3 * w := by rw [hw3, one_mul]
            _ = (w * w) * (w * w) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = a * a := by rw [hwa]
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have : x * a ^ k * x⁻¹ = (x * a * x⁻¹) ^ k := by
        rw [conj_zpow]
      rw [this]
      exact Subgroup.zpow_mem _ hc k
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      have : h = (x⁻¹ * a * x) ^ k := by
        rw [show x⁻¹ * a * x = x⁻¹ * a * x⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv, hk]; group
      rw [this]
      exact Subgroup.zpow_mem _ hc' k

end Norm

section Transfer

variable {X : Type} [Group X]

theorem mul_self_eq_one_of_orderOf_two {t : X} (ht : orderOf t = 2) : t * t = 1 := by
  rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t

theorem ne_one_of_orderOf_two {t : X} (ht : orderOf t = 2) : t ≠ 1 := by
  intro h; rw [h, orderOf_one] at ht; norm_num at ht

theorem card_centralizer_of_isLThreeTwo (hX : IsLThreeTwo X) {t : X} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set X)) = 8 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_GL_of_isLThreeTwo hX
  have hu2 : ((e t : GL (Fin 3) (ZMod 2)) : Mat3) * (e t : GL (Fin 3) (ZMod 2)) = 1 := by
    have : e t * e t = 1 := by rw [← map_mul, mul_self_eq_one_of_orderOf_two ht, map_one]
    exact congrArg Units.val this
  have hu1 : ((e t : GL (Fin 3) (ZMod 2)) : Mat3) ≠ 1 := by
    intro h
    apply ne_one_of_orderOf_two ht
    apply e.injective
    rw [map_one]
    exact Units.ext h
  rw [← card_centMat _ hu2 hu1]
  rw [← card_GL32_subtype _ (fun m hm => hm.2)]
  apply Nat.card_congr
  refine Equiv.subtypeEquiv e.toEquiv ?_
  intro x
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  constructor
  · intro h
    refine ⟨?_, det_ne_zero_GL _⟩
    have : e x * e t = e t * e x := by rw [← map_mul, h, map_mul]
    exact congrArg Units.val this
  · intro h
    apply e.injective
    rw [map_mul, map_mul]
    exact Units.ext h.1

theorem eq_one_or_eq_of_mem_center_centralizer (hX : IsLThreeTwo X) {t : X} (ht : orderOf t = 2)
    {x : X} (hx : x ∈ Subgroup.centralizer ({t} : Set X))
    (hxc : ∀ y ∈ Subgroup.centralizer ({t} : Set X), x * y = y * x) : x = 1 ∨ x = t := by
  obtain ⟨e⟩ := nonempty_mulEquiv_GL_of_isLThreeTwo hX
  set u : GL (Fin 3) (ZMod 2) := e t with hu
  have hu2 : (u : Mat3) * u = 1 := by
    have : u * u = 1 := by rw [hu, ← map_mul, mul_self_eq_one_of_orderOf_two ht, map_one]
    exact congrArg Units.val this
  have hu1 : (u : Mat3) ≠ 1 := by
    intro h
    apply ne_one_of_orderOf_two ht
    apply e.injective
    rw [map_one]
    exact Units.ext h
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hxm : ((e x : GL (Fin 3) (ZMod 2)) : Mat3) ∈ centMat u := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, det_ne_zero_GL _⟩
    have : e x * u = u * e x := by rw [hu, ← map_mul, hxt, map_mul]
    exact congrArg Units.val this
  have hcen : ∀ y ∈ centMat u, ((e x : GL (Fin 3) (ZMod 2)) : Mat3) * y = y * (e x : GL (Fin 3) (ZMod 2)) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    set g : GL (Fin 3) (ZMod 2) := GeneralLinearGroup.mkOfDetNeZero y hy.2.2 with hg
    have hgy : (g : Mat3) = y := rfl
    have hgu : g * u = u * g := Units.ext (by rw [Units.val_mul, Units.val_mul, hgy]; exact hy.2.1)
    have hmem : e.symm g ∈ Subgroup.centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hu]
      exact hgu
    have := hxc _ hmem
    have h2 : e x * g = g * e x := by
      have := congrArg e this
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    rw [← hgy]
    exact congrArg Units.val h2
  have hinv : (u : Mat3) ∈ Finset.univ.filter (fun t : Mat3 => t * t = 1 ∧ t ≠ 1) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hu2, hu1⟩
  rcases eq_of_mem_center_centMat _ hinv _ hxm hcen with h | h
  · left
    apply e.injective
    rw [map_one]
    exact Units.ext h
  · right
    apply e.injective
    exact Units.ext h

theorem matrix_facts_of_orderOf_three (e : X ≃* GL (Fin 3) (ZMod 2)) {a : X} (ha : orderOf a = 3) :
    ((e a : GL (Fin 3) (ZMod 2)) : Mat3) * (e a : GL (Fin 3) (ZMod 2)) * (e a : GL (Fin 3) (ZMod 2))
      = 1 ∧ ((e a : GL (Fin 3) (ZMod 2)) : Mat3) ≠ 1 := by
  have ha3 : a * a * a = 1 := by rw [← pow_three', ← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num at ha
  refine ⟨?_, ?_⟩
  · have : e a * e a * e a = 1 := by rw [← map_mul, ← map_mul, ha3, map_one]
    exact congrArg Units.val this
  · intro h
    apply ha1
    apply e.injective
    rw [map_one]
    exact Units.ext h

theorem exists_inverting_involution_of_isLThreeTwo (hX : IsLThreeTwo X) {a : X}
    (ha : orderOf a = 3) : ∃ y : X, orderOf y = 2 ∧ y * a = a * a * y := by
  obtain ⟨e⟩ := nonempty_mulEquiv_GL_of_isLThreeTwo hX
  obtain ⟨h3, h1⟩ := matrix_facts_of_orderOf_three e ha
  obtain ⟨m, hm2, hm1, hma⟩ := exists_invMat _ h3 h1
  have hdet : m.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hm2
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  set g : GL (Fin 3) (ZMod 2) := GeneralLinearGroup.mkOfDetNeZero m hdet with hg
  have hgm : (g : Mat3) = m := rfl
  refine ⟨e.symm g, ?_, ?_⟩
  · apply orderOf_eq_prime
    · apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, map_one, pow_two]
      exact Units.ext (by rw [Units.val_mul, hgm]; exact hm2)
    · intro h
      apply hm1
      rw [← hgm]
      have : g = 1 := by
        have := congrArg e h
        rwa [MulEquiv.apply_symm_apply, map_one] at this
      rw [this]; rfl
  · apply e.injective
    rw [map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, Units.val_mul, hgm]; exact hma)

end Transfer

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
