module

public import CFSG.LargeExtraspecial.DWFldSL2

public section

namespace CFSG.LargeExtraspecial.DW

variable {C : Type} [Group C]

theorem exists_pow_mul_eq_of_normalized {P Q M : Subgroup C}
    (hQn : ∀ p ∈ P, ∀ x ∈ Q, p * x * p⁻¹ ∈ Q) (hMP : M ≤ P) {x y : C} (hx : x ∈ Q)
    (hy : y ∈ M) (k : ℕ) : ∃ x' ∈ Q, (x * y) ^ k = x' * y ^ k := by
  induction k with
  | zero => exact ⟨1, Q.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨x', hx', he⟩ := ih
    refine ⟨x' * (y ^ k * x * (y ^ k)⁻¹), Q.mul_mem hx'
      (hQn _ (hMP (M.pow_mem hy k)) x hx), ?_⟩
    rw [pow_succ, he, pow_succ]
    group

theorem eq_one_of_mul_eq_one {Q M : Subgroup C} (hQM : Q ⊓ M = ⊥) {x y : C} (hx : x ∈ Q)
    (hy : y ∈ M) (h : x * y = 1) : y = 1 := by
  have hyx : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
  have hmem : y ∈ Q ⊓ M := ⟨hyx ▸ Q.inv_mem hx, hy⟩
  rw [hQM] at hmem
  exact hmem

variable {D : Set C}

theorem subset_of_forall_mem_radical [Finite C] (hD : IsTransClass34 D) (U : Subgroup C)
    (hDU : ∃ d ∈ D, d ∈ U) {ι : Type*} (P Q : ι → Subgroup C) (hQU : ∀ i, Q i ≤ U)
    (hQn : ∀ i, ∀ p ∈ P i, ∀ x ∈ Q i, p * x * p⁻¹ ∈ Q i) (hP : ⨆ i, P i = ⊤)
    (hall : ∀ i, ∀ s ∈ D, s ∈ U → s ∈ Q i) : D ⊆ U := by
  let S : Set C := {s | s ∈ D ∧ s ∈ U}
  have key : ∀ i, ∀ p ∈ P i, ∀ s ∈ S, p * s * p⁻¹ ∈ S := fun i p hp s hs =>
    ⟨hD.conj_mem p hs.1, hQU i (hQn i p hp s (hall i s hs.1 hs.2))⟩
  let Stab : Subgroup C :=
    { carrier := {g | ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S}
      mul_mem' := by
        intro a b ha hb s
        rw [hb s, ha (b * s * b⁻¹)]
        simp only [mul_inv_rev, mul_assoc]
      one_mem' := by
        intro s
        simp
      inv_mem' := by
        intro a ha s
        rw [ha (a⁻¹ * s * a⁻¹⁻¹)]
        simp [mul_assoc] }
  have hPS : ∀ i, P i ≤ Stab := fun i p hp s =>
    ⟨key i p hp s, fun h => by
      have := key i p⁻¹ (inv_mem hp) _ h
      simpa [mul_assoc] using this⟩
  have hStab : Stab = ⊤ := eq_top_iff.2 (hP ▸ iSup_le hPS)
  obtain ⟨d₀, -, hd₀⟩ := hD.2.1
  obtain ⟨s₀, hs₀D, hs₀U⟩ := hDU
  intro d hd
  obtain ⟨c, hc⟩ := isConj_iff.1 (((hd₀ s₀).1 hs₀D).symm.trans ((hd₀ d).1 hd))
  have hcS : c ∈ Stab := hStab ▸ Subgroup.mem_top c
  rw [← hc]
  exact ((hcS s₀).1 ⟨hs₀D, hs₀U⟩).2

theorem eq_one_of_sq_eq_one_of_charP_two {F : Type*} [Field F] [CharP F 2] {l : F}
    (hl : l ^ 2 = 1) : l = 1 := by
  have h2 : (l - 1) ^ 2 = 0 := by
    linear_combination hl + (1 - l) * (CharTwo.two_eq_zero : (2 : F) = 0)
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

theorem injective_of_ker_scalar {F G : Type*} [Field F] [CharP F 2] [Group G]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) F →* G)
    (hker : ∀ g ∈ ρ.ker, ∃ l : Fˣ, (l : F) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = (l : F) • (1 : Matrix (Fin 2) (Fin 2) F)) :
    Function.Injective ρ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  obtain ⟨l, hl, hgl⟩ := hker g hg
  rw [Subgroup.mem_bot]
  ext i j
  rw [hgl, eq_one_of_sq_eq_one_of_charP_two hl, one_smul, Matrix.SpecialLinearGroup.coe_one]

theorem exists_ne_zero_ne_one_of_four_le {F : Type*} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) : ∃ s : F, s ≠ 0 ∧ s ≠ 1 := by
  by_contra! h
  have hsurj : Function.Surjective fun b : Bool => if b then (1 : F) else 0 := by
    intro s
    by_cases hs : s = 0
    · exact ⟨false, by simp [hs]⟩
    · exact ⟨true, by simp [h s hs]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [show Nat.card Bool = 2 by simp] at hle
  omega

theorem IsTransClass34.image {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {D : Set X}
    (hD : IsTransClass34 D) : IsTransClass34 (e '' D) := by
  obtain ⟨hgen, ⟨d₀, hd₀D, hd₀⟩, hinv, hord, hsq⟩ := hD
  have hmem : ∀ y, y ∈ e '' D ↔ e.symm y ∈ D := fun y =>
    ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy, MulEquiv.symm_apply_apply]; exact hx,
      fun h => ⟨e.symm y, h, e.apply_symm_apply y⟩⟩
  refine ⟨?_, ⟨e d₀, ⟨d₀, hd₀D, rfl⟩, fun y => ?_⟩, ?_, ?_, ?_⟩
  · have hc := MonoidHom.map_closure (e : X →* Y) D
    rw [hgen, Subgroup.map_top_of_surjective _ e.surjective] at hc
    exact hc.symm
  · rw [hmem, hd₀]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      refine isConj_iff.2 ⟨e c, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, hc, MulEquiv.apply_symm_apply]
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      refine isConj_iff.2 ⟨e.symm c, ?_⟩
      rw [← hc]
      simp
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := hinv x hx
    exact ⟨fun h => h1 (by simpa using h), by rw [← map_mul, h2, map_one]⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact hord x hx y hy
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h4
    rw [← map_mul, MulEquiv.orderOf_eq] at h4
    exact ⟨(x * y) ^ 2, hsq x hx y hy h4, by simp⟩

theorem mem_of_mul_mem [Finite C] (hD : IsTransClass34 D) {P Q M : Subgroup C}
    (hQn : ∀ p ∈ P, ∀ x ∈ Q, p * x * p⁻¹ ∈ Q) (hMP : M ≤ P) (hQM : Q ⊓ M = ⊥)
    {F : Type*} [Field F] [CharP F 2] {s : F} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (φ : Matrix.SpecialLinearGroup (Fin 2) F →* C) (hφ : Function.Injective φ)
    (hφM : φ.range ≤ M) {x : C} (hx : x ∈ Q) {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hxg : x * φ g ∈ D) : x * φ g ∈ Q := by
  have hM : ∀ a, φ a ∈ M := fun a => hφM ⟨a, rfl⟩
  have hn : ∀ a, ∀ y ∈ Q, φ a * y * (φ a)⁻¹ ∈ Q := fun a => hQn _ (hMP (hM a))
  by_contra hnot
  obtain ⟨-, hsq⟩ := hD.2.2.1 _ hxg
  have hg2 : g * g = 1 := by
    apply hφ
    rw [map_mul, map_one]
    refine eq_one_of_mul_eq_one hQM (Q.mul_mem hx (hn g x hx)) (M.mul_mem (hM g) (hM g)) ?_
    rw [← hsq]
    group
  have hg1 : g ≠ 1 := fun h => hnot (by rw [h, map_one, mul_one]; exact hx)
  obtain ⟨h, hh⟩ := exists_conj_pow_ne_one_sl2 hs0 hs1 hg2 hg1
  have he := hD.conj_mem (φ h) hxg
  obtain ⟨k, hk1, hk4, hk⟩ := hD.exists_pow_eq_one hxg he
  have hx₁ : x * (φ g * (φ h * x * (φ h)⁻¹) * (φ g)⁻¹) ∈ Q :=
    Q.mul_mem hx (hn g _ (hn h x hx))
  have hw : φ (g * (h * g * h⁻¹)) ∈ M := hM _
  have hprod : x * φ g * (φ h * (x * φ g) * (φ h)⁻¹) =
      x * (φ g * (φ h * x * (φ h)⁻¹) * (φ g)⁻¹) * φ (g * (h * g * h⁻¹)) := by
    simp only [map_mul, map_inv]
    group
  obtain ⟨x', hx', hpow⟩ := exists_pow_mul_eq_of_normalized hQn hMP hx₁ hw k
  rw [← hprod, hk] at hpow
  have hw1 : φ (g * (h * g * h⁻¹)) ^ k = 1 :=
    eq_one_of_mul_eq_one hQM hx' (M.pow_mem hw k) hpow.symm
  exact hh k hk1 hk4 (hφ (by rw [map_pow, hw1, map_one]))

theorem false_of_parabolic_family [Finite C] (hD : IsTransClass34 D) (U : Subgroup C)
    (hDU : ∃ d ∈ D, d ∈ U) (hU : U ≠ ⊤) {ι : Type*} (P Q M : ι → Subgroup C)
    (hQU : ∀ i, Q i ≤ U)
    (hQn : ∀ i, ∀ p ∈ P i, ∀ x ∈ Q i, p * x * p⁻¹ ∈ Q i) (hMP : ∀ i, M i ≤ P i)
    (hQM : ∀ i, Q i ⊓ M i = ⊥) (hP : ⨆ i, P i = ⊤) (F : ι → Type*) [∀ i, Field (F i)]
    [∀ i, CharP (F i) 2] (s : ∀ i, F i) (hs0 : ∀ i, s i ≠ 0) (hs1 : ∀ i, s i ≠ 1)
    (φ : ∀ i, Matrix.SpecialLinearGroup (Fin 2) (F i) →* C)
    (hφ : ∀ i, Function.Injective (φ i)) (hφM : ∀ i, (φ i).range ≤ M i)
    (hdec : ∀ i, ∀ u ∈ U, ∃ x ∈ Q i, ∃ g, u = x * φ i g) : False := by
  have hall : ∀ i, ∀ d ∈ D, d ∈ U → d ∈ Q i := by
    intro i d hd hdU
    obtain ⟨x, hx, g, rfl⟩ := hdec i d hdU
    exact mem_of_mul_mem hD (hQn i) (hMP i) (hQM i) (hs0 i) (hs1 i) (φ i) (hφ i) (hφM i) hx hd
  have hDsub := subset_of_forall_mem_radical hD U hDU P Q hQU hQn hP hall
  apply hU
  rw [eq_top_iff, ← hD.1]
  exact (Subgroup.closure_le U).2 hDsub

end CFSG.LargeExtraspecial.DW
