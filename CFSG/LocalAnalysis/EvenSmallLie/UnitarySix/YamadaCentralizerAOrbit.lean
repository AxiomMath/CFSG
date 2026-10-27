module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaOmega

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Sporadic.Schreier

section G

variable {G : Type} [Group G]

@[expose] def conjPermHom {X : Subgroup G} {S : Set G}
    (hS : ∀ x ∈ X, ∀ y ∈ S, x * y * x⁻¹ ∈ S) : X →* Equiv.Perm S where
  toFun g :=
    { toFun := fun y => ⟨(g : G) * y * (g : G)⁻¹, hS g g.2 y y.2⟩
      invFun := fun y => ⟨(g : G)⁻¹ * y * g, by simpa using hS _ (inv_mem g.2) y y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := Equiv.ext fun y => Subtype.ext (by simp)
  map_mul' g h := Equiv.ext fun y => Subtype.ext (by simp [mul_assoc])

theorem conjPermHom_apply {X : Subgroup G} {S : Set G}
    (hS : ∀ x ∈ X, ∀ y ∈ S, x * y * x⁻¹ ∈ S) (g : X) (y : S) :
    ((conjPermHom hS g y : S) : G) = g * y * (g : G)⁻¹ :=
  rfl

end G

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem card_X_of_omega (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t}) :
    Nat.card (normalizer (toddE D t : Set G)) = 2 ^ 9 *
      Nat.card (normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  rw [← h.ncard_omega_mul, hΩ, ncard_toddA_mul_t]

theorem card_X_dvd_of_omega (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t}) :
    Nat.card (normalizer (toddE D t : Set G)) ∣ 2 ^ 9 * (2 ^ 10 * 20160 * 6) := by
  rw [h.card_X_of_omega hΩ]
  exact Nat.mul_dvd_mul_left _ h.card_NHA.2

theorem conjOrbit_a₁_eq (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t}) :
    conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G) = conjClass (toddK D) (D.a₁ : G) := by
  classical
  set X := normalizer (toddE D t : Set G)
  set O := conjOrbit X (D.a₁ : G)
  have hXA := normalizer_le_of_omega hΩ
  obtain ⟨m₁, m₂, m₃⟩ := D.a_mem
  have mA₁ : (D.a₁ : G) ∈ toddA D := ⟨_, m₁, rfl⟩
  have mA₂ : (D.a₂ : G) ∈ toddA D := ⟨_, m₂, rfl⟩
  have mA₃ : (D.a₃ : G) ∈ toddA D := ⟨_, m₃, rfl⟩
  have hOA : O ⊆ toddA D := by
    rintro _ ⟨n, hn, rfl⟩
    have := (mem_normalizer_iff.1 (inv_mem (hXA hn)) _).1 mA₁
    rwa [inv_inv] at this
  have hOK : ∀ c ∈ toddK D, ∀ y ∈ O, c * y * c⁻¹ ∈ O :=
    fun c hc y hy => conj_mem_conjOrbit' (h.toddK_le_X hc) hy
  have hc := h.ncard_eq_of_invariant (fun y hy => toddA_le_toddE D t (hOA hy)) hOK
  have htA : t ∉ toddA D := fun ht => h.t_not_mem (toddA_le D ht)
  have hatA : ∀ a ∈ toddA D, a * t ∉ O := fun a ha hat => htA (by
    have := mul_mem (inv_mem ha) (hOA hat)
    rwa [inv_mul_cancel_left] at this)
  have h1 : (1 : G) ∉ O := by
    rintro ⟨n, -, hn⟩
    apply (a_ne_one D).1
    calc (D.a₁ : G) = n * (n⁻¹ * D.a₁ * n) * n⁻¹ := by group
      _ = 1 := by rw [hn]; group
  have hself : (D.a₁ : G) ∈ O := self_mem_conjOrbit _ _
  have htO : t ∉ O := fun ht => htA (hOA ht)
  simp only [h1, hself, htO, hatA _ mA₁, hatA _ mA₂, hatA _ mA₃, ↓reduceIte, zero_add,
    add_zero] at hc
  have hdvd : O.ncard ∣ 2 ^ 9 * (2 ^ 10 * 20160 * 6) :=
    (Dvd.intro _ (ncard_conjOrbit_mul (le_normalizer (toddA_le_toddE D t mA₁)))).trans
      (h.card_X_dvd_of_omega hΩ)
  have h21 : O.ncard = 21 := by
    by_cases h2 : (D.a₂ : G) ∈ O <;> by_cases h3 : (D.a₃ : G) ∈ O <;>
      simp only [h2, h3, ↓reduceIte, add_zero] at hc <;> rw [hc] at hdvd ⊢ <;>
      norm_num at hdvd
  have hsub : conjClass (toddK D) (D.a₁ : G) ⊆ O := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c⁻¹, inv_mem (h.toddK_le_X hc), by rw [inv_inv]⟩
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [h21, (ncard_delta D).1])
    (Set.toFinite _)).symm

theorem conj_mem_delta_of_omega (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t}) :
    ∀ x ∈ normalizer (toddE D t : Set G), ∀ y ∈ conjClass (toddK D) (D.a₁ : G),
      x * y * x⁻¹ ∈ conjClass (toddK D) (D.a₁ : G) := by
  rw [← h.conjOrbit_a₁_eq hΩ]
  exact fun x hx y hy => conj_mem_conjOrbit' hx hy

theorem closure_delta_eq (h : Setting G L D t) :
    closure (conjClass (toddK D) (D.a₁ : G)) = toddA D := by
  apply h.eq_toddA_of_invariant
  · rw [closure_le]
    exact conjClass_toddK_subset D D.a_mem.1
  · intro k hk b hb
    induction hb using closure_induction with
    | mem y hy => exact subset_closure (conj_mem_conjClass hk hy)
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul y z _ _ hy hz =>
      rw [show k * (y * z) * k⁻¹ = (k * y * k⁻¹) * (k * z * k⁻¹) by group]
      exact mul_mem hy hz
    | inv y _ hy =>
      rw [show k * y⁻¹ * k⁻¹ = (k * y * k⁻¹)⁻¹ by group]
      exact inv_mem hy
  · intro hb
    apply (a_ne_one D (G := G)).1
    have : (D.a₁ : G) ∈ closure (conjClass (toddK D) (D.a₁ : G)) :=
      subset_closure (self_mem_conjClass _ _)
    rwa [hb, mem_bot] at this

theorem two_trans_delta (h : Setting G L D t) {x y z w : G}
    (hx : x ∈ conjClass (toddK D) (D.a₁ : G)) (hy : y ∈ conjClass (toddK D) (D.a₁ : G))
    (hz : z ∈ conjClass (toddK D) (D.a₁ : G)) (hw : w ∈ conjClass (toddK D) (D.a₁ : G))
    (hxy : x ≠ y) (hzw : z ≠ w) : ∃ k ∈ toddK D, k * x * k⁻¹ = z ∧ k * y * k⁻¹ = w := by
  rw [conjClass_toddK] at hx hy hz hw
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  obtain ⟨z, hz, rfl⟩ := hz
  obtain ⟨w, hw, rfl⟩ := hw
  obtain ⟨k, hk, hkx, hky⟩ := h.facts.two_trans x hx y hy z hz w hw
    (fun e => hxy (congrArg _ e)) (fun e => hzw (congrArg _ e))
  exact ⟨k, ⟨k, hk, rfl⟩, by rw [← hkx]; simp, by rw [← hky]; simp⟩

theorem eq_one_of_mem_toddK_of_mem_toddE (h : Setting G L D t) {k : G} (hk : k ∈ toddK D)
    (hkE : k ∈ toddE D t) : k = 1 :=
  Subgroup.disjoint_def.1 (disjoint_toddA_toddK D) (h.mem_toddA_of_mem_L hkE (toddK_le D hk)) hk

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
