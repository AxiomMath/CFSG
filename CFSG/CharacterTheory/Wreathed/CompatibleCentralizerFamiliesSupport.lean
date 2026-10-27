module

public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

universe u

variable {G : Type u} [Group G]

section Conjugation

theorem mem_conj_iff {Q : Subgroup G} {k y : G} :
    y ∈ Q.map (MulAut.conj k⁻¹).toMonoidHom ↔ k * y * k⁻¹ ∈ Q := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change k * (k⁻¹ * q * k⁻¹⁻¹) * k⁻¹ ∈ Q
    have hq' : k * (k⁻¹ * q * k⁻¹⁻¹) * k⁻¹ = q := by group
    rw [hq']
    exact hq
  · intro hy
    refine ⟨k * y * k⁻¹, hy, ?_⟩
    change k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y
    simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem conj_mem_conj {Q : Subgroup G} {k q : G} (hq : q ∈ Q) :
    k⁻¹ * q * k ∈ Q.map (MulAut.conj k⁻¹).toMonoidHom := by
  rw [mem_conj_iff]
  have hq' : k * (k⁻¹ * q * k) * k⁻¹ = q := by group
  rw [hq']
  exact hq

theorem map_conj_map_conj (Q : Subgroup G) (h l : G) :
    (Q.map (MulAut.conj h⁻¹).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom =
      Q.map (MulAut.conj (h * l)⁻¹).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev,
    inv_inv, mul_assoc]

theorem map_conj_one (Q : Subgroup G) : Q.map (MulAut.conj (1 : G)⁻¹).toMonoidHom = Q := by
  rw [inv_one, map_one]
  exact Subgroup.map_id Q

theorem map_conj_inv_map_conj (Q : Subgroup G) (h : G) :
    (Q.map (MulAut.conj h⁻¹).toMonoidHom).map (MulAut.conj h⁻¹⁻¹).toMonoidHom = Q := by
  rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]

theorem mem_centralizer_conj_iff {Q : Subgroup G} {k g : G} :
    g ∈ Subgroup.centralizer (Q.map (MulAut.conj k⁻¹).toMonoidHom : Set G) ↔
      k * g * k⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hg q hq
    have h := hg (k⁻¹ * q * k) (conj_mem_conj hq)
    calc q * (k * g * k⁻¹) = k * ((k⁻¹ * q * k) * g) * k⁻¹ := by group
      _ = k * (g * (k⁻¹ * q * k)) * k⁻¹ := by rw [h]
      _ = k * g * k⁻¹ * q := by group
  · intro hg y hy
    have h := hg (k * y * k⁻¹) (mem_conj_iff.mp hy)
    calc y * g = k⁻¹ * ((k * y * k⁻¹) * (k * g * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * g * k⁻¹) * (k * y * k⁻¹)) * k := by rw [h]
      _ = g * y := by group

theorem conj_mem_centralizer_conj {Q : Subgroup G} {k g : G}
    (hg : g ∈ Subgroup.centralizer (Q : Set G)) :
    k⁻¹ * g * k ∈ Subgroup.centralizer (Q.map (MulAut.conj k⁻¹).toMonoidHom : Set G) := by
  rw [mem_centralizer_conj_iff]
  have hg' : k * (k⁻¹ * g * k) * k⁻¹ = g := by group
  rw [hg']
  exact hg

theorem mem_center_conj_iff {Q : Subgroup G} {k y : G} :
    y ∈ Q.map (MulAut.conj k⁻¹).toMonoidHom ⊓
        Subgroup.centralizer (Q.map (MulAut.conj k⁻¹).toMonoidHom : Set G) ↔
      k * y * k⁻¹ ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_conj_iff, mem_centralizer_conj_iff]

theorem conj_mem_center_conj {Q : Subgroup G} {k y : G}
    (hy : y ∈ Q ⊓ Subgroup.centralizer (Q : Set G)) :
    k⁻¹ * y * k ∈ Q.map (MulAut.conj k⁻¹).toMonoidHom ⊓
      Subgroup.centralizer (Q.map (MulAut.conj k⁻¹).toMonoidHom : Set G) := by
  rw [mem_center_conj_iff]
  have hy' : k * (k⁻¹ * y * k) * k⁻¹ = y := by group
  rw [hy']
  exact hy

theorem orderOf_conj (k y : G) : orderOf (k⁻¹ * y * k) = orderOf y := by
  rw [show k⁻¹ * y * k = (MulAut.conj k⁻¹) y by simp, MulEquiv.orderOf_eq]

theorem conj_isPGroup {p : ℕ} {Q : Subgroup G} (hQ : IsPGroup p Q) (k : G) :
    IsPGroup p (Q.map (MulAut.conj k⁻¹).toMonoidHom) :=
  hQ.map _

theorem conj_ne_bot {Q : Subgroup G} (hQ : Q ≠ ⊥) (k : G) :
    Q.map (MulAut.conj k⁻¹).toMonoidHom ≠ ⊥ := by
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj k⁻¹).injective]
  exact hQ

theorem conj_le_conj {Q Q₁ : Subgroup G} (h : Q ≤ Q₁) (k : G) :
    Q.map (MulAut.conj k⁻¹).toMonoidHom ≤ Q₁.map (MulAut.conj k⁻¹).toMonoidHom :=
  Subgroup.map_mono h

end Conjugation

section Center

theorem exists_center_orderOf_eq [Finite G] {p : ℕ} [Fact p.Prime] {Q : Subgroup G}
    (hQ : IsPGroup p Q) (hQ1 : Q ≠ ⊥) :
    ∃ y ∈ Q ⊓ Subgroup.centralizer (Q : Set G), orderOf y = p := by
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
  have hZ : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  obtain ⟨k, hk⟩ := (hQ.to_subgroup (Subgroup.center Q)).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
  have hdvd : p ∣ Nat.card (Subgroup.center Q) := by
    rw [hk]
    exact dvd_pow_self p hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨((z : Q) : G), ⟨(z : Q).2, ?_⟩, ?_⟩
  · change ((z : Q) : G) ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨q, hq⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz

end Center

section FourGroup

variable {J J₁ : G}

theorem mem_four_cases (hJ : J * J = 1) (hJ₁ : J₁ * J₁ = 1) (hc : J * J₁ = J₁ * J) {t : G}
    (ht : t ∈ Subgroup.closure {J, J₁}) : t = 1 ∨ t = J ∨ t = J₁ ∨ t = J * J₁ := by
  have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ
  have hJ₁inv : J₁⁻¹ = J₁ := inv_eq_of_mul_eq_one_right hJ₁
  have hstep : ∀ x ∈ ({J, J₁} : Set G), ∀ y : G,
      (y = 1 ∨ y = J ∨ y = J₁ ∨ y = J * J₁) →
        (x * y = 1 ∨ x * y = J ∨ x * y = J₁ ∨ x * y = J * J₁) := by
    rintro x (rfl | rfl) y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl hJ
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hJ, one_mul])))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr hc.symm))
    · exact Or.inl hJ₁
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hc, mul_assoc, hJ₁, mul_one]))
  induction ht using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left x hx y _ ih => exact hstep x hx y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with rfl | rfl
    · rw [hJinv]
      exact hstep _ (Set.mem_insert _ _) y ih
    · rw [hJ₁inv]
      exact hstep _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) y ih

end FourGroup

section Extension

variable (N : Subgroup G) (lam : N →* ℂˣ)

open scoped Classical in
@[expose] def extend (g : G) : ℂˣ := if h : g ∈ N then lam ⟨g, h⟩ else 1

variable {N lam}

theorem extend_of_mem {g : G} (h : g ∈ N) : extend N lam g = lam ⟨g, h⟩ := dite_eq_left h

theorem extend_coe (v : N) : extend N lam v = lam v := by
  rw [extend_of_mem v.2]

theorem extend_mul {g g' : G} (hg : g ∈ N) (hg' : g' ∈ N) :
    extend N lam (g * g') = extend N lam g * extend N lam g' := by
  rw [extend_of_mem hg, extend_of_mem hg', extend_of_mem (N.mul_mem hg hg'), ← map_mul]
  rfl

theorem extend_conj {h g : G} (hh : h ∈ N) (hg : g ∈ N) :
    extend N lam (h⁻¹ * g * h) = extend N lam g := by
  rw [extend_of_mem hg,
    extend_of_mem (N.mul_mem (N.mul_mem (N.inv_mem hh) hg) hh)]
  have : (⟨h⁻¹ * g * h, N.mul_mem (N.mul_mem (N.inv_mem hh) hg) hh⟩ : N) =
      (⟨h, hh⟩ : N)⁻¹ * ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
  rw [this, map_mul, map_mul, mul_comm, ← mul_assoc, map_inv, mul_inv_cancel, one_mul]

end Extension

section Special

@[expose] def IsSpecial (J : G) (T Q : Subgroup G) : Prop :=
  (J ∈ Q ⊓ Subgroup.centralizer (Q : Set G) ∧
    ∀ y ∈ Q ⊓ Subgroup.centralizer (Q : Set G), orderOf y = 2 → y = J) ∨
  T ≤ Q ⊓ Subgroup.centralizer (Q : Set G)

variable {J : G} {T Q : Subgroup G}

theorem IsSpecial.mem (hJT : J ∈ T) (h : IsSpecial J T Q) : J ∈ Q := by
  rcases h with h | h
  · exact h.1.1
  · exact (h hJT).1

theorem IsSpecial.centralizer_le (hJT : J ∈ T) (h : IsSpecial J T Q) :
    Subgroup.centralizer (Q : Set G) ≤ Subgroup.centralizer {J} :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (h.mem hJT))

theorem le_centralizer_of_le_center (h : T ≤ Q ⊓ Subgroup.centralizer (Q : Set G)) :
    Q ≤ Subgroup.centralizer (T : Set G) :=
  Subgroup.le_centralizer_iff.mpr (h.trans inf_le_right)

theorem centralizer_le_of_le_center (h : T ≤ Q ⊓ Subgroup.centralizer (Q : Set G)) :
    Subgroup.centralizer (Q : Set G) ≤ Subgroup.centralizer (T : Set G) :=
  Subgroup.centralizer_le (fun _ ht => (h ht).1)

end Special

end CFSG.Wreathed.CompatibleFamilies
