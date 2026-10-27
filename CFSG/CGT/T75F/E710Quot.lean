module

public import CFSG.CGT.T75F.E710Centre

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

namespace Endgame710

variable (h : Endgame710 D M L q)
include h

theorem mk_ne_one {d : X} (hd : d ∈ D) : (QuotientGroup.mk d : X ⧸ Subgroup.center X) ≠ 1 :=
  fun h1 => h.not_mem_center hd ((QuotientGroup.eq_one_iff d).1 h1)

theorem Dhat_sq {x : X ⧸ Subgroup.center X}
    (hx : x ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D) : x * x = 1 := by
  obtain ⟨d, hd, rfl⟩ := hx
  change (QuotientGroup.mk d : X ⧸ Subgroup.center X) * QuotientGroup.mk d = 1
  rw [← QuotientGroup.mk_mul, h.sq_eq_one d hd]
  rfl

theorem Dhat_ne_one {x : X ⧸ Subgroup.center X}
    (hx : x ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D) : x ≠ 1 := by
  obtain ⟨d, hd, rfl⟩ := hx
  exact h.mk_ne_one hd

theorem Dhat_conj {x : X ⧸ Subgroup.center X}
    (hx : x ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D) (g : X ⧸ Subgroup.center X) :
    g * x * g⁻¹ ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D := by
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨g * d * g⁻¹, h.conj_mem d hd g, by simp⟩

theorem Dhat_isConj : ∃ x₀ : X ⧸ Subgroup.center X,
    (QuotientGroup.mk' (Subgroup.center X)) '' D = {g | IsConj x₀ g} := by
  obtain ⟨y, hy, -⟩ := h.exists_out
  refine ⟨QuotientGroup.mk y, ?_⟩
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨g, c, hc, hdc⟩ := h.single_class hy hd
    refine isConj_iff.2 ⟨QuotientGroup.mk g, ?_⟩
    have hc1 : (QuotientGroup.mk c : X ⧸ Subgroup.center X) = 1 :=
      (QuotientGroup.eq_one_iff c).2 hc
    change (QuotientGroup.mk g : X ⧸ Subgroup.center X) * QuotientGroup.mk y *
      (QuotientGroup.mk g)⁻¹ = QuotientGroup.mk d
    rw [hdc]
    simp [hc1]
  · intro hx
    obtain ⟨g, hg⟩ := isConj_iff.1 hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨g * y * g⁻¹, h.conj_mem y hy g, ?_⟩
    rw [← hg]
    simp

theorem Dhat_closure :
    Subgroup.closure ((QuotientGroup.mk' (Subgroup.center X)) '' D) = ⊤ := by
  rw [← MonoidHom.map_closure, h.closure_D_eq_top, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)

theorem order_mk_mul {d e : X} (hd : d ∈ D) (he : e ∈ D) :
    orderOf (QuotientGroup.mk (d * e) : X ⧸ Subgroup.center X) ∣ 2 ∨
      Odd (orderOf (QuotientGroup.mk (d * e) : X ⧸ Subgroup.center X)) := by
  obtain ⟨a, ha⟩ := h.exists_conj_mem hd
  have hd' : a⁻¹ * d * a ∈ D := by simpa using h.conj_mem d hd a⁻¹
  have he' : a⁻¹ * e * a ∈ D := by simpa using h.conj_mem e he a⁻¹
  have hord : orderOf (QuotientGroup.mk ((a⁻¹ * d * a) * (a⁻¹ * e * a)) :
      X ⧸ Subgroup.center X) = orderOf (QuotientGroup.mk (d * e) : X ⧸ Subgroup.center X) := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj (QuotientGroup.mk a : X ⧸ Subgroup.center X)⁻¹)
      (QuotientGroup.mk (d * e) : X ⧸ Subgroup.center X)
    rw [show (a⁻¹ * d * a) * (a⁻¹ * e * a) = a⁻¹ * (d * e) * a by group]
    simpa [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h1
  rw [← hord]
  set d' := a⁻¹ * d * a with hd'def
  set e' := a⁻¹ * e * a with he'def
  have hd2 := h.sq_eq_one d' hd'
  have he2 := h.sq_eq_one e' he'
  by_cases he'M : e' ∈ M
  ·
    left
    have hcomm : d' * e' = e' * d' := h.M_comm _ ha _ he'M
    have h2 : (d' * e') ^ 2 = 1 := by
      calc (d' * e') ^ 2 = d' * e' * (d' * e') := by rw [pow_two]
        _ = d' * (e' * d') * e' := by group
        _ = d' * (d' * e') * e' := by rw [hcomm]
        _ = (d' * d') * (e' * e') := by group
        _ = 1 := by rw [hd2, he2, one_mul]
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, h2]
    rfl
  · right
    obtain ⟨k, hk, hk3, hcase⟩ := h.order_cases he' he'M hd' ha
    have hinv : d' * e' = (e' * d')⁻¹ := by rw [dihedral_inv he2 hd2]
    rcases hcase with ho | ho
    ·
      have hdvd : orderOf (QuotientGroup.mk (d' * e') : X ⧸ Subgroup.center X) ∣ k := by
        have h1 := orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center X)) (d' * e')
        have h2 : orderOf (d' * e') = k := by rw [hinv, orderOf_inv, ho]
        rw [h2] at h1
        exact h1
      exact hk.of_dvd_nat hdvd
    ·
      obtain ⟨-, hcZ⟩ := h.centre_of_order_two_mul he' he'M hd' ha ho
      have hZ : (d' * e') ^ k ∈ Subgroup.center X := by
        rw [hinv, inv_pow]
        exact (Subgroup.center X).inv_mem hcZ
      have hpow : (QuotientGroup.mk (d' * e') : X ⧸ Subgroup.center X) ^ k = 1 := by
        rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff _).2 hZ
      exact hk.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)

end Endgame710

end CFSG.CGT.T75F
