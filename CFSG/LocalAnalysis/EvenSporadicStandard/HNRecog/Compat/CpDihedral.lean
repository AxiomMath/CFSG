module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private theorem mul_self_eq_one_of_orderOf_eq_two {g : G} (h : orderOf g = 2) : g * g = 1 := by
  have hh := pow_orderOf_eq_one g
  rw [h] at hh
  simpa [pow_two] using hh

private theorem dihedral_au_cube (a x : G) (ha2 : a * a = 1) (hx2 : x * x = 1) :
    a * (a * x) ^ 3 = (a * x)⁻¹ * x * (a * x) := by
  generalize hu : a * x = u
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have ha_u : a * u * a = u⁻¹ := by
    rw [← hu, mul_inv_rev, hxi, hai]
    calc a * (a * x) * a = (a * a) * x * a := by group
      _ = x * a := by rw [ha2, one_mul]
  have ha_u' : a * u = u⁻¹ * a := by
    calc a * u = a * u * (a * a) := by rw [ha2, mul_one]
      _ = (a * u * a) * a := by group
      _ = u⁻¹ * a := by rw [ha_u]
  have hx_eq : x = a * u := by
    rw [← hu, ← mul_assoc, ha2, one_mul]
  calc a * u ^ 3 = (a * u) * u ^ 2 := by group
    _ = (u⁻¹ * a) * u ^ 2 := by rw [ha_u']
    _ = u⁻¹ * (a * u ^ 2) := by group
    _ = u⁻¹ * ((a * u) * u) := by rw [pow_two, mul_assoc]
    _ = u⁻¹ * x * u := by rw [hx_eq]; group

private theorem dihedral_xu_cube (a x : G) (ha2 : a * a = 1) (hx2 : x * x = 1)
    (hb : (a * x) ^ 3 = ((a * x) ^ 3)⁻¹) :
    x * (a * x) ^ 3 = (a * x) * a * (a * x)⁻¹ := by
  generalize hu : a * x = u
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have ha_u : a * u * a = u⁻¹ := by
    rw [← hu, mul_inv_rev, hxi, hai]
    calc a * (a * x) * a = (a * a) * x * a := by group
      _ = x * a := by rw [ha2, one_mul]
  have hx_eq : x = a * u := by
    rw [← hu, ← mul_assoc, ha2, one_mul]
  have hu_a : u * a = a * u⁻¹ := by
    calc u * a = (a * a) * (u * a) := by rw [ha2, one_mul]
      _ = a * (a * u * a) := by group
      _ = a * u⁻¹ := by rw [ha_u]
  have hb' : u ^ 3 = (u ^ 3)⁻¹ := by rw [← hu]; exact hb
  have h33 : u ^ 3 * u ^ 3 = 1 := by
    have h := mul_inv_cancel (u ^ 3)
    rwa [← hb'] at h
  have h6 : u ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add]
    exact h33
  have h4 : u ^ 4 = (u ^ 2)⁻¹ := by
    have h : u ^ 4 * u ^ 2 = 1 := by
      rw [← pow_add, show (4 : ℕ) + 2 = 6 from rfl, h6]
    calc u ^ 4 = u ^ 4 * 1 := (mul_one _).symm
      _ = u ^ 4 * (u ^ 2 * (u ^ 2)⁻¹) := by rw [mul_inv_cancel]
      _ = (u ^ 4 * u ^ 2) * (u ^ 2)⁻¹ := by group
      _ = 1 * (u ^ 2)⁻¹ := by rw [h]
      _ = (u ^ 2)⁻¹ := one_mul _
  calc x * u ^ 3 = (a * u) * u ^ 3 := by rw [hx_eq]
    _ = a * u ^ 4 := by group
    _ = a * (u ^ 2)⁻¹ := by rw [h4]
    _ = (a * u⁻¹) * u⁻¹ := by group
    _ = (u * a) * u⁻¹ := by rw [hu_a]
    _ = u * a * u⁻¹ := by group

theorem cp_pow_mem_Gxy {a x : G} (ha : orderOf a = 2) (hx : orderOf x = 2) {k : ℕ}
    (hk : orderOf ((a * x) ^ k) = 2) : (a * x) ^ k ∈ Gxy a x := by
  have ha2 : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two ha
  have hx2 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hk2 : (a * x) ^ k * (a * x) ^ k = 1 := mul_self_eq_one_of_orderOf_eq_two hk
  have hki : ((a * x) ^ k)⁻¹ = (a * x) ^ k := inv_eq_of_mul_eq_one_right hk2
  have ha_u : a * (a * x) * a⁻¹ = (a * x)⁻¹ := by
    rw [mul_inv_rev, hxi, hai]
    calc a * (a * x) * a = (a * a) * x * a := by group
      _ = x * a := by rw [ha2, one_mul]
  have hx_u : x * (a * x) * x⁻¹ = (a * x)⁻¹ := by
    rw [mul_inv_rev, hxi, hai]
    calc x * (a * x) * x = x * a * (x * x) := by group
      _ = x * a := by rw [hx2, mul_one]
  have hav : a * (a * x) ^ k = (a * x) ^ k * a := by
    calc a * (a * x) ^ k = a * (a * x) ^ k * 1 := (mul_one _).symm
      _ = a * (a * x) ^ k * (a * a) := by rw [ha2]
      _ = (a * (a * x) ^ k * a) * a := by group
      _ = (a * (a * x) ^ k * a⁻¹) * a := by rw [hai]
      _ = ((a * x) ^ k)⁻¹ * a := by rw [← conj_pow, ha_u, inv_pow]
      _ = (a * x) ^ k * a := by rw [hki]
  have hxv : x * (a * x) ^ k = (a * x) ^ k * x := by
    calc x * (a * x) ^ k = x * (a * x) ^ k * 1 := (mul_one _).symm
      _ = x * (a * x) ^ k * (x * x) := by rw [hx2]
      _ = (x * (a * x) ^ k * x) * x := by group
      _ = (x * (a * x) ^ k * x⁻¹) * x := by rw [hxi]
      _ = ((a * x) ^ k)⁻¹ * x := by rw [← conj_pow, hx_u, inv_pow]
      _ = (a * x) ^ k * x := by rw [hki]
  exact mem_Gxy.2 ⟨mem_Gx.2 hav, mem_Gx.2 hxv⟩

theorem cp_Gxyz_pow_eq (a x : G) (k : ℕ) : Gxyz a ((a * x) ^ k) x = Gxy a x := by
  ext g
  rw [mem_Gxyz, mem_Gxy]
  constructor
  · rintro ⟨hga, _, hgx⟩; exact ⟨hga, hgx⟩
  · rintro ⟨hga, hgx⟩
    refine ⟨hga, ?_, hgx⟩
    rw [mem_Gx] at hga hgx ⊢
    have hcom : Commute g (a * x) := by
      rw [commute_iff_eq]
      calc g * (a * x) = (g * a) * x := by rw [mul_assoc]
        _ = (a * g) * x := by rw [← hga]
        _ = a * (g * x) := by rw [mul_assoc]
        _ = a * (x * g) := by rw [hgx]
        _ = (a * x) * g := by rw [mul_assoc]
    exact (hcom.pow_right k).symm

theorem cp_central_inv (h : F5Std a z) {x : G} (hx : IsConj a x) {k : ℕ}
    (hk : IsConj a ((a * x) ^ k) ∨ IsConj z ((a * x) ^ k)) :
    (a * x) ^ k ∈ InvIn (Gxy a x) ∧ Gxyz a ((a * x) ^ k) x = Gxy a x := by
  have ha2 := h.typ.orderOf_a
  have hx2 := h.orderOf_eq_two (Or.inl hx)
  have hk2 := h.orderOf_eq_two hk
  exact ⟨⟨cp_pow_mem_Gxy ha2 hx2 hk2, hk2⟩, cp_Gxyz_pow_eq a x k⟩

theorem cp_orb6A_cube_mem (h : F5Std a z) {x : G} (hx : x ∈ orb6A a a) :
    (a * x) ^ 3 ∈ orb2A a a ∩ orb2A a x := by
  simp only [orb6A, Set.mem_setOf_eq] at hx
  obtain ⟨hax, ho, hb6⟩ := hx
  have ha2 : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two h.typ.orderOf_a
  have hx2 : x * x = 1 :=
    mul_self_eq_one_of_orderOf_eq_two (h.orderOf_eq_two (Or.inl hax))
  have ho3 : orderOf ((a * x) ^ 3) = 2 := by
    rw [orderOf_pow_of_dvd (x := a * x) (n := 3) (by norm_num) (by rw [ho]; norm_num), ho]
  have hb : (a * x) ^ 3 = ((a * x) ^ 3)⁻¹ :=
    (inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two ho3)).symm
  have hab := dihedral_au_cube a x ha2 hx2
  have hxb := dihedral_xu_cube a x ha2 hx2 hb
  refine ⟨?_, ?_⟩
  · simp only [orb2A, Set.mem_setOf_eq]
    refine ⟨hb6, hax.trans ?_⟩
    exact isConj_iff.2 ⟨(a * x)⁻¹, by rw [inv_inv]; exact hab.symm⟩
  · simp only [orb2A, Set.mem_setOf_eq]
    exact ⟨hb6, isConj_iff.2 ⟨a * x, hxb.symm⟩⟩

theorem cp_orb6A_cube_mul_mem (h : F5Std a z) {x : G} (hx : x ∈ orb6A a a) :
    (a * x) ^ 3 * x ∈ orb3A a a := by
  have hbA := cp_orb6A_cube_mem h hx
  simp only [orb6A, Set.mem_setOf_eq] at hx
  obtain ⟨hax, ho, hb6⟩ := hx
  have ha2 : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two h.typ.orderOf_a
  have hx2 : x * x = 1 :=
    mul_self_eq_one_of_orderOf_eq_two (h.orderOf_eq_two (Or.inl hax))
  have ho3 : orderOf ((a * x) ^ 3) = 2 := by
    rw [orderOf_pow_of_dvd (x := a * x) (n := 3) (by norm_num) (by rw [ho]; norm_num), ho]
  have hb2 : (a * x) ^ 3 * (a * x) ^ 3 = 1 := mul_self_eq_one_of_orderOf_eq_two ho3
  have hb : (a * x) ^ 3 = ((a * x) ^ 3)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hb2).symm
  have hbG : (a * x) ^ 3 ∈ Gxy a x :=
    cp_pow_mem_Gxy h.typ.orderOf_a (h.orderOf_eq_two (Or.inl hax)) ho3
  have hba : a * (a * x) ^ 3 = (a * x) ^ 3 * a := mem_Gx.1 (mem_Gxy.1 hbG).1
  have hbx : x * (a * x) ^ 3 = (a * x) ^ 3 * x := mem_Gx.1 (mem_Gxy.1 hbG).2
  have hxb := dihedral_xu_cube a x ha2 hx2 hb
  have hconj : IsConj a ((a * x) ^ 3 * x) :=
    isConj_iff.2 ⟨a * x, by rw [← hbx]; exact hxb.symm⟩
  have hac : a * ((a * x) ^ 3 * x) = (a * x) ^ 4 := by
    calc a * ((a * x) ^ 3 * x) = (a * (a * x) ^ 3) * x := by rw [mul_assoc]
      _ = ((a * x) ^ 3 * a) * x := by rw [hba]
      _ = (a * x) ^ 3 * (a * x) := by rw [mul_assoc]
      _ = (a * x) ^ 4 := by rw [← pow_succ]
  have hord : orderOf (a * ((a * x) ^ 3 * x)) = 3 := by
    rw [hac, orderOf_pow' (x := a * x) (n := 4) (by norm_num), ho]
    norm_num
  simp only [orb3A, Set.mem_setOf_eq]
  refine ⟨hconj, hord, (a * x) ^ 3, hbA.1, ?_⟩
  simp only [orb2A, Set.mem_setOf_eq]
  refine ⟨hb6, ?_⟩
  have hcbb : ((a * x) ^ 3 * x) * (a * x) ^ 3 = x := by
    rw [mul_assoc, hbx, ← mul_assoc, hb2, one_mul]
  rw [hcbb]
  exact hax

end CFSG.EvenSporadicStandard.HNRecog.Section4
