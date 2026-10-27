module

public import CFSG.LargeExtraspecial.GLRSplitLevi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup QuadraticMap CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

abbrev conjSub (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem mem_conjSub {g x : G} {H : Subgroup G} : x ∈ conjSub g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

omit [Finite G] in
theorem conjSub_mul (g g' : G) (H : Subgroup G) :
    conjSub (g * g') H = conjSub g (conjSub g' H) := by
  rw [conjSub, conjSub, conjSub, Subgroup.map_map, map_mul]
  rfl

omit [Finite G] in
theorem conjSub_one (H : Subgroup G) : conjSub 1 H = H := by
  ext x; simp

omit [Finite G] in
theorem card_conjSub (g : G) (H : Subgroup G) : Nat.card (conjSub g H) = Nat.card H :=
  card_map_of_injective (MulAut.conj g).injective

theorem card_mul_two_of_isZCompl {H : Subgroup G} (hH : C.IsZCompl H) :
    Nat.card H * 2 = Nat.card C.A := by
  have hidx : (H.subgroupOf C.A).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨S.z, C.z_mem_A⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [Subgroup.coe_mul]
    rcases hH.2.2 b b.2 with h | h
    · exact Or.inr ⟨h, fun hz => (hH.mem_iff_not b.2).mp hz h⟩
    · exact Or.inl ⟨h, (hH.mem_iff_not b.2).mp h⟩
  have := relIndex_mul_card H C.A
  rw [relIndex, hidx, inf_eq_left.mpr hH.1] at this
  rw [← this, mul_comm]

omit [Finite G] in
theorem conjSub_eq_self {q : G} {H : Subgroup G} (hq : ∀ h ∈ H, q * h = h * q) :
    conjSub q H = H := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have hc := hq _ hx
    have h1 : q * (q⁻¹ * x * q) = x * q := by group
    rw [h1] at hc
    rw [mul_right_cancel hc]
    exact hx
  · intro hx
    have hc := hq x hx
    rw [show q⁻¹ * x * q = x by rw [mul_assoc, ← hc]; group]
    exact hx

theorem exists_conjSub_eq {H H' : Subgroup G} (hH : C.IsZCompl H) (hH' : C.IsZCompl H') :
    ∃ q ∈ C.B, conjSub q H = H' := by
  obtain ⟨q, hq, hqH⟩ := Config.exists_mem_B_conj hH hH'
  refine ⟨q, hq, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact hqH h hh
  · rw [card_conjSub]
    have h1 := card_mul_two_of_isZCompl hH
    have h2 := card_mul_two_of_isZCompl hH'
    omega

variable (C) in
@[expose] def IsZComplB (K : Subgroup G) : Prop :=
  K ≤ C.B ∧ S.z ∉ K ∧ ∀ b ∈ C.B, b ∈ K ∨ b * S.z ∈ K

omit [Finite G] in
theorem conj_z_eq {m : G} (hm : m ∈ S.M) : m⁻¹ * S.z * m = S.z := by
  rw [mul_assoc, ← S.z_comm hm, inv_mul_cancel_left]

omit [Finite G] in
theorem conj_mul_z_eq {m b : G} (hm : m ∈ S.M) : m⁻¹ * (b * S.z) * m = m⁻¹ * b * m * S.z := by
  rw [show m⁻¹ * (b * S.z) * m = m⁻¹ * b * m * (m⁻¹ * S.z * m) by group, conj_z_eq hm]

omit [Finite G] in
theorem conj_compl_aux {P P' H : Subgroup G} {m : G} (hm : m ∈ S.M)
    (hPP' : ∀ x ∈ P, m * x * m⁻¹ ∈ P') (hP'P : ∀ y ∈ P', m⁻¹ * y * m ∈ P) (hHP : H ≤ P)
    (hz : S.z ∉ H) (hH : ∀ a ∈ P, a ∈ H ∨ a * S.z ∈ H) :
    conjSub m H ≤ P' ∧ S.z ∉ conjSub m H ∧ ∀ b ∈ P', b ∈ conjSub m H ∨ b * S.z ∈ conjSub m H := by
  refine ⟨?_, fun h => hz ?_, fun b hb => ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact hPP' h (hHP hh)
  · rw [mem_conjSub, conj_z_eq hm] at h
    exact h
  · rcases hH _ (hP'P b hb) with h | h
    · exact Or.inl (mem_conjSub.mpr h)
    · exact Or.inr (mem_conjSub.mpr (by rw [conj_mul_z_eq hm]; exact h))

theorem outer_A_B {m : G} (hm : m ∈ S.M) (hmX : m ∉ C.X) : ∀ x ∈ C.A, m * x * m⁻¹ ∈ C.B :=
  fun _ hx => C.conj_mem_B_of_not_mem_X hm hmX hx

theorem outer_B_A {m : G} (hm : m ∈ S.M) (hmX : m ∉ C.X) : ∀ x ∈ C.B, m * x * m⁻¹ ∈ C.A :=
  fun _ hx => C.conj_mem_A_of_not_mem_X hm hmX hx

theorem inv_not_mem_X {m : G} (hmX : m ∉ C.X) : m⁻¹ ∉ C.X := fun h => hmX (by
  simpa using C.X.inv_mem h)

theorem outer_A_B' {m : G} (hm : m ∈ S.M) (hmX : m ∉ C.X) : ∀ x ∈ C.A, m⁻¹ * x * m ∈ C.B :=
  fun x hx => by simpa using outer_A_B (S.M.inv_mem hm) (inv_not_mem_X hmX) x hx

theorem outer_B_A' {m : G} (hm : m ∈ S.M) (hmX : m ∉ C.X) : ∀ x ∈ C.B, m⁻¹ * x * m ∈ C.A :=
  fun x hx => by simpa using outer_B_A (S.M.inv_mem hm) (inv_not_mem_X hmX) x hx

theorem inner_A {m : G} (hm : m ∈ C.X) : ∀ x ∈ C.A, m * x * m⁻¹ ∈ C.A :=
  fun _ hx => C.conj_mem_A hm hx

theorem inner_B {m : G} (hm : m ∈ C.X) : ∀ x ∈ C.B, m * x * m⁻¹ ∈ C.B :=
  fun _ hx => C.conj_mem_B hm hx

theorem inner_A' {m : G} (hm : m ∈ C.X) : ∀ x ∈ C.A, m⁻¹ * x * m ∈ C.A :=
  fun x hx => by simpa using inner_A (C.X.inv_mem hm) x hx

theorem inner_B' {m : G} (hm : m ∈ C.X) : ∀ x ∈ C.B, m⁻¹ * x * m ∈ C.B :=
  fun x hx => by simpa using inner_B (C.X.inv_mem hm) x hx

theorem isZComplB_conj_outer {H : Subgroup G} (hH : C.IsZCompl H) {m : G} (hm : m ∈ S.M)
    (hmX : m ∉ C.X) : IsZComplB C (conjSub m H) :=
  conj_compl_aux hm (outer_A_B hm hmX) (outer_B_A' hm hmX) hH.1 hH.2.1 hH.2.2

theorem isZCompl_conj_outer {K : Subgroup G} (hK : IsZComplB C K) {m : G} (hm : m ∈ S.M)
    (hmX : m ∉ C.X) : C.IsZCompl (conjSub m K) :=
  conj_compl_aux hm (outer_B_A hm hmX) (outer_A_B' hm hmX) hK.1 hK.2.1 hK.2.2

theorem isZCompl_conj_inner {H : Subgroup G} (hH : C.IsZCompl H) {m : G} (hm : m ∈ C.X) :
    C.IsZCompl (conjSub m H) :=
  conj_compl_aux (C.X_le_M hm) (inner_A hm) (inner_A' hm) hH.1 hH.2.1 hH.2.2

theorem isZComplB_conj_inner {K : Subgroup G} (hK : IsZComplB C K) {m : G} (hm : m ∈ C.X) :
    IsZComplB C (conjSub m K) :=
  conj_compl_aux (C.X_le_M hm) (inner_B hm) (inner_B' hm) hK.1 hK.2.1 hK.2.2

omit [Finite G] in
theorem conjSub_conjSub_inv (g : G) (H : Subgroup G) : conjSub g (conjSub g⁻¹ H) = H := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem exists_conjSub_eq_B {σ₀ : G} (hσ₀ : σ₀ ∈ S.M) (hσ₀X : σ₀ ∉ C.X) {K K' : Subgroup G}
    (hK : IsZComplB C K) (hK' : IsZComplB C K') : ∃ q ∈ C.A, conjSub q K = K' := by
  obtain ⟨q', hq', hq'H⟩ := exists_conjSub_eq
    (isZCompl_conj_outer hK (S.M.inv_mem hσ₀) (inv_not_mem_X hσ₀X))
    (isZCompl_conj_outer hK' (S.M.inv_mem hσ₀) (inv_not_mem_X hσ₀X))
  refine ⟨σ₀ * q' * σ₀⁻¹, outer_B_A hσ₀ hσ₀X q' hq', ?_⟩
  rw [conjSub_mul, conjSub_mul, hq'H, conjSub_conjSub_inv]

@[expose] def GoodIn (A₀ B₀ : Subgroup G) (m : G) : Prop := conjSub m A₀ = A₀ ∧ conjSub m B₀ = B₀

@[expose] def GoodOut (A₀ B₀ : Subgroup G) (m : G) : Prop := conjSub m A₀ = B₀ ∧ conjSub m B₀ = A₀

section Good

variable {A₀ B₀ : Subgroup G} {m m' : G}

omit [Finite G]

theorem GoodOut.mul (h : GoodOut A₀ B₀ m) (h' : GoodOut A₀ B₀ m') : GoodIn A₀ B₀ (m * m') :=
  ⟨by rw [conjSub_mul, h'.1, h.2], by rw [conjSub_mul, h'.2, h.1]⟩

theorem GoodIn.mul_out (h : GoodIn A₀ B₀ m) (h' : GoodOut A₀ B₀ m') : GoodOut A₀ B₀ (m * m') :=
  ⟨by rw [conjSub_mul, h'.1, h.2], by rw [conjSub_mul, h'.2, h.1]⟩

theorem GoodOut.mul_in (h : GoodOut A₀ B₀ m) (h' : GoodIn A₀ B₀ m') : GoodOut A₀ B₀ (m * m') :=
  ⟨by rw [conjSub_mul, h'.1, h.1], by rw [conjSub_mul, h'.2, h.2]⟩

theorem GoodOut.inv (h : GoodOut A₀ B₀ m) : GoodOut A₀ B₀ m⁻¹ :=
  ⟨by rw [← h.2, ← conjSub_mul, inv_mul_cancel, conjSub_one],
    by rw [← h.1, ← conjSub_mul, inv_mul_cancel, conjSub_one]⟩

theorem GoodIn.inv (h : GoodIn A₀ B₀ m) : GoodIn A₀ B₀ m⁻¹ :=
  ⟨by conv_lhs => rw [← h.1]
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one],
    by conv_lhs => rw [← h.2]
       rw [← conjSub_mul, inv_mul_cancel, conjSub_one]⟩

end Good

variable {A₀ B₀ : Subgroup G} (hA₀ : C.IsZCompl A₀) (hB₀ : IsZComplB C B₀) {σ₀ : G}
  (hσ₀ : σ₀ ∈ S.M) (hσ₀X : σ₀ ∉ C.X)
include hA₀ hB₀ hσ₀ hσ₀X

theorem exists_goodOut {m₀ : G} (hm₀ : m₀ ∈ S.M) (hm₀X : m₀ ∉ C.X) :
    ∃ q ∈ S.QG, GoodOut A₀ B₀ (q * m₀) := by
  obtain ⟨qB, hqB, hqBH⟩ := exists_conjSub_eq (isZCompl_conj_outer hB₀ hm₀ hm₀X) hA₀
  obtain ⟨qA, hqA, hqAK⟩ :=
    exists_conjSub_eq_B hσ₀ hσ₀X (isZComplB_conj_outer hA₀ hm₀ hm₀X) hB₀
  refine ⟨qA * qB, S.QG.mul_mem (C.A_le_QG hqA) (C.B_le_QG hqB), ?_, ?_⟩
  · rw [conjSub_mul, conjSub_mul, conjSub_eq_self (fun h hh => C.B_comm hqB
      ((isZComplB_conj_outer hA₀ hm₀ hm₀X).1 hh)), hqAK]
  · rw [conjSub_mul, conjSub_mul, hqBH, conjSub_eq_self (fun h hh => C.A_comm hqA (hA₀.1 hh))]

theorem exists_goodIn {m₀ : G} (hm₀ : m₀ ∈ C.X) : ∃ q ∈ S.QG, GoodIn A₀ B₀ (q * m₀) := by
  obtain ⟨qB, hqB, hqBH⟩ := exists_conjSub_eq (isZCompl_conj_inner hA₀ hm₀) hA₀
  obtain ⟨qA, hqA, hqAK⟩ := exists_conjSub_eq_B hσ₀ hσ₀X (isZComplB_conj_inner hB₀ hm₀) hB₀
  refine ⟨qA * qB, S.QG.mul_mem (C.A_le_QG hqA) (C.B_le_QG hqB), ?_, ?_⟩
  · rw [conjSub_mul, conjSub_mul, hqBH, conjSub_eq_self (fun h hh => C.A_comm hqA (hA₀.1 hh))]
  · rw [conjSub_mul, conjSub_mul, conjSub_eq_self (fun h hh => C.B_comm hqB
      ((isZComplB_conj_inner hB₀ hm₀).1 hh)), hqAK]

omit hσ₀ hσ₀X in
theorem eq_one_or_z_of_goodIn {q : G} (hq : q ∈ S.QG) (hg : GoodIn A₀ B₀ q) :
    q = 1 ∨ q = S.z := by
  have hcomm : ∀ {H : Subgroup G}, conjSub q H = H → S.z ∉ H → H ≤ S.QG →
      ∀ a ∈ H, q * a = a * q := fun {H} hH hz hHQ a ha => by
    have h1 : q * a * q⁻¹ ∈ H := by
      rw [← hH]; exact mem_conjSub.mpr (by simpa [mul_assoc] using ha)
    have h2 : q * a * q⁻¹ * a⁻¹ ∈ H := H.mul_mem h1 (H.inv_mem ha)
    rcases S.commutator_eq_one_or_z hq (hHQ ha) with h | h
    · calc q * a = q * a * q⁻¹ * a⁻¹ * (a * q) := by group
        _ = a * q := by rw [h, one_mul]
    · exact absurd (h ▸ h2) hz
  have hA : ∀ a ∈ A₀, q * a = a * q := hcomm hg.1 hA₀.2.1 (hA₀.1.trans C.A_le_QG)
  have hB : ∀ b ∈ B₀, q * b = b * q := hcomm hg.2 hB₀.2.1 (hB₀.1.trans C.B_le_QG)
  have hclA : S.cl q ∈ C.At := C.mem_At_of_forall_polar fun w hw => by
    obtain ⟨a, haQ, rfl⟩ := S.exists_cl w
    rcases hA₀.2.2 a ⟨haQ, hw⟩ with h | h
    · exact (S.polar_cl_eq_zero_iff haQ hq).mpr (hA a h).symm
    · rw [← S.cl_mul_z haQ]
      exact (S.polar_cl_eq_zero_iff (S.QG.mul_mem haQ S.z_mem_QG) hq).mpr (hA _ h).symm
  have hclB : S.cl q ∈ C.Bt := C.mem_Bt_of_forall_polar fun w hw => by
    obtain ⟨b, hbQ, rfl⟩ := S.exists_cl w
    rcases hB₀.2.2 b ⟨hbQ, hw⟩ with h | h
    · exact (S.polar_cl_eq_zero_iff hbQ hq).mpr (hB b h).symm
    · rw [← S.cl_mul_z hbQ]
      exact (S.polar_cl_eq_zero_iff (S.QG.mul_mem hbQ S.z_mem_QG) hq).mpr (hB _ h).symm
  exact (S.cl_eq_zero_iff hq).mp (C.eq_zero_of_mem_inf hclA hclB)

end CFSG.LargeExtraspecial.GLW4
