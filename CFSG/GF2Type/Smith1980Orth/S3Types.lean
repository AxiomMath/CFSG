module

public import CFSG.GF2Type.Smith1980Orth.S2Coord
public import CFSG.GF2Type.Smith1980Orth.S2Lbar
public import CFSG.GF2Type.Smith1980Orth.LocalAssembly

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private instance instFiniteDimensionalVt (g : G) (t : S.O) :
    FiniteDimensional (ZMod 2) (Vt S g t) :=
  Module.Finite.of_finite

private theorem ρ_pow_mul_eq_one_iff {x y : G} (hxM : x ∈ S.M) (hyM : y ∈ S.M) (n : ℕ) :
    (S.ρ ⟨x, hxM⟩ * S.ρ ⟨y, hyM⟩) ^ n = 1 ↔ (x * y) ^ n ∈ S.QG := by
  rw [← map_mul, ← map_pow, S.ρ_eq_one_iff]
  rfl

private theorem eq_one_of_pow_two_of_pow_three {M : Type*} [Group M] {x : M} (h2 : x ^ 2 = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

private theorem sq_eq_one_of_comm {M : Type*} [Group M] {a b : M} (haa : a * a = 1)
    (hbb : b * b = 1) (hc : a * b = b * a) : (a * b) ^ 2 = 1 := by
  rw [pow_two]
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hc]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [haa, hbb, mul_one]

private theorem mul_ne_one_of_ne {M : Type*} [Group M] {a b : M} (haa : a * a = 1) (hab : a ≠ b) :
    a * b ≠ 1 :=
  fun h => hab (mul_left_cancel (h.trans haa.symm)).symm

private theorem false_of_comm_of_pow_three {M : Type*} [Group M] {a b : M} (haa : a * a = 1)
    (hbb : b * b = 1) (hc : a * b = b * a) (hab : a ≠ b) (h3 : (a * b) ^ 3 = 1) : False :=
  mul_ne_one_of_ne haa hab (eq_one_of_pow_two_of_pow_three (sq_eq_one_of_comm haa hbb hc) h3)

private theorem eq_of_mem_of_finrank_le_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V} (hU : finrank (ZMod 2) U ≤ 1)
    {a b : V} (ha : a ∈ U) (hb : b ∈ U) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : a = b := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hU
  obtain ⟨c₁, h₁⟩ := hv ⟨a, ha⟩
  obtain ⟨c₂, h₂⟩ := hv ⟨b, hb⟩
  have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases key c₁ with rfl | rfl
  · exact absurd (by simpa using (congrArg Subtype.val h₁).symm) ha0
  rcases key c₂ with rfl | rfl
  · exact absurd (by simpa using (congrArg Subtype.val h₂).symm) hb0
  simpa using (congrArg Subtype.val h₁).symm.trans (congrArg Subtype.val h₂)

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

@[expose] def IsTInv (s : S.O) : Prop := s = D.t ∨ s = D.k * D.t ∨ s = D.k * D.k * D.t

@[expose] def IsUInv (s : S.O) : Prop := ∃ hs : s ∈ D.Cbar,
  IsTypeA D.QV (D.resC ⟨s, hs⟩) 2

@[expose] def OTypes : Prop := ∀ x : G, IsConj S.z x → ∀ hx : x ∈ S.M, x ∉ S.QG →
  D.IsTInv (S.ρ ⟨x, hx⟩) ∨ D.IsUInv (S.ρ ⟨x, hx⟩)

private theorem k_mul_kk : D.k * (D.k * D.k) = 1 :=
  (pow_three D.k).symm.trans D.k_cube

private theorem kk_mul_k : D.k * D.k * D.k = 1 :=
  (pow_three' D.k).symm.trans D.k_cube

private theorem t_mul_k_mul_t : D.t * D.k * D.t = D.k * D.k := by
  have h := D.t_inv
  rwa [D.t_inv_eq, D.k_inv] at h

private theorem t_mul_kk_mul_t : D.t * (D.k * D.k) * D.t = D.k := by
  have e : D.t * (D.k * D.k) * D.t = (D.t * D.k * D.t) * (D.t * D.k * D.t) := by
    calc D.t * (D.k * D.k) * D.t = D.t * D.k * (D.t * D.t) * D.k * D.t := by
          rw [D.t_mul_t]; group
      _ = (D.t * D.k * D.t) * (D.t * D.k * D.t) := by group
  rw [e, D.t_mul_k_mul_t]
  calc D.k * D.k * (D.k * D.k) = D.k * D.k * D.k * D.k := by group
    _ = D.k := by rw [D.kk_mul_k, one_mul]

theorem mul_self_of_isTInv {a : S.O} (ha : D.IsTInv a) : a * a = 1 := by
  rcases ha with rfl | rfl | rfl
  · exact D.t_mul_t
  · calc D.k * D.t * (D.k * D.t) = D.k * (D.t * D.k * D.t) := by group
      _ = 1 := by rw [D.t_mul_k_mul_t, D.k_mul_kk]
  · calc D.k * D.k * D.t * (D.k * D.k * D.t) = D.k * D.k * (D.t * (D.k * D.k) * D.t) := by group
      _ = 1 := by rw [D.t_mul_kk_mul_t, D.kk_mul_k]

theorem mul_eq_of_isTInv {a b : S.O} (ha : D.IsTInv a) (hb : D.IsTInv b) :
    a * b = 1 ∨ a * b = D.k ∨ a * b = D.k * D.k := by
  have haa := D.mul_self_of_isTInv ha
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact Or.inl haa
  · exact Or.inr (Or.inr ((mul_assoc D.t D.k D.t).symm.trans D.t_mul_k_mul_t))
  · exact Or.inr (Or.inl ((mul_assoc D.t (D.k * D.k) D.t).symm.trans D.t_mul_kk_mul_t))
  · exact Or.inr (Or.inl (by rw [mul_assoc, D.t_mul_t, mul_one]))
  · exact Or.inl haa
  · exact Or.inr (Or.inr (by
      calc D.k * D.t * (D.k * D.k * D.t) = D.k * (D.t * (D.k * D.k) * D.t) := by group
        _ = D.k * D.k := by rw [D.t_mul_kk_mul_t]))
  · exact Or.inr (Or.inr (by rw [mul_assoc, D.t_mul_t, mul_one]))
  · exact Or.inr (Or.inl (by
      calc D.k * D.k * D.t * (D.k * D.t) = D.k * D.k * (D.t * D.k * D.t) := by group
        _ = D.k * D.k * (D.k * D.k) := by rw [D.t_mul_k_mul_t]
        _ = D.k * D.k * D.k * D.k := by group
        _ = D.k := by rw [D.kk_mul_k, one_mul]))
  · exact Or.inl haa

theorem mul_pow_three_of_isTInv {a b : S.O} (ha : D.IsTInv a) (hb : D.IsTInv b) :
    (a * b) ^ 3 = 1 := by
  rcases D.mul_eq_of_isTInv ha hb with h | h | h <;> rw [h]
  · exact one_pow 3
  · exact D.k_cube
  · calc (D.k * D.k) ^ 3 = (D.k ^ 3) ^ 2 := by rw [← sq, ← pow_mul, ← pow_mul]
      _ = 1 := by rw [D.k_cube, one_pow]

theorem mem_sup_of_isTInv {a : S.O} (ha : D.IsTInv a) : a ∈ D.Obar ⊔ zpowers D.t := by
  have hk : D.k ∈ D.Obar ⊔ zpowers D.t := mem_sup_left D.k_mem_Obar
  have ht : D.t ∈ D.Obar ⊔ zpowers D.t := mem_sup_right (mem_zpowers D.t)
  rcases ha with rfl | rfl | rfl
  · exact ht
  · exact mul_mem hk ht
  · exact mul_mem (mul_mem hk hk) ht

theorem comm_of_isTInv_of_mem_Cbar {a c : S.O} (ha : D.IsTInv a) (hc : c ∈ D.Cbar) :
    a * c = c * a :=
  mem_centralizer_iff.mp hc.2 a (D.mem_sup_of_isTInv ha)

theorem resC_mul_pow_eq_one_iff (c d : D.Cbar) (n : ℕ) :
    (D.resC c * D.resC d) ^ n = 1 ↔
      ((c : S.O) * (d : S.O)) ^ n = 1 := by
  rw [← map_mul, ← map_pow, ← map_one D.resC,
    D.resC_injective.eq_iff]
  constructor
  · intro h
    simpa using congrArg Subtype.val h
  · intro h
    exact Subtype.ext (by simpa using h)

theorem mul_self_of_isUInv {a : S.O} (ha : D.IsUInv a) : a * a = 1 := by
  obtain ⟨hs, hA⟩ := ha
  simpa using (D.resC_mul_pow_eq_one_iff ⟨a, hs⟩ ⟨a, hs⟩ 1).mp (by rw [pow_one]; exact hA.2.2.1)

theorem mul_self_of_types {a : S.O} (ha : D.IsTInv a ∨ D.IsUInv a) : a * a = 1 :=
  ha.elim D.mul_self_of_isTInv D.mul_self_of_isUInv

theorem mem_commSpace_t_iff_coord {x : S.Qt} :
    x ∈ commSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔ ∃ u : Vt S D.g D.t, x = D.coord (u, 0) := by
  rw [D.commSpace_eq]
  exact D.mem_Vt_iff_coord

theorem mem_commSpace_kt_iff_coord {x : S.Qt} :
    x ∈ commSpace ((D.k * D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔
      ∃ u : Vt S D.g D.t, x = D.coord (u, u) := by
  rw [mem_commSpace]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := D.coord.surjective w
    refine ⟨a + b, ?_⟩
    rw [coe_mul_apply, D.t_apply_coord, D.k_apply_coord, ← map_sub D.coord]
    refine congrArg D.coord (Prod.ext ?_ ?_)
    · show b - a = a + b
      rw [sub_eq_add_vec (ZMod 2), add_comm]
    · show a + b + b - b = a + b
      abel
  · rintro ⟨u, rfl⟩
    refine ⟨D.coord (u, 0), ?_⟩
    rw [coe_mul_apply, D.t_apply_coord, D.k_apply_coord, ← map_sub D.coord]
    refine congrArg D.coord (Prod.ext ?_ ?_)
    · show 0 - u = u
      rw [sub_eq_add_vec (ZMod 2), zero_add]
    · show u + 0 + 0 - 0 = u
      simp

theorem mem_commSpace_kkt_iff_coord {x : S.Qt} :
    x ∈ commSpace ((D.k * D.k * D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔
      ∃ u : Vt S D.g D.t, x = D.coord (0, u) := by
  rw [mem_commSpace]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := D.coord.surjective w
    refine ⟨a, ?_⟩
    rw [coe_mul_apply, coe_mul_apply, D.t_apply_coord, D.k_apply_coord, D.k_apply_coord,
      ← map_sub D.coord]
    refine congrArg D.coord (Prod.ext ?_ ?_)
    · show a + b + b - a = 0
      calc a + b + b - a = b + b := by abel
        _ = 0 := OrthoF2.vec_add_self b
    · show b + (a + b + b) - b = a
      calc b + (a + b + b) - b = a + (b + b) := by abel
        _ = a := by rw [OrthoF2.vec_add_self, add_zero]
  · rintro ⟨u, rfl⟩
    refine ⟨D.coord (u, 0), ?_⟩
    rw [coe_mul_apply, coe_mul_apply, D.t_apply_coord, D.k_apply_coord, D.k_apply_coord,
      ← map_sub D.coord]
    refine congrArg D.coord (Prod.ext ?_ ?_)
    · show u + 0 + 0 - u = 0
      simp
    · show 0 + (u + 0 + 0) - 0 = u
      simp

theorem commSpace_kt_eq : commSpace ((D.k * D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = D.Wkt := by
  ext x
  rw [D.mem_commSpace_kt_iff_coord, D.mem_Wkt_iff_coord]

theorem commSpace_kkt_eq : commSpace ((D.k * D.k * D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = D.Wk := by
  ext x
  rw [D.mem_commSpace_kkt_iff_coord, D.mem_Wk_iff_coord]

theorem coord_mem_commSpace_t_iff (u w : Vt S D.g D.t) :
    D.coord (u, w) ∈ commSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔ w = 0 := by
  rw [D.mem_commSpace_t_iff_coord]
  constructor
  · rintro ⟨u', h⟩
    exact (Prod.mk.inj (D.coord.injective h)).2
  · rintro rfl
    exact ⟨u, rfl⟩

theorem coord_mem_commSpace_kt_iff (u w : Vt S D.g D.t) :
    D.coord (u, w) ∈ commSpace ((D.k * D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔ u = w := by
  rw [D.mem_commSpace_kt_iff_coord]
  constructor
  · rintro ⟨u', h⟩
    have h' := Prod.mk.inj (D.coord.injective h)
    exact h'.1.trans h'.2.symm
  · rintro rfl
    exact ⟨u, rfl⟩

theorem coord_mem_commSpace_kkt_iff (u w : Vt S D.g D.t) :
    D.coord (u, w) ∈ commSpace ((D.k * D.k * D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔ u = 0 := by
  rw [D.mem_commSpace_kkt_iff_coord]
  constructor
  · rintro ⟨u', h⟩
    exact (Prod.mk.inj (D.coord.injective h)).1
  · rintro rfl
    exact ⟨w, rfl⟩

theorem mem_commSpace_Cbar_iff_coord (c : D.Cbar) {x : S.Qt} :
    x ∈ commSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔ ∃ u v : Vt S D.g D.t,
      u ∈ commSpace (D.resC c) ∧
        v ∈ commSpace (D.resC c) ∧ x = D.coord (u, v) := by
  rw [mem_commSpace]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := D.coord.surjective w
    refine ⟨D.resC c a - a, D.resC c b - b,
      sub_mem_commSpace _ _, sub_mem_commSpace _ _, ?_⟩
    rw [D.Cbar_apply_coord, ← map_sub D.coord]
    rfl
  · rintro ⟨u, v, hu, hv, rfl⟩
    obtain ⟨a, rfl⟩ := mem_commSpace.mp hu
    obtain ⟨b, rfl⟩ := mem_commSpace.mp hv
    refine ⟨D.coord (a, b), ?_⟩
    rw [D.Cbar_apply_coord, ← map_sub D.coord]
    rfl

theorem mem_commSpace_iff_coord_of_mem_Cbar {c : S.O} (hc : c ∈ D.Cbar) {x : S.Qt} :
    x ∈ commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔ ∃ u v : Vt S D.g D.t,
      u ∈ commSpace (D.resC ⟨c, hc⟩) ∧
        v ∈ commSpace (D.resC ⟨c, hc⟩) ∧ x = D.coord (u, v) :=
  D.mem_commSpace_Cbar_iff_coord ⟨c, hc⟩

theorem coord_mem_commSpace_Cbar_iff (c : D.Cbar) (u w : Vt S D.g D.t) :
    D.coord (u, w) ∈ commSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔
      u ∈ commSpace (D.resC c) ∧
        w ∈ commSpace (D.resC c) := by
  rw [D.mem_commSpace_Cbar_iff_coord]
  constructor
  · rintro ⟨u', w', hu, hw, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.coord.injective h)
    exact ⟨hu, hw⟩
  · rintro ⟨hu, hw⟩
    exact ⟨u, w, hu, hw, rfl⟩

private def Sing2 (u w : Vt S D.g D.t) : Prop :=
  D.QV u = 0 ∧ D.QV w = 0 ∧ (u ≠ 0 → w ≠ 0 → u = w)

private theorem sing2_of_mem {P : Submodule (ZMod 2) (Vt S D.g D.t)}
    (hP : ∀ x ∈ P, D.QV x = 0) {u w : Vt S D.g D.t} (hu : u ∈ P) (hw : w ∈ P)
    (h : w = 0 ∨ u = w ∨ u = 0) : D.Sing2 u w := by
  refine ⟨hP u hu, hP w hw, fun hu0 hw0 => ?_⟩
  rcases h with h | h | h
  · exact absurd h hw0
  · exact h
  · exact absurd h hu0

private theorem isConj_of_sing2 {u w : Vt S D.g D.t} (h : D.Sing2 u w) :
    ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ S.cl c = D.coord (u, w) := by
  by_cases h0 : D.coord (u, w) = 0
  · exact ⟨S.z, IsConj.refl _, S.z_mem_QG, by rw [S.cl_z, h0]⟩
  obtain ⟨c, hcQ, hc⟩ := S.exists_cl (D.coord (u, w))
  have hcz : c ≠ S.z := by
    rintro rfl
    exact h0 (hc.symm.trans S.cl_z)
  refine ⟨c, (D.isConj_z_iff_coord hcQ hcz).mpr ?_, hcQ, hc⟩
  obtain ⟨hu, hw, huw⟩ := h
  by_cases hu0 : u = 0
  · subst hu0
    have hw0 : w ≠ 0 := fun hw0 => h0 (by rw [hw0]; simp)
    exact ⟨w, hw0, hw, Or.inr (Or.inl hc)⟩
  by_cases hw0 : w = 0
  · subst hw0
    exact ⟨u, hu0, hu, Or.inl hc⟩
  · exact ⟨u, hu0, hu, Or.inr (Or.inr (by rw [hc, huw hu0 hw0]))⟩

theorem coord_cases_of_isTInv {a : S.O} (ha : D.IsTInv a) {u w : Vt S D.g D.t}
    (h : D.coord (u, w) ∈ commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt)) : w = 0 ∨ u = w ∨ u = 0 := by
  rcases ha with rfl | rfl | rfl
  · exact Or.inl ((D.coord_mem_commSpace_t_iff u w).mp h)
  · exact Or.inr (Or.inl ((D.coord_mem_commSpace_kt_iff u w).mp h))
  · exact Or.inr (Or.inr ((D.coord_mem_commSpace_kkt_iff u w).mp h))

theorem eq_zero_of_isTInv_of_ne {a b : S.O} (ha : D.IsTInv a) (hb : D.IsTInv b) (hab : a ≠ b)
    {u w : Vt S D.g D.t} (h1 : D.coord (u, w) ∈ commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (h2 : D.coord (u, w) ∈ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt)) : u = 0 ∧ w = 0 := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · rw [D.coord_mem_commSpace_t_iff] at h1
    rw [D.coord_mem_commSpace_kt_iff] at h2
    exact ⟨h2.trans h1, h1⟩
  · rw [D.coord_mem_commSpace_t_iff] at h1
    rw [D.coord_mem_commSpace_kkt_iff] at h2
    exact ⟨h2, h1⟩
  · rw [D.coord_mem_commSpace_kt_iff] at h1
    rw [D.coord_mem_commSpace_t_iff] at h2
    exact ⟨h1.trans h2, h2⟩
  · exact absurd rfl hab
  · rw [D.coord_mem_commSpace_kt_iff] at h1
    rw [D.coord_mem_commSpace_kkt_iff] at h2
    exact ⟨h2, h1.symm.trans h2⟩
  · rw [D.coord_mem_commSpace_kkt_iff] at h1
    rw [D.coord_mem_commSpace_t_iff] at h2
    exact ⟨h1, h2⟩
  · rw [D.coord_mem_commSpace_kkt_iff] at h1
    rw [D.coord_mem_commSpace_kt_iff] at h2
    exact ⟨h1, h2.symm.trans h1⟩
  · exact absurd rfl hab

private theorem finrank_inf_le_one (c d : D.Cbar)
    (hc : IsTypeA D.QV (D.resC c) 2)
    (hd : IsTypeA D.QV (D.resC d) 2) (hcd : c ≠ d) :
    finrank (ZMod 2) ↥(commSpace (D.resC c) ⊓
      commSpace (D.resC d)) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hne : commSpace (D.resC c) ≠
      commSpace (D.resC d) := fun h =>
    hcd (D.resC_injective (OrthoF2.eq_of_commSpace_eq D.QV_nondegenerate hc hd h))
  have h1 := Submodule.finrank_mono (inf_le_left : commSpace (D.resC c) ⊓
    commSpace (D.resC d) ≤ commSpace (D.resC c))
  have h2 := Submodule.finrank_mono (inf_le_right : commSpace (D.resC c) ⊓
    commSpace (D.resC d) ≤ commSpace (D.resC d))
  rw [hc.2.2.2.1] at h1
  rw [hd.2.2.2.1] at h2
  have e1 := Submodule.eq_of_le_of_finrank_eq
    (inf_le_left : commSpace (D.resC c) ⊓ commSpace (D.resC d) ≤ _) (by rw [hc.2.2.2.1]; omega)
  have e2 := Submodule.eq_of_le_of_finrank_eq
    (inf_le_right : commSpace (D.resC c) ⊓ commSpace (D.resC d) ≤ _) (by rw [hd.2.2.2.1]; omega)
  exact hne (e1.symm.trans e2)

private theorem inf_eq_bot_of_pow_three (c d : D.Cbar)
    (hc : IsTypeA D.QV (D.resC c) 2)
    (hd : IsTypeA D.QV (D.resC d) 2)
    (h3 : ((c : S.O) * (d : S.O)) ^ 3 = 1) (h1 : (c : S.O) * (d : S.O) ≠ 1) :
    commSpace (D.resC c) ⊓ commSpace (D.resC d) =
      ⊥ := by
  have hord : orderOf (D.resC c * D.resC d) = 3 := by
    refine orderOf_eq_prime ((D.resC_mul_pow_eq_one_iff c d 3).mpr h3) fun h => h1 ?_
    simpa using (D.resC_mul_pow_eq_one_iff c d 1).mp (by rw [pow_one]; exact h)
  exact (commSpace_mul_of_orderOf_eq_three D.QV_nondegenerate hc hd hord).1

private theorem uu_pow_cases (c d : D.Cbar)
    (hc : IsTypeA D.QV (D.resC c) 2)
    (hd : IsTypeA D.QV (D.resC d) 2) :
    ((c : S.O) * (d : S.O)) ^ 1 = 1 ∨ ((c : S.O) * (d : S.O)) ^ 2 = 1 ∨
      ((c : S.O) * (d : S.O)) ^ 3 = 1 ∨ ((c : S.O) * (d : S.O)) ^ 4 = 1 := by
  obtain ⟨hmem, -⟩ := aschbacher_3_7 D.QV_nondegenerate hc hd
  have hpow := pow_orderOf_eq_one (D.resC c * D.resC d)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h <;> rw [h] at hpow
  · exact Or.inl ((D.resC_mul_pow_eq_one_iff c d 1).mp hpow)
  · exact Or.inr (Or.inl ((D.resC_mul_pow_eq_one_iff c d 2).mp hpow))
  · exact Or.inr (Or.inr (Or.inl ((D.resC_mul_pow_eq_one_iff c d 3).mp hpow)))
  · exact Or.inr (Or.inr (Or.inr ((D.resC_mul_pow_eq_one_iff c d 4).mp hpow)))

theorem pow_eq_one_cases_of_types {a b : S.O} (ha : D.IsTInv a ∨ D.IsUInv a)
    (hb : D.IsTInv b ∨ D.IsUInv b) :
    (a * b) ^ 1 = 1 ∨ (a * b) ^ 2 = 1 ∨ (a * b) ^ 3 = 1 ∨ (a * b) ^ 4 = 1 := by
  have haa := D.mul_self_of_types ha
  have hbb := D.mul_self_of_types hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Or.inr (Or.inr (Or.inl (D.mul_pow_three_of_isTInv ha hb)))
  · obtain ⟨hs, -⟩ := hb
    exact Or.inr (Or.inl (sq_eq_one_of_comm haa hbb (D.comm_of_isTInv_of_mem_Cbar ha hs)))
  · obtain ⟨hs, -⟩ := ha
    exact Or.inr (Or.inl (sq_eq_one_of_comm haa hbb (D.comm_of_isTInv_of_mem_Cbar hb hs).symm))
  · obtain ⟨hsa, hα⟩ := ha
    obtain ⟨hsb, hβ⟩ := hb
    exact D.uu_pow_cases ⟨a, hsa⟩ ⟨b, hsb⟩ hα hβ

private theorem sing2_and_zero_of_mem {a b : S.O} (ha : D.IsTInv a ∨ D.IsUInv a)
    (hb : D.IsTInv b ∨ D.IsUInv b) (hab : a ≠ b) {u w : Vt S D.g D.t}
    (h1 : D.coord (u, w) ∈ commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (h2 : D.coord (u, w) ∈ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    D.Sing2 u w ∧ ((a * b) ^ 3 = 1 → u = 0 ∧ w = 0) := by
  have haa := D.mul_self_of_types ha
  have hbb := D.mul_self_of_types hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  ·
    have h0 := D.eq_zero_of_isTInv_of_ne ha hb hab h1 h2
    refine ⟨⟨?_, ?_, fun hu => absurd h0.1 hu⟩, fun _ => h0⟩
    · rw [h0.1, map_zero]
    · rw [h0.2, map_zero]
  ·
    obtain ⟨hs, hβ⟩ := hb
    obtain ⟨hu, hw⟩ := (D.coord_mem_commSpace_Cbar_iff ⟨b, hs⟩ u w).mp h2
    exact ⟨D.sing2_of_mem hβ.2.2.2.2 hu hw (D.coord_cases_of_isTInv ha h1), fun h3 =>
      (false_of_comm_of_pow_three haa hbb (D.comm_of_isTInv_of_mem_Cbar ha hs) hab h3).elim⟩
  ·
    obtain ⟨hs, hα⟩ := ha
    obtain ⟨hu, hw⟩ := (D.coord_mem_commSpace_Cbar_iff ⟨a, hs⟩ u w).mp h1
    exact ⟨D.sing2_of_mem hα.2.2.2.2 hu hw (D.coord_cases_of_isTInv hb h2), fun h3 =>
      (false_of_comm_of_pow_three haa hbb (D.comm_of_isTInv_of_mem_Cbar hb hs).symm hab
        h3).elim⟩
  ·
    obtain ⟨hsa, hα⟩ := ha
    obtain ⟨hsb, hβ⟩ := hb
    obtain ⟨hu1, hw1⟩ := (D.coord_mem_commSpace_Cbar_iff ⟨a, hsa⟩ u w).mp h1
    obtain ⟨hu2, hw2⟩ := (D.coord_mem_commSpace_Cbar_iff ⟨b, hsb⟩ u w).mp h2
    have hcd : (⟨a, hsa⟩ : D.Cbar) ≠ ⟨b, hsb⟩ := fun h => hab (congrArg Subtype.val h)
    refine ⟨⟨hα.2.2.2.2 u hu1, hα.2.2.2.2 w hw1, fun hu0 hw0 => ?_⟩, fun h3 => ?_⟩
    · exact eq_of_mem_of_finrank_le_one (D.finrank_inf_le_one ⟨a, hsa⟩ ⟨b, hsb⟩ hα hβ hcd)
        (Submodule.mem_inf.mpr ⟨hu1, hu2⟩) (Submodule.mem_inf.mpr ⟨hw1, hw2⟩) hu0 hw0
    · have hbot := D.inf_eq_bot_of_pow_three ⟨a, hsa⟩ ⟨b, hsb⟩ hα hβ h3
        (mul_ne_one_of_ne haa hab)
      refine ⟨?_, ?_⟩
      · have hu : u ∈ commSpace (D.resC ⟨a, hsa⟩) ⊓
            commSpace (D.resC ⟨b, hsb⟩) := Submodule.mem_inf.mpr ⟨hu1, hu2⟩
        rw [hbot] at hu
        exact (Submodule.mem_bot _).mp hu
      · have hw : w ∈ commSpace (D.resC ⟨a, hsa⟩) ⊓
            commSpace (D.resC ⟨b, hsb⟩) := Submodule.mem_inf.mpr ⟨hw1, hw2⟩
        rw [hbot] at hw
        exact (Submodule.mem_bot _).mp hw

theorem exists_isConj_of_mem_inf {a b : S.O} (ha : D.IsTInv a ∨ D.IsUInv a)
    (hb : D.IsTInv b ∨ D.IsUInv b) (hab : a ≠ b) {v : S.Qt}
    (hv : v ∈ commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ S.cl c = v := by
  obtain ⟨⟨u, w⟩, rfl⟩ := D.coord.surjective v
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hv
  exact D.isConj_of_sing2 (D.sing2_and_zero_of_mem ha hb hab h1 h2).1

theorem inf_eq_bot_of_pow_three_of_types {a b : S.O} (ha : D.IsTInv a ∨ D.IsUInv a)
    (hb : D.IsTInv b ∨ D.IsUInv b) (hab : a ≠ b) (h3 : (a * b) ^ 3 = 1) :
    commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨⟨u, w⟩, rfl⟩ := D.coord.surjective v
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hv
  obtain ⟨rfl, rfl⟩ := (D.sing2_and_zero_of_mem ha hb hab h1 h2).2 h3
  simp

theorem oe23_of_types (h : D.OTypes) : OE23 S := by
  intro x y hx hy hxM hyM hxQ hyQ
  rcases D.pow_eq_one_cases_of_types (h x hx hxM hxQ) (h y hy hyM hyQ) with h1 | h2 | h3 | h4
  · exact Or.inl (by simpa using (ρ_pow_mul_eq_one_iff hxM hyM 1).mp h1)
  · exact Or.inr (Or.inl ((ρ_pow_mul_eq_one_iff hxM hyM 2).mp h2))
  · exact Or.inr (Or.inr (Or.inl ((ρ_pow_mul_eq_one_iff hxM hyM 3).mp h3)))
  · exact Or.inr (Or.inr (Or.inr ((ρ_pow_mul_eq_one_iff hxM hyM 4).mp h4)))

theorem oe25_of_types (h : D.OTypes) : OE25 S := by
  intro x y hx hy hxM hyM hxQ hyQ hxyQ
  have ha := h x hx hxM hxQ
  have hb := h y hy hyM hyQ
  have hab1 : S.ρ ⟨x, hxM⟩ * S.ρ ⟨y, hyM⟩ ≠ 1 := fun h1 =>
    hxyQ (by simpa using (ρ_pow_mul_eq_one_iff hxM hyM 1).mp (by rw [pow_one]; exact h1))
  have hne : S.ρ ⟨x, hxM⟩ ≠ S.ρ ⟨y, hyM⟩ := fun h1 =>
    hab1 (by rw [← h1]; exact D.mul_self_of_types ha)
  refine ⟨fun _ v hv => ?_, fun h3 => ?_⟩
  · rw [S.commQt_of_mem hxM, S.commQt_of_mem hyM] at hv
    exact D.exists_isConj_of_mem_inf ha hb hne hv
  · rw [S.commQt_of_mem hxM, S.commQt_of_mem hyM]
    exact D.inf_eq_bot_of_pow_three_of_types ha hb hne ((ρ_pow_mul_eq_one_iff hxM hyM 3).mpr h3)

end S2Data

end CFSG.GF2Type.Smith1980Orth
