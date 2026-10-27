module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8a
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup DihedralGroup

variable {G : Type*} [Group G]

theorem EndB.four_ne_zero_zmod {m : ℕ} (hm : 3 ≤ m) : (4 : ZMod (2 ^ m)) ≠ 0 := by
  intro h
  have h4 : ((4 : ℕ) : ZMod (2 ^ m)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h4
  have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem EndB.dih_r_comm {n : ℕ} {i : ZMod n} (hi : i + i = 0) (y : DihedralGroup n) :
    r i * y = y * r i := by
  rcases y with j | j
  · simp only [r_mul_r, add_comm]
  · simp only [r_mul_sr, sr_mul_r, sr.injEq]
    have : -i = i := by rw [neg_eq_iff_add_eq_zero, hi]
    rw [sub_eq_add_neg, this]

theorem EndB.dih_comm_of_normal {R : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    (e : ↥R ≃* DihedralGroup (2 ^ m)) {N : Subgroup G} (hNR : N ≤ R)
    (hNn : ∀ r ∈ R, ∀ x ∈ N, r * x * r⁻¹ ∈ N) (hN2 : ∀ x ∈ N, x * x = 1) {x : G}
    (hx : x ∈ N) {y : G} (hy : y ∈ R) : y * x = x * y := by
  set x' : ↥R := ⟨x, hNR hx⟩
  set y' : ↥R := ⟨y, hy⟩
  suffices h : y' * x' = x' * y' from congrArg Subtype.val h
  apply e.injective
  rw [map_mul, map_mul]
  rcases hex : e x' with i | i
  ·
    have hxx : e x' * e x' = 1 := by
      rw [← map_mul, ← map_one e]
      congr 1
      exact Subtype.ext (hN2 x hx)
    rw [hex, r_mul_r, ← r_zero, r.injEq] at hxx
    exact (EndB.dih_r_comm hxx (e y')).symm
  ·
    exfalso
    set d : ↥R := e.symm (r 1)
    have hdN : (d : G) * x * (d : G)⁻¹ * x⁻¹ ∈ N :=
      mul_mem (hNn d d.2 x hx) (inv_mem hx)
    have h2 := hN2 _ hdN
    have he : e (d * x' * d⁻¹ * x'⁻¹) = r 2 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hex, MulEquiv.apply_symm_apply]
      simp only [r_mul_sr, sr_mul_r, inv_r, inv_sr, sr_mul_sr, r.injEq]
      ring
    have h4 : e (d * x' * d⁻¹ * x'⁻¹) * e (d * x' * d⁻¹ * x'⁻¹) = 1 := by
      rw [← map_mul, ← map_one e]
      congr 1
      exact Subtype.ext h2
    rw [he, r_mul_r, ← r_zero, r.injEq] at h4
    exact EndB.four_ne_zero_zmod hm (by rw [← h4]; norm_num)

theorem EndB.dih_comm_of_comm_sq {R : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    (e : ↥R ≃* DihedralGroup (2 ^ m)) {x : G} (hxR : x ∈ R) (hx2 : x * x = 1)
    (hxd : x * (e.symm (r 2) : G) = (e.symm (r 2) : G) * x) {y : G} (hy : y ∈ R) :
    y * x = x * y := by
  set x' : ↥R := ⟨x, hxR⟩
  set y' : ↥R := ⟨y, hy⟩
  suffices h : y' * x' = x' * y' from congrArg Subtype.val h
  apply e.injective
  rw [map_mul, map_mul]
  have hxd' : e x' * r 2 = r 2 * e x' := by
    have : x' * e.symm (r 2) = e.symm (r 2) * x' := Subtype.ext hxd
    have h1 := congrArg e this
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  rcases hex : e x' with i | i
  · have hxx : e x' * e x' = 1 := by
      rw [← map_mul, ← map_one e]
      congr 1
      exact Subtype.ext hx2
    rw [hex, r_mul_r, ← r_zero, r.injEq] at hxx
    exact (EndB.dih_r_comm hxx (e y')).symm
  · exfalso
    rw [hex, sr_mul_r, r_mul_sr, sr.injEq] at hxd'
    exact EndB.four_ne_zero_zmod hm (by
      have : (4 : ZMod (2 ^ m)) = (i + 2) - (i - 2) := by ring
      rw [this, hxd', sub_self])

theorem EndB.dih_card_center_le {R : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (e : ↥R ≃* DihedralGroup (2 ^ m)) : Nat.card ↥(R ⊓ centralizer (R : Set G)) ≤ 2 := by
  have hn2 : (2 ^ m : ℕ) ≠ 2 := by
    intro h
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have heven : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  have hZ := DihedralGroup.center_eq_closure_of_even_ne_two heven hn2
  have hcard : Nat.card (Subgroup.center (DihedralGroup (2 ^ m))) ≤ 2 := by
    rw [hZ, Nat.card_zpowers]
    apply orderOf_le_of_pow_eq_one (by norm_num)
    rw [r_pow, ← r_zero, r.injEq]
    have h1 : ((2 ^ m / 2 : ℕ) : ZMod (2 ^ m)) * ((2 : ℕ) : ZMod (2 ^ m)) =
        ((2 ^ m : ℕ) : ZMod (2 ^ m)) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (dvd_pow_self 2 (by omega))]
    rw [h1, ZMod.natCast_self]
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : ↥(R ⊓ centralizer (R : Set G)) => (⟨e ⟨x, x.2.1⟩, ?_⟩ :
      Subgroup.center (DihedralGroup (2 ^ m)))) ?_) hcard
  · rw [Subgroup.mem_center_iff]
    intro d
    obtain ⟨y, rfl⟩ := e.surjective d
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp x.2.2) y y.2)
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    have h2 := e.injective h1
    have h3 : (a : G) = b := congrArg (fun x : ↥R => (x : G)) h2
    exact Subtype.ext h3

theorem EndB.card_le_of_comm_mem [Finite G] {R Z : Subgroup G} {α : G}
    (h : ∀ r ∈ R, α * r * α⁻¹ * r⁻¹ ∈ Z) :
    Nat.card R ≤ Nat.card ↥(R ⊓ centralizer ({α} : Set G)) * Nat.card Z := by
  classical
  have hfin := Set.toFinite (Z : Set G)
  have h1 := L415.card_le_of_fiber (A := R) (K := centralizer ({α} : Set G))
    (fun r => α * r * α⁻¹ * r⁻¹) (fun a _ a' _ haa => by
      rw [mem_centralizer_singleton_iff]
      have : α * (a⁻¹ * a') * α⁻¹ = a⁻¹ * a' := by
        calc α * (a⁻¹ * a') * α⁻¹ = (α * a * α⁻¹ * a⁻¹ * a)⁻¹ * (α * a' * α⁻¹ * a'⁻¹ * a') := by
              group
          _ = a⁻¹ * a' := by rw [haa]; group
      calc a⁻¹ * a' * α = α * (a⁻¹ * a') * α⁻¹ * α := by rw [this]
        _ = α * (a⁻¹ * a') := by group) hfin.toFinset (fun a ha => by
      rw [Set.Finite.mem_toFinset]
      exact h a ha)
  rwa [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq] at h1

end CFSG.ComponentClassification.HarrisLit
