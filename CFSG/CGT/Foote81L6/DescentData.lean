module

public import CFSG.CGT.Foote81L6.DescentCore

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

theorem orderOf_mul_eq_two_of_comm {G : Type*} [Group G] {u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v = v * u) (hne : u * v ≠ 1) : orderOf (u * v) = 2 := by
  refine orderOf_eq_prime ?_ hne
  rw [sq]
  calc u * v * (u * v) = u * (v * u) * v := by group
    _ = u * (u * v) * v := by rw [huv]
    _ = (u * u) * (v * v) := by group
    _ = 1 := by rw [hu, hv, one_mul]

theorem orderOf_ne_four_of_mul_self_eq_one {G : Type*} [Group G] {g : G} (h : g * g = 1) :
    orderOf g ≠ 4 := by
  intro h4
  have := orderOf_dvd_of_pow_eq_one (show g ^ 2 = 1 by rw [sq]; exact h)
  rw [h4] at this
  norm_num at this

namespace FooteCore

variable {G : Type*} [Group G] [Finite G] {T : Subgroup G} {k n : ℕ}
  (D : FooteCore G T (k + 3) n) {O : Subgroup G} [O.Normal]
  (hO : Odd (Nat.card O)) [(D.descM O).Normal]

local notation "ρ" => QuotientGroup.mk' (D.descM O)

theorem exists_conj_mul_a_of_involution {y : G} (hy : y ∈ D.A) (hy2 : orderOf y = 2)
    (hya : y ≠ D.a) : ∃ u ∈ D.A, u * y * u⁻¹ = y * D.a := by
  have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  rcases h : D.eA ⟨y, hy⟩ with i | i
  · exfalso
    have hrr : (r i : DihedralGroup (2 ^ (k + 2))) * r i = 1 := by
      rw [← h, ← map_mul, ← map_one D.eA]
      congr 1
      exact Subtype.ext hyy
    rcases r_mul_self_eq_one_iff.1 hrr with h1 | h1
    · have : (⟨y, hy⟩ : ↥D.A) = 1 := D.eA.injective (by rw [h, h1, map_one])
      have := congrArg Subtype.val this
      rw [show ((⟨y, hy⟩ : ↥D.A) : G) = y from rfl, OneMemClass.coe_one] at this
      rw [this, orderOf_one] at hy2
      omega
    · apply hya
      have : (⟨y, hy⟩ : ↥D.A) = ⟨D.a, D.a_mem⟩ := D.eA.injective (by rw [h, h1, D.eA_a])
      exact congrArg Subtype.val this
  · obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_sr_mul_zc (k := k) i)
    refine ⟨D.eA.symm c, (D.eA.symm c).2, ?_⟩
    have : D.eA.symm c * ⟨y, hy⟩ * (D.eA.symm c)⁻¹ = ⟨y, hy⟩ * ⟨D.a, D.a_mem⟩ := by
      apply D.eA.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h, hc, map_mul, h, D.eA_a]
    exact congrArg Subtype.val this

include hO in
theorem exists_lift_involution {xb : G ⧸ D.descM O} (hx : xb ∈ D.A.map ρ) (hx2 : orderOf xb = 2)
    (hxa : xb ≠ ρ D.a₀) : ∃ x ∈ D.A, ρ x = xb ∧ orderOf x = 2 ∧ x ≠ D.a := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hyy : y * y ∈ zpowers D.a := by
    rw [← D.T_inf_descM hO]
    refine mem_inf.2 ⟨mul_mem (D.A_le_T hy) (D.A_le_T hy), ?_⟩
    have : ρ (y * y) = 1 := by rw [map_mul, ← sq, ← hx2]; exact pow_orderOf_eq_one _
    exact (QuotientGroup.eq_one_iff _).1 this
  rcases h : D.eA ⟨y, hy⟩ with i | i
  · exfalso
    rcases D.mem_zpowers_a_iff.1 hyy with h1 | h1
    · have hrr : (r i : DihedralGroup (2 ^ (k + 2))) * r i = 1 := by
        rw [← h, ← map_mul, ← map_one D.eA]
        congr 1
        exact Subtype.ext h1
      rcases r_mul_self_eq_one_iff.1 hrr with h2 | h2
      · have : (⟨y, hy⟩ : ↥D.A) = 1 := D.eA.injective (by rw [h, h2, map_one])
        have hy1 : y = 1 := congrArg Subtype.val this
        rw [hy1, map_one, orderOf_one] at hx2
        omega
      · have : (⟨y, hy⟩ : ↥D.A) = ⟨D.a, D.a_mem⟩ := D.eA.injective (by rw [h, h2, D.eA_a])
        have hya : y = D.a := congrArg Subtype.val this
        have : ρ y = 1 := by
          rw [hya, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact mem_sup_right (mem_zpowers _)
        rw [this, orderOf_one] at hx2
        omega
    · have hrr : (r i : DihedralGroup (2 ^ (k + 2))) * r i = zc (k + 2) := by
        rw [← h, ← map_mul, ← D.eA_a]
        congr 1
        exact Subtype.ext h1
      apply hxa
      have hρa : ρ D.a = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact mem_sup_right (mem_zpowers _)
      rcases r_mul_self_eq_zc_iff.1 hrr with h2 | h2
      · have : (⟨y, hy⟩ : ↥D.A) = D.eA.symm (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) := by
          rw [MulEquiv.eq_symm_apply, h, h2]
        have hy' : y = D.a₀ := by rw [D.a₀_eq]; exact congrArg Subtype.val this
        rw [hy']
      · have : (⟨y, hy⟩ : ↥D.A) = D.eA.symm (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) *
            ⟨D.a, D.a_mem⟩ := by
          apply D.eA.injective
          rw [map_mul, MulEquiv.apply_symm_apply, h, h2, D.eA_a, zc_eq_r, r_mul_r]
        have hy' : y = D.a₀ * D.a := by rw [D.a₀_eq]; exact congrArg Subtype.val this
        rw [hy', map_mul, hρa, mul_one]
  · refine ⟨y, hy, rfl, ?_, ?_⟩
    · rw [show orderOf y = orderOf (D.eA ⟨y, hy⟩) by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk], h, orderOf_sr]
    · intro hya
      have : D.eA ⟨y, hy⟩ = D.eA ⟨D.a, D.a_mem⟩ := by congr 1; exact Subtype.ext hya
      rw [h, D.eA_a, zc_eq_r] at this
      cases this

include hO in
theorem orderOf_mk_of_mem_B {x : G} (hx : x ∈ D.B) : orderOf (ρ x) = orderOf x := by
  have hinj : Function.Injective ((ρ).comp D.B.subtype) := by
    intro u v h
    exact Subtype.ext (D.mem_B_of_mk_eq hO u.2 v.2 h)
  have := orderOf_injective ((ρ).comp D.B.subtype) hinj ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at this
  exact this

theorem orderOf_mul_of_A_B {x r : G} (hx : x ∈ D.A) (hx2 : orderOf x = 2) (hr : r ∈ D.B)
    (hr2 : orderOf r = 2) : orderOf (x * r) = 2 ∧ orderOf (x * r * D.a) = 2 := by
  have hxx : x * x = 1 := by rw [← sq, ← hx2]; exact pow_orderOf_eq_one x
  have hrr : r * r = 1 := by rw [← sq, ← hr2]; exact pow_orderOf_eq_one r
  have hxr : x * r = r * x := D.A_comm_B x hx r hr
  have hne : x * r ≠ 1 := by
    intro h
    have hxB : x ∈ D.B := by
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_mem hr
    have : x ∈ D.A ⊓ D.B := mem_inf.2 ⟨hx, hxB⟩
    rw [D.A_inf_B, mem_bot] at this
    rw [this, orderOf_one] at hx2
    omega
  have h1 := orderOf_mul_eq_two_of_comm hxx hrr hxr hne
  refine ⟨h1, orderOf_mul_eq_two_of_comm ?_ D.a_mul_a ?_ ?_⟩
  · rw [← sq, ← h1]; exact pow_orderOf_eq_one _
  · exact D.a_comm_T (mul_mem (D.A_le_T hx) (D.B_le_T hr))
  · intro h
    have hr' : r = x⁻¹ * D.a⁻¹ := by
      calc r = x⁻¹ * (x * r * D.a) * D.a⁻¹ := by group
        _ = x⁻¹ * D.a⁻¹ := by rw [h, mul_one]
    have : r ∈ D.A ⊓ D.B := mem_inf.2 ⟨hr' ▸ mul_mem (inv_mem hx) (inv_mem D.a_mem), hr⟩
    rw [D.A_inf_B, mem_bot] at this
    rw [this, orderOf_one] at hr2
    omega

end FooteCore

namespace FooteData

variable {G : Type*} [Group G] [Finite G] {T : Subgroup G} {k n : ℕ}
  (D : FooteData G T (k + 3) n) {O : Subgroup G} [O.Normal]
  (hO : Odd (Nat.card O)) [(D.descM O).Normal]
  (haO : ∀ g : G, g * D.a * g⁻¹ * D.a⁻¹ ∈ O)

local notation "ρ" => QuotientGroup.mk' (D.descM O)

include hO haO in
theorem lift_isConj {x y : G} (hx : x ∈ T) (hy : y ∈ T) (h : IsConj (ρ x) (ρ y)) :
    IsConj x y ∨ IsConj x (y * D.a) := by
  have h2 : ∀ {u : G}, u ∈ T → ∃ k : ℕ, u ^ (2 ^ k) = 1 := by
    intro u hu
    obtain ⟨j, hj⟩ := D.isPGroup_T ⟨u, hu⟩
    exact ⟨j, congrArg Subtype.val hj⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
  exact isConj_or_isConj_mul_of_isConj_mk_sup (M := D.descM O) hO D.a_mul_a haO rfl (h2 hx)
    (h2 hy) (D.a_comm_T hy) h

include hO haO in
theorem descent_fusion (hB₀t : ∀ x ∈ D.B₀, ∀ y ∈ D.B₀, x * (D.t * y * D.t⁻¹) = (D.t * y * D.t⁻¹) * x) :
    (∀ x ∈ (D.toFooteCore.descent hO).A, orderOf x = 2 → x ≠ (D.toFooteCore.descent hO).a →
      ∀ r ∈ (D.toFooteCore.descent hO).B₀, orderOf r = 2 →
        ¬ IsConj (D.toFooteCore.descent hO).a (x * r)) ∧
    (∀ r ∈ (D.toFooteCore.descent hO).B₀, orderOf r = 2 →
      ¬ IsConj (D.toFooteCore.descent hO).a (r * (D.toFooteCore.descent hO).b₁)) ∧
    (∀ x ∈ (D.toFooteCore.descent hO).A, orderOf x = 2 → x ≠ (D.toFooteCore.descent hO).a →
      ∀ y ∈ (D.toFooteCore.descent hO).A, orderOf y = 2 → y ≠ (D.toFooteCore.descent hO).a →
      ∀ r ∈ (D.toFooteCore.descent hO).B₀, orderOf r = 2 → ¬ IsConj (x * r) y) ∧
    (∀ x ∈ (D.toFooteCore.descent hO).A, orderOf x = 2 → x ≠ (D.toFooteCore.descent hO).a →
      ∀ r ∈ (D.toFooteCore.descent hO).B₀, orderOf r = 2 →
        ¬ IsConj (x * r * (D.toFooteCore.descent hO).b₁) (x * (D.toFooteCore.descent hO).b₀)) ∧
    (∀ r ∈ (D.toFooteCore.descent hO).B₀, orderOf r = 2 →
      ¬ IsConj (D.toFooteCore.descent hO).a
        (r * ((D.toFooteCore.descent hO).t * r * (D.toFooteCore.descent hO).t⁻¹))) := by
  have hB₀B : ∀ {r : G}, r ∈ D.B₀ → r ∈ D.B := fun hr => D.B₀_le_B hr
  have ha₀T : D.a₀ ∈ T := D.A_le_T D.a₀_mem
  have hord4 := D.orderOf_a₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ hx hx2 hxa _ ⟨r, hr, rfl⟩ hr2 hc
    obtain ⟨x, hxA, rfl, hx2', hxa'⟩ := D.toFooteCore.exists_lift_involution hO hx hx2 hxa
    rw [D.orderOf_mk_of_mem_B hO (hB₀B hr)] at hr2
    rw [← map_mul] at hc
    have hxrT : x * r ∈ T := mul_mem (D.A_le_T hxA) (D.B_le_T (hB₀B hr))
    obtain ⟨h1, h2⟩ := D.orderOf_mul_of_A_B hxA hx2' (hB₀B hr) hr2
    rcases D.lift_isConj hO haO ha₀T hxrT hc with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [← SemiconjBy.orderOf_eq _ hc, hord4] at h1; omega
    · rw [← SemiconjBy.orderOf_eq _ hc, hord4] at h2; omega
  · rintro _ ⟨r, hr, rfl⟩ hr2 hc
    rw [D.orderOf_mk_of_mem_B hO (hB₀B hr)] at hr2
    change IsConj (ρ D.a₀) (ρ r * ρ D.b₁) at hc
    rw [← map_mul] at hc
    have hrb : r * D.b₁ ∈ D.B := mul_mem (hB₀B hr) D.b₁_mem_B
    have hrr : r * r = 1 := by rw [← sq, ← hr2]; exact pow_orderOf_eq_one r
    have hne : r * D.b₁ ≠ 1 := by
      intro h
      have : r ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨hr, by
        rw [eq_inv_of_mul_eq_one_left h]; exact inv_mem D.b₁_mem⟩
      rw [D.B₀_inf_B₁, mem_bot] at this
      rw [this, orderOf_one] at hr2
      omega
    have h1 := orderOf_mul_eq_two_of_comm hrr D.b₁_mul_b₁ (D.B₀_comm_B₁ r hr D.b₁ D.b₁_mem) hne
    have h2 : orderOf (r * D.b₁ * D.a) = 2 := by
      refine orderOf_mul_eq_two_of_comm ?_ D.a_mul_a (D.a_comm_T (D.B_le_T hrb)) ?_
      · rw [← sq, ← h1]; exact pow_orderOf_eq_one _
      · intro h
        apply D.a_not_mem_B
        rw [eq_inv_of_mul_eq_one_right h]
        exact inv_mem hrb
    rcases D.lift_isConj hO haO ha₀T (D.B_le_T hrb) hc with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [← SemiconjBy.orderOf_eq _ hc, hord4] at h1; omega
    · rw [← SemiconjBy.orderOf_eq _ hc, hord4] at h2; omega
  · rintro _ hx hx2 hxa _ hy hy2 hya _ ⟨r, hr, rfl⟩ hr2 hc
    obtain ⟨x, hxA, rfl, hx2', hxa'⟩ := D.toFooteCore.exists_lift_involution hO hx hx2 hxa
    obtain ⟨y, hyA, rfl, hy2', hya'⟩ := D.toFooteCore.exists_lift_involution hO hy hy2 hya
    rw [D.orderOf_mk_of_mem_B hO (hB₀B hr)] at hr2
    rw [← map_mul] at hc
    have hxrT : x * r ∈ T := mul_mem (D.A_le_T hxA) (D.B_le_T (hB₀B hr))
    apply D.fusion_iii x hxA hx2' hxa' y hyA hy2' hya' r hr hr2
    rcases D.lift_isConj hO haO hxrT (D.A_le_T hyA) hc with h | h
    · exact h
    · obtain ⟨u, -, hu⟩ := D.exists_conj_mul_a_of_involution hyA hy2' hya'
      exact h.trans (isConj_iff.2 ⟨u, hu⟩).symm
  · rintro _ hx hx2 hxa _ ⟨r, hr, rfl⟩ hr2 hc
    obtain ⟨x, hxA, rfl, hx2', hxa'⟩ := D.toFooteCore.exists_lift_involution hO hx hx2 hxa
    rw [D.orderOf_mk_of_mem_B hO (hB₀B hr)] at hr2
    change IsConj (ρ x * ρ r * ρ D.b₁) (ρ x * ρ D.b₀) at hc
    rw [← map_mul, ← map_mul, ← map_mul] at hc
    have h1T : x * r * D.b₁ ∈ T :=
      mul_mem (mul_mem (D.A_le_T hxA) (D.B_le_T (hB₀B hr))) (D.B_le_T D.b₁_mem_B)
    have h2T : x * D.b₀ ∈ T := mul_mem (D.A_le_T hxA) (D.B_le_T D.b₀_mem_B)
    apply D.fusion_iv x hxA hx2' hxa' r hr hr2
    rcases D.lift_isConj hO haO h1T h2T hc with h | h
    · exact h
    · obtain ⟨u, huA, hu⟩ := D.exists_conj_mul_a_of_involution hxA hx2' hxa'
      refine h.trans (isConj_iff.2 ⟨u, ?_⟩).symm
      have hub : u * D.b₀ = D.b₀ * u := D.A_comm_B u huA D.b₀ D.b₀_mem_B
      have hab : D.a * D.b₀ = D.b₀ * D.a := (D.a_comm_T (D.B_le_T D.b₀_mem_B)).symm
      calc u * (x * D.b₀) * u⁻¹ = u * x * u⁻¹ * (u * D.b₀ * u⁻¹) := by group
        _ = x * D.a * D.b₀ := by rw [hu, hub, mul_inv_cancel_right]
        _ = x * D.b₀ * D.a := by rw [mul_assoc, hab, ← mul_assoc]
  · rintro _ ⟨r, hr, rfl⟩ hr2 hc
    rw [D.orderOf_mk_of_mem_B hO (hB₀B hr)] at hr2
    change IsConj (ρ D.a₀) (ρ r * (ρ D.t * ρ r * (ρ D.t)⁻¹)) at hc
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul] at hc
    have hrr : r * r = 1 := by rw [← sq, ← hr2]; exact pow_orderOf_eq_one r
    have hrtT : r * (D.t * r * D.t⁻¹) ∈ T :=
      mul_mem (D.B_le_T (hB₀B hr)) (D.B_le_T (D.conj_t_B _ (hB₀B hr)))
    have hsq : r * (D.t * r * D.t⁻¹) * (r * (D.t * r * D.t⁻¹)) = 1 := by
      have hc' := hB₀t r hr r hr
      calc r * (D.t * r * D.t⁻¹) * (r * (D.t * r * D.t⁻¹))
          = r * ((D.t * r * D.t⁻¹) * r) * (D.t * r * D.t⁻¹) := by group
        _ = r * (r * (D.t * r * D.t⁻¹)) * (D.t * r * D.t⁻¹) := by rw [hc']
        _ = (r * r) * (D.t * (r * r) * D.t⁻¹) := by group
        _ = 1 := by rw [hrr, mul_one, mul_inv_cancel, one_mul]
    have hsq' : r * (D.t * r * D.t⁻¹) * D.a * (r * (D.t * r * D.t⁻¹) * D.a) = 1 := by
      have hca := D.a_comm_T hrtT
      calc r * (D.t * r * D.t⁻¹) * D.a * (r * (D.t * r * D.t⁻¹) * D.a)
          = r * (D.t * r * D.t⁻¹) * (D.a * (r * (D.t * r * D.t⁻¹))) * D.a := by group
        _ = r * (D.t * r * D.t⁻¹) * ((r * (D.t * r * D.t⁻¹)) * D.a) * D.a := by rw [hca]
        _ = (r * (D.t * r * D.t⁻¹) * (r * (D.t * r * D.t⁻¹))) * (D.a * D.a) := by group
        _ = 1 := by rw [hsq, D.a_mul_a, one_mul]
    rcases D.lift_isConj hO haO ha₀T hrtT hc with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact orderOf_ne_four_of_mul_self_eq_one hsq (by rw [← SemiconjBy.orderOf_eq _ hc, hord4])
    · exact orderOf_ne_four_of_mul_self_eq_one hsq' (by rw [← SemiconjBy.orderOf_eq _ hc, hord4])

@[expose] noncomputable def descent
    (hB₀t : ∀ x ∈ D.B₀, ∀ y ∈ D.B₀, x * (D.t * y * D.t⁻¹) = (D.t * y * D.t⁻¹) * x) :
    FooteData (G ⧸ D.descM O) (T.map (QuotientGroup.mk' (D.descM O))) (k + 2) n :=
  { D.toFooteCore.descent hO with
    fusion_i := (D.descent_fusion hO haO hB₀t).1
    fusion_ii := (D.descent_fusion hO haO hB₀t).2.1
    fusion_iii := (D.descent_fusion hO haO hB₀t).2.2.1
    fusion_iv := (D.descent_fusion hO haO hB₀t).2.2.2.1
    fusion_v := (D.descent_fusion hO haO hB₀t).2.2.2.2 }

end FooteData

namespace FooteCore

variable {G : Type*} [Group G] [Finite G] {T : Subgroup G} {k n : ℕ}
  (D : FooteCore G T (k + 3) n) {O : Subgroup G} [O.Normal]
  (hO : Odd (Nat.card O)) [(D.descM O).Normal]

local notation "ρ" => QuotientGroup.mk' (D.descM O)

include hO in
theorem mk_ne_one_of_mem_T {x : G} (hx : x ∈ T) (hx1 : x ≠ 1) (hxa : x ≠ D.a) : ρ x ≠ 1 := by
  intro h
  have : x ∈ T ⊓ D.descM O := mem_inf.2 ⟨hx, (QuotientGroup.eq_one_iff _).1 h⟩
  rw [D.T_inf_descM hO, D.mem_zpowers_a_iff] at this
  rcases this with h1 | h1
  · exact hx1 h1
  · exact hxa h1

include hO in
theorem mem_of_mk_mem {X : Subgroup G} (hXT : X ≤ T) (haX : D.a ∈ X) {x : G} (hx : x ∈ T)
    (h : ρ x ∈ X.map ρ) : x ∈ X := by
  obtain ⟨y, hy, hxy⟩ := h
  have h1 : y⁻¹ * x ∈ T ⊓ D.descM O := by
    refine mem_inf.2 ⟨mul_mem (inv_mem (hXT hy)) hx, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hxy
    exact QuotientGroup.eq.1 hxy
  rw [D.T_inf_descM hO, D.mem_zpowers_a_iff] at h1
  rw [← mul_inv_cancel_left y x]
  rcases h1 with h1 | h1 <;> rw [h1]
  · rw [mul_one]; exact hy
  · exact mul_mem hy haX

include hO in
theorem stronglyInvolutionClosed_of_map {X : Subgroup G} (hXT : X ≤ T) (haX : D.a ∈ X)
    (haO : ∀ g : G, g * D.a * g⁻¹ * D.a⁻¹ ∈ O)
    (h : StronglyInvolutionClosed (X.map ρ) (T.map ρ)) : StronglyInvolutionClosed X T := by
  intro x hx hx2 g hg
  by_cases hxa : x = D.a
  · subst hxa
    have : g * D.a * g⁻¹ * D.a⁻¹ ∈ T ⊓ O :=
      mem_inf.2 ⟨mul_mem hg (inv_mem D.a_mem_T), haO g⟩
    rw [D.T_inf_eq_bot_of_odd hO, mem_bot] at this
    rw [mul_inv_eq_one.1 this]
    exact haX
  · have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx2; omega
    have hρx2 : orderOf (ρ x) = 2 := by
      refine orderOf_eq_prime ?_ (D.mk_ne_one_of_mem_T hO (hXT hx) hx1 hxa)
      rw [← map_pow, ← hx2, pow_orderOf_eq_one, map_one]
    have := h (ρ x) ⟨x, hx, rfl⟩ hρx2 (ρ g) (by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact ⟨_, hg, rfl⟩)
    rw [← map_inv, ← map_mul, ← map_mul] at this
    exact D.mem_of_mk_mem hO hXT haX hg this

include hO in
theorem Astar_descent : (D.descent hO).Astar = D.Astar.map ρ := by
  rw [Astar, Astar, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨xb, hx, hx2, hxa, rfl⟩
    obtain ⟨x, hxA, rfl, hx2', hxa'⟩ := D.exists_lift_involution hO hx hx2 hxa
    refine ⟨x * D.b, ⟨x, hxA, hx2', hxa', rfl⟩, ?_⟩
    show ρ (x * (D.b₀ * D.b₁)) = ρ x * (ρ D.b₀ * ρ D.b₁)
    rw [map_mul, map_mul]
  · rintro ⟨_, ⟨x, hxA, hx2, hxa, rfl⟩, rfl⟩
    refine ⟨ρ x, ⟨x, hxA, rfl⟩, ?_, ?_, ?_⟩
    · have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx2; omega
      refine orderOf_eq_prime ?_ (D.mk_ne_one_of_mem_T hO (D.A_le_T hxA) hx1 hxa)
      rw [← map_pow, ← hx2, pow_orderOf_eq_one, map_one]
    · intro h
      have h1 : x⁻¹ * D.a₀ ∈ T ⊓ D.descM O := by
        refine mem_inf.2 ⟨mul_mem (inv_mem (D.A_le_T hxA)) (D.A_le_T D.a₀_mem), ?_⟩
        have h' : ρ x = ρ D.a₀ := h
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h'
        exact QuotientGroup.eq.1 h'
      rw [D.T_inf_descM hO, D.mem_zpowers_a_iff] at h1
      have hord := D.orderOf_a₀
      rcases h1 with h1 | h1
      · rw [show D.a₀ = x by rw [← mul_inv_cancel_left x D.a₀, h1, mul_one]] at hord
        omega
      · have : D.a₀ = x * D.a := by rw [← mul_inv_cancel_left x D.a₀, h1]
        have hxx : x * x = 1 := by rw [← sq, ← hx2]; exact pow_orderOf_eq_one x
        have hxa' : x * D.a = D.a * x := D.a_comm_T (D.A_le_T hxA)
        have hsq : x * D.a * (x * D.a) = 1 := by
          calc x * D.a * (x * D.a) = x * (D.a * x) * D.a := by group
            _ = x * (x * D.a) * D.a := by rw [hxa']
            _ = (x * x) * (D.a * D.a) := by group
            _ = 1 := by rw [hxx, D.a_mul_a, one_mul]
        exact orderOf_ne_four_of_mul_self_eq_one hsq (this ▸ hord)
    · show ρ x * (ρ D.b₀ * ρ D.b₁) = ρ (x * (D.b₀ * D.b₁))
      rw [map_mul, map_mul]

end FooteCore

end CFSG.CGT.Foote81L6

