module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveB
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveConj

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem eq_one_of_sq_of_cube {x : G} (h2 : x ^ 2 = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3, inv_one, mul_one]

theorem mem_normalizer_inf_centralizer {N : Subgroup G} {g : G}
    (hg : g ∈ normalizer (N : Set G)) :
    g ∈ normalizer ((N ⊓ centralizer (N : Set G) : Subgroup G) : Set G) :=
  inf_mem_normalizer hg (mem_normalizer_centralizer hg)

namespace Hyp

variable {fr : JankoFrame G z}

theorem At_le_M (_h : Hyp fr) : fr.At ≤ fr.M := inf_le_left

theorem Atz_le_M (_h : Hyp fr) : fr.Atz ≤ fr.M := inf_le_left

theorem Mbar_le_M (h : Hyp fr) : fr.Mbar ≤ fr.M := sup_le h.At_le_M h.Atz_le_M

theorem ZN_le_N (_h : Hyp fr) : fr.ZN ≤ fr.N := inf_le_left

theorem P3bar_le_ZN (_h : Hyp fr) : fr.P3bar ≤ fr.ZN := inf_le_left

theorem P3bbar_le_ZN (_h : Hyp fr) : fr.P3bbar ≤ fr.ZN := inf_le_left

theorem P3bar_le_At (h : Hyp fr) : fr.P3bar ≤ fr.At :=
  le_inf (h.P3bar_le_ZN.trans h.p11.ZN_le_M) inf_le_right

theorem P3bbar_le_Atz (h : Hyp fr) : fr.P3bbar ≤ fr.Atz :=
  le_inf (h.P3bbar_le_ZN.trans h.p11.ZN_le_M) inf_le_right

theorem S_le_ZN (h : Hyp fr) : fr.S ≤ fr.ZN := sup_le h.P3bar_le_ZN h.P3bbar_le_ZN

theorem S_le_Mbar (h : Hyp fr) : fr.S ≤ fr.Mbar := sup_le_sup h.P3bar_le_At h.P3bbar_le_Atz

theorem S_le_M (h : Hyp fr) : fr.S ≤ fr.M := h.S_le_Mbar.trans h.Mbar_le_M

theorem s₁_mem_ZN (h : Hyp fr) : fr.s₁ ∈ fr.ZN := by
  rw [h.p11.ZN_eq]
  refine (le_sup_left : fr.P₁ ≤ fr.P₁ ⊔ fr.S) ?_
  rw [fr.P₁_eq]
  exact Subgroup.mem_zpowers _

theorem M_comm (h : Hyp fr) {a b : G} (ha : a ∈ fr.M) (hb : b ∈ fr.M) : a * b = b * a :=
  h.p10.M_comm a ha b hb

theorem z_mem_normalizer_N (h : Hyp fr) : z ∈ normalizer (fr.N : Set G) :=
  h.L_le_normalizer_N h.z_mem_L

theorem mem_normalizer_ZN {g : G} (_h : Hyp fr) (hg : g ∈ normalizer (fr.N : Set G)) :
    g ∈ normalizer (fr.ZN : Set G) :=
  mem_normalizer_inf_centralizer hg

theorem z_mem_normalizer_At (h : Hyp fr) : z ∈ normalizer (fr.At : Set G) :=
  inf_mem_normalizer h.z_mem_normalizer_M
    (mem_normalizer_centralizer_singleton h.t_comm_z.symm)

theorem z_mem_normalizer_Atz (h : Hyp fr) : z ∈ normalizer (fr.Atz : Set G) := by
  refine inf_mem_normalizer h.z_mem_normalizer_M (mem_normalizer_centralizer_singleton ?_)
  rw [← mul_assoc, ← h.t_comm_z, mul_assoc]

theorem z_mem_normalizer_P3bar (h : Hyp fr) : z ∈ normalizer (fr.P3bar : Set G) :=
  inf_mem_normalizer (h.mem_normalizer_ZN h.z_mem_normalizer_N)
    (mem_normalizer_centralizer_singleton h.t_comm_z.symm)

theorem t_mem_centralizer_P3bar (_h : Hyp fr) : fr.t ∈ centralizer (fr.P3bar : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2

theorem comm_t_of_comm_tz (_h : Hyp fr) {x : G} (h1 : x * (fr.t * z) = fr.t * z * x)
    (h2 : x * z = z * x) : x * fr.t = fr.t * x := by
  calc x * fr.t = x * (fr.t * z) * z⁻¹ := by group
    _ = fr.t * z * x * z⁻¹ := by rw [h1]
    _ = fr.t * (x * z) * z⁻¹ := by rw [mul_assoc fr.t, ← h2]
    _ = fr.t * x := by group

theorem Atz_inf_z (h : Hyp fr) : fr.Atz ⊓ centralizer ({z} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hxz⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxM, hxtz⟩ := Subgroup.mem_inf.mp hx1
  rw [Subgroup.mem_centralizer_singleton_iff] at hxtz hxz
  have hxP : x ∈ fr.P₁ := by
    rw [← h.p10.M_inf_centralizer_z]
    exact ⟨hxM, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩
  exact (Subgroup.mem_bot).mpr (h.eq_one_of_mem_P₁_of_comm_t hxP (h.comm_t_of_comm_tz hxtz hxz))

theorem z_inv_of_mem_At (h : Hyp fr) {x : G} (hx : x ∈ fr.At) : z * x * z⁻¹ = x⁻¹ :=
  conj_eq_inv_of_inf_eq_bot (fun _ ha _ hb => h.M_comm (h.At_le_M ha) (h.At_le_M hb))
    h.z_mul_z h.z_mem_normalizer_At h.p10.At_inf_centralizer_z hx

theorem z_inv_of_mem_Atz (h : Hyp fr) {x : G} (hx : x ∈ fr.Atz) : z * x * z⁻¹ = x⁻¹ :=
  conj_eq_inv_of_inf_eq_bot (fun _ ha _ hb => h.M_comm (h.Atz_le_M ha) (h.Atz_le_M hb))
    h.z_mul_z h.z_mem_normalizer_Atz h.Atz_inf_z hx

theorem At_le_normalizer_Atz (h : Hyp fr) : fr.At ≤ normalizer (fr.Atz : Set G) :=
  le_normalizer_of_commute fun _ ha _ hb => h.M_comm (h.At_le_M ha) (h.Atz_le_M hb)

theorem z_inv_of_mem_Mbar (h : Hyp fr) {x : G} (hx : x ∈ fr.Mbar) : z * x * z⁻¹ = x⁻¹ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup h.At_le_normalizer_Atz hx
  rw [show z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) by group, h.z_inv_of_mem_At ha,
    h.z_inv_of_mem_Atz hb, mul_inv_rev, h.M_comm (inv_mem (h.Atz_le_M hb))
      (inv_mem (h.At_le_M ha))]

theorem z_inv_of_mem_S (h : Hyp fr) {x : G} (hx : x ∈ fr.S) : z * x * z⁻¹ = x⁻¹ :=
  h.z_inv_of_mem_Mbar (h.S_le_Mbar hx)

theorem pow_three_of_mem_M (h : Hyp fr) {x : G} (hx : x ∈ fr.M) : x ^ 3 = 1 :=
  h.p10.M_pow_three x hx

theorem eq_one_of_mem_Mbar_of_comm_z (h : Hyp fr) {x : G} (hx : x ∈ fr.Mbar)
    (hxz : x * z = z * x) : x = 1 := by
  have h1 := h.z_inv_of_mem_Mbar hx
  rw [← hxz, mul_inv_cancel_right] at h1
  refine eq_one_of_sq_of_cube ?_ (h.pow_three_of_mem_M (h.Mbar_le_M hx))
  rw [sq]
  nth_rewrite 2 [h1]
  exact mul_inv_cancel x

theorem t_inv_of_mem_P3bbar (h : Hyp fr) {x : G} (hx : x ∈ fr.P3bbar) :
    fr.t * x * fr.t⁻¹ = x⁻¹ := by
  have h1 : fr.t * z * x * (fr.t * z)⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    rw [← this, mul_inv_cancel_right]
  have h2 := h.z_inv_of_mem_S ((le_sup_right : fr.P3bbar ≤ fr.S) hx)
  have h3 : z⁻¹ * x * z = x⁻¹ := by
    rw [h.z_inv]
    rw [h.z_inv] at h2
    exact h2
  calc fr.t * x * fr.t⁻¹ = (fr.t * z) * (z⁻¹ * x * z) * (fr.t * z)⁻¹ := by group
    _ = (fr.t * z) * x⁻¹ * (fr.t * z)⁻¹ := by rw [h3]
    _ = ((fr.t * z) * x * (fr.t * z)⁻¹)⁻¹ := by group
    _ = x⁻¹ := by rw [h1]

theorem P3bar_inf_P3bbar (h : Hyp fr) : fr.P3bar ⊓ fr.P3bbar = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have hxt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx1).2
  have hxtz := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx2).2
  have hxz : x * z = z * x := by
    calc x * z = x * fr.t⁻¹ * (fr.t * z) := by group
      _ = fr.t⁻¹ * x * (fr.t * z) := by
        rw [show x * fr.t⁻¹ = fr.t⁻¹ * (fr.t * x) * fr.t⁻¹ by group, ← hxt]; group
      _ = fr.t⁻¹ * (fr.t * z) * x := by rw [mul_assoc, hxtz, ← mul_assoc]
      _ = z * x := by group
  rw [← h.p10.At_inf_centralizer_z]
  exact ⟨h.P3bar_le_At hx1, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩

theorem P3bar_le_normalizer_P3bbar (h : Hyp fr) : fr.P3bar ≤ normalizer (fr.P3bbar : Set G) :=
  le_normalizer_of_commute fun _ ha _ hb =>
    h.M_comm (h.p11.ZN_le_M (h.P3bar_le_ZN ha)) (h.p11.ZN_le_M (h.P3bbar_le_ZN hb))

theorem card_S (h : Hyp fr) : Nat.card fr.S = 9 := by
  rw [JankoFrame.S, card_sup_of_inf_eq_bot h.P3bar_le_normalizer_P3bbar h.P3bar_inf_P3bbar,
    h.p11.card_P3bar, h.p11.card_P3bbar]

theorem At_inf_Atz (h : Hyp fr) : fr.At ⊓ fr.Atz = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have hxt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx1).2
  have hxtz := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx2).2
  have hxz : x * z = z * x := by
    calc x * z = x * fr.t⁻¹ * (fr.t * z) := by group
      _ = fr.t⁻¹ * x * (fr.t * z) := by
        rw [show x * fr.t⁻¹ = fr.t⁻¹ * (fr.t * x) * fr.t⁻¹ by group, ← hxt]; group
      _ = fr.t⁻¹ * (fr.t * z) * x := by rw [mul_assoc, hxtz, ← mul_assoc]
      _ = z * x := by group
  rw [← h.p10.At_inf_centralizer_z]
  exact ⟨hx1, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩

theorem card_Mbar (h : Hyp fr) : Nat.card fr.Mbar = 81 := by
  rw [JankoFrame.Mbar, card_sup_of_inf_eq_bot h.At_le_normalizer_Atz h.At_inf_Atz,
    h.p10.card_At, h.p10.card_Atz]

theorem P₁_le_centralizer_z (h : Hyp fr) : fr.P₁ ≤ centralizer ({z} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp h.z_mem_centralizer_P₁) x hx

theorem eq_one_of_mem_P₁_of_mem_Mbar (h : Hyp fr) {x : G} (hx1 : x ∈ fr.P₁)
    (hx2 : x ∈ fr.Mbar) : x = 1 :=
  h.eq_one_of_mem_Mbar_of_comm_z hx2
    (Subgroup.mem_centralizer_singleton_iff.mp (h.P₁_le_centralizer_z hx1))

theorem s₁_ne_one (_h : Hyp fr) : fr.s₁ ≠ 1 := by
  intro h1
  have := fr.orderOf_s₁
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem s₁_mem_P₁ (_h : Hyp fr) : fr.s₁ ∈ fr.P₁ := by
  rw [fr.P₁_eq]
  exact Subgroup.mem_zpowers _

theorem s₁_not_mem_Mbar (h : Hyp fr) : fr.s₁ ∉ fr.Mbar := fun hs =>
  h.s₁_ne_one (h.eq_one_of_mem_P₁_of_mem_Mbar h.s₁_mem_P₁ hs)

theorem s₁_not_mem_S (h : Hyp fr) : fr.s₁ ∉ fr.S := fun hs => h.s₁_not_mem_Mbar (h.S_le_Mbar hs)

theorem ZN_inf_Mbar (h : Hyp fr) : fr.ZN ⊓ fr.Mbar = fr.S := by
  have hle : fr.S ≤ fr.ZN ⊓ fr.Mbar := le_inf h.S_le_ZN h.S_le_Mbar
  have h9 : 9 ∣ Nat.card (fr.ZN ⊓ fr.Mbar : Subgroup G) := h.card_S ▸ Subgroup.card_dvd_of_le hle
  have h27 : Nat.card (fr.ZN ⊓ fr.Mbar : Subgroup G) ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : fr.ZN ⊓ fr.Mbar ≤ fr.ZN)
    rw [h.p11.card_ZN] at this
    exact this
  have hne : Nat.card (fr.ZN ⊓ fr.Mbar : Subgroup G) ≠ 27 := by
    intro h27'
    have := Subgroup.eq_of_le_of_card_ge (inf_le_left : fr.ZN ⊓ fr.Mbar ≤ fr.ZN)
      (by rw [h27', h.p11.card_ZN])
    exact h.s₁_not_mem_Mbar
      (Subgroup.mem_inf.mp (this.symm ▸ h.s₁_mem_ZN : fr.s₁ ∈ fr.ZN ⊓ fr.Mbar)).2
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h27
  have h9' : Nat.card (fr.ZN ⊓ fr.Mbar : Subgroup G) = 9 := by
    interval_cases m <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9', h.card_S])).symm

theorem isConj_s₃_of_mem_S (h : Hyp fr) {x : G} (hx : x ∈ fr.S) (hx1 : x ≠ 1) :
    IsConj x fr.s₃ :=
  h.p11.isConj_of_mem_Mbar x (h.S_le_Mbar hx) hx1

theorem exists_P3bar_eq (h : Hyp fr) : ∃ y : G, fr.P3bar = zpowers y ∧ orderOf y = 3 := by
  obtain ⟨y, hy, hy1⟩ := CFSG.Walter.J1.exists_ne_one_of_card h.p11.card_P3bar (by norm_num)
  have heq := CFSG.Walter.J1.eq_zpowers_of_card_prime Nat.prime_three h.p11.card_P3bar hy hy1
  refine ⟨y, heq, ?_⟩
  rw [← Nat.card_zpowers, ← heq, h.p11.card_P3bar]

theorem exists_P3bbar_eq (h : Hyp fr) : ∃ y : G, fr.P3bbar = zpowers y ∧ orderOf y = 3 := by
  obtain ⟨y, hy, hy1⟩ := CFSG.Walter.J1.exists_ne_one_of_card h.p11.card_P3bbar (by norm_num)
  have heq := CFSG.Walter.J1.eq_zpowers_of_card_prime Nat.prime_three h.p11.card_P3bbar hy hy1
  refine ⟨y, heq, ?_⟩
  rw [← Nat.card_zpowers, ← heq, h.p11.card_P3bbar]

theorem ℓ_sq_mem_normalizer_N (h : Hyp fr) : fr.ℓ ^ 2 ∈ normalizer (fr.N : Set G) :=
  Subgroup.pow_mem _ (h.L_le_normalizer_N h.ℓ_mem_L) 2

theorem ℓ_sq_conj_mem_P3bbar (h : Hyp fr) {x : G} (hx : x ∈ fr.P3bar) :
    fr.ℓ ^ 2 * x * (fr.ℓ ^ 2)⁻¹ ∈ fr.P3bbar := by
  have hZ := h.mem_normalizer_ZN h.ℓ_sq_mem_normalizer_N
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hZ x).mp (h.P3bar_le_ZN hx), ?_⟩
  have hxt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  rw [Subgroup.mem_centralizer_singleton_iff, ← h.ℓ_sq_conj_t]
  calc fr.ℓ ^ 2 * x * (fr.ℓ ^ 2)⁻¹ * (fr.ℓ ^ 2 * fr.t * (fr.ℓ ^ 2)⁻¹) =
        fr.ℓ ^ 2 * (x * fr.t) * (fr.ℓ ^ 2)⁻¹ := by group
    _ = fr.ℓ ^ 2 * (fr.t * x) * (fr.ℓ ^ 2)⁻¹ := by rw [hxt]
    _ = _ := by group

theorem ℓ_sq_inv_conj_mem_P3bar (h : Hyp fr) {x : G} (hx : x ∈ fr.P3bbar) :
    (fr.ℓ ^ 2)⁻¹ * x * fr.ℓ ^ 2 ∈ fr.P3bar := by
  have hZ := h.mem_normalizer_ZN (inv_mem h.ℓ_sq_mem_normalizer_N)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp hZ x).mp (h.P3bbar_le_ZN hx)
    rwa [inv_inv] at this
  have hxt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  rw [Subgroup.mem_centralizer_singleton_iff, ← h.ℓ_sq_inv_conj_tz]
  calc (fr.ℓ ^ 2)⁻¹ * x * fr.ℓ ^ 2 * ((fr.ℓ ^ 2)⁻¹ * (fr.t * z) * fr.ℓ ^ 2) =
        (fr.ℓ ^ 2)⁻¹ * (x * (fr.t * z)) * fr.ℓ ^ 2 := by group
    _ = (fr.ℓ ^ 2)⁻¹ * (fr.t * z * x) * fr.ℓ ^ 2 := by rw [hxt]
    _ = _ := by group

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
