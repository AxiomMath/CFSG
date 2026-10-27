module

public import CFSG.GH74.Uniqueness.Section153

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

structure Hyp156 (M : Subgroup X) (n : ℕ) (L D K J Mo V U Y : Subgroup X) : Prop where
  F : Facts15 M n L D K J Mo V
  U_le : U ≤ J
  Y_le : Y ≤ J
  U_pgroup : IsPGroup 2 U
  U_two : ∀ j ∈ J, IsPGroup 2 (zpowers j) → j ∈ U
  U_sq : ∀ x ∈ U, x * x = 1
  Y_odd : Odd (Nat.card Y)
  Y_comm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a
  JUY : ∀ j ∈ J, ∃ x ∈ U, ∃ y ∈ Y, j = x * y
  fpf : ∀ y ∈ Y, y ≠ 1 → ∀ x ∈ U, y * x = x * y → x = 1
  U_ne : U ≠ ⊥
  C0_two : ∀ g ∈ centralizer (Mo : Set X), IsPGroup 2 (zpowers g) → g ∈ V
  C0_eq : ∀ g ∈ centralizer (Mo : Set X), ∃ v ∈ V, ∃ y ∈ Y, g = v * y
  inv_U : ∀ d ∈ D, orderOf d = 2 → d ∈ U
  VD_eq : V ⊓ D = U
  TI : ∀ g : X, (∃ x ∈ U, x ≠ 1 ∧ g * x * g⁻¹ ∈ U) → g ∈ normalizer (L : Set X)
  NU : normalizer (L : Set X) ≤ normalizer (U : Set X)

namespace Hyp156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V U Y : Subgroup X}

omit [Finite X] in
theorem U_le_V (H : Hyp156 M n L D K J Mo V U Y) : U ≤ V := H.VD_eq ▸ inf_le_left

omit [Finite X] in
theorem U_le_D (H : Hyp156 M n L D K J Mo V U Y) : U ≤ D := H.U_le.trans H.F.J_le_D

omit [Finite X] in
theorem U_comm_Mo (H : Hyp156 M n L D K J Mo V U Y) {u : X} (hu : u ∈ U) {m : X} (hm : m ∈ Mo) :
    u * m = m * u := H.F.J_comm_Mo (H.U_le hu) hm

omit [Finite X] in
theorem mem_E (H : Hyp156 M n L D K J Mo V U Y) {x : X} (hx : x ∈ Mo ⊔ U) :
    ∃ m ∈ Mo, ∃ u ∈ U, x = m * u :=
  Bender.exists_mul_of_mem_sup_of_commute (fun _ hm _ hu => (H.U_comm_Mo hu hm).symm) hx

omit [Finite X] in
theorem E_le_V (H : Hyp156 M n L D K J Mo V U Y) : Mo ⊔ U ≤ V := sup_le H.F.Mo_le_V H.U_le_V

omit [Finite X] in
theorem E_le_M (H : Hyp156 M n L D K J Mo V U Y) : Mo ⊔ U ≤ M := H.E_le_V.trans H.F.V_le

omit [Finite X] in
theorem eq_one_of_mem_Mo_U (H : Hyp156 M n L D K J Mo V U Y) {x : X} (hxMo : x ∈ Mo)
    (hxU : x ∈ U) : x = 1 := H.F.eq_one_of_mem_L_J (H.F.Mo_le_L hxMo) (H.U_le hxU)

omit [Finite X] in
theorem E_sq (H : Hyp156 M n L D K J Mo V U Y) {x : X} (hx : x ∈ Mo ⊔ U) : x * x = 1 := by
  obtain ⟨m, hm, u, hu, rfl⟩ := H.mem_E hx
  have hc := H.U_comm_Mo hu hm
  calc m * u * (m * u) = (m * m) * (u * u) := by
        calc m * u * (m * u) = m * (u * m) * u := by group
          _ = m * (m * u) * u := by rw [hc]
          _ = (m * m) * (u * u) := by group
    _ = 1 := by rw [H.F.Mo_sq m hm, H.U_sq u hu, one_mul]

omit [Finite X] in
theorem E_comm (H : Hyp156 M n L D K J Mo V U Y) {x y : X} (hx : x ∈ Mo ⊔ U)
    (hy : y ∈ Mo ⊔ U) : x * y = y * x := by
  have h1 := H.E_sq (mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (H.E_sq hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (H.E_sq hy)
  have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  calc x * y = (x * y)⁻¹ := hxy.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

omit [Finite X] in
theorem card_E (H : Hyp156 M n L D K J Mo V U Y) : Nat.card ↥(Mo ⊔ U) = 2 ^ n * Nat.card U := by
  have hn : ∀ u ∈ U, ∀ m ∈ Mo, u * m * u⁻¹ ∈ Mo := fun u hu m hm => by
    rw [H.U_comm_Mo hu hm, mul_inv_cancel_right]
    exact hm
  have hinf : Mo ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact mem_bot.mpr (H.eq_one_of_mem_Mo_U (mem_inf.mp hx).1 (mem_inf.mp hx).2)
  rw [card_sup_of_normal hn hinf, H.F.card_Mo]

omit [Finite X] in
theorem E_le_N (H : Hyp156 M n L D K J Mo V U Y) : Mo ⊔ U ≤ normalizer (L : Set X) := by
  refine sup_le (fun m hm => ?_) (fun u hu => ?_)
  · exact le_normalizer (H.F.Mo_le_L hm)
  · rw [mem_normalizer_iff]
    intro l
    have hc : ∀ l ∈ L, u * l = l * u := fun l hl => H.F.J_comm (H.U_le hu) hl
    constructor
    · intro hl
      rw [hc l hl, mul_inv_cancel_right]
      exact hl
    · intro hl
      have h1 := hc _ hl
      have h2 : u * l * u⁻¹ = l := by
        calc u * l * u⁻¹ = u⁻¹ * (u * (u * l * u⁻¹) * u⁻¹) * u := by group
          _ = u⁻¹ * (u * l * u⁻¹ * u * u⁻¹) * u := by rw [h1]
          _ = l := by group
      rw [← h2]
      exact hl

omit [Finite X] in
theorem NV_L (H : Hyp156 M n L D K J Mo V U Y) {x : X} (hxV : x ∈ V)
    (hxN : x ∈ normalizer (L : Set X)) : x ∈ Mo ⊔ U := by
  obtain ⟨m, hm, d, hd, rfl⟩ := H.F.NM_eq x (H.F.V_le hxV) hxN
  have hdV : d ∈ V := by
    have e : d = m⁻¹ * (m * d) := by group
    rw [e]
    exact mul_mem (inv_mem (H.F.Mo_le_V hm)) hxV
  have hdU : d ∈ U := by
    rw [← H.VD_eq]
    exact mem_inf.mpr ⟨hdV, hd⟩
  exact mul_mem (mem_sup_left hm) (mem_sup_right hdU)

omit [Finite X] in
theorem mem_N_U_iff (H : Hyp156 M n L D K J Mo V U Y) {g : X} :
    g ∈ normalizer (U : Set X) ↔ g ∈ normalizer (L : Set X) := by
  refine ⟨fun hg => ?_, fun hg => H.NU hg⟩
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hno
    push Not at hno
    apply H.U_ne
    rw [eq_bot_iff]
    intro x hx
    exact mem_bot.mpr (hno x hx)
  exact H.TI g ⟨u, hu, hu1, (mem_normalizer_iff.mp hg u).mp hu⟩

omit [Finite X] in
theorem centralizer_le_N (H : Hyp156 M n L D K J Mo V U Y) {u : X} (hu : u ∈ U) (hu1 : u ≠ 1)
    {x : X} (hxu : x * u = u * x) : x ∈ normalizer (L : Set X) := by
  have hne : zpowers u ≠ ⊥ := by
    intro hb
    apply hu1
    have := mem_zpowers u
    rw [hb] at this
    exact mem_bot.mp this
  exact H.F.NY_le (zpowers u) (zpowers_le.mpr (H.U_le hu)) hne
    (mem_normalizer_zpowers_of_commute hxu)

omit [Finite X] in
theorem K_conj_E (H : Hyp156 M n L D K J Mo V U Y) {k : X} (hk : k ∈ K) {x : X}
    (hx : x ∈ Mo ⊔ U) : k * x * k⁻¹ ∈ Mo ⊔ U := by
  have hkN : k ∈ normalizer (L : Set X) := H.F.D_le_N (H.F.K_le_D hk)
  refine conj_mem_sup (fun m hm => H.F.Mo_normal k (H.F.K_le_M hk) m hm) (fun u hu => ?_) hx
  exact (mem_normalizer_iff.mp (H.NU hkN) u).mp hu

omit [Finite X] in
theorem cent_E (H : Hyp156 M n L D K J Mo V U Y) {k : X} (hk : k ∈ K) (hk1 : k ≠ 1) {x : X}
    (hx : x ∈ Mo ⊔ U) (hkx : k * x = x * k) : x ∈ U := by
  obtain ⟨m, hm, u, hu, rfl⟩ := H.mem_E hx
  have hku : k * u = u * k := (H.F.J_comm (H.U_le hu) (H.F.K_le_L hk)).symm
  have hkm : k * m = m * k := by
    have h1 : k * m * u = m * k * u := by
      calc k * m * u = k * (m * u) := by group
        _ = m * u * k := hkx
        _ = m * (u * k) := by group
        _ = m * (k * u) := by rw [hku]
        _ = m * k * u := by group
    exact mul_right_cancel h1
  rw [H.F.K_fpf k hk hk1 m hm hkm, one_mul]
  exact hu

end Hyp156

namespace Hyp156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V U Y : Subgroup X}

theorem two_le_card_U (H : Hyp156 M n L D K J Mo V U Y) : 2 ≤ Nat.card U := by
  have h1 : 1 < Nat.card U := (Subgroup.one_lt_card_iff_ne_bot U).mpr H.U_ne
  omega

omit [Finite X] in
theorem four_le_q (H : Hyp156 M n L D K J Mo V U Y) : 4 ≤ 2 ^ n := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) H.F.two_le

omit [Finite X] in
theorem M_inf_NU (H : Hyp156 M n L D K J Mo V U Y) :
    M ⊓ normalizer (U : Set X) = Mo ⊔ D := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgM, hgN⟩ := mem_inf.mp hg
    obtain ⟨m, hm, d, hd, rfl⟩ := H.F.NM_eq g hgM (H.mem_N_U_iff.mp hgN)
    exact mul_mem (mem_sup_left hm) (mem_sup_right hd)
  · refine sup_le (fun m hm => mem_inf.mpr ⟨H.F.Mo_le_M hm, H.NU (le_normalizer (H.F.Mo_le_L hm))⟩)
      (fun d hd => mem_inf.mpr ⟨H.F.D_le hd, H.NU (H.F.D_le_N hd)⟩)

omit [Finite X] in
theorem card_Mo_sup_D (H : Hyp156 M n L D K J Mo V U Y) :
    Nat.card ↥(Mo ⊔ D) = 2 ^ n * Nat.card D := by
  have hinf : Mo ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact mem_bot.mpr (H.F.eq_one_of_mem_Mo_D (mem_inf.mp hx).1 (mem_inf.mp hx).2)
  rw [card_sup_of_normal (fun d hd x hx => H.F.Mo_normal d (H.F.D_le hd) x hx) hinf, H.F.card_Mo]

omit [Finite X] in
theorem index_mul_card {A B : Subgroup X} (hAB : A ≤ B) :
    (A.subgroupOf B).index * Nat.card A = Nat.card B := by
  have h1 := Subgroup.card_mul_index (A.subgroupOf B)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv] at h1
  rw [mul_comm]
  exact h1

theorem index_M_NU (H : Hyp156 M n L D K J Mo V U Y) :
    ((M ⊓ normalizer (U : Set X)).subgroupOf M).index = 2 ^ (2 * n) := by
  have h1 := index_mul_card (inf_le_left : M ⊓ normalizer (U : Set X) ≤ M)
  have hc : Nat.card ↥(M ⊓ normalizer (U : Set X)) = 2 ^ n * Nat.card D := by
    rw [H.M_inf_NU, H.card_Mo_sup_D]
  rw [hc, H.F.card_M] at h1
  have hpos : 0 < 2 ^ n * Nat.card D := Nat.mul_pos (by positivity) Nat.card_pos
  have h2 : 2 ^ (3 * n) * Nat.card D = 2 ^ (2 * n) * (2 ^ n * Nat.card D) := by
    rw [← mul_assoc, ← pow_add]
    ring_nf
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

omit [Finite X] in
@[expose] def conjSet (H : Subgroup X) (U : Subgroup X) : Set X :=
  {y : X | ∃ g ∈ H, ∃ a ∈ U, a ≠ 1 ∧ y = g * a * g⁻¹}

omit [Finite X] in
theorem TI_of (H' : Hyp156 M n L D K J Mo V U Y) (H : Subgroup X) :
    ∀ g ∈ H, ∀ a ∈ U, a ≠ 1 → g * a * g⁻¹ ∈ U → g ∈ normalizer (U : Set X) :=
  fun g _ a ha ha1 hga => H'.NU (H'.TI g ⟨a, ha, ha1, hga⟩)

theorem ncard_conjSet_M (H : Hyp156 M n L D K J Mo V U Y) :
    (conjSet M U).ncard = 2 ^ (2 * n) * (Nat.card U - 1) := by
  rw [conjSet, ncard_conj_TI (H.TI_of M), H.index_M_NU]

omit [Finite X] in
theorem conj_not_mem_Mo (H : Hyp156 M n L D K J Mo V U Y) {g : X} (hg : g ∈ M) {a : X}
    (ha : a ∈ U) (ha1 : a ≠ 1) : g * a * g⁻¹ ∉ Mo := by
  intro h
  have := H.F.Mo_normal g⁻¹ (inv_mem hg) _ h
  have e : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
  rw [e] at this
  exact ha1 (H.eq_one_of_mem_Mo_U this ha)

omit [Finite X] in
theorem conjSet_disjoint_Mo (H : Hyp156 M n L D K J Mo V U Y) {G : Subgroup X} (hG : G ≤ M) :
    Disjoint (conjSet G U) (Mo : Set X) := by
  rw [Set.disjoint_left]
  rintro _ ⟨g, hg, a, ha, ha1, rfl⟩
  exact H.conj_not_mem_Mo (hG hg) ha ha1

theorem E_ne_V (H : Hyp156 M n L D K J Mo V U Y) : (Mo ⊔ U : Subgroup X) ≠ V := by
  intro hEV
  have hsub : conjSet M U ∪ (Mo : Set X) ⊆ ((Mo ⊔ U : Subgroup X) : Set X) := by
    refine Set.union_subset ?_ (fun x hx => mem_sup_left hx)
    rintro _ ⟨g, hg, a, ha, -, rfl⟩
    rw [hEV]
    exact H.F.V_normal g hg a (H.U_le_V ha)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hMo : (Mo : Set X).ncard = 2 ^ n := by
    rw [← Nat.card_coe_set_eq]
    exact H.F.card_Mo
  have hE : ((Mo ⊔ U : Subgroup X) : Set X).ncard = 2 ^ n * Nat.card U := by
    rw [← Nat.card_coe_set_eq]
    exact H.card_E
  rw [Set.ncard_union_eq (H.conjSet_disjoint_Mo le_rfl) (Set.toFinite _) (Set.toFinite _),
    H.ncard_conjSet_M, hMo, hE] at h1
  have hr := H.two_le_card_U
  have hq := H.four_le_q
  have h2 : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
  rw [h2] at h1
  set q := 2 ^ n
  set r := Nat.card U
  have h3 : q * q * (r - 1) + q ≤ q * r := h1
  have h4 : q * r = q * (r - 1) + q := by
    rw [Nat.mul_sub, mul_one]
    have : q ≤ q * r := Nat.le_mul_of_pos_right q (by omega)
    omega
  rw [h4] at h3
  have h5 : q * q * (r - 1) ≤ q * (r - 1) := by omega
  have h6 : 0 < q * (r - 1) := Nat.mul_pos (by omega) (by omega)
  nlinarith

end Hyp156

end CFSG.GH74.Uniqueness
