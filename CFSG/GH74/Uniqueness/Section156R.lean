module

public import CFSG.GH74.Uniqueness.Section156A
public import CFSG.GH74.Uniqueness.Section154

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

namespace Hyp156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V U Y : Subgroup X}

omit [Finite X] in
abbrev R1 (V Mo U : Subgroup X) : Subgroup X := V ⊓ normalizer ((Mo ⊔ U : Subgroup X) : Set X)

omit [Finite X] in
theorem E_le_R1 (H : Hyp156 M n L D K J Mo V U Y) : Mo ⊔ U ≤ R1 V Mo U :=
  le_inf H.E_le_V le_normalizer

omit [Finite X] in
theorem R1_le_V : R1 V Mo U ≤ V := inf_le_left

omit [Finite X] in
theorem K_conj_V (H : Hyp156 M n L D K J Mo V U Y) {k : X} (hk : k ∈ K) {x : X} (hx : x ∈ V) :
    k * x * k⁻¹ ∈ V := H.F.V_normal k (H.F.K_le_M hk) x hx

theorem K_conj_R1 (H : Hyp156 M n L D K J Mo V U Y) {k : X} (hk : k ∈ K) {x : X}
    (hx : x ∈ R1 V Mo U) : k * x * k⁻¹ ∈ R1 V Mo U := by
  obtain ⟨hxV, hxN⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨H.K_conj_V hk hxV, ?_⟩
  have hkN : k ∈ normalizer ((Mo ⊔ U : Subgroup X) : Set X) :=
    mem_normalizer_of_conj_mem fun y hy => H.K_conj_E hk hy
  exact mul_mem (mul_mem hkN hxN) (inv_mem hkN)

theorem cent_R1 (H : Hyp156 M n L D K J Mo V U Y) {k : X} (hk : k ∈ K) (hk1 : k ≠ 1) {x : X}
    (hx : x ∈ R1 V Mo U) (hkx : k * x = x * k) : x ∈ U := by
  obtain ⟨hxV, hxN⟩ := mem_inf.mp hx
  have hxU : x ∈ normalizer (U : Set X) := by
    refine mem_normalizer_of_conj_mem fun u hu => ?_
    have h1 : x * u * x⁻¹ ∈ Mo ⊔ U := (mem_normalizer_iff.mp hxN u).mp (mem_sup_right hu)
    have hku : k * u = u * k := (H.F.J_comm (H.U_le hu) (H.F.K_le_L hk)).symm
    have h2 : k * (x * u * x⁻¹) = (x * u * x⁻¹) * k := by
      have hxk : x⁻¹ * k = k * x⁻¹ := by
        calc x⁻¹ * k = x⁻¹ * (k * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * k) * x⁻¹ := by rw [hkx]
          _ = k * x⁻¹ := by group
      calc k * (x * u * x⁻¹) = (k * x) * u * x⁻¹ := by group
        _ = x * (k * u) * x⁻¹ := by rw [hkx]; group
        _ = x * u * (k * x⁻¹) := by rw [hku]; group
        _ = x * u * (x⁻¹ * k) := by rw [hxk]
        _ = (x * u * x⁻¹) * k := by group
    exact H.cent_E hk hk1 h1 h2
  have hxE := H.NV_L hxV (H.mem_N_U_iff.mp hxU)
  exact H.cent_E hk hk1 hxE hkx

theorem exists_commute_pow_mem_coset {k : X} (hk1 : k ≠ 1) (hkodd : Odd (orderOf k))
    {N : Subgroup X} (hN : IsPGroup 2 N) (hkN : ∀ m ∈ N, k * m * k⁻¹ ∈ N) {x : X}
    (hx : x⁻¹ * (k * x * k⁻¹) ∈ N) :
    ∃ e : ℕ, k ^ e ≠ 1 ∧ ∃ c : X, x⁻¹ * c ∈ N ∧ k ^ e * c = c * k ^ e := by
  obtain ⟨e, hpr, hdvd, hke⟩ := exists_pow_orderOf_prime hk1
  have hp2 : orderOf (k ^ e) ≠ 2 := by
    intro h2
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hkodd) (even_iff_two_dvd.mpr hdvd)
  have hkjN : ∀ j : ℕ, ∀ m ∈ N, k ^ j * m * (k ^ j)⁻¹ ∈ N := by
    intro j
    induction j with
    | zero => intro m hm; simpa using hm
    | succ j ih =>
      intro m hm
      have := hkN _ (ih m hm)
      have e : k * (k ^ j * m * (k ^ j)⁻¹) * k⁻¹ = k ^ (j + 1) * m * (k ^ (j + 1))⁻¹ := by
        rw [pow_succ']
        group
      rwa [e] at this
  have hinv : ∀ j : ℕ, x⁻¹ * (k ^ j * x * (k ^ j)⁻¹) ∈ N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := hkN _ ih
      have e1 : x⁻¹ * (k ^ (j + 1) * x * (k ^ (j + 1))⁻¹) =
          (x⁻¹ * (k * x * k⁻¹)) * (k * (x⁻¹ * (k ^ j * x * (k ^ j)⁻¹)) * k⁻¹) := by
        rw [pow_succ']
        group
      rw [e1]
      exact mul_mem hx h1
  obtain ⟨c, hc, hcomm⟩ := exists_commute_mem_coset hpr hp2
    (isPGroup_zpowers_of_orderOf rfl) hN (hkjN e) (hinv e)
  exact ⟨e, hke, c, hc, hcomm⟩

omit [Finite X] in
theorem odd_orderOf_K (H : Hyp156 M n L D K J Mo V U Y) {k : X} (hk : k ∈ K) :
    Odd (orderOf k) := by
  have := orderOf_dvd_natCard (⟨k, hk⟩ : ↥K)
  rw [Subgroup.orderOf_mk] at this
  exact Odd.of_dvd_nat H.F.odd_card_K this

omit [Finite X] in
theorem pow_mem_K {k : X} (hk : k ∈ K) (e : ℕ) : k ^ e ∈ K := pow_mem hk e

theorem free_R1 (H : Hyp156 M n L D K J Mo V U Y) {k : X} (hk : k ∈ K) (hk1 : k ≠ 1) {x : X}
    (hx : x ∈ R1 V Mo U) (hxk : x⁻¹ * (k * x * k⁻¹) ∈ Mo ⊔ U) : x ∈ Mo ⊔ U := by
  have hEP : IsPGroup 2 ↥(Mo ⊔ U) := H.F.V_pgroup.to_le H.E_le_V
  obtain ⟨e, hke, c, hc, hcomm⟩ := exists_commute_pow_mem_coset hk1 (H.odd_orderOf_K hk) hEP
    (fun m hm => H.K_conj_E hk hm) hxk
  have hcR : c ∈ R1 V Mo U := by
    have e1 : c = x * (x⁻¹ * c) := by group
    rw [e1]
    exact mul_mem hx (H.E_le_R1 hc)
  have hcU := H.cent_R1 (pow_mem hk e) hke hcR hcomm
  have e1 : x = c * (x⁻¹ * c)⁻¹ := by group
  rw [e1]
  exact mul_mem (mem_sup_right hcU) (inv_mem hc)

end Hyp156

namespace Hyp156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V U Y : Subgroup X}

theorem E_ne_R1 (H : Hyp156 M n L D K J Mo V U Y) : (Mo ⊔ U : Subgroup X) ≠ R1 V Mo U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hE
  obtain ⟨g, hgV, hgE, hgN⟩ := exists_mem_normalizer_not_mem H.F.V_pgroup H.E_le_V H.E_ne_V
  exact hgE (hE ▸ mem_inf.mpr ⟨hgV, hgN⟩)

theorem R1_inf_NU (H : Hyp156 M n L D K J Mo V U Y) :
    R1 V Mo U ⊓ normalizer (U : Set X) = Mo ⊔ U := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgR, hgN⟩ := mem_inf.mp hg
    exact H.NV_L (mem_inf.mp hgR).1 (H.mem_N_U_iff.mp hgN)
  · refine le_inf H.E_le_R1 (fun e he => mem_normalizer_of_conj_mem fun x hx => ?_)
    rw [H.E_comm he (mem_sup_right hx), mul_inv_cancel_right]
    exact hx

omit [Finite X] in
theorem index_dvd_card {A B : Subgroup X} (hAB : A ≤ B) :
    (A.subgroupOf B).index ∣ Nat.card B :=
  Dvd.intro _ (index_mul_card hAB)

theorem index_R1 (H : Hyp156 M n L D K J Mo V U Y) :
    ((Mo ⊔ U : Subgroup X).subgroupOf (R1 V Mo U)).index = 2 ^ n := by
  set q₁ := ((Mo ⊔ U : Subgroup X).subgroupOf (R1 V Mo U)).index with hq₁
  have hdvd := card_dvd_index_sub_one (A := K) H.E_le_R1 (fun k hk x hx => H.K_conj_R1 hk hx)
    (fun k hk x hx => H.K_conj_E hk hx) (fun k hk hk1 x hx hxk => H.free_R1 hk hk1 hx hxk)
  rw [H.F.card_K] at hdvd
  have hR1P : IsPGroup 2 (R1 V Mo U) := H.F.V_pgroup.to_le inf_le_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hR1P.exists_card_eq
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (ha ▸ index_dvd_card H.E_le_R1)
  rw [← hq₁] at hb hdvd
  have hq₁1 : q₁ ≠ 1 := by
    intro h1
    apply H.E_ne_R1
    have h2 := index_mul_card H.E_le_R1
    rw [← hq₁, h1, one_mul] at h2
    exact eq_of_le_of_card_ge H.E_le_R1 h2.symm.le
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hq₁1 (by rw [hb, pow_zero])
  have hq := H.four_le_q
  have hlow : 2 ^ n ≤ q₁ := by
    have h2 : 2 ≤ q₁ := by
      rw [hb]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hb0)
    have h3 := Nat.le_of_dvd (by omega) hdvd
    omega
  have hsub : conjSet (R1 V Mo U) U ∪ (Mo : Set X) ⊆ ((Mo ⊔ U : Subgroup X) : Set X) := by
    refine Set.union_subset ?_ (fun x hx => mem_sup_left hx)
    rintro _ ⟨g, hg, a, ha, -, rfl⟩
    exact (mem_normalizer_iff.mp (mem_inf.mp hg).2 a).mp (mem_sup_right ha)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hMo : (Mo : Set X).ncard = 2 ^ n := by
    rw [← Nat.card_coe_set_eq]
    exact H.F.card_Mo
  have hE : ((Mo ⊔ U : Subgroup X) : Set X).ncard = 2 ^ n * Nat.card U := by
    rw [← Nat.card_coe_set_eq]
    exact H.card_E
  have hR1M : R1 V Mo U ≤ M := inf_le_left.trans H.F.V_le
  rw [Set.ncard_union_eq (H.conjSet_disjoint_Mo hR1M) (Set.toFinite _) (Set.toFinite _), hMo,
    hE, conjSet, ncard_conj_TI (H.TI_of _), H.R1_inf_NU, ← hq₁] at h1
  have hr := H.two_le_card_U
  set r := Nat.card U
  have h4 : 2 ^ n * r = 2 ^ n * (r - 1) + 2 ^ n := by
    rw [Nat.mul_sub, mul_one]
    have : 2 ^ n ≤ 2 ^ n * r := Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [h4] at h1
  have h5 : q₁ * (r - 1) ≤ 2 ^ n * (r - 1) := by omega
  have hup : q₁ ≤ 2 ^ n := Nat.le_of_mul_le_mul_right h5 (by omega)
  exact le_antisymm hup hlow

theorem card_R1 (H : Hyp156 M n L D K J Mo V U Y) :
    Nat.card (R1 V Mo U) = 2 ^ (2 * n) * Nat.card U := by
  rw [← index_mul_card H.E_le_R1, H.index_R1, H.card_E, two_mul, pow_add, mul_assoc]

theorem inf_Y_eq_bot (H : Hyp156 M n L D K J Mo V U Y) {P : Subgroup X} (hP : IsPGroup 2 P) :
    P ⊓ Y = ⊥ :=
  eq_bot_of_forall_sq (hP.to_le inf_le_left) fun _ hx hx2 =>
    Facts15.eq_one_of_mem_odd H.Y_odd (mem_inf.mp hx).2 hx2

theorem card_J (H : Hyp156 M n L D K J Mo V U Y) : Nat.card J = Nat.card U * Nat.card Y := by
  have hJ : J = U ⊔ Y := by
    refine le_antisymm (fun j hj => ?_) (sup_le H.U_le H.Y_le)
    obtain ⟨x, hx, y, hy, rfl⟩ := H.JUY j hj
    exact mul_mem (mem_sup_left hx) (mem_sup_right hy)
  rw [hJ]
  refine card_sup_of_normal (fun y hy x hx => ?_) (H.inf_Y_eq_bot H.U_pgroup)
  refine H.U_two _ (mul_mem (mul_mem (H.Y_le hy) (H.U_le hx)) (inv_mem (H.Y_le hy))) ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxP : IsPGroup 2 (zpowers x) := H.U_pgroup.to_le (zpowers_le.mpr hx)
  obtain ⟨k, hk⟩ := hxP.exists_card_eq
  refine IsPGroup.of_card (n := k) ?_
  rw [Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ← Nat.card_zpowers, hk]

theorem card_V_le (H : Hyp156 M n L D K J Mo V U Y) : Nat.card V ≤ 2 ^ (3 * n) * Nat.card U := by
  have hC : centralizer (Mo : Set X) = V ⊔ Y := by
    refine le_antisymm (fun g hg => ?_) (sup_le H.F.V_le_C0 (H.Y_le.trans H.F.J_le_C0))
    obtain ⟨v, hv, y, hy, rfl⟩ := H.C0_eq g hg
    exact mul_mem (mem_sup_left hv) (mem_sup_right hy)
  have hcard : Nat.card (centralizer (Mo : Set X)) = Nat.card V * Nat.card Y := by
    rw [hC]
    exact card_sup_of_normal (fun y hy v hv => H.F.V_normal y (H.F.J_le_M (H.Y_le hy)) v hv)
      (H.inf_Y_eq_bot H.F.V_pgroup)
  have h := H.F.card_C0_dvd
  rw [hcard, H.card_J, ← mul_assoc] at h
  exact Nat.le_of_dvd (Nat.mul_pos (by positivity) Nat.card_pos)
    (Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h)

end Hyp156

namespace Hyp156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V U Y : Subgroup X}

omit [Finite X] in
theorem M_inf_NL (H : Hyp156 M n L D K J Mo V U Y) :
    M ⊓ normalizer (L : Set X) = Mo ⊔ D := by
  rw [← H.M_inf_NU]
  ext g
  simp only [mem_inf]
  exact ⟨fun h => ⟨h.1, H.NU h.2⟩, fun h => ⟨h.1, H.mem_N_U_iff.mp h.2⟩⟩

theorem R1_normal_and_big (H : Hyp156 M n L D K J Mo V U Y) :
    (∀ g ∈ M, ∀ x ∈ R1 V Mo U, g * x * g⁻¹ ∈ R1 V Mo U) ∧
    (R1 V Mo U ≠ V → Nat.card V = 2 ^ (3 * n) * Nat.card U ∧
      (∀ g ∈ M, ∃ v ∈ V, ∃ d ∈ D, g = v * d) ∧
      ∀ k ∈ K, k ≠ 1 → ∀ x ∈ V, x⁻¹ * (k * x * k⁻¹) ∈ R1 V Mo U → x ∈ R1 V Mo U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hR : R1 V Mo U = V
  · refine ⟨fun g hg x hx => ?_, fun h => absurd hR h⟩
    rw [hR] at hx ⊢
    exact H.F.V_normal g hg x hx
  set R := R1 V Mo U with hRdef
  set N₁ : Subgroup X := V ⊓ normalizer (R : Set X) with hN₁
  have hRN₁ : R ≤ N₁ := le_inf inf_le_left le_normalizer
  have hRP : IsPGroup 2 R := H.F.V_pgroup.to_le inf_le_left
  have hfree : ∀ k ∈ K, k ≠ 1 → ∀ x ∈ N₁, x⁻¹ * (k * x * k⁻¹) ∈ R → x ∈ R := by
    intro k hk hk1 x hx hxk
    obtain ⟨e, hke, c, hc, hcomm⟩ := exists_commute_pow_mem_coset hk1 (H.odd_orderOf_K hk) hRP
      (fun m hm => H.K_conj_R1 hk hm) hxk
    have hcN : c ∈ N₁ := by
      have e1 : c = x * (x⁻¹ * c) := by group
      rw [e1]
      exact mul_mem hx (hRN₁ hc)
    have hcU : c ∈ normalizer (U : Set X) := by
      refine mem_normalizer_of_conj_mem fun y hy => ?_
      have hyR : c * y * c⁻¹ ∈ R :=
        (mem_normalizer_iff.mp (mem_inf.mp hcN).2 y).mp (H.E_le_R1 (mem_sup_right hy))
      have hky : k ^ e * y = y * k ^ e :=
        (H.F.J_comm (H.U_le hy) (H.F.K_le_L (pow_mem hk e))).symm
      refine H.cent_R1 (pow_mem hk e) hke hyR ?_
      have hck : c⁻¹ * k ^ e = k ^ e * c⁻¹ := by
        calc c⁻¹ * k ^ e = c⁻¹ * (k ^ e * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * k ^ e) * c⁻¹ := by rw [hcomm]
          _ = k ^ e * c⁻¹ := by group
      calc k ^ e * (c * y * c⁻¹) = (k ^ e * c) * y * c⁻¹ := by group
        _ = c * (k ^ e * y) * c⁻¹ := by rw [hcomm]; group
        _ = c * y * (k ^ e * c⁻¹) := by rw [hky]; group
        _ = c * y * (c⁻¹ * k ^ e) := by rw [hck]
        _ = c * y * c⁻¹ * k ^ e := by group
    have hcE := H.NV_L (mem_inf.mp hcN).1 (H.mem_N_U_iff.mp hcU)
    have e1 : x = c * (x⁻¹ * c)⁻¹ := by group
    rw [e1]
    exact mul_mem (H.E_le_R1 hcE) (inv_mem hc)
  have hdvd := card_dvd_index_sub_one (A := K) hRN₁
    (fun k hk x hx => mem_inf.mpr ⟨H.K_conj_V hk (mem_inf.mp hx).1,
      mul_mem (mul_mem (mem_normalizer_of_conj_mem fun y hy => H.K_conj_R1 hk hy)
        (mem_inf.mp hx).2) (inv_mem (mem_normalizer_of_conj_mem fun y hy => H.K_conj_R1 hk hy))⟩)
    (fun k hk x hx => H.K_conj_R1 hk hx) hfree
  rw [H.F.card_K] at hdvd
  have hne : R ≠ N₁ := by
    intro hRN
    obtain ⟨g, hgV, hgR, hgN⟩ := exists_mem_normalizer_not_mem H.F.V_pgroup inf_le_left hR
    have hg : g ∈ N₁ := mem_inf.mpr ⟨hgV, hgN⟩
    rw [← hRN] at hg
    exact hgR hg
  set i₁ := (R.subgroupOf N₁).index with hi₁
  have hN₁P : IsPGroup 2 N₁ := H.F.V_pgroup.to_le inf_le_left
  obtain ⟨a, ha⟩ := hN₁P.exists_card_eq
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (ha ▸ index_dvd_card hRN₁)
  rw [← hi₁] at hb
  have hi1 : i₁ ≠ 1 := by
    intro h1
    apply hne
    have h2 := index_mul_card hRN₁
    rw [← hi₁, h1, one_mul] at h2
    exact eq_of_le_of_card_ge hRN₁ h2.symm.le
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hi1 (by rw [hb, pow_zero])
  have hq := H.four_le_q
  have hlow : 2 ^ n ≤ i₁ := by
    have h2 : 2 ≤ i₁ := by
      rw [hb]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hb0)
    have h3 := Nat.le_of_dvd (by omega) hdvd
    omega
  have hN₁card : 2 ^ (3 * n) * Nat.card U ≤ Nat.card N₁ := by
    rw [← index_mul_card hRN₁, ← hi₁, hRdef, H.card_R1]
    calc 2 ^ (3 * n) * Nat.card U = 2 ^ n * (2 ^ (2 * n) * Nat.card U) := by
          rw [← mul_assoc, ← pow_add]
          ring_nf
      _ ≤ i₁ * (2 ^ (2 * n) * Nat.card U) := Nat.mul_le_mul_right _ hlow
  have hVle := H.card_V_le
  have hN₁V : N₁ = V := eq_of_le_of_card_ge inf_le_left (hVle.trans hN₁card)
  have hVcard : Nat.card V = 2 ^ (3 * n) * Nat.card U :=
    le_antisymm hVle (hN₁card.trans (hN₁V ▸ le_rfl))
  have hMN : M ⊓ normalizer (L : Set X) ≤ normalizer (V : Set X) := fun g hg =>
    mem_normalizer_of_conj_mem fun v hv => H.F.V_normal g (mem_inf.mp hg).1 v hv
  have h1 := Sec128.card_sup_mul_card_inf_of_le_normalizer hMN
  have hinf : V ⊓ (M ⊓ normalizer (L : Set X)) = Mo ⊔ U := by
    apply le_antisymm
    · intro g hg
      exact H.NV_L (mem_inf.mp hg).1 (mem_inf.mp (mem_inf.mp hg).2).2
    · exact le_inf H.E_le_V (le_inf H.E_le_M H.E_le_N)
  have hcMN : Nat.card ↥(M ⊓ normalizer (L : Set X)) = 2 ^ n * Nat.card D := by
    rw [H.M_inf_NL, H.card_Mo_sup_D]
  rw [hinf, H.card_E, hcMN, hVcard] at h1
  have hsupM : V ⊔ (M ⊓ normalizer (L : Set X)) = M := by
    refine eq_of_le_of_card_ge (sup_le H.F.V_le inf_le_left) ?_
    rw [H.F.card_M]
    have hpos : 0 < 2 ^ n * Nat.card U := Nat.mul_pos (by positivity) Nat.card_pos
    have h2 : Nat.card ↥(V ⊔ (M ⊓ normalizer (L : Set X))) * (2 ^ n * Nat.card U) =
        2 ^ (3 * n) * Nat.card D * (2 ^ n * Nat.card U) := by
      rw [h1]
      ring
    exact (Nat.eq_of_mul_eq_mul_right hpos h2).ge
  have hdecomp : ∀ g ∈ M, ∃ v ∈ V, ∃ h ∈ M ⊓ normalizer (L : Set X), g = v * h := by
    intro g hg
    rw [← hsupM] at hg
    exact exists_mul_of_sup_eq (fun h hh v hv => H.F.V_normal h (mem_inf.mp hh).1 v hv) hg
  refine ⟨fun g hg x hx => ?_, fun _ => ⟨hVcard, fun g hg => ?_, fun k hk hk1 x hx hxk => ?_⟩⟩
  · obtain ⟨v, hv, h, hh, rfl⟩ := hdecomp g hg
    obtain ⟨hhM, hhN⟩ := mem_inf.mp hh
    have hhE : h ∈ normalizer ((Mo ⊔ U : Subgroup X) : Set X) :=
      mem_normalizer_of_conj_mem fun y hy => conj_mem_sup (fun m hm => H.F.Mo_normal h hhM m hm)
        (fun u hu => (mem_normalizer_iff.mp (H.NU hhN) u).mp hu) hy
    have hhx : h * x * h⁻¹ ∈ R := by
      obtain ⟨hxV, hxN⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨H.F.V_normal h hhM x hxV, mul_mem (mul_mem hhE hxN) (inv_mem hhE)⟩
    have hvN : v ∈ normalizer (R : Set X) := (mem_inf.mp (hN₁V.symm ▸ hv : v ∈ N₁)).2
    have e1 : v * h * x * (v * h)⁻¹ = v * (h * x * h⁻¹) * v⁻¹ := by group
    rw [e1]
    exact (mem_normalizer_iff.mp hvN _).mp hhx
  · obtain ⟨v, hv, h, hh, rfl⟩ := hdecomp g hg
    obtain ⟨m, hm, d, hd, rfl⟩ := H.F.NM_eq h (mem_inf.mp hh).1 (mem_inf.mp hh).2
    exact ⟨v * m, mul_mem hv (H.F.Mo_le_V hm), d, hd, by group⟩
  · exact hfree k hk hk1 x (hN₁V.symm ▸ hx) hxk

end Hyp156

end CFSG.GH74.Uniqueness
