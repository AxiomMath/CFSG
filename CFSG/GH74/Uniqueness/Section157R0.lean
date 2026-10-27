module

public import CFSG.GH74.Uniqueness.Section156Defs
public import CFSG.GH74.Uniqueness.Section15Derived
public import CFSG.GH74.Uniqueness.Section15Aux3
public import CFSG.GH74.Uniqueness.Section157Norm

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

namespace Sec157

private theorem exists_pow_prime_order {a : X} (ha : a ≠ 1) :
    ∃ e : ℕ, (orderOf (a ^ e)).Prime ∧ orderOf (a ^ e) ∣ orderOf a ∧ a ^ e ≠ 1 := by
  have h1 : orderOf a ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨r, hr, hra⟩ := Nat.exists_prime_and_dvd h1
  have hord := orderOf_pow_orderOf_div (orderOf_pos a).ne' hra
  refine ⟨orderOf a / r, ?_, ?_, ?_⟩
  · rw [hord]
    exact hr
  · rw [hord]
    exact hra
  · intro h
    rw [h, orderOf_one] at hord
    exact hr.one_lt.ne hord

omit [Finite X] in
private theorem isPGroup_zpowers_of_orderOf' {p : ℕ} {x : X} (hx : orderOf x = p) :
    IsPGroup p (zpowers x) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, hx, pow_one]

omit [Finite X] in
theorem pow_fix_coset {N : Subgroup X} {k x : X} (hkN : ∀ m ∈ N, k * m * k⁻¹ ∈ N)
    (hfix : x⁻¹ * (k * x * k⁻¹) ∈ N) (j : ℕ) : x⁻¹ * (k ^ j * x * (k ^ j)⁻¹) ∈ N := by
  induction j with
  | zero => simp [N.one_mem]
  | succ j ih =>
    have e : x⁻¹ * (k ^ (j + 1) * x * (k ^ (j + 1))⁻¹) =
        (x⁻¹ * (k * x * k⁻¹)) * (k * (x⁻¹ * (k ^ j * x * (k ^ j)⁻¹)) * k⁻¹) := by
      rw [pow_succ']
      group
    rw [e]
    exact N.mul_mem hfix (hkN _ ih)

omit [Finite X] in
theorem card_mul_index_subgroupOf {N P : Subgroup X} (h : N ≤ P) :
    Nat.card N * (N.subgroupOf P).index = Nat.card P := by
  rw [← Nat.card_congr (subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.card_mul_index (N.subgroupOf P)

omit [Finite X] in
theorem ncard_coe_subgroup (H : Subgroup X) : (H : Set X).ncard = Nat.card H :=
  (Nat.card_coe_set_eq (H : Set X)).symm

omit [Finite X] in
theorem comm_of_three_sq {x y : X} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y * (x * y) = 1) :
    x * y = y * x := by
  have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [mul_inv_rev, h1, h2] at h3
  exact h3.symm

end Sec157

namespace Conf156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V R₁ : Subgroup X} {u : X}

omit [Finite X] in
theorem u_inv (C : Conf156 M n L D K J Mo V R₁ u) : u⁻¹ = u := inv_eq_of_mul_eq_one_right C.u_sq

omit [Finite X] in
theorem u_not_mem_Mo (C : Conf156 M n L D K J Mo V R₁ u) : u ∉ Mo := fun h =>
  C.u_ne (C.F.eq_one_of_mem_L_J (C.F.Mo_le_L h) C.u_mem_J)

omit [Finite X] in
theorem D_comm_u (C : Conf156 M n L D K J Mo V R₁ u) {d : X} (hd : d ∈ D) : d * u * d⁻¹ = u := by
  rcases C.J_eq _ (C.F.D_conj_J hd C.u_mem_J) with h | h
  · exact absurd (by simpa using h) C.u_ne
  · exact h

omit [Finite X] in
theorem card_J (C : Conf156 M n L D K J Mo V R₁ u) : Nat.card J = 2 := by
  have hJ : J = zpowers u := by
    apply le_antisymm
    · intro j hj
      rcases C.J_eq j hj with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · exact zpowers_le.mpr C.u_mem_J
  have h2 : orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact C.u_sq) C.u_ne
  rw [hJ, Nat.card_zpowers, h2]

omit [Finite X] in
theorem R₁_le_M (C : Conf156 M n L D K J Mo V R₁ u) : R₁ ≤ M := C.R₁_le.trans C.F.V_le

omit [Finite X] in
theorem four_le (C : Conf156 M n L D K J Mo V R₁ u) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) C.F.two_le

omit [Finite X] in
theorem exists_ne_one_K (C : Conf156 M n L D K J Mo V R₁ u) : ∃ k ∈ K, k ≠ 1 := by
  by_contra h
  have hK : K = ⊥ := (eq_bot_iff_forall K).mpr fun x hx => by_contra fun hx1 => h ⟨x, hx, hx1⟩
  have h1 := C.F.card_K
  rw [hK, card_bot] at h1
  have := C.four_le
  omega

omit [Finite X] in
theorem cent_le_N (C : Conf156 M n L D K J Mo V R₁ u) {w : X} (h : w * u = u * w) :
    w ∈ normalizer (L : Set X) := by
  refine C.F.NY_le (zpowers u) (zpowers_le.mpr C.u_mem_J)
    (fun h0 => C.u_ne (zpowers_eq_bot.mp h0)) ?_
  refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  exact ((Commute.symm (h : Commute w u)).zpow_left i).eq

omit [Finite X] in
theorem sq_mul_Mo (C : Conf156 M n L D K J Mo V R₁ u) {x m : X} (hx : x ∈ V) (hm : m ∈ Mo) :
    x * m * (x * m) = x * x := by
  have hc : x * m = m * x := C.F.V_comm x hx m hm
  have hmm : m * m = 1 := C.F.Mo_sq m hm
  calc x * m * (x * m) = x * (m * x) * m := by group
    _ = x * (x * m) * m := by rw [← hc]
    _ = x * x * (m * m) := by group
    _ = x * x := by rw [hmm, mul_one]

theorem coset_fix (C : Conf156 M n L D K J Mo V R₁ u) {k : X} (hk : k ∈ K) (hk1 : k ≠ 1) {x : X}
    (hx : x ∈ R₁) (hfix : x⁻¹ * (k * x * k⁻¹) ∈ Mo) : x ∈ Mo ∨ u * x ∈ Mo := by
  have F := C.F
  obtain ⟨e, hpr, hdvd, hne⟩ := Sec157.exists_pow_prime_order hk1
  have hk'K : k ^ e ∈ K := K.pow_mem hk e
  have hcardK : orderOf k ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : ↥K)
    rwa [Subgroup.orderOf_mk] at this
  have hp2 : orderOf (k ^ e) ≠ 2 := by
    intro h2
    have h3 : 2 ∣ Nat.card K := h2 ▸ hdvd.trans hcardK
    exact (Nat.not_even_iff_odd.mpr F.odd_card_K) (even_iff_two_dvd.mpr h3)
  have hv : x⁻¹ * (k ^ e * x * (k ^ e)⁻¹) ∈ Mo :=
    Sec157.pow_fix_coset (fun m hm => F.Mo_normal k (F.K_le_M hk) m hm) hfix e
  obtain ⟨c, hc1, hc2⟩ := exists_commute_mem_coset hpr hp2
    (Sec157.isPGroup_zpowers_of_orderOf' rfl) F.Mo_isPGroup
    (fun m hm => F.Mo_normal (k ^ e) (F.K_le_M hk'K) m hm) hv
  have hcR : c ∈ R₁ := by
    have e1 : c = x * (x⁻¹ * c) := by group
    rw [e1]
    exact R₁.mul_mem hx (C.Mo_le_R₁ hc1)
  rcases C.cent_K (k ^ e) hk'K hne c hcR hc2 with h | h
  · left
    rw [h, mul_one] at hc1
    simpa using Mo.inv_mem hc1
  · right
    rw [h] at hc1
    have := Mo.inv_mem hc1
    rwa [mul_inv_rev, inv_inv, C.u_inv] at this

theorem exists_R0 (C : Conf156 M n L D K J Mo V R₁ u) :
    ∃ R₀ : Subgroup X, Mo ≤ R₀ ∧ R₀ ≤ R₁ ∧ u ∉ R₀ ∧ (∀ x ∈ R₁, x ∈ R₀ ∨ u * x ∈ R₀) ∧
      Nat.card R₁ = 2 * Nat.card R₀ ∧ ∀ k ∈ K, ∀ x ∈ R₀, k * x * k⁻¹ ∈ R₀ := by
  have F := C.F
  obtain ⟨k₁, hk₁, hk₁1⟩ := C.exists_ne_one_K
  obtain ⟨R₀, h1, h2, h3, h4, h5, h6⟩ := Sec157.exists_invariant_index_two (M := M) (N := Mo)
    (P := R₁) (A := K) (u := u) F.Mo_normal C.R₁_normal C.Mo_le_R₁ C.R₁_le_M F.K_le_M
    F.odd_card_K
    (Sec157.comm_mem_of_sq_mem (fun g hg x hx => F.Mo_normal g (C.R₁_le_M hg) x hx) C.sq_R₁)
    C.u_mem_R₁ C.u_not_mem_Mo (by rw [C.u_sq]; exact Mo.one_mem)
    (fun a ha => C.D_comm_u (F.K_le_D ha))
    (fun x hx hfix => C.coset_fix hk₁ hk₁1 hx (hfix k₁ hk₁))
  exact ⟨R₀, h1, h2, h3, h4, h5, fun k hk x hx =>
    h6 k (F.K_le_M hk) (fun a ha => K.mul_mem (K.mul_mem hk ha) (K.inv_mem hk)) x hx⟩

structure R0Data (M K Mo R₁ R₀ : Subgroup X) (n : ℕ) (u : X) : Prop where
  Mo_le : Mo ≤ R₀
  le_R₁ : R₀ ≤ R₁
  u_not_mem : u ∉ R₀
  cases : ∀ x ∈ R₁, x ∈ R₀ ∨ u * x ∈ R₀
  card_R₀ : Nat.card R₀ = 2 ^ (2 * n)
  K_conj : ∀ k ∈ K, ∀ x ∈ R₀, k * x * k⁻¹ ∈ R₀
  normal : ∀ g ∈ M, ∀ x ∈ R₀, g * x * g⁻¹ ∈ R₀
  abelian : ∀ a ∈ R₀, ∀ b ∈ R₀, a * b = b * a
  sq_ne : ∀ x ∈ R₀, x ∉ Mo → x * x ≠ 1
  inv : ∀ x ∈ R₀, u * x * u⁻¹ = x⁻¹
  invol : ∀ x ∈ R₁, x ∉ R₀ → x * x = 1

theorem exists_R0Data (C : Conf156 M n L D K J Mo V R₁ u) :
    ∃ R₀ : Subgroup X, R0Data M K Mo R₁ R₀ n u := by
  have F := C.F
  obtain ⟨R₀, hMo, hle, hu, hcases, hcard, hKc⟩ := C.exists_R0
  have hn4 := C.four_le
  have hcardR₀ : Nat.card R₀ = 2 ^ (2 * n) := by
    have h := C.card_R₁
    rw [hcard, pow_succ] at h
    omega
  have hfree : ∀ k ∈ K, k ≠ 1 → ∀ x ∈ R₀, x⁻¹ * (k * x * k⁻¹) ∈ Mo → x ∈ Mo := by
    intro k hk hk1 x hx hxk
    rcases C.coset_fix hk hk1 (hle hx) hxk with h | h
    · exact h
    · exact absurd (by simpa using R₀.mul_mem (hMo h) (R₀.inv_mem hx)) hu
  have hindex : (Mo.subgroupOf R₀).index = 2 ^ n := by
    have h := Sec157.card_mul_index_subgroupOf hMo
    rw [F.card_Mo, hcardR₀, two_mul, pow_add] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have htrans : ∀ x ∈ R₀, x ∉ Mo → ∀ y ∈ R₀, y ∉ Mo → ∃ a ∈ K, y⁻¹ * (a * x * a⁻¹) ∈ Mo :=
    trans_of_free_of_card hMo hKc (fun a ha x hx => F.Mo_normal a (F.K_le_M ha) x hx) hfree
      (by rw [hindex, F.card_K])
  have hsq_iff : ∀ a ∈ R₀, a ∉ Mo → ∀ b ∈ R₀, b ∉ Mo → a * a = 1 → b * b = 1 := by
    intro a ha haMo b hb hbMo ha2
    obtain ⟨k, hk, hkab⟩ := htrans a ha haMo b hb hbMo
    obtain ⟨m, hm, e1⟩ : ∃ m ∈ Mo, k * a * k⁻¹ = b * m :=
      ⟨b⁻¹ * (k * a * k⁻¹), hkab, by group⟩
    have h2 : (k * a * k⁻¹) * (k * a * k⁻¹) = 1 := by
      calc (k * a * k⁻¹) * (k * a * k⁻¹) = k * (a * a) * k⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    rw [e1, C.sq_mul_Mo (C.R₁_le (hle hb)) hm] at h2
    exact h2
  have hex : ∃ a ∈ R₀, a ∉ Mo := by
    by_contra h
    have hle' : R₀ ≤ Mo := fun x hx => by_contra fun hxn => h ⟨x, hx, hxn⟩
    have h1 := Subgroup.card_le_of_le hle'
    rw [hcardR₀, F.card_Mo] at h1
    have h2 : 2 ^ n < 2 ^ (2 * n) :=
      Nat.pow_lt_pow_right (by norm_num) (by have := F.two_le; omega)
    omega
  have hno : ∀ a ∈ R₀, a ∉ Mo → a * a ≠ 1 := by
    intro a ha haMo ha2
    have hall : ∀ x ∈ R₀, x * x = 1 := by
      intro x hx
      by_cases hxMo : x ∈ Mo
      · exact F.Mo_sq x hxMo
      · exact hsq_iff a ha haMo x hx hxMo ha2
    have habel : ∀ x ∈ R₀, ∀ y ∈ R₀, x * y = y * x := fun x hx y hy =>
      Sec157.comm_of_three_sq (hall x hx) (hall y hy) (hall _ (R₀.mul_mem hx hy))
    obtain ⟨g, hg, hga⟩ := C.inv_R₁ a (hle ha) haMo ha2
    have hu' : u = g⁻¹ * a * g := by rw [← hga]; group
    let A₀ : Subgroup X := R₀.map (MulAut.conj g⁻¹).toMonoidHom
    have hA₀card : Nat.card A₀ = Nat.card R₀ :=
      card_map_of_injective (MulAut.conj g⁻¹).injective
    have hA₀N : A₀ ≤ normalizer (L : Set X) := by
      rintro _ ⟨y, hy, rfl⟩
      apply C.cent_le_N
      have hya : y * a = a * y := habel y hy a ha
      show g⁻¹ * y * g⁻¹⁻¹ * u = u * (g⁻¹ * y * g⁻¹⁻¹)
      calc g⁻¹ * y * g⁻¹⁻¹ * u = g⁻¹ * (y * a) * g := by rw [hu']; group
        _ = g⁻¹ * (a * y) * g := by rw [hya]
        _ = u * (g⁻¹ * y * g⁻¹⁻¹) := by rw [hu']; group
    have hA₀sq : ∀ w ∈ A₀, w * w = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      show (g⁻¹ * y * g⁻¹⁻¹) * (g⁻¹ * y * g⁻¹⁻¹) = 1
      calc (g⁻¹ * y * g⁻¹⁻¹) * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (y * y) * g := by group
        _ = 1 := by rw [hall y hy]; group
    have hrank := F.rank_le A₀ hA₀N hA₀sq
    have hJ : Nat.card ↥(A₀ ⊓ J) ≤ 2 := (card_le_of_le inf_le_right).trans C.card_J.le
    have h1 : 2 ^ n * 2 ^ n ≤ 2 ^ n * 2 :=
      calc 2 ^ n * 2 ^ n = Nat.card A₀ := by rw [hA₀card, hcardR₀, two_mul, pow_add]
        _ ≤ 2 ^ n * Nat.card ↥(A₀ ⊓ J) := hrank
        _ ≤ 2 ^ n * 2 := Nat.mul_le_mul_left _ hJ
    have h2 := Nat.le_of_mul_le_mul_left h1 (by positivity)
    omega
  have hsub : {x : X | x ∈ R₁ ∧ x * x ≠ 1} ⊆ (R₀ : Set X) \ (Mo : Set X) := by
    have hT : (R₀ : Set X) \ (Mo : Set X) ⊆ {x : X | x ∈ R₁ ∧ x * x ≠ 1} :=
      fun x hx => ⟨hle hx.1, hno x hx.1 hx.2⟩
    have hcardT : ((R₀ : Set X) \ (Mo : Set X)).ncard = 2 ^ n * (2 ^ n - 1) := by
      rw [Set.ncard_sdiff (fun x hx => hMo hx) (Set.toFinite _), Sec157.ncard_coe_subgroup,
        Sec157.ncard_coe_subgroup, hcardR₀, F.card_Mo, two_mul, pow_add, Nat.mul_sub_one]
    have hS : ({x : X | x ∈ R₁ ∧ x * x ≠ 1}).ncard ≤ ((R₀ : Set X) \ (Mo : Set X)).ncard := by
      rw [C.card_four, hcardT]
    exact (Set.eq_of_subset_of_ncard_le hT hS (Set.toFinite _)).symm.subset
  have hS : ∀ x ∈ R₁, x * x ≠ 1 → x ∈ R₀ ∧ x ∉ Mo := fun x hx hx2 => hsub ⟨hx, hx2⟩
  have hinvol : ∀ x ∈ R₁, x ∉ R₀ → x * x = 1 := fun x hx hxR₀ =>
    by_contra fun h => hxR₀ (hS x hx h).1
  have hinv : ∀ x ∈ R₀, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    have hux : u * x ∈ R₁ := R₁.mul_mem C.u_mem_R₁ (hle hx)
    have huxn : u * x ∉ R₀ := fun h => hu (by simpa using R₀.mul_mem h (R₀.inv_mem hx))
    have h2 := hinvol _ hux huxn
    rw [C.u_inv]
    have h3 : u * x * u * x = 1 := by simpa [mul_assoc] using h2
    exact eq_inv_of_mul_eq_one_left h3
  have habel : ∀ a ∈ R₀, ∀ b ∈ R₀, a * b = b * a := by
    intro a ha b hb
    have h1 := hinv (a * b) (R₀.mul_mem ha hb)
    have h2 : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
    rw [h2, hinv a ha, hinv b hb, mul_inv_rev] at h1
    have h3 := congrArg (fun z => z⁻¹) h1
    simpa using h3.symm
  have hnormal : ∀ g ∈ M, ∀ x ∈ R₀, g * x * g⁻¹ ∈ R₀ := by
    intro g hg x hx
    by_cases hxMo : x ∈ Mo
    · exact hMo (F.Mo_normal g hg x hxMo)
    · have h1 : g * x * g⁻¹ ∈ R₁ := C.R₁_normal g hg x (hle hx)
      have h2 : (g * x * g⁻¹) * (g * x * g⁻¹) ≠ 1 := by
        intro h
        apply hno x hx hxMo
        have e : x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
        rw [e, h]
        group
      exact (hS _ h1 h2).1
  exact ⟨R₀, hMo, hle, hu, hcases, hcardR₀, hKc, hnormal, habel, hno, hinv, hinvol⟩

end Conf156

end CFSG.GH74.Uniqueness
