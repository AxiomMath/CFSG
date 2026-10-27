module

public import CFSG.GH74.Uniqueness.SU.SU13TC6A

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

section Alg

variable {G : Type} [Group G]

theorem conj_trivial_of_odd {z y₀ : G} (hz : z * z = 1) (hy₀ : Odd (orderOf y₀))
    (S : Set G) (hS : ∀ y ∈ S, y₀⁻¹ * y * y₀ ∈ S) (hzS : ∀ y ∈ S, z * y * z⁻¹ = y₀⁻¹ * y * y₀) :
    ∀ y ∈ S, z * y * z⁻¹ = y := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h2 : ∀ y ∈ S, y₀⁻¹ * (y₀⁻¹ * y * y₀) * y₀ = y := by
    intro y hy
    have h1 := hzS y hy
    have h3 := hzS _ (hS y hy)
    have h4 : z * (y₀⁻¹ * y * y₀) * z⁻¹ = y := by
      rw [← h1, hzi]
      calc z * (z * y * z) * z = (z * z) * y * (z * z) := by group
        _ = y := by rw [hz]; group
    exact h3.symm.trans h4
  have hcomm2 : ∀ y ∈ S, y₀ ^ 2 * y = y * y₀ ^ 2 := by
    intro y hy
    have := h2 y hy
    calc y₀ ^ 2 * y = y₀ ^ 2 * (y₀⁻¹ * (y₀⁻¹ * y * y₀) * y₀) := by rw [this]
      _ = y * y₀ ^ 2 := by simp only [pow_two]; group
  obtain ⟨k, hk⟩ := hy₀
  have hy₀' : (y₀ ^ 2) ^ (k + 1) = y₀ := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf y₀ + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  intro y hy
  rw [hzS y hy]
  have hc : Commute (y₀ ^ 2) y := hcomm2 y hy
  have hy' : y₀ * y = y * y₀ := by
    have := (hc.pow_left (k + 1)).eq
    rw [hy₀'] at this
    exact this
  calc y₀⁻¹ * y * y₀ = y₀⁻¹ * (y * y₀) := by group
    _ = y₀⁻¹ * (y₀ * y) := by rw [hy']
    _ = y := by group

end Alg

theorem factorization_three_12 : (3 ^ 7 * 12).factorization 3 = 8 := by
  rw [show 3 ^ 7 * 12 = 3 ^ 8 * 4 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_three]
  have h4 : (4 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h4]

theorem factorization_three_60 : (3 ^ 7 * 60).factorization 3 = 8 := by
  rw [show 3 ^ 7 * 60 = 3 ^ 8 * 20 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_three]
  have h4 : (20 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h4]

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem mem_cent_comap {C : Subgroup G} {d : ↥C} :
    d ∈ (centralizer ((oc C : Subgroup G) : Set G)).comap C.subtype ↔
      ∀ y ∈ oc C, (d : G) * y = y * (d : G) := by
  rw [Subgroup.mem_comap, mem_centralizer_iff]
  exact ⟨fun h y hy => (h y hy).symm, fun h y hy => (h y hy).symm⟩

omit [Finite G] in
theorem cent_comap_normal (C : Subgroup G) :
    ((centralizer ((oc C : Subgroup G) : Set G)).comap C.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_cent_comap] at hn ⊢
  intro y hy
  have hy' : (g : G)⁻¹ * y * g ∈ oc C := by
    have := conj_mem_oc (X := C) (g := (g : G)⁻¹) (C.inv_mem g.2) hy
    simpa using this
  have h1 := hn _ hy'
  change (g : G) * n * (g : G)⁻¹ * y = y * ((g : G) * n * (g : G)⁻¹)
  calc (g : G) * n * (g : G)⁻¹ * y = (g : G) * (n * ((g : G)⁻¹ * y * g)) * (g : G)⁻¹ := by group
    _ = (g : G) * (((g : G)⁻¹ * y * g) * n) * (g : G)⁻¹ := by rw [h1]
    _ = y * ((g : G) * n * (g : G)⁻¹) := by group

theorem false_of_cent_top {C : Subgroup G} {z : G} (hz : orderOf z = 2) (hzC : z ∈ C)
    (htop : ((centralizer ((oc C : Subgroup G) : Set G)).comap C.subtype).map (proj C) = ⊤)
    (hYz : ¬ oc C ≤ centralizer ({z} : Set G)) : False := by
  let D : Subgroup ↥C := (centralizer ((oc C : Subgroup G) : Set G)).comap C.subtype
  let zc : ↥C := ⟨z, hzC⟩
  have hzK : proj C zc ∈ D.map (proj C) := by rw [htop]; exact mem_top _
  obtain ⟨d, hdD, hdz⟩ := Subgroup.mem_map.mp hzK
  have hy₀C : zc⁻¹ * d ∈ pPrimeCore 2 ↥C := by
    rw [← ker_proj C, MonoidHom.mem_ker, map_mul, map_inv, hdz]
    exact inv_mul_cancel _
  have hy₀ : z⁻¹ * (d : G) ∈ oc C := mem_oc.mpr ⟨(zc⁻¹ * d).2, hy₀C⟩
  set y₀ : G := z⁻¹ * (d : G) with hy₀def
  have hy₀odd : Odd (orderOf y₀) := by
    have h1 : orderOf (⟨y₀, hy₀⟩ : oc C) ∣ Nat.card (oc C) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat (odd_card_oc C) h1
  have hdc : ∀ w ∈ oc C, (d : G) * w = w * d := mem_cent_comap.mp hdD
  have hz_eq : z = (d : G) * y₀⁻¹ := by rw [hy₀def]; group
  have hz2 : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have hS : ∀ y ∈ (oc C : Set G), y₀⁻¹ * y * y₀ ∈ (oc C : Set G) := by
    intro y hy
    have hy₀C' : y₀ ∈ C := oc_le C hy₀
    have := conj_mem_oc (X := C) (g := y₀⁻¹) (C.inv_mem hy₀C') hy
    simpa using this
  have hzS : ∀ y ∈ (oc C : Set G), z * y * z⁻¹ = y₀⁻¹ * y * y₀ := by
    intro y hy
    have hw := hdc _ (hS y hy)
    calc z * y * z⁻¹ = ((d : G) * y₀⁻¹) * y * ((d : G) * y₀⁻¹)⁻¹ := by rw [← hz_eq]
      _ = (d : G) * (y₀⁻¹ * y * y₀) * (d : G)⁻¹ := by group
      _ = y₀⁻¹ * y * y₀ := by rw [hw]; group
  have hcen := conj_trivial_of_odd hz2 hy₀odd (oc C : Set G) hS hzS
  refine hYz (fun y hy => ?_)
  rw [mem_centralizer_singleton_iff]
  have := hcen y hy
  calc y * z = (z * y * z⁻¹) * z := by rw [this]
    _ = z * y := by group

namespace Ctx9

variable (X : Ctx9 G z)

theorem not_Y_le_cent_z : ¬ X.Y ≤ centralizer ({z} : Set G) := by
  intro hle
  have hYE : X.Y ≤ X.E := by
    intro y hy
    have : y ∈ oc X.C ⊓ centralizer ({z} : Set G) := mem_inf.mpr ⟨hy, hle hy⟩
    rw [X.l3.Y_cent] at this
    exact this
  have := Subgroup.card_le_of_le hYE
  rw [X.Y_card, X.L.E.E_card] at this
  norm_num at this

theorem z_mem_C : z ∈ X.C := mem_centralizer_singleton_iff.mpr X.L.e.s₂_comm.symm

theorem mem_Y_of_cent_three {c : G} (hcC : c ∈ X.C) (hcc : ∀ y ∈ X.Y, c * y = y * c) {m : ℕ}
    (hc3 : c ^ (3 ^ m) = 1) : c ∈ X.Y := by
  by_contra hcY
  let D : Subgroup ↥X.C := (centralizer ((oc X.C : Subgroup G) : Set G)).comap X.C.subtype
  have hDn := cent_comap_normal X.C
  have hKn : (D.map (proj X.C)).Normal := hDn.map (proj X.C) (proj_surjective X.C)
  let cc : ↥X.C := ⟨c, hcC⟩
  have hcD : cc ∈ D := mem_cent_comap.mpr (fun y hy => hcc y hy)
  have hcK : proj X.C cc ∈ D.map (proj X.C) := Subgroup.mem_map_of_mem _ hcD
  have hne : proj X.C cc ≠ 1 := by
    intro h
    apply hcY
    have : cc ∈ pPrimeCore 2 ↥X.C := by rw [← ker_proj X.C, MonoidHom.mem_ker]; exact h
    exact mem_oc.mpr ⟨hcC, this⟩
  have hpow : (proj X.C cc) ^ (3 ^ m) = 1 := by
    rw [← map_pow]
    have : cc ^ (3 ^ m) = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hpow)
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk'
    exact hne (orderOf_eq_one_iff.mp hk')
  have h3 : 3 ∣ Nat.card (D.map (proj X.C)) := by
    have h1 : orderOf (⟨proj X.C cc, hcK⟩ : D.map (proj X.C)) ∣ Nat.card (D.map (proj X.C)) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hk'] at h1
    exact (dvd_pow_self 3 hk0).trans h1
  have htop := X.l3.cbar.three _ hKn h3
  exact false_of_cent_top X.hz X.z_mem_C htop X.not_Y_le_cent_z

theorem card_Zy_ne_three : Nat.card X.Zy ≠ 3 := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : zpowers X.L.e.s₂ = X.Zy :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr X.s₂_mem_Zy)
      (by rw [h3, Nat.card_zpowers, X.L.e.s₂_ord])
  have hY3 : IsPGroup 3 X.Y := IsPGroup.of_card (n := 7) X.Y_card
  obtain ⟨Ys, hYYs, hYsC, hYsp, -, hYscard⟩ :=
    exists_sylow_sub_ge (p := 3) (W := X.C) (P := X.Y) X.Y_le_C hY3
  have hfac : (Nat.card X.C).factorization 3 = 8 := by
    rcases X.l3.C_card with h | h
    · rw [h]; exact factorization_three_12
    · rw [h]; exact factorization_three_60
  have hYs8 : Nat.card Ys = 3 ^ 8 := by rw [hYscard, hfac]
  have hZYs : ∀ x ∈ Ys, (∀ y ∈ Ys, x * y = y * x) → x ∈ zpowers X.L.e.s₂ := by
    intro x hx hxc
    have hxC : x ∈ X.C := hYsC hx
    obtain ⟨m, hm⟩ : ∃ m : ℕ, x ^ (3 ^ m) = 1 := by
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf).mp hYsp ⟨x, hx⟩
      rw [Subgroup.orderOf_mk] at hm
      exact ⟨m, by rw [← hm]; exact pow_orderOf_eq_one x⟩
    have hxY : x ∈ X.Y := X.mem_Y_of_cent_three hxC (fun y hy => hxc y (hYYs hy)) hm
    rw [hZ]
    exact mem_inf.mpr ⟨hxY, mem_centralizer_iff.mpr fun y hy => (hxc y (hYYs hy)).symm⟩
  have hPT : zpowers X.L.e.s₂ ≤ Ys := (zpowers_le).mpr (hYYs X.s₂_mem_Y)
  have hPc : ∀ x ∈ zpowers X.L.e.s₂, ∀ y ∈ Ys, x * y = y * x := fun x hx y hy =>
    zpowers_comm_of_mem_centralizer (hYsC hy) hx
  have hmax : ∀ R' : Subgroup G, R' ≤ normalizer (zpowers X.L.e.s₂ : Set G) → IsPGroup 3 R' →
      Ys ≤ R' → R' = Ys := by
    intro R' hR'N hR'p hYsR'
    have hR'C : R' ≤ X.C := by
      intro g hg
      have hodd : Odd (orderOf g) := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hR'p ⟨g, hg⟩
        rw [Subgroup.orderOf_mk] at hk
        rw [hk]; exact Odd.pow (by decide)
      exact mem_centralizer_singleton_iff.mpr
        (centralizes_of_normalizes_zpowers X.L.e.s₂_ord (hR'N hg) hodd)
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 3)).mp hR'p
    have hdvd : Nat.card R' ∣ Nat.card X.C := Subgroup.card_dvd_of_le hR'C
    have ha8 : a ≤ 8 := by
      by_contra hlt
      have h9 : 3 ^ 9 ∣ 3 ^ a := pow_dvd_pow 3 (by omega)
      rw [ha] at hdvd
      have := h9.trans hdvd
      rcases X.l3.C_card with h | h <;> rw [h] at this <;> norm_num at this
    refine (Subgroup.eq_of_le_of_card_ge hYsR' ?_).symm
    rw [ha, hYs8]
    exact Nat.pow_le_pow_right (by norm_num) ha8
  obtain ⟨Q, hQ⟩ := hYsp.exists_le_sylow
  have hQeq : (Q : Subgroup G) = Ys :=
    eq_of_isPGroup_le_of_normalizer (p := 3) (H := normalizer (zpowers X.L.e.s₂ : Set G))
      (E := zpowers X.L.e.s₂) (Es := Ys) (R := Q) le_rfl
      (fun g hg => mem_normalizer_of_center hPc hPT hZYs hg) hmax Q.isPGroup' hQ
  have hQcard : Nat.card Q = 3 ^ 8 := by
    have : Nat.card (Q : Subgroup G) = Nat.card Ys := by rw [hQeq]
    rw [← hYs8]; exact this
  have h1 : Nat.card Q = 3 ^ (Nat.card G).factorization 3 := Sylow.card_eq_multiplicity Q
  have h9 : 9 ≤ (Nat.card G).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp X.h39
  have : 3 ^ 9 ≤ 3 ^ (Nat.card G).factorization 3 := Nat.pow_le_pow_right (by norm_num) h9
  rw [← h1, hQcard] at this
  norm_num at this

theorem card_Zy : Nat.card X.Zy = 3 ^ 4 :=
  X.card_Zy_cases.resolve_left X.card_Zy_ne_three

theorem card_C_twelve : Nat.card X.C = 3 ^ 7 * 12 := by
  rcases X.l3.C_card with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h5 : 5 ∣ Nat.card X.C := by rw [h]; norm_num
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥X.C) 5 h5
    have hc5 : orderOf (c : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hc
    have hcC : (c : G) ∈ X.C := c.2
    have hs₂c : (c : G) * X.L.e.s₂ = X.L.e.s₂ * (c : G) := mem_centralizer_singleton_iff.mp hcC
    have hord : ∀ k : ℕ, 0 < k → k ≤ 3 → ¬ 5 ∣ 3 ^ k - 1 := fun k hk hk3 => by
      interval_cases k <;> norm_num
    have hfZ : (c : G) ∈ normalizer (X.Zy : Set G) :=
      mem_normalizer_of_forall (fun c hc n hn => X.conj_Zy hc hn) hcC
    have hsf : zpowers X.L.e.s₂ ≤ X.Zy ⊓ centralizer ({(c : G)} : Set G) := by
      rw [zpowers_le]
      exact mem_inf.mpr ⟨X.s₂_mem_Zy, mem_centralizer_singleton_iff.mpr hs₂c.symm⟩
    have hr : 3 ∣ Nat.card (X.Zy ⊓ centralizer ({(c : G)} : Set G) : Subgroup G) := by
      have := Subgroup.card_dvd_of_le hsf
      rwa [Nat.card_zpowers, X.L.e.s₂_ord] at this
    have hZc : X.Zy ≤ centralizer ({(c : G)} : Set G) :=
      le_centralizer_of_card (p := 3) (q := 5) (r := 3) (m := 3) hc5 hfZ
        (by rw [X.card_Zy]; norm_num) (by norm_num) (by norm_num) hr hord
    have hfY : (c : G) ∈ normalizer (X.Y : Set G) :=
      mem_normalizer_of_forall (fun c hc n hn => X.conj_Y hc hn) hcC
    have hr' : 3 ^ 4 ∣ Nat.card (X.Y ⊓ centralizer ({(c : G)} : Set G) : Subgroup G) := by
      have hle : X.Zy ≤ X.Y ⊓ centralizer ({(c : G)} : Set G) := fun x hx =>
        mem_inf.mpr ⟨(mem_inf.mp hx).1, hZc hx⟩
      have := Subgroup.card_dvd_of_le hle
      rwa [X.card_Zy] at this
    have hYc : X.Y ≤ centralizer ({(c : G)} : Set G) :=
      le_centralizer_of_card (p := 3) (q := 5) (r := 3 ^ 4) (m := 3) hc5 hfY
        (by rw [X.Y_card]; norm_num) (by norm_num) (by norm_num) hr' hord
    obtain ⟨a, ha, h' | h'⟩ := cent_E_le X.L.f X.L.E X.hWc X.hz X.hW5 X.l (g := (c : G))
      (fun x hx => (mem_centralizer_singleton_iff.mp (hYc (X.E_le_Y hx))).symm)
    · have h3 := A_exp X.L.f X.L.E X.hWc X.hW5 X.hz a ha
      rw [← h'] at h3
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hc5] at this
      omega
    · have hodd : Odd (orderOf (a * z)) := by rw [← h', hc5]; decide
      exact not_odd_orderOf_mul_z X.L.f X.L.E X.hWc X.hz X.hW5 ha hodd

end Ctx9

end CFSG.GH74.Uniqueness.SU.SU13
