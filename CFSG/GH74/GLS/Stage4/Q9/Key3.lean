module

public import CFSG.GH74.GLS.Stage4.Q9.OddPackage
public import CFSG.GH74.GLS.Stage4.Q9.Aut4
public import CFSG.GH74.GLS.Stage4.Q9.OddSmall3
public import CFSG.GH74.GLS.Stage4.Q9.MixedCore
public import CFSG.GH74.GLS.Stage4.Q9.Bound3

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

section Key3Aux

variable {G : Type*} [Group G]

private theorem orderOf_conj_eq {z : G} (g : G) : orderOf (g * z * g⁻¹) = orderOf z := by
  simpa using (MulAut.conj g).orderOf_eq z

private theorem eq_one_or_eq_of_mem_zpowers {z : G} (hz : orderOf z = 2) :
    ∀ s ∈ zpowers z, s = 1 ∨ s = z := by
  intro s hs
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
  have hk := zpow_mod_orderOf z k
  rw [hz] at hk
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h2 with h | h
  · left
    rw [← hk, h, zpow_zero]
  · right
    rw [← hk, h, zpow_one]

private theorem centralizer_le_of_factor {z y : G} (O : Subgroup G)
    (hfac : ∀ a ∈ centralizer ({y} : Set G), ∃ c ∈ centralizer ({y} : Set G), c * z = z * c ∧
      ∃ o ∈ O, a = c * o)
    (hOz : ∀ o ∈ O, z * o = o * z) : centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) := by
  intro a ha
  obtain ⟨c, -, hcz, o, ho, rfl⟩ := hfac a ha
  rw [mem_centralizer_singleton_iff]
  calc c * o * z = c * (z * o) := by rw [mul_assoc, hOz o ho]
    _ = (c * z) * o := by rw [mul_assoc]
    _ = (z * c) * o := by rw [hcz]
    _ = z * (c * o) := by rw [mul_assoc]

private theorem eq_of_involution_of_sylow [Finite G] {z : G} (A S : Subgroup G) (hSA : S ≤ A)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex A) (hSinv : ∀ s ∈ S, orderOf s = 2 → s = z)
    (hAz : ∀ g ∈ A, g * z = z * g) : ∀ e : G, orderOf e = 2 → e ∈ A → e = z := by
  intro e he heA
  have hS'p : IsPGroup 2 (S.subgroupOf A) := hS2.of_equiv (subgroupOfEquivOfLe hSA).symm
  let T : Sylow 2 A := hS'p.toSylow hSidx
  have hTmem : ∀ x : A, x ∈ (T : Subgroup A) ↔ (x : G) ∈ S := fun x => Iff.rfl
  obtain ⟨e', he'e⟩ : ∃ e' : A, (e' : G) = e := ⟨⟨e, heA⟩, rfl⟩
  have he' : orderOf e' = 2 := by rw [← orderOf_coe e', he'e, he]
  have hpe : IsPGroup 2 (zpowers e') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he', pow_one])
  obtain ⟨Q, hQ⟩ := hpe.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A T Q
  have he'Q : e' ∈ (Q : Subgroup A) := hQ (mem_zpowers e')
  rw [← hg, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at he'Q
  obtain ⟨t, ht, hte⟩ := he'Q
  have hte' : (g : G) * (t : G) * (g : G)⁻¹ = e := by
    have := congrArg Subtype.val hte
    rw [← he'e]
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have ht2 : orderOf (t : G) = 2 := by
    rw [← he, ← hte', orderOf_conj_eq]
  have htz : (t : G) = z := hSinv _ ((hTmem t).mp ht) ht2
  rw [← hte', htz]
  calc (g : G) * z * (g : G)⁻¹ = z * (g : G) * (g : G)⁻¹ := by rw [hAz g g.2]
    _ = z := by group

end Key3Aux

private theorem key3_sylow_index {G : Type*} [Group G] [Finite G] {z y : G}
    (hz : orderOf z = 2) (hyz : z * y = y * z)
    (S : Subgroup G) (hSy : ∀ s ∈ S, s * y = y * s) (hS2 : IsPGroup 2 S) (hzS : z ∈ S)
    (hSz : ∀ s ∈ S, s * z = z * s)
    (hZS : ∀ s ∈ S, (∀ w ∈ S, s * w = w * s) → s = 1 ∨ s = z)
    (hSyl : ¬ 2 ∣ S.relIndex (centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G))) :
    ¬ 2 ∣ S.relIndex (centralizer ({y} : Set G)) :=
  sylow_of_centralizer_two hz _ S (mem_centralizer_singleton_iff.mpr hyz)
    (fun s hs => mem_centralizer_singleton_iff.mpr (hSy s hs)) hS2 hzS hSz hZS hSyl

private theorem key3_inv_of_le {G : Type*} [Group G] [Finite G] {z y : G}
    (hz : orderOf z = 2) (hyz : z * y = y * z)
    (S : Subgroup G) (hSy : ∀ s ∈ S, s * y = y * s) (hS2 : IsPGroup 2 S) (hzS : z ∈ S)
    (hSz : ∀ s ∈ S, s * z = z * s)
    (hZS : ∀ s ∈ S, (∀ w ∈ S, s * w = w * s) → s = 1 ∨ s = z)
    (hSinv : ∀ s ∈ S, orderOf s = 2 → s = z)
    (hSyl : ¬ 2 ∣ S.relIndex (centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G)))
    (hAC : centralizer ({y} : Set G) ≤ centralizer ({z} : Set G)) :
    ∀ e : G, orderOf e = 2 → e ∈ centralizer ({y} : Set G) → e = z :=
  eq_of_involution_of_sylow _ S (fun s hs => mem_centralizer_singleton_iff.mpr (hSy s hs)) hS2
    (key3_sylow_index hz hyz S hSy hS2 hzS hSz hZS hSyl) hSinv
    (fun _ hg => mem_centralizer_singleton_iff.mp (hAC hg))

private theorem key3_odd_core {G : Type*} [Group G] [Finite G] {z y u : G}
    (hz : orderOf z = 2) (hyz : z * y = y * z)
    (hu : orderOf u = 2) (huz : u * z = z * u) (hune : u ≠ z) (huy : u * y * u⁻¹ = y⁻¹)
    (hone : ∀ w : G, orderOf w = 2 → IsConj z w)
    (hCpr : ∀ r : ℕ, r.Prime → r ∣ Nat.card (centralizer ({z} : Set G)) → r = 2 ∨ r = 3 ∨ r = 5)
    (hC5 : (Nat.card (centralizer ({z} : Set G))).factorization 5 ≤ 2)
    (S : Subgroup G) (hSy : ∀ s ∈ S, s * y = y * s) (hS2 : IsPGroup 2 S) (hzS : z ∈ S)
    (hSz : ∀ s ∈ S, s * z = z * s)
    (hZS : ∀ s ∈ S, (∀ w ∈ S, s * w = w * s) → s = 1 ∨ s = z)
    (hSinv : ∀ s ∈ S, orderOf s = 2 → s = z)
    (hSyl : ¬ 2 ∣ S.relIndex (centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G))) :
    ∃ O : Subgroup G, O ≤ centralizer ({y} : Set G) ∧
      (∀ a ∈ centralizer ({y} : Set G), ∀ o ∈ O, a * o * a⁻¹ ∈ O) ∧ Odd (Nat.card O) ∧
      (∀ a ∈ centralizer ({y} : Set G), ∃ c ∈ centralizer ({y} : Set G), c * z = z * c ∧
        ∃ o ∈ O, a = c * o) ∧
      (∀ r : ℕ, r.Prime → r ∣ Nat.card O → r = 3 ∨ r = 5) := by
  have hzA : z ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr hyz
  have hSA : S ≤ centralizer ({y} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hSy s hs)
  have hSidx : ¬ 2 ∣ S.relIndex (centralizer ({y} : Set G)) :=
    key3_sylow_index hz hyz S hSy hS2 hzS hSz hZS hSyl
  have huA : ∀ a ∈ centralizer ({y} : Set G), u * a * u⁻¹ ∈ centralizer ({y} : Set G) := by
    intro a ha
    have hay : Commute a y := mem_centralizer_singleton_iff.mp ha
    have hay' : a * y⁻¹ = y⁻¹ * a := hay.inv_right
    have hy' : u * y⁻¹ * u⁻¹ = y := by
      calc u * y⁻¹ * u⁻¹ = (u * y * u⁻¹)⁻¹ := by group
        _ = y := by rw [huy, inv_inv]
    rw [mem_centralizer_singleton_iff]
    calc u * a * u⁻¹ * y = u * a * u⁻¹ * (u * y⁻¹ * u⁻¹) := by rw [hy']
      _ = u * (a * y⁻¹) * u⁻¹ := by group
      _ = u * (y⁻¹ * a) * u⁻¹ := by rw [hay']
      _ = (u * y⁻¹ * u⁻¹) * (u * a * u⁻¹) := by group
      _ = y * (u * a * u⁻¹) := by rw [hy']
  have hwc : ∀ g ∈ centralizer ({y} : Set G), g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z := by
    intro g _ hg
    exact hSinv _ hg (by rw [orderOf_conj_eq g, hz])
  obtain ⟨O, hOA, hOnorm, hOodd, hfac, -, -, hprime, -⟩ :=
    oddcore_package hz hu huz.symm hune.symm hone hCpr hC5 (centralizer ({y} : Set G)) S hzA huA
      hSA hS2 hSidx hzS hSz hwc
  exact ⟨O, hOA, hOnorm, hOodd, hfac, hprime⟩

theorem key3k {G : Type*} [Group G] [Finite G] {z y u₁ : G}
    (hz : orderOf z = 2) (hy3 : orderOf y = 3) (hyz : z * y = y * z)
    (hu₁ : orderOf u₁ = 2) (hu₁z : u₁ * z = z * u₁) (hu₁ne : u₁ ≠ z) (hu₁y : u₁ * y * u₁⁻¹ = y⁻¹)
    (hone : ∀ w : G, orderOf w = 2 → IsConj z w)
    (hCpr : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) →
      r = 2 ∨ r = 3 ∨ r = 5)
    (hC5 : (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 5 ≤ 2)
    (hG3 : (Nat.card G).factorization 3 ≤ 4) (hG5 : (Nat.card G).factorization 5 ≤ 2)
    (S : Subgroup G) (hSy : ∀ s ∈ S, s * y = y * s) (hS2 : IsPGroup 2 S) (hzS : z ∈ S)
    (hSz : ∀ s ∈ S, s * z = z * s)
    (hZS : ∀ s ∈ S, (∀ w ∈ S, s * w = w * s) → s = 1 ∨ s = z)
    (hSinv : ∀ s ∈ S, orderOf s = 2 → s = z)
    (hSyl : ¬ 2 ∣ S.relIndex
      (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)))
    (hoddC : ∀ M : Subgroup G,
      M ≤ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) →
      (∀ c ∈ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ m ∈ M, c * m * c⁻¹ ∈ M) →
      Odd (Nat.card M) → ∀ m ∈ M, ∃ n : ℕ, orderOf m = 3 ^ n)
    (Kb : Subgroup G) (hKby : ∀ k ∈ Kb, k * y = y * k) (hzKb : z ∈ Kb)
    (hKbz : ∀ k ∈ Kb, z * k = k * z)
    (Pb : Subgroup G) (hPbK : Pb ≤ Kb) (hPb3 : IsPGroup 3 Pb) (hPb9 : Nat.card Pb = 9)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    (eb : ↥Kb ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  have _ := hy3
  obtain ⟨O, hOA, hOnorm, hOodd, hfac, hprime⟩ :=
    key3_odd_core hz hyz hu₁ hu₁z hu₁ne hu₁y hone hCpr hC5 S hSy hS2 hzS hSz hZS hSinv hSyl
  have hKbA : Kb ≤ centralizer ({y} : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.mpr (hKby k hk)
  have hKO : ∀ k ∈ Kb, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho => hOnorm k (hKbA hk) o ho
  have h3 : (Nat.card O).factorization 3 ≤ 2 := by
    have hdisj : ∀ x ∈ Pb, x ∈ O → x = 1 := fun x hx hxO =>
      sl2_nine_inf_odd_normal_trivial Kb O hKO hOodd hF eb x (hPbK hx) hxO
    have hbound := sylow_bound_of_normalizing 3 O Pb hPb3
      (fun q hq o ho => hKO q (hPbK hq) o ho) hdisj
    have hPb : (Nat.card Pb).factorization 3 = 2 := by
      rw [hPb9, show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
      simp
    omega
  have h5 : (Nat.card O).factorization 5 ≤ 2 :=
    le_trans ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_subgroup_dvd_card O) 5) hG5
  have hz3 : ∀ o ∈ O, z * o = o * z → ∃ n : ℕ, orderOf o = 3 ^ n := by
    intro o ho hoz
    refine hoddC (O ⊓ centralizer ({z} : Set G)) ?_ ?_ ?_ o
      ⟨ho, mem_centralizer_singleton_iff.mpr hoz.symm⟩
    · exact fun m hm => ⟨hOA hm.1, hm.2⟩
    · intro c hc m hm
      refine ⟨hOnorm c hc.1 m hm.1, ?_⟩
      have hcz : Commute c z := mem_centralizer_singleton_iff.mp hc.2
      have hmz : Commute m z := mem_centralizer_singleton_iff.mp hm.2
      exact mem_centralizer_singleton_iff.mpr ((hcz.mul_left hmz).mul_left hcz.inv_left)
    · exact Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le inf_le_left)
  exact centralizer_le_of_factor O hfac
    (odd_core_small3 hz _ O Kb hOodd hOA hOnorm hKbA hzKb hKbz hF eb hprime h3 h5 hz3)

theorem key3k_inv {G : Type*} [Group G] [Finite G] {z y u₁ : G}
    (hz : orderOf z = 2) (hy3 : orderOf y = 3) (hyz : z * y = y * z)
    (hu₁ : orderOf u₁ = 2) (hu₁z : u₁ * z = z * u₁) (hu₁ne : u₁ ≠ z) (hu₁y : u₁ * y * u₁⁻¹ = y⁻¹)
    (hone : ∀ w : G, orderOf w = 2 → IsConj z w)
    (hCpr : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) →
      r = 2 ∨ r = 3 ∨ r = 5)
    (hC5 : (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 5 ≤ 2)
    (hG3 : (Nat.card G).factorization 3 ≤ 4) (hG5 : (Nat.card G).factorization 5 ≤ 2)
    (S : Subgroup G) (hSy : ∀ s ∈ S, s * y = y * s) (hS2 : IsPGroup 2 S) (hzS : z ∈ S)
    (hSz : ∀ s ∈ S, s * z = z * s)
    (hZS : ∀ s ∈ S, (∀ w ∈ S, s * w = w * s) → s = 1 ∨ s = z)
    (hSinv : ∀ s ∈ S, orderOf s = 2 → s = z)
    (hSyl : ¬ 2 ∣ S.relIndex
      (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)))
    (hoddC : ∀ M : Subgroup G,
      M ≤ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) →
      (∀ c ∈ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ m ∈ M, c * m * c⁻¹ ∈ M) →
      Odd (Nat.card M) → ∀ m ∈ M, ∃ n : ℕ, orderOf m = 3 ^ n)
    (Kb : Subgroup G) (hKby : ∀ k ∈ Kb, k * y = y * k) (hzKb : z ∈ Kb)
    (hKbz : ∀ k ∈ Kb, z * k = k * z)
    (Pb : Subgroup G) (hPbK : Pb ≤ Kb) (hPb3 : IsPGroup 3 Pb) (hPb9 : Nat.card Pb = 9)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    (eb : ↥Kb ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({z} : Set G) ∧
      ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer ({y} : Set G) → e = z := by
  have hAC := key3k hz hy3 hyz hu₁ hu₁z hu₁ne hu₁y hone hCpr hC5 hG3 hG5 S hSy hS2 hzS hSz hZS hSinv
    hSyl hoddC Kb hKby hzKb hKbz Pb hPbK hPb3 hPb9 hF eb
  exact ⟨hAC, key3_inv_of_le hz hyz S hSy hS2 hzS hSz hZS hSinv hSyl hAC⟩

private theorem key3m_data {G : Type*} [Group G] [Finite G] {z y : G}
    (hz : orderOf z = 2) (hyz : z * y = y * z)
    (hC2 : (Nat.card ↥(centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G))).factorization 2 = 1) :
    (∀ s ∈ zpowers z, s * y = y * s) ∧ IsPGroup 2 (zpowers z) ∧ z ∈ zpowers z ∧
      (∀ s ∈ zpowers z, s * z = z * s) ∧
      (∀ s ∈ zpowers z, (∀ w ∈ zpowers z, s * w = w * s) → s = 1 ∨ s = z) ∧
      (∀ s ∈ zpowers z, orderOf s = 2 → s = z) ∧
      ¬ 2 ∣ (zpowers z).relIndex (centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G)) := by
  have hzA : z ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr hyz
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hSAC : zpowers z ≤ centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G) :=
    zpowers_le.mpr ⟨hzA, hzC⟩
  have hcases := eq_one_or_eq_of_mem_zpowers hz
  refine ⟨fun s hs => mem_centralizer_singleton_iff.mp (hSAC hs).1,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]), mem_zpowers z,
    fun s hs => mem_centralizer_singleton_iff.mp (hSAC hs).2, fun s hs _ => hcases s hs,
    fun s hs hs2 => (hcases s hs).resolve_left (by rintro rfl; simp at hs2), ?_⟩
  intro h2
  have h := (zpowers z).relIndex_mul_card (centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G))
  rw [inf_of_le_left hSAC, Nat.card_zpowers, hz] at h
  have h4 : 2 ^ 2 ∣ Nat.card ↥(centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G)) := by
    rw [← h]
    obtain ⟨m, hm⟩ := h2
    rw [hm]
    exact ⟨m, by ring⟩
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h4
  omega

theorem key3m {G : Type*} [Group G] [Finite G] {z y u₁ : G}
    (hz : orderOf z = 2) (hy3 : orderOf y = 3) (hyz : z * y = y * z)
    (hu₁ : orderOf u₁ = 2) (hu₁z : u₁ * z = z * u₁) (hu₁ne : u₁ ≠ z) (hu₁y : u₁ * y * u₁⁻¹ = y⁻¹)
    (hone : ∀ w : G, orderOf w = 2 → IsConj z w)
    (hCpr : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) →
      r = 2 ∨ r = 3 ∨ r = 5)
    (hC5 : (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 5 ≤ 2)
    (hG3 : (Nat.card G).factorization 3 ≤ 4) (hG5 : (Nat.card G).factorization 5 ≤ 2)
    (h27 : ∀ r : G, orderOf r = 5 → ¬ 27 ∣ Nat.card (Subgroup.centralizer ({r} : Set G)))
    (P : Subgroup G) (hP3 : IsPGroup 3 P) (hP81 : Nat.card P = 81) (hPy : ∀ p ∈ P, p * y = y * p)
    (hPz : ∀ p ∈ P, p * z = z * p)
    (hC2 : (Nat.card ↥(Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({z} : Set G))).factorization 2 = 1)
    (hoddC : ∀ c ∈ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      Odd (orderOf c) → c ∈ P) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  have _ := hy3
  have hzA : z ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr hyz
  obtain ⟨hSy, hS2, hzS, hSz, hZS, hSinv, hSyl⟩ := key3m_data hz hyz hC2
  obtain ⟨O, hOA, hOnorm, hOodd, hfac, hprime⟩ :=
    key3_odd_core hz hyz hu₁ hu₁z hu₁ne hu₁y hone hCpr hC5 (zpowers z) hSy hS2 hzS hSz hZS hSinv
      hSyl
  have hOz : ∀ o ∈ O, z * o * z⁻¹ ∈ O := fun o ho => hOnorm z hzA o ho
  have hPO : ∀ p ∈ P, ∀ o ∈ O, p * o * p⁻¹ ∈ O := fun p hp o ho =>
    hOnorm p (mem_centralizer_singleton_iff.mpr (hPy p hp)) o ho
  have hCz : ∀ o ∈ O, z * o = o * z → o ∈ P := by
    intro o ho hoz
    exact hoddC o ⟨hOA ho, mem_centralizer_singleton_iff.mpr hoz.symm⟩
      (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O ho))
  have h5 : (Nat.card O).factorization 5 ≤ 2 :=
    le_trans ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_subgroup_dvd_card O) 5) hG5
  have hC5' : ∀ r ∈ O, orderOf r = 5 →
      ¬ 27 ∣ Nat.card ↥(P ⊓ centralizer ({r} : Set G)) := by
    intro r _ hr5 h
    exact h27 r hr5 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  exact centralizer_le_of_factor O hfac
    (mixed_core_trivial hz O P hOodd hOz hP3 hP81 hPz hPO hCz hprime h5 hG3 hC5')

theorem key3m_inv {G : Type*} [Group G] [Finite G] {z y u₁ : G}
    (hz : orderOf z = 2) (hy3 : orderOf y = 3) (hyz : z * y = y * z)
    (hu₁ : orderOf u₁ = 2) (hu₁z : u₁ * z = z * u₁) (hu₁ne : u₁ ≠ z) (hu₁y : u₁ * y * u₁⁻¹ = y⁻¹)
    (hone : ∀ w : G, orderOf w = 2 → IsConj z w)
    (hCpr : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) →
      r = 2 ∨ r = 3 ∨ r = 5)
    (hC5 : (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 5 ≤ 2)
    (hG3 : (Nat.card G).factorization 3 ≤ 4) (hG5 : (Nat.card G).factorization 5 ≤ 2)
    (h27 : ∀ r : G, orderOf r = 5 → ¬ 27 ∣ Nat.card (Subgroup.centralizer ({r} : Set G)))
    (P : Subgroup G) (hP3 : IsPGroup 3 P) (hP81 : Nat.card P = 81) (hPy : ∀ p ∈ P, p * y = y * p)
    (hPz : ∀ p ∈ P, p * z = z * p)
    (hC2 : (Nat.card ↥(Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({z} : Set G))).factorization 2 = 1)
    (hoddC : ∀ c ∈ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      Odd (orderOf c) → c ∈ P) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({z} : Set G) ∧
      ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer ({y} : Set G) → e = z := by
  have hAC := key3m hz hy3 hyz hu₁ hu₁z hu₁ne hu₁y hone hCpr hC5 hG3 hG5 h27 P hP3 hP81 hPy hPz hC2
    hoddC
  obtain ⟨hSy, hS2, hzS, hSz, hZS, hSinv, hSyl⟩ := key3m_data hz hyz hC2
  exact ⟨hAC, key3_inv_of_le hz hyz (zpowers z) hSy hS2 hzS hSz hZS hSinv hSyl hAC⟩

end CFSG.GH74.GLS.Stage4.Q9
