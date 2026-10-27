module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOrdersSupport

public section

namespace CFSG.Semidihedral.Principal.FieldFactorOneFixedCore

theorem odd_half_torusOrder {q : ℕ} (hq : Odd q) :
    Odd ((if q % 4 = 1 then q + 1 else q - 1) / 2) := by
  rw [Nat.odd_iff] at hq ⊢
  split_ifs with h <;> omega

theorem one_lt_half_torusOrder {q : ℕ} (hq : 5 < q) :
    1 < (if q % 4 = 1 then q + 1 else q - 1) / 2 := by
  split_ifs <;> omega

theorem not_dvd_half_torusOrder {p q : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hq : Odd q) :
    ¬ p ∣ (if q % 4 = 1 then q + 1 else q - 1) / 2 := by
  intro h
  rw [Nat.odd_iff] at hq
  have h2 : p ∣ (if q % 4 = 1 then q + 1 else q - 1) :=
    h.trans (Nat.div_dvd_of_dvd (by split_ifs <;> omega))
  split_ifs at h2
  · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp h2))
  · have h3 := Nat.dvd_sub hpq h2
    rw [show q - (q - 1) = 1 by omega] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem mem_of_index_two_of_odd_orderOf {X : Type*} [Group X] {Y : Subgroup X}
    (hY : Y.index = 2) {x : X} (hx : Odd (orderOf x)) : x ∈ Y := by
  obtain ⟨k, hk⟩ := hx
  have h1 : x * (x ^ 2) ^ k = 1 := by
    rw [← pow_mul, ← pow_succ', show 2 * k + 1 = orderOf x by omega, pow_orderOf_eq_one]
  rw [eq_inv_of_mul_eq_one_left h1]
  exact Y.inv_mem (Y.pow_mem (Subgroup.sq_mem_of_index_two hY x) k)

theorem mul_inv_mem_of_index_two {X : Type*} [Group X] {Y : Subgroup X} (hY : Y.index = 2)
    {a b : X} (ha : a ∉ Y) (hb : b ∉ Y) : a * b⁻¹ ∈ Y := by
  rw [Subgroup.mul_mem_iff_of_index_two hY]
  simp [ha, hb]

theorem mem_normalizer_of_conj_mem {X : Type*} [Group X] [Finite X] {H : Subgroup X} {g : X}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set X) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hxy : y = x := by
    have h' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    simpa using h'
  rwa [← hxy]

theorem exists_mul_of_mem_sup_of_commute {X : Type*} [Group X] {H K : Subgroup X}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : X} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let P : Subgroup X :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := by
        rintro _ _ ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        refine ⟨h * h', H.mul_mem hh hh', k * k', K.mul_mem hk hk', ?_⟩
        calc h * k * (h' * k') = h * (k * h') * k' := by group
          _ = h * (h' * k) * k' := by rw [hHK h' hh' k hk]
          _ = h * h' * (k * k') := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev]
        exact (hHK h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)).symm }
  have hle : H ⊔ K ≤ P :=
    sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
      (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
  exact hle hx

theorem exists_mulEquiv_prod_three {X : Type*} [Group X] {V A W D : Subgroup X}
    (hVD : V ≤ D) (hAD : A ≤ D) (hWD : W ≤ D)
    (hVA : ∀ v ∈ V, ∀ a ∈ A, v * a = a * v) (hVW : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v)
    (hAW : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a)
    (hinj : ∀ v ∈ V, ∀ a ∈ A, ∀ w ∈ W, v * a * w = 1 → v = 1 ∧ a = 1 ∧ w = 1)
    (hsurj : ∀ x ∈ D, ∃ v ∈ V, ∃ a ∈ A, ∃ w ∈ W, x = v * a * w) :
    ∃ e : (V × A × W) ≃* D, ∀ x : V × A × W, (e x : X) = x.1 * x.2.1 * x.2.2 := by
  let f : V × A × W →* D :=
    { toFun := fun x => ⟨x.1 * x.2.1 * x.2.2,
        D.mul_mem (D.mul_mem (hVD x.1.2) (hAD x.2.1.2)) (hWD x.2.2.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        rintro ⟨v, a, w⟩ ⟨v', a', w'⟩
        apply Subtype.ext
        change (v : X) * v' * (a * a') * (w * w') = v * a * w * (v' * a' * w')
        have h1 : (w : X) * v' = v' * w := (hVW v' v'.2 w w.2).symm
        have h2 : (a : X) * v' = v' * a := (hVA v' v'.2 a a.2).symm
        have h3 : (w : X) * a' = a' * w := (hAW a' a'.2 w w.2).symm
        calc (v : X) * v' * (a * a') * (w * w') = v * (v' * a) * a' * w * w' := by group
          _ = v * (a * v') * a' * w * w' := by rw [h2]
          _ = v * a * v' * (a' * w) * w' := by group
          _ = v * a * v' * (w * a') * w' := by rw [h3]
          _ = v * a * (v' * w) * a' * w' := by group
          _ = v * a * (w * v') * a' * w' := by rw [h1]
          _ = v * a * w * (v' * a' * w') := by group }
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨v, a, w⟩ h
    have h' : (v : X) * a * w = 1 := congrArg Subtype.val h
    obtain ⟨hv, ha, hw⟩ := hinj v v.2 a a.2 w w.2 h'
    exact Prod.ext (Subtype.ext hv) (Prod.ext (Subtype.ext ha) (Subtype.ext hw))
  have hfsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨v, hv, a, ha, w, hw, rfl⟩ := hsurj x hx
    exact ⟨(⟨v, hv⟩, ⟨a, ha⟩, ⟨w, hw⟩), rfl⟩
  exact ⟨MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩, fun x => rfl⟩

theorem mem_closure_pair_cases {X : Type*} [Group X] {t s : X} (hts : t * s = s * t)
    (ht2 : t * t = 1) (hs2 : s * s = 1) {v : X} (hv : v ∈ Subgroup.closure ({t, s} : Set X)) :
    v = 1 ∨ v = t ∨ v = s ∨ v = t * s := by
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    have hst : s * (t * s) = t := by rw [hts, ← mul_assoc, hs2, one_mul]
    have hts' : t * (t * s) = s := by rw [← mul_assoc, ht2, one_mul]
    have hst' : t * s * s = t := by rw [mul_assoc, hs2, mul_one]
    have hst'' : t * s * t = s := by rw [hts, mul_assoc, ht2, mul_one]
    have htss : t * s * (t * s) = 1 := by rw [← mul_assoc, hst'', hs2]
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, ht2, hs2, hst, hts', hst', hst'', htss, ← hts, true_or,
        or_true]
  | inv x _ hx =>
    have hinv : (t * s)⁻¹ = t * s := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hs2, inv_eq_of_mul_eq_one_right ht2, hts]
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ht2))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hs2)))
    · exact Or.inr (Or.inr (Or.inr hinv))

theorem mem_centralizer_closure_pair_iff {X : Type*} [Group X] {t s x : X} :
    x ∈ Subgroup.centralizer (Subgroup.closure ({t, s} : Set X) : Set X) ↔
      x * t = t * x ∧ x * s = s * x := by
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h t (Set.mem_insert _ _)).symm, (h s (Set.mem_insert_of_mem _ rfl)).symm⟩
  · rintro ⟨h1, h2⟩ g hg
    rcases hg with rfl | rfl
    · exact h1.symm
    · exact h2.symm

theorem mem_normalizer_closure_pair {X : Type*} [Group X] [Finite X] {t s g : X}
    (hts : t * s = s * t) (ht2 : t * t = 1) (hs2 : s * s = 1) (hgt : g * t * g⁻¹ = t)
    (hgs : g * s * g⁻¹ = t * s) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({t, s} : Set X) : Set X) := by
  have htV : t ∈ Subgroup.closure ({t, s} : Set X) := Subgroup.subset_closure (by simp)
  have hsV : s ∈ Subgroup.closure ({t, s} : Set X) := Subgroup.subset_closure (by simp)
  apply mem_normalizer_of_conj_mem
  intro x hx
  rcases mem_closure_pair_cases hts ht2 hs2 hx with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [hgt]
    exact htV
  · rw [hgs]
    exact Subgroup.mul_mem _ htV hsV
  · have h : g * (t * s) * g⁻¹ = (g * t * g⁻¹) * (g * s * g⁻¹) := by group
    rw [h, hgt, hgs, ← mul_assoc, ht2, one_mul]
    exact hsV

theorem eq_one_of_sq_eq_one_of_odd {X : Type*} [Group X] {x : X} (hx : Odd (orderOf x))
    (h2 : x ^ 2 = 1) : x = 1 := by
  have h := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hx
    exact absurd hx (by decide)

theorem central_involution_facts {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S) {t : G}
    (htS : t ∈ (S : Subgroup G)) (htZ : ∀ x ∈ (S : Subgroup G), x * t = t * x) (ht1 : t ≠ 1) :
    orderOf t = 2 ∧ (S : Subgroup G) ⊓ Subgroup.centralizer (S : Set G) = Subgroup.zpowers t := by
  obtain ⟨-, hcard, -⟩ := CFSG.Semidihedral.supplied_index_two_and_element_structure n hn fS
  let tS : (S : Subgroup G) := ⟨t, htS⟩
  have htZc : tS ∈ Subgroup.center (S : Subgroup G) :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (htZ y y.2)
  have htS1 : tS ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hord : orderOf tS = 2 := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center (S : Subgroup G)) htZc
    rw [hcard] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) htS1
    · exact h1
  have ht2 : orderOf t = 2 := by
    rw [← hord]
    exact Subgroup.orderOf_coe tS
  have hzle : Subgroup.zpowers tS ≤ Subgroup.center (S : Subgroup G) := Subgroup.zpowers_le.mpr htZc
  have hzeq : Subgroup.zpowers tS = Subgroup.center (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hcard, Nat.card_zpowers, hord])
  refine ⟨ht2, le_antisymm ?_ ?_⟩
  · rintro x ⟨hxS, hxc⟩
    have hxZ : (⟨x, hxS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp hxc y y.2)
    rw [← hzeq] at hxZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h := congrArg Subtype.val hk
    rwa [SubgroupClass.coe_zpow] at h
  · rw [Subgroup.zpowers_le]
    exact ⟨htS, Subgroup.mem_centralizer_iff.mpr htZ⟩

theorem exists_mulEquiv_prod_two {X : Type*} [Group X] {J N Y : Subgroup X}
    (hJN : J ⊔ N = Y) (hdisj : J ⊓ N = ⊥) (hcomm : ∀ j ∈ J, ∀ x ∈ N, j * x = x * j) :
    ∃ μ : J × N ≃* Y, ∀ x : J × N, (μ x : X) = x.1 * x.2 := by
  let f : J × N →* Y :=
    { toFun := fun x => ⟨x.1 * x.2, hJN ▸ Subgroup.mul_mem_sup x.1.2 x.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        rintro ⟨j, x⟩ ⟨j', x'⟩
        apply Subtype.ext
        change (j : X) * j' * (x * x') = j * x * (j' * x')
        have h := hcomm j' j'.2 x x.2
        calc (j : X) * j' * (x * x') = j * (j' * x) * x' := by group
          _ = j * (x * j') * x' := by rw [h]
          _ = j * x * (j' * x') := by group }
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨j, x⟩ h
    have h' : (j : X) * x = 1 := congrArg Subtype.val h
    have hjx : (j : X) = (x : X)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hj : (j : X) ∈ J ⊓ N := ⟨j.2, hjx ▸ N.inv_mem x.2⟩
    rw [hdisj, Subgroup.mem_bot] at hj
    have hx : (x : X) = 1 := by
      rw [hj, one_mul] at h'
      exact h'
    exact Prod.ext (Subtype.ext hj) (Subtype.ext hx)
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hJN] at hy
    obtain ⟨j, hj, x, hx, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
    exact ⟨(⟨j, hj⟩, ⟨x, hx⟩), rfl⟩
  exact ⟨MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩, fun x => rfl⟩

theorem card_comap_subtype_of_le {X : Type*} [Group X] {H K : Subgroup X} (h : H ≤ K) :
    Nat.card (H.comap K.subtype) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem isMulCommutative_comap_subtype {X : Type*} [Group X] {H : Subgroup X} (K : Subgroup X)
    (hH : IsMulCommutative H) : IsMulCommutative (H.comap K.subtype) :=
  ⟨⟨fun a b => by
    have h := congrArg Subtype.val
      (hH.is_comm.comm ⟨((a : K) : X), a.2⟩ ⟨((b : K) : X), b.2⟩)
    exact Subtype.ext (Subtype.ext h)⟩⟩

theorem sylow_le_centralizer_of_eq {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n) {S : Subgroup G}
    (fS : CFSG.Open.SemidihedralGroup n ≃* S) {t : G}
    (ht : t = (fS (CFSG.Semidihedral.r n) : G) ^ 2 ^ (n - 2)) :
    S ≤ Subgroup.centralizer ({t} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨hz, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨a, ha⟩ := fS.surjective ⟨x, hx⟩
  have hc := Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn) a
  have hc' := congrArg (fun w => ((fS w : S) : G)) hc
  simp only [map_mul, Subgroup.coe_mul, ha, hz] at hc'
  exact hc'

theorem eq_of_orderOf_eq_two_of_isCyclic {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : IsCyclic H) {a b : X} (ha : a ∈ H) (hb : b ∈ H) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) : a = b := by
  classical
  let : Fintype H := Fintype.ofFinite H
  by_contra hab
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha2
    omega
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb2
    omega
  have hsq : ∀ x : X, orderOf x = 2 → x ^ 2 = 1 := fun x hx => by
    rw [← hx, pow_orderOf_eq_one]
  have hsub : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H) ⊆
      Finset.univ.filter (fun x : H => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by simpa using hsq a ha2)
    · exact Subtype.ext (by simpa using hsq b hb2)
  have hcard : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact hab (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hb1 (congrArg Subtype.val h).symm⟩
  have hle := Finset.card_le_card hsub
  have hcyc := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  omega

end CFSG.Semidihedral.Principal.FieldFactorOneFixedCore
