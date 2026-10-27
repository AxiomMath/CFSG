module

public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionEightSubgroupsSupport

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open QuaternionGroup

theorem eq_closure_of_quaternionEight {S : Type*} [Group S] (n : ℕ) (hn : 4 ≤ n)
    (f : SemidihedralGroup n ≃* S) {r s z : S} (hrdef : r = f (CFSG.Semidihedral.r n))
    (hsdef : s = f (CFSG.Semidihedral.s n)) (hzdef : z = r ^ (2 ^ (n - 1) / 2))
    (Q : Subgroup S) (e₀ : Q ≃* QuaternionGroup 2) :
    ∃ i : ℤ, Odd i ∧ Q = Subgroup.closure {r ^ (2 ^ (n - 1) / 4), r ^ i * s} := by
  have hn3 : 3 ≤ n := by omega
  have hcardQ : Nat.card Q = 8 := by
    rw [Nat.card_congr e₀.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQtop : Q ≠ ⊤ := fun h => by
    rw [h, Subgroup.card_top, ← Nat.card_congr f.toEquiv, card n hn3] at hcardQ
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hnoncomm : ¬ ∀ g h : Q, g * h = h * g := fun h => by
    have h1 := h (e₀.symm (a 1)) (e₀.symm (xa 0))
    rw [← map_mul, ← map_mul, e₀.symm.injective.eq_iff] at h1
    exact quaternionGroup_two_not_comm h1
  have hQA : ¬ Q ≤ Subgroup.zpowers r := fun hle => hnoncomm fun g h => by
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle g.2)
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hle h.2)
    show (g : S) * h = h * g
    rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]
  obtain ⟨-, hcoord⟩ := proper_subgroup_forms_aux n hn f hrdef hsdef hzdef Q
  obtain ⟨k, i, hk, -, hTA, hTgen, hprop⟩ := hcoord hQA
  obtain ⟨-, heven, hodd⟩ := hprop hQtop
  have hr : orderOf r = 2 ^ (n - 1) := by rw [hrdef]; exact sd_orderOf_r hn f
  have hcardTA : Nat.card (Q ⊓ Subgroup.zpowers r : Subgroup S) = 2 ^ (n - 1 - k) := by
    rw [hTA, Nat.card_zpowers, orderOf_pow_of_dvd (by positivity)
      (by rw [hr]; exact Nat.pow_dvd_pow 2 hk), hr, Nat.pow_div hk (by norm_num)]
  rcases Nat.even_or_odd i with hie | hio
  · exfalso
    obtain ⟨hne, hbot⟩ := heven hie
    by_cases h : Q ⊓ Subgroup.zpowers r = ⊥
    · have := (hbot h).2
      omega
    · obtain ⟨φ, -, -⟩ := hne h
      exact dihedral_ne_quaternionGroup_two (fun h1 => h (Subgroup.card_eq_one.mp h1))
        (φ.trans e₀)
  · obtain ⟨hzTA, hcyc, hquat⟩ := hodd hio
    obtain ⟨c, hcdef⟩ : ∃ c, c = n - 1 - k := ⟨_, rfl⟩
    rw [← hcdef] at hcardTA
    have hc : c = 2 := by
      rcases c with _ | _ | c
      · exfalso
        rw [pow_zero, Subgroup.card_eq_one] at hcardTA
        rw [hcardTA, Subgroup.mem_bot] at hzTA
        have hz : orderOf z = 2 := by rw [hzdef, hrdef]; exact image_z_orderOf hn3 f
        rw [hzTA, orderOf_one] at hz
        exact absurd hz (by norm_num)
      · exfalso
        have := (hcyc (by rw [hcardTA, pow_one])).2
        omega
      · have h4 : 4 ≤ Nat.card (Q ⊓ Subgroup.zpowers r : Subgroup S) := by
          rw [hcardTA, pow_add]
          have := Nat.one_le_two_pow (n := c)
          omega
        obtain ⟨φ, -, -⟩ := hquat h4
        have hφ := Nat.card_congr φ.toEquiv
        have hhalf : 2 ^ (c + 1 + 1) / 2 = 2 ^ (c + 1) := by
          rw [pow_succ 2 (c + 1), Nat.mul_div_cancel _ (by norm_num)]
        rw [hcardTA, hhalf, Nat.card_eq_fintype_card, QuaternionGroup.card, hcardQ] at hφ
        have h2 : 2 ^ (c + 1) = 2 ^ 1 := by omega
        have := Nat.pow_right_injective (le_refl 2) h2
        omega
    have hkn : k = n - 3 := by omega
    refine ⟨(i : ℤ), by exact_mod_cast hio, ?_⟩
    have hpow : 2 ^ k = 2 ^ (n - 1) / 4 := by
      rw [hkn, show n - 1 = (n - 3) + 2 by omega, pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num,
        Nat.mul_div_cancel _ (by norm_num)]
    rw [hTgen, zpow_natCast, hpow]

theorem quaternionEight_local {S : Type*} [Group S] {n : ℕ} (hn : 4 ≤ n) (hn3 : 3 ≤ n)
    (f : SemidihedralGroup n ≃* S) {i : ZMod (modulus n)} (hi : i.val % 2 = 1) {v x : S}
    (hv : v = f (element n hn3 ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) 0))
    (hx : x = f (element n hn3 i 1)) :
    Subgroup.centralizer (Subgroup.closure {v, x} : Set S) =
        Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2)) ∧
      (Subgroup.center (Subgroup.closure {v, x})).map (Subgroup.closure {v, x}).subtype =
        Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2)) ∧
      Subgroup.normalizer (Subgroup.closure {v, x} : Set S) =
        Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 8), x} ∧
      Nat.card (Subgroup.normalizer (Subgroup.closure {v, x} : Set S)) = 16 ∧
      (n = 4 → Subgroup.normalizer (Subgroup.closure {v, x} : Set S) = ⊤) ∧
      (5 ≤ n → Nonempty (Subgroup.normalizer (Subgroup.closure {v, x} : Set S) ≃*
        QuaternionGroup 4)) ∧
      Nat.card (Subgroup.closure {v, x}).normalizerMonoidHom.range = 8 := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Subgroup.closure ({v, x} : Set S) := ⟨_, rfl⟩
  rw [← hQ]
  have := finite_of_semidihedral hn3 f
  have hC := centralizer_quaternionEight hn hn3 f hv hx hQ
  have hZ := center_quaternionEight hn hn3 f hv hx hQ
  have hN := normalizer_quaternionEight hn hn3 f hi hv hx hQ
  have htop : n = 4 → Subgroup.normalizer (Q : Set S) = ⊤ := fun h4 => by
    rw [hN]
    exact closure_eighth_eq_top hn3 f hx h4
  have hq16 : 5 ≤ n → Nonempty (Subgroup.normalizer (Q : Set S) ≃* QuaternionGroup 4) := by
    intro hn5
    obtain ⟨u, hu⟩ : ∃ u, u = f (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0) :=
      ⟨_, rfl⟩
    obtain ⟨huo, hxu, hx2, hxux⟩ := eighth_relations hn3 f hi hx hn5 hu
    have hN' : Subgroup.normalizer (Q : Set S) = Subgroup.closure {u, x} := by
      rw [hu]
      exact hN
    have huN : u ∈ Subgroup.normalizer (Q : Set S) :=
      hN' ▸ Subgroup.subset_closure (Set.mem_insert _ _)
    have hxN : x ∈ Subgroup.normalizer (Q : Set S) :=
      hN' ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hgen := closure_pair_subtype_eq_top huN hxN hN'
    have huo' : orderOf (⟨u, huN⟩ : Subgroup.normalizer (Q : Set S)) = 2 * 4 := by
      rw [Subgroup.orderOf_mk, huo]
    have hxu' : (⟨x, hxN⟩ : Subgroup.normalizer (Q : Set S)) ∉
        Subgroup.zpowers (⟨u, huN⟩ : Subgroup.normalizer (Q : Set S)) := fun h => by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
      exact hxu (Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa using congrArg Subtype.val hj⟩)
    have hx2' : (⟨x, hxN⟩ : Subgroup.normalizer (Q : Set S)) ^ 2 =
        (⟨u, huN⟩ : Subgroup.normalizer (Q : Set S)) ^ 4 := Subtype.ext (by simpa using hx2)
    have hxux' : (⟨x, hxN⟩ : Subgroup.normalizer (Q : Set S)) * ⟨u, huN⟩ *
        (⟨x, hxN⟩ : Subgroup.normalizer (Q : Set S))⁻¹ =
        (⟨u, huN⟩ : Subgroup.normalizer (Q : Set S))⁻¹ := Subtype.ext (by simpa using hxux)
    obtain ⟨⟨e, -, -⟩, -⟩ :=
      quaternion_normal_form_isomorphism (m := 4) (by norm_num) hgen huo' hxu' hx2' hxux'
    exact ⟨e.symm⟩
  have hcard : Nat.card (Subgroup.normalizer (Q : Set S)) = 16 := by
    rcases Nat.lt_or_ge n 5 with h | h
    · rw [htop (by omega), Subgroup.card_top, ← Nat.card_congr f.toEquiv, card n hn3,
        show n = 4 by omega]
      norm_num
    · obtain ⟨e⟩ := hq16 h
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have himage : Nat.card Q.normalizerMonoidHom.range = 8 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Q.normalizerMonoidHom.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      Subgroup.normalizerMonoidHom_ker, hcard] at h1
    have h2 : Nat.card ((Subgroup.centralizer (Q : Set S)).subgroupOf
        (Subgroup.normalizer (Q : Set S))) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer _)).toEquiv, hC, Nat.card_zpowers,
        image_z_orderOf hn3 f]
    rw [h2] at h1
    omega
  refine ⟨hC, hZ, ?_, hcard, htop, hq16, himage⟩
  rw [hN, image_eighth_eq hn hn3 f]

theorem quaternion_eight_subgroups_aux {S : Type*} [Group S] (n : ℕ) (hn : 4 ≤ n)
    (f : SemidihedralGroup n ≃* S) {r s v z : S} (hrdef : r = f (CFSG.Semidihedral.r n))
    (hsdef : s = f (CFSG.Semidihedral.s n)) (hvdef : v = r ^ (2 ^ (n - 1) / 4))
    (hzdef : z = r ^ (2 ^ (n - 1) / 2)) :
    (∀ T : Subgroup S, Nonempty (T ≃* QuaternionGroup 2) ↔
      ∃ i : ℤ, Odd i ∧ T = Subgroup.closure {v, r ^ i * s}) ∧
    (∀ T T' : Subgroup S, Nonempty (T ≃* QuaternionGroup 2) →
      Nonempty (T' ≃* QuaternionGroup 2) →
      ∃ g ∈ Subgroup.zpowers r, T' = T.map (MulAut.conj g).toMonoidHom) ∧
    ∀ i : ℤ, Odd i →
      Subgroup.centralizer (Subgroup.closure {v, r ^ i * s} : Set S) = Subgroup.zpowers z ∧
      (Subgroup.center (Subgroup.closure {v, r ^ i * s})).map
          (Subgroup.closure {v, r ^ i * s}).subtype = Subgroup.zpowers z ∧
      Subgroup.normalizer (Subgroup.closure {v, r ^ i * s} : Set S) =
        Subgroup.closure {r ^ (2 ^ (n - 1) / 8), r ^ i * s} ∧
      Nat.card (Subgroup.normalizer (Subgroup.closure {v, r ^ i * s} : Set S)) = 16 ∧
      (n = 4 → Subgroup.normalizer (Subgroup.closure {v, r ^ i * s} : Set S) = ⊤) ∧
      (5 ≤ n → Nonempty (Subgroup.normalizer (Subgroup.closure {v, r ^ i * s} : Set S) ≃*
        QuaternionGroup 4)) ∧
      Nat.card (Subgroup.closure {v, r ^ i * s}).normalizerMonoidHom.range = 8 := by
  have hn3 : 3 ≤ n := by omega
  have hv : v = f (element n hn3 ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) 0) := by
    rw [hvdef, hrdef, image_quarter_eq hn f]
  have hxi : ∀ i : ℤ, r ^ i * s = f (element n hn3 (i : ZMod (modulus n)) 1) := fun i => by
    rw [hrdef, hsdef, image_zpow_mul_s_eq hn3 f]
  have hchar : ∀ T : Subgroup S, Nonempty (T ≃* QuaternionGroup 2) ↔
      ∃ i : ℤ, Odd i ∧ T = Subgroup.closure {v, r ^ i * s} := by
    intro T
    constructor
    · rintro ⟨e₀⟩
      rw [hvdef]
      exact eq_closure_of_quaternionEight n hn f hrdef hsdef hzdef T e₀
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨e, -⟩ :=
        quaternionEight_equiv hn hn3 f (intCast_val_mod_two hn3 hi) hv (hxi i) rfl
      exact ⟨e.symm⟩
  refine ⟨hchar, ?_, ?_⟩
  · intro T T' hT hT'
    obtain ⟨i, hi, rfl⟩ := (hchar T).mp hT
    obtain ⟨j, hj, rfl⟩ := (hchar T').mp hT'
    rw [hxi i, hxi j, hrdef]
    exact quaternionEight_conj hn hn3 f hv (intCast_val_mod_two hn3 hi)
      (intCast_val_mod_two hn3 hj)
  · intro i hi
    have h := quaternionEight_local hn hn3 f (intCast_val_mod_two hn3 hi) hv (hxi i)
    rw [← hrdef, ← hzdef] at h
    exact h

theorem quaternion_eight_subgroups_and_normalizers {S : Type*} [Group S] (n : ℕ) (hn : 4 ≤ n)
    (f : SemidihedralGroup n ≃* S) :
    let r := f (CFSG.Semidihedral.r n)
    let s := f (CFSG.Semidihedral.s n)
    let m := 2 ^ (n - 1)
    let v := r ^ (m / 4)
    let z := r ^ (m / 2)
    let Q : ℤ → Subgroup S := fun i => Subgroup.closure {v, r ^ i * s}
    (∀ T : Subgroup S, Nonempty (T ≃* QuaternionGroup 2) ↔ ∃ i : ℤ, Odd i ∧ T = Q i) ∧
    (∀ T T' : Subgroup S, Nonempty (T ≃* QuaternionGroup 2) →
      Nonempty (T' ≃* QuaternionGroup 2) →
      ∃ g ∈ Subgroup.zpowers r, T' = T.map (MulAut.conj g).toMonoidHom) ∧
    ∀ i : ℤ, Odd i →
      Subgroup.centralizer (Q i : Set S) = Subgroup.zpowers z ∧
      (Subgroup.center (Q i)).map (Q i).subtype = Subgroup.zpowers z ∧
      Subgroup.normalizer (Q i : Set S) = Subgroup.closure {r ^ (m / 8), r ^ i * s} ∧
      Nat.card (Subgroup.normalizer (Q i : Set S)) = 16 ∧
      (n = 4 → Subgroup.normalizer (Q i : Set S) = ⊤) ∧
      (5 ≤ n → Nonempty (Subgroup.normalizer (Q i : Set S) ≃* QuaternionGroup 4)) ∧
      Nat.card (Q i).normalizerMonoidHom.range = 8 := by
  intro r s m v z Q
  exact quaternion_eight_subgroups_aux n hn f rfl rfl rfl rfl

end CFSG.Semidihedral.Local
