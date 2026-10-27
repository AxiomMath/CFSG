module

public import CFSG.Quasithin.Recognition.M12AscV

public section

namespace CFSG.GH74.M12.Thm1

open Subgroup CFSG.Quasithin
open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem three_dvd_card_of_fpf {α : Type*} [Finite α] (σ : Equiv.Perm α) (h3 : σ ^ 3 = 1)
    (hfix : ∀ a, σ a ≠ a) : 3 ∣ Nat.card α := by
  classical
  have := Fintype.ofFinite α
  by_contra h
  rw [Nat.card_eq_fintype_card] at h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) h
    (by simpa using h3)
  exact hfix a ha

theorem mem_normalizer_of_conj {U : Subgroup G} [Finite G] {g : G}
    (h : ∀ u ∈ U, g * u * g⁻¹ ∈ U) : g ∈ normalizer (U : Set G) := by
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  have heq : U.map (MulAut.conj g).toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (Nat.card_congr
      (Subgroup.equivMapOfInjective U (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv))
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    have : g * x * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 this
    have : u = x := by
      have := congrArg (fun w => g⁻¹ * w * g) hue
      simpa [MulAut.conj_apply, mul_assoc] using this
    rw [← this]; exact hu

noncomputable def rho (hyp : Asc03Hyp G z) : ↥(ascH z) →* Equiv.Perm (Fin 3) :=
  hyp.quotient_S3.some.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(ascH z)))

theorem rho_eq_one_iff (hyp : Asc03Hyp G z) (h : ↥(ascH z)) :
    rho hyp h = 1 ↔ (h : G) ∈ ascQ z := by
  rw [mem_ascQ_iff]
  constructor
  · intro h1
    refine ⟨h.2, ?_⟩
    have : (QuotientGroup.mk' (CFSG.pCore 2 ↥(ascH z))) h = 1 :=
      hyp.quotient_S3.some.injective (by simpa [rho] using h1)
    exact (QuotientGroup.eq_one_iff _).1 this
  · rintro ⟨_, hq⟩
    have hq' : h ∈ CFSG.pCore 2 ↥(ascH z) := hq
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥(ascH z))) h = 1 :=
      (QuotientGroup.eq_one_iff _).2 hq'
    show hyp.quotient_S3.some (QuotientGroup.mk' _ h) = 1
    rw [h1, map_one]

theorem z_ne_one (hyp : Asc03Hyp G z) : z ≠ 1 := (extraspecialAt_ascQ hyp).ne_one

theorem z_mul_z (hyp : Asc03Hyp G z) : z * z = 1 := (extraspecialAt_ascQ hyp).sq_eq

theorem card_ascQ (hyp : Asc03Hyp G z) : Nat.card ↥(ascQ z) = 32 :=
  (extraspecialAt_ascQ hyp).card_eq

theorem isPGroup_ascQ (hyp : Asc03Hyp G z) : IsPGroup 2 ↥(ascQ z) :=
  IsPGroup.of_card (n := 5) (by rw [card_ascQ hyp]; norm_num)

theorem card_ascH' (hyp : Asc03Hyp G z) : Nat.card ↥(ascH z) = 192 := AscModel.card_ascH hyp

theorem conj_mem_ascQ {h q : G} (hh : h ∈ ascH z) (hq : q ∈ ascQ z) : h * q * h⁻¹ ∈ ascQ z := by
  obtain ⟨hqH, hqP⟩ := (mem_ascQ_iff z q).1 hq
  have := (CFSG.pCore_normal (p := 2) (G := ↥(ascH z))).conj_mem _ hqP ⟨h, hh⟩
  rw [mem_ascQ_iff]
  exact ⟨(ascH z).mul_mem ((ascH z).mul_mem hh hqH) ((ascH z).inv_mem hh), this⟩

theorem le_ascQ_of_normal {S : Subgroup G} (hS : S ≤ ascH z)
    (hn : ∀ h ∈ ascH z, ∀ s ∈ S, h * s * h⁻¹ ∈ S) (hp : IsPGroup 2 ↥S) : S ≤ ascQ z := by
  intro s hs
  rw [mem_ascQ_iff]
  refine ⟨hS hs, ?_⟩
  have hN : (S.subgroupOf (ascH z)).Normal := ⟨fun n hn' h => by
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    simpa using hn h.1 h.2 n.1 hn'⟩
  have hP : IsPGroup 2 ↥(S.subgroupOf (ascH z)) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
  have hle : S.subgroupOf (ascH z) ≤ CFSG.pCore 2 ↥(ascH z) := le_sSup ⟨hN, hP⟩
  exact hle (Subgroup.mem_subgroupOf.2 hs)

theorem isPGroup_of_not_three [Finite G] (hyp : Asc03Hyp G z) {S : Subgroup G}
    (hS : S ≤ ascH z) (h3 : ∀ y ∈ S, orderOf y ≠ 3) : IsPGroup 2 ↥S := by
  have hdvd : Nat.card S ∣ 192 := by
    rw [← card_ascH' hyp]; exact Subgroup.card_dvd_of_le hS
  have h3' : ¬ 3 ∣ Nat.card S := by
    intro h
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h
    exact h3 y y.2 ((Subgroup.orderOf_coe y).trans hy)
  have h64 : Nat.card S ∣ 2 ^ 6 := by
    have hc : Nat.Coprime (Nat.card S) 3 := (Nat.coprime_comm.1
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3'))
    exact hc.dvd_of_dvd_mul_right (by simpa using hdvd)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h64
  exact IsPGroup.of_card hk

theorem not_mem_ascQ_of_order_three [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy3 : orderOf y = 3) :
    y ∉ ascQ z := by
  intro hyQ
  obtain ⟨k, hk⟩ := isPGroup_ascQ hyp ⟨y, hyQ⟩
  have h1 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hy3] at h2
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
  omega

theorem cent_of_order_three [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy : y ∈ ascH z)
    (hy3 : orderOf y = 3) {q : G} (hq : q ∈ ascQ z) (hqy : q * y = y * q) : q = 1 ∨ q = z := by
  set y' : ↥(ascH z) := ⟨y, hy⟩
  have hord : orderOf y' = 3 := by rw [← Subgroup.orderOf_coe]; exact hy3
  have hxp : IsPGroup 3 (Subgroup.zpowers y') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X, hX⟩ := hxp.exists_le_sylow
  have hXcard : Nat.card ↥(X : Subgroup ↥(ascH z)) = 3 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 X.isPGroup'
    have hdvd : 3 ^ k ∣ 192 := by
      rw [← card_ascH' hyp, ← hk]
      exact Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have : 3 ^ 2 ∣ 192 := (pow_dvd_pow 3 hk2).trans hdvd
      norm_num at this
    have hge : 3 ≤ Nat.card ↥(X : Subgroup ↥(ascH z)) := by
      have := Subgroup.card_le_of_le hX
      rwa [Nat.card_zpowers, hord] at this
    rw [hk] at hge ⊢
    interval_cases k <;> simp_all
  have hXeq : Subgroup.zpowers y' = (X : Subgroup ↥(ascH z)) :=
    Subgroup.eq_of_le_of_card_ge hX (by rw [hXcard, Nat.card_zpowers, hord])
  obtain ⟨hqH, hqP⟩ := (mem_ascQ_iff z q).1 hq
  have hcomm : ∀ x ∈ (X : Subgroup ↥(ascH z)), x * ⟨q, hqH⟩ = ⟨q, hqH⟩ * x := by
    intro x hx
    rw [← hXeq] at hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hc : Commute y' ⟨q, hqH⟩ := Subtype.ext hqy.symm
    exact (hc.zpow_left k).eq
  have hz := hyp.centralizer_X X ⟨q, hqH⟩ hqP hcomm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hz2 : z ^ k = 1 ∨ z ^ k = z := by
    rw [← zpow_mod_orderOf, hyp.orderTwo]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; simp [h]
    · right; simp [h]
  have hk' : z ^ k = q := hk
  rcases hz2 with h | h
  · left; rw [← hk', h]
  · right; rw [← hk', h]

theorem eq_of_conj_mem [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy : y ∈ ascH z)
    (hy3 : orderOf y = 3) {q : G} (hq : q ∈ ascQ z)
    (h : y * q * y⁻¹ = q ∨ y * q * y⁻¹ = q * z) : q = 1 ∨ q = z := by
  rcases h with h | h
  · exact cent_of_order_three hyp hy hy3 hq (by
      calc q * y = (y * q * y⁻¹) * y := by rw [h]
        _ = y * q := by group)
  · exfalso
    have hyz : y * z * y⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hy
      calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [this]
        _ = z := by group
    have hyyy : y * y * y = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy3, pow_three, ← mul_assoc] at this
      exact this
    have h2 : (y * y * y) * q * (y * y * y)⁻¹ = q * z := by
      calc (y * y * y) * q * (y * y * y)⁻¹ = y * (y * (y * q * y⁻¹) * y⁻¹) * y⁻¹ := by group
        _ = y * (y * (q * z) * y⁻¹) * y⁻¹ := by rw [h]
        _ = y * ((y * q * y⁻¹) * (y * z * y⁻¹)) * y⁻¹ := by group
        _ = y * ((q * z) * z) * y⁻¹ := by rw [h, hyz]
        _ = y * q * y⁻¹ := by rw [mul_assoc q z z, z_mul_z hyp, mul_one]
        _ = q * z := h
    rw [hyyy, one_mul, inv_one, mul_one] at h2
    have : z = 1 := by
      have := congrArg (fun w => q⁻¹ * w) h2
      simpa using this.symm
    exact z_ne_one hyp this

theorem exists_order_three [Finite G] (hyp : Asc03Hyp G z) : ∃ y ∈ ascH z, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card ↥(ascH z) by
    rw [card_ascH' hyp]; norm_num)
  exact ⟨y, y.2, (Subgroup.orderOf_coe y).trans hy⟩

theorem conj_mem_of_z_mem {Q U : Subgroup G} (hE : ExtraspecialAt Q z) (hU : U ≤ Q)
    (hzU : z ∈ U) {q u : G} (hq : q ∈ Q) (hu : u ∈ U) : q * u * q⁻¹ ∈ U := by
  have h : q * u * q⁻¹ = (q * u * q⁻¹ * u⁻¹) * u := by group
  rw [h]
  rcases hE.comm_mem q hq u (hU hu) with h1 | h1
  · rw [h1, one_mul]; exact hu
  · rw [h1]; exact U.mul_mem hzU hu

theorem eq_of_cent_ascQ [Finite G] (hyp : Asc03Hyp G z) {c : G} (hc : c ∈ ascH z)
    (hcQ : ∀ q ∈ ascQ z, c * q = q * c) : c = 1 ∨ c = z := by
  set C : Subgroup G := ascH z ⊓ Subgroup.centralizer (ascQ z : Set G)
  have hCH : C ≤ ascH z := inf_le_left
  have hcC : c ∈ C := ⟨hc, Subgroup.mem_centralizer_iff.2 fun q hq => (hcQ q hq).symm⟩
  have hnC : ∀ h ∈ ascH z, ∀ x ∈ C, h * x * h⁻¹ ∈ C := by
    intro h hh x hx
    refine Subgroup.mem_inf.2 ⟨(ascH z).mul_mem ((ascH z).mul_mem hh hx.1) ((ascH z).inv_mem hh), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : h⁻¹ * q * h ∈ ascQ z := by
      simpa using conj_mem_ascQ ((ascH z).inv_mem hh) hq
    have := (Subgroup.mem_centralizer_iff.1 hx.2) _ hq'
    calc q * (h * x * h⁻¹) = h * ((h⁻¹ * q * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * q * h)) * h⁻¹ := by rw [this]
      _ = h * x * h⁻¹ * q := by group
  have h3 : ∀ y ∈ C, orderOf y ≠ 3 := by
    intro y hy hy3
    have hall : ∀ q ∈ ascQ z, q = 1 ∨ q = z := fun q hq =>
      cent_of_order_three hyp hy.1 hy3 hq ((Subgroup.mem_centralizer_iff.1 hy.2) q hq)
    have := card_le_two_of_forall hall
    rw [card_ascQ hyp] at this
    omega
  have hCQ : C ≤ ascQ z := le_ascQ_of_normal hCH hnC (isPGroup_of_not_three hyp hCH h3)
  exact (extraspecialAt_ascQ hyp).center_le c (hCQ hcC) hcQ

theorem card_of_inv [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy : y ∈ ascH z)
    (hy3 : orderOf y = 3) {U : Subgroup G} (hUQ : U ≤ ascQ z) (hzU : z ∈ U)
    (hUy : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    Nat.card U = 2 ∨ Nat.card U = 8 ∨ Nat.card U = 32 := by
  classical
  have hyyy : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy3, pow_three, ← mul_assoc] at this
    exact this
  have hUy' : ∀ u ∈ U, y⁻¹ * u * y ∈ U := by
    intro u hu
    have h1 := hUy u hu
    have h2 := hUy _ h1
    have : y⁻¹ * u * y = y * (y * u * y⁻¹) * y⁻¹ := by
      calc y⁻¹ * u * y = (y * y * y) * (y⁻¹ * u * y) * (y * y * y)⁻¹ := by rw [hyyy]; group
        _ = y * (y * u * y⁻¹) * y⁻¹ := by group
    rw [this]; exact h2
  set S : Set G := (U : Set G) \ {1, z}
  have hz1 : (1 : G) ≠ z := (z_ne_one hyp).symm
  let σ : Equiv.Perm ↥S :=
    { toFun := fun u => ⟨y * u * y⁻¹, by
        refine ⟨hUy u u.2.1, ?_⟩
        intro hm
        rcases hm with hm | hm
        · apply u.2.2; left
          have := congrArg (fun w => y⁻¹ * w * y) hm
          simpa [mul_assoc] using this
        · apply u.2.2; right
          have hyz : y⁻¹ * z * y = z := by
            have := Subgroup.mem_centralizer_singleton_iff.1 hy
            calc y⁻¹ * z * y = y⁻¹ * (y * z) := by rw [mul_assoc, this]
              _ = z := by group
          have := congrArg (fun w => y⁻¹ * w * y) (Set.mem_singleton_iff.1 hm)
          rw [hyz] at this
          simpa [mul_assoc] using this⟩
      invFun := fun u => ⟨y⁻¹ * u * y, by
        refine ⟨hUy' u u.2.1, ?_⟩
        intro hm
        rcases hm with hm | hm
        · apply u.2.2; left
          have := congrArg (fun w => y * w * y⁻¹) hm
          simpa [mul_assoc] using this
        · apply u.2.2; right
          have hyz : y * z * y⁻¹ = z := by
            have := Subgroup.mem_centralizer_singleton_iff.1 hy
            calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [this]
              _ = z := by group
          have := congrArg (fun w => y * w * y⁻¹) (Set.mem_singleton_iff.1 hm)
          rw [hyz] at this
          simpa [mul_assoc] using this⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc]) }
  have hσ3 : σ ^ 3 = 1 := by
    ext u
    show y * (y * (y * u * y⁻¹) * y⁻¹) * y⁻¹ = u
    calc y * (y * (y * (u : G) * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * u * (y * y * y)⁻¹ := by group
      _ = u := by rw [hyyy]; group
  have hfix : ∀ u, σ u ≠ u := by
    intro u hu
    have hu' : y * (u : G) * y⁻¹ = u := congrArg Subtype.val hu
    rcases eq_of_conj_mem hyp hy hy3 (hUQ u.2.1) (Or.inl hu') with h | h
    · exact u.2.2 (Or.inl h)
    · exact u.2.2 (Or.inr h)
  have h3 := three_dvd_card_of_fpf σ hσ3 hfix
  have hsub : ({1, z} : Set G) ⊆ (U : Set G) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact U.one_mem
    · exact hzU
  have hS : S.ncard = (U : Set G).ncard - 2 := by
    rw [Set.ncard_sdiff hsub, Set.ncard_pair hz1]
  have hU : Nat.card U = (U : Set G).ncard := Nat.card_coe_set_eq _
  have hSc : Nat.card ↥S = S.ncard := Nat.card_coe_set_eq _
  have hdvd : Nat.card U ∣ 32 := by
    rw [← card_ascQ hyp]; exact Subgroup.card_dvd_of_le hUQ
  have hge : 2 ≤ Nat.card U := by
    rw [hU]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hz1] at this
    exact this
  rw [hSc, hS, ← hU] at h3
  have hd : Nat.divisors 32 = {1, 2, 4, 8, 16, 32} := by decide
  have hmem : Nat.card U ∈ Nat.divisors 32 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  rw [hd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h <;> rw [h] at h3 hge ⊢ <;> omega

theorem mul_self_mul_self_eq_one {y : G} (hy3 : orderOf y = 3) : y * y * y = 1 := by
  have := pow_orderOf_eq_one y
  rw [hy3, pow_three, ← mul_assoc] at this
  exact this

theorem inv_conj_mem {y : G} (hy3 : orderOf y = 3) {U : Subgroup G}
    (hUy : ∀ u ∈ U, y * u * y⁻¹ ∈ U) {u : G} (hu : u ∈ U) : y⁻¹ * u * y ∈ U := by
  have hyyy := mul_self_mul_self_eq_one hy3
  have : y⁻¹ * u * y = y * (y * u * y⁻¹) * y⁻¹ := by
    calc y⁻¹ * u * y = (y * y * y) * (y⁻¹ * u * y) * (y * y * y)⁻¹ := by rw [hyyy]; group
      _ = y * (y * u * y⁻¹) * y⁻¹ := by group
  rw [this]
  exact hUy _ (hUy u hu)

theorem trip [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy : y ∈ ascH z) (hy3 : orderOf y = 3)
    {s : G} (hsQ : s ∈ ascQ z) :
    s * (y * s * y⁻¹) * (y * (y * s * y⁻¹) * y⁻¹) = 1 ∨
      s * (y * s * y⁻¹) * (y * (y * s * y⁻¹) * y⁻¹) = z := by
  have hE := extraspecialAt_ascQ hyp
  have hyyy := mul_self_mul_self_eq_one hy3
  set s' := y * s * y⁻¹ with hs'
  set s'' := y * s' * y⁻¹ with hs''
  have hs'Q : s' ∈ ascQ z := conj_mem_ascQ hy hsQ
  have hs''Q : s'' ∈ ascQ z := conj_mem_ascQ hy hs'Q
  have hws : s' * s'' ∈ ascQ z := (ascQ z).mul_mem hs'Q hs''Q
  have hm : s * s' * s'' ∈ ascQ z := (ascQ z).mul_mem ((ascQ z).mul_mem hsQ hs'Q) hs''Q
  have hys'' : y * s'' * y⁻¹ = s := by
    calc y * s'' * y⁻¹ = (y * y * y) * s * (y * y * y)⁻¹ := by rw [hs'', hs']; group
      _ = s := by rw [hyyy]; group
  have hconj : y * (s * s' * s'') * y⁻¹ = s' * s'' * s := by
    calc y * (s * s' * s'') * y⁻¹ = (y * s * y⁻¹) * (y * s' * y⁻¹) * (y * s'' * y⁻¹) := by group
      _ = s' * s'' * s := by rw [hys'']
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hE.sq_eq
  apply eq_of_conj_mem hyp hy hy3 hm
  rw [hconj]
  rcases hE.comm_mem s hsQ (s' * s'') hws with h | h
  · left
    calc s' * s'' * s = (s * (s' * s'') * s⁻¹ * (s' * s'')⁻¹)⁻¹ * (s * (s' * s'')) := by group
      _ = s * s' * s'' := by rw [h]; group
  · right
    calc s' * s'' * s = (s * (s' * s'') * s⁻¹ * (s' * s'')⁻¹)⁻¹ * (s * (s' * s'')) := by group
      _ = z⁻¹ * (s * s' * s'') := by rw [h]; group
      _ = s * s' * s'' * z := by rw [hzinv, hE.central _ hm]

@[expose] def lineOf (z s y : G) : Subgroup G := Subgroup.closure {z, s, y * s * y⁻¹}

theorem closure_elem {T : Set G} (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hT2 : ∀ a ∈ T, a * a = 1) :
    ∀ a ∈ Subgroup.closure T, ∀ b ∈ Subgroup.closure T, a * a = 1 ∧ a * b = b * a := by
  have hcomm := Subgroup.isMulCommutative_closure (k := T) (fun x hx y hy _ => hT x hx y hy)
  have hab : ∀ a ∈ Subgroup.closure T, ∀ b ∈ Subgroup.closure T, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : Subgroup.closure T)
      ⟨b, hb⟩)
  intro a ha b hb
  refine ⟨?_, hab a ha b hb⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hT2 x hx
  | one => exact one_mul 1
  | mul x y hx hy ihx ihy =>
    have hxy := hab x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ihx, inv_one]

theorem lineOf_facts [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy : y ∈ ascH z)
    (hy3 : orderOf y = 3) {s : G} (hsQ : s ∈ ascQ z) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hsz : s ≠ z) :
    lineOf z s y ≤ ascQ z ∧ Nat.card ↥(lineOf z s y) = 8 ∧
      (∀ a ∈ lineOf z s y, ∀ b ∈ lineOf z s y, a * a = 1 ∧ a * b = b * a) ∧
      z ∈ lineOf z s y ∧ s ∈ lineOf z s y ∧ y * s * y⁻¹ ∈ lineOf z s y ∧
      (∀ u ∈ lineOf z s y, y * u * y⁻¹ ∈ lineOf z s y) := by
  have hE := extraspecialAt_ascQ hyp
  set s' := y * s * y⁻¹ with hs'
  have hs'Q : s' ∈ ascQ z := conj_mem_ascQ hy hsQ
  have hs'2 : s' * s' = 1 := by
    calc s' * s' = y * (s * s) * y⁻¹ := by rw [hs']; group
      _ = 1 := by rw [hs2]; group
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hy
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [this]
      _ = z := by group
  obtain ⟨c, hc, hcm⟩ : ∃ c, (c = 1 ∨ c = z) ∧ s * s' * (y * s' * y⁻¹) = c :=
    ⟨_, trip hyp hy hy3 hsQ, rfl⟩
  have hs'' : y * s' * y⁻¹ = s' * s * c := by
    calc y * s' * y⁻¹ = (s * s')⁻¹ * (s * s' * (y * s' * y⁻¹)) := by group
      _ = s'⁻¹ * s⁻¹ * c := by rw [hcm]; group
      _ = s' * s * c := by
        rw [inv_eq_of_mul_eq_one_right hs'2, inv_eq_of_mul_eq_one_right hs2]
  have hc2 : c * c = 1 := by
    rcases hc with rfl | rfl
    · exact one_mul 1
    · exact hE.sq_eq
  have hccent : ∀ q ∈ ascQ z, q * c = c * q := by
    rcases hc with rfl | rfl
    · intro q _; simp
    · exact hE.central
  have hs''2 : (y * s' * y⁻¹) * (y * s' * y⁻¹) = 1 := by
    calc (y * s' * y⁻¹) * (y * s' * y⁻¹) = y * (s' * s') * y⁻¹ := by group
      _ = 1 := by rw [hs'2]; group
  have hcomm : s * s' = s' * s := by
    have h1 : (s' * s * c) * (s' * s * c) = 1 := by rw [← hs'']; exact hs''2
    have hcc : (s' * s) * c = c * (s' * s) := hccent _ ((ascQ z).mul_mem hs'Q hsQ)
    have h2 : (s' * s) * (s' * s) = 1 := by
      calc (s' * s) * (s' * s) = (s' * s) * (s' * s) * (c * c) := by rw [hc2, mul_one]
        _ = (s' * s) * ((s' * s) * c) * c := by group
        _ = (s' * s) * (c * (s' * s)) * c := by rw [hcc]
        _ = (s' * s * c) * (s' * s * c) := by group
        _ = 1 := h1
    calc s * s' = s * s' * (s' * s * (s' * s)) := by rw [h2, mul_one]
      _ = s * (s' * s') * s * s' * s := by group
      _ = s * s * s' * s := by rw [hs'2]; group
      _ = s' * s := by rw [hs2]; group
  have hT : ∀ a ∈ ({z, s, s'} : Set G), ∀ b ∈ ({z, s, s'} : Set G), a * b = b * a := by
    have hzs : z * s = s * z := (hE.central s hsQ).symm
    have hzs' : z * s' = s' * z := (hE.central s' hs'Q).symm
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | rfl | assumption | exact hzs.symm | exact hzs'.symm | exact hcomm.symm
  have hT2 : ∀ a ∈ ({z, s, s'} : Set G), a * a = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hE.sq_eq
    · exact hs2
    · exact hs'2
  have hL := closure_elem hT hT2
  have hzL : z ∈ lineOf z s y := Subgroup.subset_closure (by simp)
  have hsL : s ∈ lineOf z s y := Subgroup.subset_closure (by simp)
  have hs'L : s' ∈ lineOf z s y := Subgroup.subset_closure (by simp [hs'])
  have hcL : c ∈ lineOf z s y := by
    rcases hc with rfl | rfl
    · exact one_mem _
    · exact hzL
  have hLQ : lineOf z s y ≤ ascQ z := by
    refine (Subgroup.closure_le _).2 ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hE.mem
    · exact hsQ
    · exact hs'Q
  have hle8 : Nat.card ↥(lineOf z s y) ≤ 8 :=
    hE.card_abelian_le hLQ (fun a ha b hb => (hL a ha b hb).2)
  have hzs : z * s = s * z := (hE.central s hsQ).symm
  set V := fourGroup z s hE.sq_eq hs2 hzs with hV
  have hVcard : Nat.card ↥V = 4 := card_fourGroup hE.ne_one hs1 hsz
  have hVL : V ≤ lineOf z s y := by
    intro x hx
    rcases mem_fourGroup.1 hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hzL
    · exact hsL
    · exact mul_mem hzL hsL
  have hs'V : s' ∉ V := by
    intro hx
    rcases mem_fourGroup.1 hx with h | h | h | h
    · apply hs1
      have := congrArg (fun w => y⁻¹ * w * y) h
      simpa [hs', mul_assoc] using this
    · apply hsz
      have := congrArg (fun w => y⁻¹ * w * y) h
      have hyz' : y⁻¹ * z * y = z := by
        have hc := Subgroup.mem_centralizer_singleton_iff.1 hy
        calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
          _ = y⁻¹ * (y * z) := by rw [← hc]
          _ = z := by group
      rw [hyz'] at this
      simpa [hs', mul_assoc] using this
    · rcases eq_of_conj_mem hyp hy hy3 hsQ (Or.inl h) with h' | h'
      · exact hs1 h'
      · exact hsz h'
    · rcases eq_of_conj_mem hyp hy hy3 hsQ (Or.inr (h.trans hzs)) with h' | h'
      · exact hs1 h'
      · exact hsz h'
  have hVlt : V < lineOf z s y := lt_of_le_of_ne hVL (fun h => hs'V (h ▸ hs'L))
  have hcardlt := Subgroup.card_lt_of_lt hVlt
  have hdvd : Nat.card ↥V ∣ Nat.card ↥(lineOf z s y) := Subgroup.card_dvd_of_le hVL
  rw [hVcard] at hcardlt hdvd
  have h8 : Nat.card ↥(lineOf z s y) = 8 := by
    obtain ⟨k, hk⟩ := hdvd
    have : k = 2 := by omega
    omega
  refine ⟨hLQ, h8, hL, hzL, hsL, hs'L, ?_⟩
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [hyz]; exact hzL
    · exact hs'L
    · rw [hs'']; exact mul_mem (mul_mem hs'L hsL) hcL
  | one => simp
  | mul a b _ _ iha ihb =>
    have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [this]; exact mul_mem iha ihb
  | inv a _ iha =>
    have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem iha

theorem z_mem_of_card_eight [Finite G] {Q : Subgroup G} (hE : ExtraspecialAt Q z)
    {A : Subgroup G} (hA : A ≤ Q) (hA8 : Nat.card ↥A = 8)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : z ∈ A := by
  by_contra hz
  set B := Subgroup.closure ((A : Set G) ∪ {z}) with hB
  have hS : ∀ a ∈ (A : Set G) ∪ {z}, ∀ b ∈ (A : Set G) ∪ {z}, a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · exact hAab a ha b hb
    · rw [Set.mem_singleton_iff.1 hb]; exact hE.central a (hA ha)
    · rw [Set.mem_singleton_iff.1 ha]; exact (hE.central b (hA hb)).symm
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
  have hcomm := Subgroup.isMulCommutative_closure (k := (A : Set G) ∪ {z})
    (fun x hx y hy _ => hS x hx y hy)
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : B) ⟨b, hb⟩)
  have hBQ : B ≤ Q := (Subgroup.closure_le _).2
    (Set.union_subset (fun x hx => hA hx) (Set.singleton_subset_iff.2 hE.mem))
  have hAB : A < B := lt_of_le_of_ne (fun x hx => Subgroup.subset_closure (Or.inl hx))
    (fun h => hz (h ▸ Subgroup.subset_closure (Or.inr rfl)))
  have h1 := Subgroup.card_lt_of_lt hAB
  have h2 := hE.card_abelian_le hBQ hBab
  omega

theorem inter_eq_of_ne [Finite G] {X Y V : Subgroup G} (hX8 : Nat.card ↥X = 8)
    (hY8 : Nat.card ↥Y = 8) (hV4 : Nat.card ↥V = 4) (hVX : V ≤ X) (hVY : V ≤ Y) (hXY : X ≠ Y) :
    ((X : Set G) ∩ (Y : Set G)) = (V : Set G) := by
  have hle : V ≤ X ⊓ Y := le_inf hVX hVY
  have h1 : Nat.card ↥V ∣ Nat.card ↥(X ⊓ Y) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(X ⊓ Y) ∣ Nat.card ↥X := Subgroup.card_dvd_of_le inf_le_left
  have h3 : Nat.card ↥(X ⊓ Y) ≠ 8 := by
    intro h
    apply hXY
    have hXle : X ≤ Y := by
      have : X ⊓ Y = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hX8])
      rw [← this]; exact inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hXle (by rw [hX8, hY8])
  rw [hV4] at h1
  rw [hX8] at h2
  have h4 : Nat.card ↥(X ⊓ Y) = 4 := by
    have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    have hmem : Nat.card ↥(X ⊓ Y) ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨h2, by norm_num⟩
    rw [hd] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h <;> rw [h] at h1 h3 ⊢ <;> omega
  have heq : X ⊓ Y = V := (Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hV4])).symm
  rw [← heq]
  rfl

theorem eq_or_eq_of_three [Finite G] {Q : Subgroup G} (hE : ExtraspecialAt Q z) {s : G}
    (hsQ : s ∈ Q) (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z) {A B C : Subgroup G}
    (hA : A ≤ Q) (hB : B ≤ Q) (hC : C ≤ Q)
    (hA8 : Nat.card ↥A = 8) (hB8 : Nat.card ↥B = 8) (hC8 : Nat.card ↥C = 8)
    (hAe : ∀ a ∈ A, ∀ b ∈ A, a * a = 1 ∧ a * b = b * a)
    (hBe : ∀ a ∈ B, ∀ b ∈ B, a * a = 1 ∧ a * b = b * a)
    (hCe : ∀ a ∈ C, ∀ b ∈ C, a * a = 1 ∧ a * b = b * a)
    (hsA : s ∈ A) (hsB : s ∈ B) (hsC : s ∈ C) : A = B ∨ A = C ∨ B = C := by
  classical
  obtain ⟨h16, x, hxP, hxx⟩ := hE.exists_sq_eq_of_noncentral hsQ hs1 hsz
  set P := Q ⊓ Subgroup.centralizer ({s} : Set G) with hP
  have hle : ∀ X : Subgroup G, X ≤ Q → (∀ a ∈ X, ∀ b ∈ X, a * a = 1 ∧ a * b = b * a) →
      s ∈ X → X ≤ P := by
    intro X hX hXe hsX a ha
    exact ⟨hX ha, Subgroup.mem_centralizer_singleton_iff.2 (hXe a ha s hsX).2⟩
  have hzA := z_mem_of_card_eight hE hA hA8 (fun a ha b hb => (hAe a ha b hb).2)
  have hzB := z_mem_of_card_eight hE hB hB8 (fun a ha b hb => (hBe a ha b hb).2)
  have hzC := z_mem_of_card_eight hE hC hC8 (fun a ha b hb => (hCe a ha b hb).2)
  have hzs : z * s = s * z := (hE.central s hsQ).symm
  set V := fourGroup z s hE.sq_eq hs2 hzs with hV
  have hV4 : Nat.card ↥V = 4 := card_fourGroup hE.ne_one hs1 hsz
  have hVle : ∀ X : Subgroup G, z ∈ X → s ∈ X → V ≤ X := by
    intro X hz hs a ha
    rcases mem_fourGroup.1 ha with rfl | rfl | rfl | rfl
    · exact X.one_mem
    · exact hz
    · exact hs
    · exact X.mul_mem hz hs
  by_contra hne
  push Not at hne
  obtain ⟨hAB, hAC, hBC⟩ := hne
  have iAB := inter_eq_of_ne hA8 hB8 hV4 (hVle A hzA hsA) (hVle B hzB hsB) hAB
  have iAC := inter_eq_of_ne hA8 hC8 hV4 (hVle A hzA hsA) (hVle C hzC hsC) hAC
  have iBC := inter_eq_of_ne hB8 hC8 hV4 (hVle B hzB hsB) (hVle C hzC hsC) hBC
  have nA : (A : Set G).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hA8
  have nB : (B : Set G).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hB8
  have nC : (C : Set G).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hC8
  have nV : (V : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hV4
  have nP : (P : Set G).ncard = 16 := by rw [← Nat.card_coe_set_eq]; exact h16
  have u1 := Set.ncard_union_add_ncard_inter (A : Set G) (B : Set G)
  rw [iAB, nA, nB, nV] at u1
  have u2 := Set.ncard_union_add_ncard_inter ((A : Set G) ∪ (B : Set G)) (C : Set G)
  have hinter : ((A : Set G) ∪ (B : Set G)) ∩ (C : Set G) = (V : Set G) := by
    rw [Set.union_inter_distrib_right, iAC, iBC, Set.union_self]
  rw [hinter, nC, nV] at u2
  have hsub : (A : Set G) ∪ (B : Set G) ∪ (C : Set G) ⊆ (P : Set G) := by
    intro a ha
    rcases ha with (ha | ha) | ha
    · exact hle A hA hAe hsA ha
    · exact hle B hB hBe hsB ha
    · exact hle C hC hCe hsC ha
  have heq : (A : Set G) ∪ (B : Set G) ∪ (C : Set G) = (P : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  have hx : x ∈ (A : Set G) ∪ (B : Set G) ∪ (C : Set G) := by rw [heq]; exact hxP
  have hx1 : x * x = 1 := by
    rcases hx with (hx | hx) | hx
    · exact (hAe x hx x hx).1
    · exact (hBe x hx x hx).1
    · exact (hCe x hx x hx).1
  exact hE.ne_one (hxx.symm.trans hx1)

theorem exists_compl_four [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy : y ∈ ascH z)
    (hy3 : orderOf y = 3) {F : Subgroup G} (hFQ : F ≤ ascQ z) (hF8 : Nat.card ↥F = 8)
    (hFe : ∀ a ∈ F, ∀ b ∈ F, a * a = 1 ∧ a * b = b * a) (hzF : z ∈ F)
    (hFy : ∀ f ∈ F, y * f * y⁻¹ ∈ F) :
    ∃ A : Subgroup G, A ≤ F ∧ Nat.card ↥A = 4 ∧ z ∉ A ∧
      ∀ v : G, (∀ f ∈ F, v * f * v⁻¹ ∈ F) → v * y * v⁻¹ = y⁻¹ →
        ∀ a ∈ A, v * a * v⁻¹ ∈ A := by
  have hE := extraspecialAt_ascQ hyp
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hy
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [this]
      _ = z := by group
  let φ : ↥F →* ↥F :=
    { toFun := fun f => ⟨f * (y * f * y⁻¹)⁻¹, F.mul_mem f.2 (F.inv_mem (hFy f f.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun f g => Subtype.ext (by
        show ((f : G) * g) * (y * ((f : G) * g) * y⁻¹)⁻¹ =
          ((f : G) * (y * f * y⁻¹)⁻¹) * ((g : G) * (y * g * y⁻¹)⁻¹)
        have hc := (hFe _ (F.inv_mem (hFy f f.2)) _ (F.mul_mem g.2 (F.inv_mem (hFy g g.2)))).2
        calc ((f : G) * g) * (y * ((f : G) * g) * y⁻¹)⁻¹ =
            f * (((g : G) * (y * g * y⁻¹)⁻¹) * (y * f * y⁻¹)⁻¹) := by group
          _ = f * ((y * f * y⁻¹)⁻¹ * ((g : G) * (y * g * y⁻¹)⁻¹)) := by rw [hc]
          _ = ((f : G) * (y * f * y⁻¹)⁻¹) * ((g : G) * (y * g * y⁻¹)⁻¹) := by group) }
  have hφ : ∀ f : ↥F, ((φ f : ↥F) : G) = f * (y * f * y⁻¹)⁻¹ := fun f => rfl
  have hker : ∀ f ∈ φ.ker, f = 1 ∨ f = ⟨z, hzF⟩ := by
    intro f hf
    have h1 : (f : G) * (y * f * y⁻¹)⁻¹ = 1 := by
      rw [← hφ]; exact congrArg Subtype.val (MonoidHom.mem_ker.1 hf)
    have h2 : y * (f : G) * y⁻¹ = f := (mul_inv_eq_one.1 h1).symm
    rcases eq_of_conj_mem hyp hy hy3 (hFQ f.2) (Or.inl h2) with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  have hzker : (⟨z, hzF⟩ : ↥F) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hφ]
    show z * (y * z * y⁻¹)⁻¹ = 1
    rw [hyz, mul_inv_cancel]
  have hker2 : Nat.card ↥φ.ker = 2 := by
    have hle := card_le_two_of_forall hker
    have hne : φ.ker ≠ ⊥ := by
      intro h
      rw [h] at hzker
      have := (Subgroup.mem_bot.1 hzker)
      exact hE.ne_one (congrArg Subtype.val this)
    have hlt := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    omega
  have hrange : Nat.card ↥φ.range = 4 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker2, hF8] at h1
    omega
  refine ⟨φ.range.map F.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [← hrange]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective φ.range F.subtype
      F.subtype_injective).toEquiv).symm
  · intro hz
    obtain ⟨a, ⟨f, rfl⟩, hfa⟩ := Subgroup.mem_map.1 hz
    have h1 : (f : G) * (y * f * y⁻¹)⁻¹ = z := hfa
    have h2 : y * (f : G) * y⁻¹ = f * z := by
      have : y * (f : G) * y⁻¹ = z⁻¹ * f := by
        calc y * (f : G) * y⁻¹ = ((f : G) * (y * f * y⁻¹)⁻¹)⁻¹ * f := by group
          _ = z⁻¹ * f := by rw [h1]
      rw [this, inv_eq_of_mul_eq_one_right hE.sq_eq, hE.central f (hFQ f.2)]
    rcases eq_of_conj_mem hyp hy hy3 (hFQ f.2) (Or.inr h2) with h | h
    · rw [h] at h1; simp at h1; exact hE.ne_one h1.symm
    · rw [h, hyz, mul_inv_cancel] at h1; exact hE.ne_one h1.symm
  · intro v hvF hvy a ha
    obtain ⟨b, ⟨f, rfl⟩, rfl⟩ := Subgroup.mem_map.1 ha
    set f' := v * (f : G) * v⁻¹ with hf'
    have hf'F : f' ∈ F := hvF f f.2
    set f'' := y⁻¹ * f' * y with hf''
    have hf''F : f'' ∈ F := inv_conj_mem hy3 hFy hf'F
    have hyf'' : y * f'' * y⁻¹ = f' := by rw [hf'']; group
    have hval : v * ((f : G) * (y * f * y⁻¹)⁻¹) * v⁻¹ = (f'' * (y * f'' * y⁻¹)⁻¹)⁻¹ := by
      rw [hyf'']
      have hvy' : v * y⁻¹ * v⁻¹ = y := by
        calc v * y⁻¹ * v⁻¹ = (v * y * v⁻¹)⁻¹ := by group
          _ = y := by rw [hvy, inv_inv]
      calc v * ((f : G) * (y * f * y⁻¹)⁻¹) * v⁻¹ =
          f' * ((v * y * v⁻¹) * f' * (v * y⁻¹ * v⁻¹))⁻¹ := by rw [hf']; group
        _ = f' * (y⁻¹ * f' * y)⁻¹ := by rw [hvy, hvy']
        _ = (f'' * f'⁻¹)⁻¹ := by rw [hf'']; group
    rw [show ((F.subtype : ↥F →* G) (φ f) : G) = (f : G) * (y * f * y⁻¹)⁻¹ from rfl, hval]
    refine Subgroup.inv_mem _ (Subgroup.mem_map.2 ⟨φ ⟨f'', hf''F⟩, ⟨⟨f'', hf''F⟩, rfl⟩, rfl⟩)

end CFSG.GH74.M12.Thm1
