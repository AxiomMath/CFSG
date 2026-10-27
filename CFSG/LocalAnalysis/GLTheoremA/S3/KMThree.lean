module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KMMin
public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S3.KM

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A T : Subgroup G}

theorem Ctx.exists_ne_one (c : Ctx p A T) : ∃ b ∈ A, b ≠ 1 := by
  by_contra h
  push Not at h
  exact c.ne_bot (eq_bot_iff.2 fun x hx => mem_bot.2 (h x hx))

theorem Ctx.exists_noncomm (c : Ctx p A T) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    ∃ t ∈ T, b * t ≠ t * b := by
  by_contra h
  push Not at h
  exact hb1 (c.faithful b hb h)

theorem Ctx.T_ne_bot (c : Ctx p A T) : T ≠ ⊥ := by
  obtain ⟨b, hb, hb1⟩ := c.exists_ne_one
  obtain ⟨t, ht, hne⟩ := c.exists_noncomm hb hb1
  intro hbot
  rw [hbot, mem_bot] at ht
  exact hne (by rw [ht]; simp)

theorem Ctx.hyp_exists_ne_one (c : Ctx p A T) {H : Subgroup G} (hH : IsHyp p A H) :
    ∃ b ∈ H, b ≠ 1 := by
  by_contra h
  push Not at h
  have hH1 : H = ⊥ := eq_bot_iff.2 fun x hx => mem_bot.2 (h x hx)
  have h1 : Nat.card H = 1 := by rw [hH1]; simp
  have h2 := hH.2
  rw [h1, one_mul] at h2
  have h3 := c.card_ge
  have h4 : p < p ^ 3 := by
    have := c.prime.two_le
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right c.prime.one_lt (by norm_num)
  omega

theorem Ctx.card_eq_four_of_fpf (c : Ctx p A T) (hp3 : p = 3) {H : Subgroup G} (hH : IsHyp p A H)
    {U : Subgroup G} (hU : IsElemAbelian 2 U) (hUT : U ≤ T)
    (hUC : ∀ u ∈ U, ∀ h ∈ H, h * u = u * h) (hUn : A ≤ normalizer (U : Set G)) (hU1 : U ≠ ⊥)
    (hfix : ∀ y ∈ U, (∀ a ∈ A, a * y = y * a) → y = 1) : Nat.card U = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα, hαH⟩ := hH.exists_not_mem c.prime
  have hsup := hH.sup_zpowers c.prime hα hαH
  have hmod : Nat.card U ≡ 1 [MOD p] := by
    refine card_modEq_one_of_inf_centralizer_eq_bot c.prime (c.pow_p hα) (hUn hα) ?_
    intro y hy hyα
    exact hfix y hy (commute_of_sup_zpowers hsup (fun h hh => hUC y hy h hh) hyα)
  have hle : Nat.card U ≤ 4 :=
    c.rank1 hH (V := U) (fun x hx => Subgroup.mem_inf.2 ⟨hUT hx,
      mem_centralizer_iff.2 fun h hh => hUC x hx h hh⟩) hU
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hU).exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hU1
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.1 hk
  unfold Nat.ModEq at hmod
  subst hp3
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · exact absurd rfl hk0
  · rw [hk] at hmod
    norm_num at hmod
  · rw [hk]
    norm_num

theorem Ctx.exists_U0 (c : Ctx p A T) (hp3 : p = 3)
    (hfix : ∀ y ∈ zOmega T, (∀ a ∈ A, a * y = y * a) → y = 1) :
    ∃ H₀ : Subgroup G, IsHyp p A H₀ ∧
      Nat.card (zOmega T ⊓ centralizer (H₀ : Set G) : Subgroup G) = 4 := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => c.comm ha hb
  have hZn : A ≤ normalizer (zOmega T : Set G) := le_normalizer_zOmega c.norm
  have hZ2 : IsPGroup 2 (zOmega T) := c.two.to_le zOmega_le
  have hex : ∃ H₀ : Subgroup G, IsHyp p A H₀ ∧ zOmega T ⊓ centralizer (H₀ : Set G) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply zOmega_ne_bot c.two c.T_ne_bot
    rw [eq_bot_iff]
    exact le_of_forall_isHyp c.prime c.elem c.ne_bot hZn (c.not_dvd_card hZ2)
      (fun H hH => (hcon H hH).le)
  obtain ⟨H₀, hH₀, hne⟩ := hex
  refine ⟨H₀, hH₀, c.card_eq_four_of_fpf hp3 hH₀ ?_ ?_ ?_ ?_ hne ?_⟩
  · exact isElemAbelian_mono (isElemAbelian_zOmega T) inf_le_left
  · exact inf_le_left.trans zOmega_le
  · intro u hu h hh
    exact mem_centralizer_iff.1 (mem_inf.1 hu).2 h hh
  · exact le_normalizer_inf_centralizer hAc hH₀.1 hZn
  · intro y hy hyA
    exact hfix y (mem_inf.1 hy).1 hyA

theorem Ctx.exists_centralizer_ne_one_of_three (c : Ctx p A T) (hp3 : p = 3) :
    ∃ t ∈ T, t ≠ 1 ∧ ∀ a ∈ A, a * t = t * a := by
  by_contra hcon
  push Not at hcon
  have hC : ∀ t ∈ T, (∀ a ∈ A, a * t = t * a) → t = 1 := fun t ht h => by
    by_contra h1
    obtain ⟨a, ha, hne⟩ := hcon t ht h1
    exact hne (h a ha)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => c.comm ha hb
  obtain ⟨H₀, hH₀, hU₀⟩ := c.exists_U0 hp3 (fun y hy hyA => hC y (zOmega_le hy) hyA)
  set U₀ := zOmega T ⊓ centralizer (H₀ : Set G) with hU₀def
  obtain ⟨b, hbH₀, hb1⟩ := c.hyp_exists_ne_one hH₀
  have hbA : b ∈ A := hH₀.1 hbH₀
  obtain ⟨t, htT, htb⟩ := c.exists_noncomm hbA hb1
  obtain ⟨S, H, hS⟩ := exists_atom c.prime c.odd c.elem c.two c.norm hbA ⟨t, htT, htb⟩
  have hsup : H ⊔ zpowers b = A := hS.hyp.sup_zpowers c.prime hbA hS.not_mem
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    by_contra hnc
    have hcomm : ⁅S, S⁆ ≠ ⊥ := by
      intro h
      apply hnc
      intro x hx y hy
      have := commutator_eq_bot_iff_le_centralizer.1 h hx
      exact (mem_centralizer_iff.1 this y hy).symm
    rw [hS.commutator_eq_squares] at hcomm
    obtain ⟨f, hf, hf1⟩ := exists_mem_ne_one hcomm
    have hfS : f ∈ S := hS.squares_le hf
    have hfA : ∀ a ∈ A, a * f = f * a :=
      commute_of_sup_zpowers hsup (fun h hh => hS.cent f hfS h hh) (hS.squares_b hf)
    exact hf1 (hC f (hS.le hfS) hfA)
  have hSe : IsElemAbelian 2 S :=
    ⟨⟨⟨fun a b => Subtype.ext (hSc a a.2 b b.2)⟩⟩, fun x hx => hS.sq_eq_one_of_comm hSc hx⟩
  have hfixS : ∀ y ∈ S, (∀ a ∈ A, a * y = y * a) → y = 1 := fun y hy hyA => hC y (hS.le hy) hyA
  have hS4 : Nat.card S = 4 :=
    c.card_eq_four_of_fpf hp3 hS.hyp hSe hS.le hS.cent hS.inv hS.ne hfixS
  have hSU : S ⊓ U₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyS, hyU⟩ := mem_inf.1 hy
    have hyb : b * y = y * b := mem_centralizer_iff.1 (mem_inf.1 hyU).2 b hbH₀
    have hyA : ∀ a ∈ A, a * y = y * a :=
      commute_of_sup_zpowers hsup (fun h hh => hS.cent y hyS h hh) hyb
    exact mem_bot.2 (hC y (hS.le hyS) hyA)
  have hne : H ≠ H₀ := fun h => hS.not_mem (h ▸ hbH₀)
  have hcard9 : Nat.card (H ⊓ H₀ : Subgroup G) * p ^ 2 = Nat.card A :=
    IsHyp.card_inf c.prime hAc hS.hyp hH₀ hne
  have hUe : IsElemAbelian 2 U₀ := isElemAbelian_mono (isElemAbelian_zOmega T) inf_le_left
  have hcommSU : ∀ x ∈ S, ∀ y ∈ U₀, x * y = y * x := fun x hx y hy =>
    (mem_zOmega.1 (mem_inf.1 hy).1).2.1 x (hS.le hx)
  obtain ⟨hVe, hVcard⟩ := isElemAbelian_sup_of_commuting hSe hUe hcommSU
  have hV16 : Nat.card (S ⊔ U₀ : Subgroup G) = 16 := by
    rw [hSU, Subgroup.card_bot, hS4, hU₀] at hVcard
    omega
  have hVT : S ⊔ U₀ ≤ T ⊓ centralizer ((H ⊓ H₀ : Subgroup G) : Set G) := by
    refine le_inf (sup_le hS.le (inf_le_left.trans zOmega_le)) (sup_le ?_ ?_)
    · intro x hx
      rw [mem_centralizer_iff]
      intro h hh
      exact hS.cent x hx h (mem_inf.1 hh).1
    · intro x hx
      rw [mem_centralizer_iff]
      intro h hh
      exact mem_centralizer_iff.1 (mem_inf.1 hx).2 h (mem_inf.1 hh).2
  have := c.rank2 (inf_le_left.trans hS.hyp.1) hcard9 hVT hVe
  omega

theorem exists_involution_pow {T : Subgroup G} (hT : IsPGroup 2 T) {t : G} (ht : t ∈ T)
    (ht1 : t ≠ 1) : ∃ n : ℕ, (t ^ n) ^ 2 = 1 ∧ t ^ n ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT.exists_orderOf_eq_pow (⟨t, ht⟩ : T)
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact ht1 (orderOf_eq_one_iff.1 (by simpa using hk))
  refine ⟨2 ^ (k - 1), ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ]
    have : k - 1 + 1 = k := by omega
    rw [this, ← hk]
    exact pow_orderOf_eq_one t
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hk] at this
    have h2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 this
    omega

theorem card_two_pow_le_four {n : ℕ} (h : ∃ k : ℕ, n = 2 ^ k) (h4 : n ≤ 4) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  obtain ⟨k, rfl⟩ := h
  have hk : k ≤ 2 := by
    by_contra hk
    push Not at hk
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · left; rfl
  · right; left; rfl
  · right; right; rfl

theorem Ctx.centralizes_of_three (c : Ctx p A T) (hp3 : p = 3) {z : G} (hzZ : z ∈ zOmega T)
    (hz1 : z ≠ 1) (hzA : ∀ a ∈ A, a * z = z * a) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVT : V ≤ T) (hVn : A ≤ normalizer (V : Set G)) :
    ∀ x ∈ V, ∀ a ∈ A, a * x = x * a := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => c.comm ha hb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVle : V ≤ centralizer (A : Set G) := by
    refine le_of_forall_isHyp c.prime c.elem c.ne_bot hVn (c.not_dvd_card (c.two.to_le hVT)) ?_
    intro H hH
    set X := V ⊓ centralizer (H : Set G) with hX
    obtain ⟨α, hα, hαH⟩ := hH.exists_not_mem c.prime
    have hsup := hH.sup_zpowers c.prime hα hαH
    have hXe : IsElemAbelian 2 X := isElemAbelian_mono hV inf_le_left
    have hXT : X ≤ T ⊓ centralizer (H : Set G) := le_inf (inf_le_left.trans hVT) inf_le_right
    have hX4 : Nat.card X ≤ 4 := c.rank1 hH hXT hXe
    have hXn : A ≤ normalizer (X : Set G) := le_normalizer_inf_centralizer hAc hH.1 hVn
    have hXα : X ≤ centralizer ({α} : Set G) := by
      by_contra hnot
      set X₀ := X ⊓ centralizer ({α} : Set G) with hX₀
      have hlt : Nat.card X₀ < Nat.card X := by
        refine lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left) fun heq => hnot ?_
        have : X₀ = X := Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge
        exact this ▸ inf_le_right
      haveI : Fact p.Prime := ⟨c.prime⟩
      have hmod : Nat.card X ≡ Nat.card X₀ [MOD p] :=
        card_modEq_card_inf_centralizer (c.pow_p hα) (hXn hα)
      have hX2 : IsPGroup 2 X := isPGroup_of_isElemAbelian hXe
      have hX₀2 : IsPGroup 2 X₀ := hX2.to_le inf_le_left
      obtain ⟨k, hk⟩ := hX2.exists_card_eq
      obtain ⟨j, hj⟩ := hX₀2.exists_card_eq
      have h1 := card_two_pow_le_four ⟨k, hk⟩ hX4
      have h2 := card_two_pow_le_four ⟨j, hj⟩ (by omega)
      unfold Nat.ModEq at hmod
      subst hp3
      have hX4' : Nat.card X = 4 ∧ Nat.card X₀ = 1 := by omega
      have hze : IsElemAbelian 2 (zpowers z) := by
        refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
        · apply Subtype.ext
          obtain ⟨i, hi⟩ := mem_zpowers_iff.1 a.2
          obtain ⟨j, hj⟩ := mem_zpowers_iff.1 b.2
          show (a : G) * b = b * a
          rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
        · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
            (mem_zOmega.1 hzZ).2.2, one_zpow]
      have hzpT : zpowers z ≤ T := zpowers_le.2 (zOmega_le hzZ)
      have hcomm : ∀ x ∈ X, ∀ y ∈ zpowers z, x * y = y * x := by
        intro x hx y hy
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy
        have h1 : x * z = z * x := (mem_zOmega.1 hzZ).2.1 x (hVT (mem_inf.1 hx).1)
        exact (Commute.zpow_right h1 i : Commute x (z ^ i)).eq
      obtain ⟨hEe, hEcard⟩ := isElemAbelian_sup_of_commuting hXe hze hcomm
      have hXz : X ⊓ zpowers z = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨hyX, hyz⟩ := mem_inf.1 hy
        have hyα : y ∈ centralizer ({α} : Set G) := by
          rw [mem_centralizer_singleton_iff]
          obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hyz
          exact ((Commute.zpow_right (hzA α hα) i : Commute α (z ^ i)).eq).symm
        have hyX₀ : y ∈ X₀ := mem_inf.2 ⟨hyX, hyα⟩
        have hX₀bot : X₀ = ⊥ := Subgroup.card_eq_one.1 hX4'.2
        rw [hX₀bot] at hyX₀
        exact hyX₀
      have hz2 : Nat.card (zpowers z) = 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (mem_zOmega.1 hzZ).2.2 hz1
      rw [hXz, Subgroup.card_bot, hX4'.1, hz2] at hEcard
      have hEle : X ⊔ zpowers z ≤ T ⊓ centralizer (H : Set G) := by
        refine sup_le hXT (le_inf hzpT ?_)
        intro x hx
        rw [mem_centralizer_iff]
        intro h hh
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
        exact (Commute.zpow_right (hzA h (hH.1 hh)) i : Commute h (z ^ i)).eq
      have := c.rank1 hH hEle hEe
      omega
    intro x hx
    rw [mem_centralizer_iff]
    intro a ha
    exact commute_of_sup_zpowers hsup (fun h hh => (mem_centralizer_iff.1 (mem_inf.1 hx).2 h hh))
      (mem_centralizer_singleton_iff.1 (hXα hx)).symm a ha
  intro x hx a ha
  exact mem_centralizer_iff.1 (hVle hx) a ha

theorem Ctx.exists_central_involution_of_three (c : Ctx p A T) (hp3 : p = 3)
    (hC : ∃ t ∈ T, t ≠ 1 ∧ ∀ a ∈ A, a * t = t * a) :
    ∃ z ∈ zOmega T, z ≠ 1 ∧ ∀ a ∈ A, a * z = z * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hfix : ∀ y ∈ zOmega T, (∀ a ∈ A, a * y = y * a) → y = 1 := fun y hy hyA => by
    by_contra h1
    obtain ⟨a, ha, hne⟩ := hcon y hy h1
    exact hne (hyA a ha)
  obtain ⟨H₀, hH₀, hU₀⟩ := c.exists_U0 hp3 hfix
  set U₀ := zOmega T ⊓ centralizer (H₀ : Set G) with hU₀def
  obtain ⟨t, htT, ht1, htA⟩ := hC
  obtain ⟨n, hn2, hn1⟩ := exists_involution_pow c.two htT ht1
  set c₀ := t ^ n with hc₀
  have hc₀T : c₀ ∈ T := T.pow_mem htT n
  have hc₀A : ∀ a ∈ A, a * c₀ = c₀ * a := fun a ha => (Commute.pow_right (htA a ha) n).eq
  have hze : IsElemAbelian 2 (zpowers c₀) := isElemAbelian_zpowers hn2
  have hzpT : zpowers c₀ ≤ T := zpowers_le.2 hc₀T
  have hUe : IsElemAbelian 2 U₀ := isElemAbelian_mono (isElemAbelian_zOmega T) inf_le_left
  have hcomm : ∀ x ∈ U₀, ∀ y ∈ zpowers c₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy
    have h1 : Commute x c₀ := ((mem_zOmega.1 (mem_inf.1 hx).1).2.1 c₀ hc₀T).symm
    exact (Commute.zpow_right h1 i).eq
  obtain ⟨hEe, hEcard⟩ := isElemAbelian_sup_of_commuting hUe hze hcomm
  have hUc : U₀ ⊓ zpowers c₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyU, hyz⟩ := mem_inf.1 hy
    have hyA : ∀ a ∈ A, a * y = y * a := by
      intro a ha
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hyz
      exact (Commute.zpow_right (hc₀A a ha) i : Commute a (c₀ ^ i)).eq
    exact mem_bot.2 (hfix y (mem_inf.1 hyU).1 hyA)
  have hc2 : Nat.card (zpowers c₀) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hn2 hn1
  rw [hUc, Subgroup.card_bot, hU₀, hc2] at hEcard
  have hEle : U₀ ⊔ zpowers c₀ ≤ T ⊓ centralizer (H₀ : Set G) := by
    refine sup_le (le_inf (inf_le_left.trans zOmega_le) inf_le_right) (le_inf hzpT ?_)
    intro x hx
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
    exact (Commute.zpow_right (hc₀A h (hH₀.1 hh)) i : Commute h (c₀ ^ i)).eq
  have := c.rank1 hH₀ hEle hEe
  omega

theorem conj_mem_map_of_characteristic {T : Subgroup G} {Q : Subgroup T} (hQ : Q.Characteristic)
    {a : G} (ha : a ∈ normalizer (T : Set G)) {x : G} (hx : x ∈ Q.map T.subtype) :
    a * x * a⁻¹ ∈ Q.map T.subtype := by
  obtain ⟨x', hx', rfl⟩ := mem_map.1 hx
  have h := (characteristic_iff_map_le.1 hQ) (T.normalizerMonoidHom ⟨a, ha⟩)
    (mem_map_of_mem _ hx')
  refine mem_map.2 ⟨_, h, ?_⟩
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem Ctx.isCyclic_of_three (c : Ctx p A T) (hp3 : p = 3)
    (hC : ∃ t ∈ T, t ≠ 1 ∧ ∀ a ∈ A, a * t = t * a) :
    ∀ Q : Subgroup T, Q.Characteristic → IsMulCommutative Q → IsCyclic Q := by
  intro Q hQc hQab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzZ, hz1, hzA⟩ := c.exists_central_involution_of_three hp3 hC
  set Q' : Subgroup G := Q.map T.subtype with hQ'
  have hQ'T : Q' ≤ T := Subgroup.map_subtype_le Q
  have hQ'c : ∀ x ∈ Q', ∀ y ∈ Q', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := mem_map.1 hy
    have := hQab.1.comm (⟨x', hx'⟩ : Q) ⟨y', hy'⟩
    exact congrArg (fun q : Q => ((q : T) : G)) this
  have hVn : A ≤ normalizer (omega1 Q' hQ'c : Set G) := by
    intro a ha
    apply mem_normalizer_of_conj_mem
    intro y hy
    refine ⟨conj_mem_map_of_characteristic hQc (c.norm ha) hy.1, ?_⟩
    have : (a * y * a⁻¹) ^ 2 = a * y ^ 2 * a⁻¹ := by
      rw [pow_two, pow_two]; group
    rw [this, hy.2]; group
  have hVe := isElemAbelian_omega1 hQ'c
  have hVT : omega1 Q' hQ'c ≤ T := (omega1_le hQ'c).trans hQ'T
  have hVA := c.centralizes_of_three hp3 hzZ hz1 hzA hVe hVT hVn
  have hV2 : Nat.card (omega1 Q' hQ'c) ≤ 2 :=
    c.rank0 (V := omega1 Q' hQ'c) (le_inf hVT (fun x hx => mem_centralizer_iff.2
      (fun a ha => hVA x hx a ha))) hVe
  haveI := hQab
  letI : CommGroup Q := Group.commGroupOfCenterEqTop Subgroup.center_eq_top
  have hQ2 : IsPGroup 2 Q := IsPGroup.to_subgroup c.two Q
  obtain ⟨e, he⟩ := hQ2.exists_card_eq
  refine CFSG.TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
    e Q hQ2 he ?_
  intro l r hl hr
  have hmem : ∀ w : Q, orderOf w = 2 → ((w : T) : G) ∈ omega1 Q' hQ'c ∧ ((w : T) : G) ≠ 1 := by
    intro w hw
    have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    refine ⟨⟨mem_map.2 ⟨(w : T), w.2, rfl⟩, ?_⟩, ?_⟩
    · have := congrArg (fun q : Q => ((q : T) : G)) hw2
      simpa using this
    · intro h1
      have : w = 1 := Subtype.ext (Subtype.ext h1)
      rw [this, orderOf_one] at hw
      omega
  obtain ⟨hl1, hl2⟩ := hmem l hl
  obtain ⟨hr1, hr2⟩ := hmem r hr
  have := eq_of_card_le_two hV2 hl1 hr1 hl2 hr2
  exact Subtype.ext (Subtype.ext this)

end CFSG.LocalAnalysis.GLTheoremA.S3.KM
