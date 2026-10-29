module

public import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Goldschmidt.G310
open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_modEq_one_of_noFixed [Finite G] {p : ℕ} [Fact p.Prime] {P A : Subgroup G}
    (hP : IsPGroup p P) (hA : P ≤ Subgroup.normalizer (A : Set G))
    (hfix : ∀ a ∈ A, a ≠ 1 → ∃ g ∈ P, g * a ≠ a * g) : Nat.card A ≡ 1 [MOD p] := by
  classical
  let _ : MulAction P A :=
    { smul := fun g a => ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.1 (hA g.2) a).1 a.2⟩
      one_smul := fun a => Subtype.ext (show ((1 : P) : G) * (a : G) * ((1 : P) : G)⁻¹ = a by simp)
      mul_smul := fun g h a => Subtype.ext (show ((g * h : P) : G) * (a : G) * ((g * h : P) : G)⁻¹ =
        (g : G) * ((h : G) * (a : G) * (h : G)⁻¹) * (g : G)⁻¹ by simp [mul_assoc]) }
  have h := hP.card_modEq_card_fixedPoints (α := A)
  have hfp : Nat.card (MulAction.fixedPoints P A) = 1 := by
    have h1 : (⟨1, A.one_mem⟩ : A) ∈ MulAction.fixedPoints P A := fun g =>
      Subtype.ext (show (g : G) * 1 * (g : G)⁻¹ = 1 by simp)
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨_, h1⟩, fun x => ?_⟩
    obtain ⟨⟨a, ha⟩, hx⟩ := x
    refine Subtype.ext (Subtype.ext ?_)
    by_contra hne
    obtain ⟨g, hg, hga⟩ := hfix a ha hne
    have := congrArg Subtype.val (hx ⟨g, hg⟩)
    change g * a * g⁻¹ = a at this
    exact hga (calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [this])
  rwa [hfp] at h

@[expose] def omegaCenterPow (r : ℕ) (S : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ S ∧ (∀ h ∈ S, g * h = h * g) ∧ g ^ r = 1}
  mul_mem' := by
    rintro a b ⟨haS, hac, har⟩ ⟨hbS, hbc, hbr⟩
    refine ⟨S.mul_mem haS hbS, fun h hh => ?_, ?_⟩
    · rw [mul_assoc, hbc h hh, ← mul_assoc, hac h hh, mul_assoc]
    · rw [(Commute.mul_pow (hac b hbS) r), har, hbr, one_mul]
  one_mem' := ⟨S.one_mem, fun h _ => by simp, one_pow r⟩
  inv_mem' := by
    rintro a ⟨haS, hac, har⟩
    refine ⟨S.inv_mem haS, fun h hh => ?_, by rw [inv_pow, har, inv_one]⟩
    have := hac h hh
    calc a⁻¹ * h = a⁻¹ * (h * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * h) * a⁻¹ := by rw [this]
      _ = h * a⁻¹ := by group

theorem mem_omegaCenterPow {r : ℕ} {S : Subgroup G} {g : G} :
    g ∈ omegaCenterPow r S ↔ g ∈ S ∧ (∀ h ∈ S, g * h = h * g) ∧ g ^ r = 1 := Iff.rfl

theorem omegaCenterPow_le (r : ℕ) (S : Subgroup G) : omegaCenterPow r S ≤ S := fun _ hg => hg.1

theorem normalizer_le_normalizer_omegaCenterPow (r : ℕ) (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (omegaCenterPow r S : Set G) := by
  intro g hg
  have hS := Subgroup.mem_normalizer_iff.1 hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨haS, hac, har⟩
    refine ⟨(hS a).1 haS, fun h hh => ?_, by rw [conj_pow, har, mul_one, mul_inv_cancel]⟩
    have hh' : g⁻¹ * h * g ∈ S := by
      have := (hS (g⁻¹ * h * g)).2 (by simpa [mul_assoc] using hh)
      exact this
    have := hac _ hh'
    calc g * a * g⁻¹ * h = g * (a * (g⁻¹ * h * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * h * g) * a) * g⁻¹ := by rw [this]
      _ = h * (g * a * g⁻¹) := by group
  · rintro ⟨haS, hac, har⟩
    refine ⟨(hS a).2 haS, fun h hh => ?_, ?_⟩
    · have hh' : g * h * g⁻¹ ∈ S := (hS h).1 hh
      have := hac _ hh'
      have e : g * (a * h) * g⁻¹ = g * (h * a) * g⁻¹ := by
        calc g * (a * h) * g⁻¹ = g * a * g⁻¹ * (g * h * g⁻¹) := by group
          _ = g * h * g⁻¹ * (g * a * g⁻¹) := this
          _ = g * (h * a) * g⁻¹ := by group
      simpa using e
    · rw [conj_pow] at har
      have : g * (a ^ r) * g⁻¹ = g * 1 * g⁻¹ := by rw [mul_one, mul_inv_cancel]; exact har
      simpa using this

theorem omegaCenterPow_ne_bot [Finite G] {r : ℕ} (hr : r.Prime) {S : Subgroup G}
    (hS : IsPGroup r S) (hS1 : S ≠ ⊥) : omegaCenterPow r S ≠ ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  have hnt : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hS1
  have hc : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hcard : r ∣ Nat.card (Subgroup.center S) := by
    rcases (hS.to_subgroup (Subgroup.center S)).card_eq_or_dvd with h | h
    · have := Finite.one_lt_card_iff_nontrivial.2 hc
      omega
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hcard
  intro hbot
  have hw : ((z : S) : G) ∈ omegaCenterPow r S := by
    refine ⟨(z : S).2, fun h hh => ?_, ?_⟩
    · have := congrArg (fun x : S => (x : G)) (Subgroup.mem_center_iff.1 z.2 ⟨h, hh⟩)
      exact this.symm
    · have h1 : z ^ r = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have := congrArg (fun x : Subgroup.center S => ((x : S) : G)) h1
      simpa using this
  rw [hbot, Subgroup.mem_bot] at hw
  have : z = 1 := Subtype.ext (Subtype.ext hw)
  rw [this, orderOf_one] at hz
  exact hr.one_lt.ne hz

theorem exists_elemAbelian_modEq_one [Finite G] {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    {P N : Subgroup G} (hP : IsPGroup p P) (hN : ¬ p ∣ Nat.card N)
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hrN : r ∣ Nat.card N)
    (hfix : ∀ a : G, orderOf a = r → ∃ g ∈ P, g * a ≠ a * g) :
    ∃ A : Subgroup G, A ≤ N ∧ A ≠ ⊥ ∧ IsPGroup r A ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (∀ a ∈ A, a ^ r = 1) ∧ Nat.card A ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hbotn : P ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g _ =>
    Subgroup.mem_normalizer_iff.2 fun h => by simp [Subgroup.mem_bot]
  obtain ⟨S, ⟨hSN, hSr, hSmax⟩, -, hPS⟩ :=
    exists_invariant_sylow_containing hp hr hP hN hPN bot_le IsPGroup.of_bot hbotn
  have hS1 : S ≠ ⊥ := by
    rintro rfl
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hrN
    have hz : IsPGroup r (Subgroup.zpowers ((g : N) : G)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_coe, hg]
    have hle : Subgroup.zpowers ((g : N) : G) ≤ N := by
      rw [Subgroup.zpowers_le]; exact g.2
    have h := hSmax _ hle hz bot_le
    have hmem : ((g : N) : G) ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers _
    rw [Subgroup.mem_bot] at hmem
    have : g = 1 := Subtype.ext hmem
    rw [this, orderOf_one] at hg
    exact hr.one_lt.ne hg
  refine ⟨omegaCenterPow r S, (omegaCenterPow_le r S).trans hSN, omegaCenterPow_ne_bot hr hSr hS1,
    hSr.to_le (omegaCenterPow_le r S), fun a ha b hb => ha.2.1 b hb.1, fun a ha => ha.2.2, ?_⟩
  refine card_modEq_one_of_noFixed hP (hPS.trans (normalizer_le_normalizer_omegaCenterPow r S))
    fun a ha ha1 => hfix a (orderOf_eq_prime ha.2.2 ha1)

theorem inf_eq_bot_and_commute_of_odd [Finite G] {X K Y : Subgroup G} (hK : IsPGroup 2 K)
    (hKn : ∀ g ∈ X, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hKX : K ≤ X) {x : G}
    (hY : Y ≤ X ⊓ Subgroup.centralizer {x})
    (hYn : ∀ g ∈ X ⊓ Subgroup.centralizer {x}, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hodd : Odd (Nat.card Y)) :
    Y ⊓ K = ⊥ ∧ ∀ y ∈ Y, ∀ k ∈ K ⊓ Subgroup.centralizer {x}, y * k = k * y := by
  have hbot : Y ⊓ K = ⊥ := by
    have h2 : IsPGroup 2 (Y ⊓ K : Subgroup G) := hK.to_le inf_le_right
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have hdvd : Nat.card (Y ⊓ K : Subgroup G) ∣ Nat.card Y :=
      Subgroup.card_dvd_of_le inf_le_left
    rcases n with _ | n
    · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hn)
    · exfalso
      rw [hn, pow_succ] at hdvd
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (dvd_trans (Dvd.intro_left _ rfl) hdvd))
  refine ⟨hbot, fun y hy k hk => ?_⟩
  have hkX : k ∈ X ⊓ Subgroup.centralizer {x} :=
    Subgroup.mem_inf.2 ⟨hKX (Subgroup.mem_inf.1 hk).1, (Subgroup.mem_inf.1 hk).2⟩
  have hyX : y ∈ X := (Subgroup.mem_inf.1 (hY hy)).1
  have hcY : y * k * y⁻¹ * k⁻¹ ∈ Y := by
    have := hYn k hkX y⁻¹ (Y.inv_mem hy)
    have h := Y.mul_mem hy this
    simpa [mul_assoc] using h
  have hcK : y * k * y⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem (hKn y hyX k (Subgroup.mem_inf.1 hk).1) (K.inv_mem (Subgroup.mem_inf.1 hk).1)
  have h1 : y * k * y⁻¹ * k⁻¹ = 1 := by
    have := Subgroup.mem_inf.2 ⟨hcY, hcK⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  calc y * k = y * k * y⁻¹ * k⁻¹ * (k * y) := by group
    _ = k * y := by rw [h1, one_mul]

theorem exists_conj_pow_of_factorization_eq_one {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hcard : (Nat.card H).factorization p = 1) {x y : H} (hx : orderOf x = p)
    (hy : orderOf y = p) : ∃ g : H, ∃ k : ℕ, y = g * x ^ k * g⁻¹ := by
  have hpx : Nat.card (Subgroup.zpowers x) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_zpowers, hx, hcard, pow_one]
  have hpy : Nat.card (Subgroup.zpowers y) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_zpowers, hy, hcard, pow_one]
  let P : Sylow p H := Sylow.ofCard (Subgroup.zpowers x) hpx
  let Q : Sylow p H := Sylow.ofCard (Subgroup.zpowers y) hpy
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  have hQ : (Q : Subgroup H) = MulAut.conj g • Subgroup.zpowers x := by
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
  have hyQ : y ∈ (Q : Subgroup H) := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.mem_zpowers y
  rw [hQ] at hyQ
  obtain ⟨t, ht, hty⟩ := (Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj g) _).1 hyQ
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨g, (n % (p : ℤ)).toNat, ?_⟩
  have hn : x ^ n = x ^ ((n % (p : ℤ)).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne'), ← hx, zpow_mod_orderOf]
  rw [← hn, ← hty]
  simp [MulAut.smul_def, MulAut.conj_apply]

theorem exists_mem_conj_pow_of_factorization_eq_one [Finite G] {K : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hfac : (Nat.card K).factorization p = 1) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (ox : orderOf x = p) (oy : orderOf y = p) : ∃ g ∈ K, ∃ k : ℕ, y = g * x ^ k * g⁻¹ := by
  obtain ⟨g, k, e⟩ := exists_conj_pow_of_factorization_eq_one hfac
    (x := (⟨x, hx⟩ : K)) (y := ⟨y, hy⟩) (by rw [Subgroup.orderOf_mk]; exact ox)
    (by rw [Subgroup.orderOf_mk]; exact oy)
  exact ⟨g, g.2, k, congrArg Subtype.val e⟩

theorem card_centralizer_mulEquiv_apply {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (a : K) :
    Nat.card (Subgroup.centralizer ({e a} : Set K')) =
      Nat.card (Subgroup.centralizer ({a} : Set K)) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem card_centralizer_conj_eq (g a : G) :
    Nat.card (Subgroup.centralizer ({g * a * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) :=
  card_centralizer_mulEquiv_apply (MulAut.conj g) a

theorem centralizer_pow_eq_of_prime [Finite G] {p : ℕ} [hp : Fact p.Prime] {y : G} (hy : orderOf y = p)
    {k : ℕ} (hk : y ^ k ≠ 1) :
    Subgroup.centralizer ({y ^ k} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  have hle : Subgroup.zpowers (y ^ k) ≤ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.npow_mem_zpowers y k
  have hyk : orderOf (y ^ k) = p := by
    have h1 : (y ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, ← hy, pow_orderOf_eq_one,
      one_pow]
    exact orderOf_eq_prime h1 hk
  have heq : Subgroup.zpowers (y ^ k) = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hy, hyk])
  have hmem : y ∈ Subgroup.zpowers (y ^ k) := heq ▸ Subgroup.mem_zpowers y
  apply le_antisymm
  · intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← hm]
    exact ((Commute.zpow_left (show Commute (y ^ k) c from hc.symm) m)).eq.symm
  · intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact ((Commute.pow_left (show Commute y c from hc.symm) k)).eq.symm

theorem ten_le_of_two_pow_modEq_eleven {k : ℕ} (hk : 2 ^ k ≡ 1 [MOD 11]) (hk0 : k ≠ 0) :
    10 ≤ k := by
  have h1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  by_contra h
  push Not at h
  interval_cases k <;> revert hk <;> decide

theorem twelve_le_of_two_pow_modEq_thirteen {k : ℕ} (hk : 2 ^ k ≡ 1 [MOD 13]) (hk0 : k ≠ 0) :
    12 ≤ k := by
  have h1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  by_contra h
  push Not at h
  interval_cases k <;> revert hk <;> decide

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
