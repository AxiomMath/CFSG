module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankTwoShapes

theorem eq_of_sq_eq_one_of_isCyclic {G : Type*} [Group G] [IsCyclic G] {a b : G}
    (ha : a ^ 2 = 1) (ha1 : a ≠ 1) (hb : b ^ 2 = 1) (hb1 : b ≠ 1) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoa : orderOf a = 2 := orderOf_eq_prime ha ha1
  have hob : orderOf b = 2 := orderOf_eq_prime hb hb1
  have : Finite (Subgroup.zpowers a) := finite_zpowers.mpr (orderOf_pos_iff.mp (by omega))
  have : Finite (Subgroup.zpowers b) := finite_zpowers.mpr (orderOf_pos_iff.mp (by omega))
  have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hob])
  have hmem : b ∈ Subgroup.zpowers a := heq ▸ Subgroup.mem_zpowers b
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← zpow_mod_orderOf, hoa] at hk
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_zero] at hk
    exact absurd hk.symm hb1
  · rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_one] at hk
    exact hk

theorem isCyclic_iff_subgroup_card_prime_unique {p : ℕ} [hp : Fact p.Prime] {A : Type*}
    [CommGroup A] [Finite A] (hA : IsPGroup p A) :
    IsCyclic A ↔ ∀ B C : Subgroup A, Nat.card B = p → Nat.card C = p → B = C := by
  constructor
  · intro _ B C hB hC
    exact IsCyclic.subgroup_eq_iff_card_eq.mpr (hB.trans hC.symm)
  · intro huniq
    by_contra hnc
    obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := A))
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA) g
    have hexp : Monoid.exponent A = p ^ k := hg.symm.trans hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · apply hnc
      have hall : ∀ x : A, x = 1 := fun x => by
        have hx := Monoid.pow_exponent_eq_one x
        rwa [hexp, hk0, pow_zero, pow_one] at hx
      have : Subsingleton A := ⟨fun x y => (hall x).trans (hall y).symm⟩
      exact isCyclic_of_subsingleton
    · have hne : Subgroup.zpowers g ≠ ⊤ := fun htop =>
        hnc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, htop⟩)
      obtain ⟨h, hh, hhp⟩ : ∃ h : A, h ∉ Subgroup.zpowers g ∧ h ^ p ∈ Subgroup.zpowers g := by
        have hQ : IsPGroup p (A ⧸ Subgroup.zpowers g) := hA.to_quotient _
        have hnt : Nontrivial (A ⧸ Subgroup.zpowers g) := QuotientGroup.nontrivial_iff.mpr hne
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
        have hn0 : n ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hn
          exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hn
        obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' p (hn ▸ dvd_pow_self p hn0)
        obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
        refine ⟨h, fun hmem => ?_, ?_⟩
        · have h1 : (QuotientGroup.mk h : A ⧸ Subgroup.zpowers g) = 1 :=
            (QuotientGroup.eq_one_iff h).mpr hmem
          rw [h1, orderOf_one] at hq
          exact hp.out.one_lt.ne hq
        · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hhp
      have hpj : (p : ℤ) ∣ j := by
        have h1 : g ^ (j * (p : ℤ) ^ (k - 1)) = 1 := by
          rw [zpow_mul, hj, ← zpow_natCast, ← zpow_mul, ← Nat.cast_pow, ← Nat.cast_mul,
            ← pow_succ', Nat.sub_add_cancel hkpos, zpow_natCast, ← hexp,
            Monoid.pow_exponent_eq_one]
        have h2 : (p : ℤ) ^ (k - 1) * p ∣ (p : ℤ) ^ (k - 1) * j := by
          have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h1
          rw [hg, hexp] at h3
          have e : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ (k - 1) * p := by
            rw [Nat.cast_pow, ← pow_succ, Nat.sub_add_cancel hkpos]
          rwa [e, mul_comm j] at h3
        exact (mul_dvd_mul_iff_left
          (pow_ne_zero (k - 1) (by exact_mod_cast hp.out.ne_zero : (p : ℤ) ≠ 0))).mp h2
      obtain ⟨j', rfl⟩ := hpj
      set h' := h * g ^ (-j') with hh'
      have hh'p : h' ^ p = 1 := by
        calc h' ^ p = h ^ p * (g ^ (-j')) ^ p := mul_pow _ _ _
          _ = g ^ ((p : ℤ) * j') * g ^ (-j' * p) := by
            rw [← hj, ← zpow_natCast (g ^ (-j')), ← zpow_mul]
          _ = 1 := by
            rw [← zpow_add, show (p : ℤ) * j' + -j' * p = 0 by ring, zpow_zero]
      have hh'g : h' ∉ Subgroup.zpowers g := by
        intro hmem
        apply hh
        have : h = h' * g ^ j' := by rw [hh', mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
          mul_one]
        rw [this]
        exact Subgroup.mul_mem _ hmem (Subgroup.zpow_mem_zpowers g j')
      have hh'1 : h' ≠ 1 := fun h1 => hh'g (h1 ▸ Subgroup.one_mem _)
      set g' := g ^ p ^ (k - 1) with hg'
      have hg'p : g' ^ p = 1 := by
        rw [hg', ← pow_mul, ← pow_succ, Nat.sub_add_cancel hkpos, ← hexp,
          Monoid.pow_exponent_eq_one]
      have hg'1 : g' ≠ 1 := by
        apply pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.out.ne_zero)
        rw [hg, hexp]
        exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)
      have heq := huniq (Subgroup.zpowers h') (Subgroup.zpowers g')
        (by rw [Nat.card_zpowers]; exact orderOf_eq_prime hh'p hh'1)
        (by rw [Nat.card_zpowers]; exact orderOf_eq_prime hg'p hg'1)
      apply hh'g
      have hle : Subgroup.zpowers g' ≤ Subgroup.zpowers g :=
        Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _)
      exact hle (heq ▸ Subgroup.mem_zpowers h')

theorem isCyclic_iff_elementary_card_le {p : ℕ} [hp : Fact p.Prime] {A : Type*}
    [CommGroup A] [Finite A] (hA : IsPGroup p A) :
    IsCyclic A ↔ ∀ E : Subgroup A, (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p := by
  constructor
  · intro _ E hE
    have hexp : Monoid.exponent E ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun e => Subtype.ext (by simpa using hE e e.2)
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.out.pos hexp
  · intro hrank
    rw [isCyclic_iff_subgroup_card_prime_unique hA]
    intro B C hB hC
    have hpow : ∀ D : Subgroup A, Nat.card D = p → D ≤ (powMonoidHom p : A →* A).ker := by
      intro D hD d hd
      rw [MonoidHom.mem_ker, powMonoidHom_apply, ← orderOf_dvd_iff_pow_eq_one, ← hD]
      exact Subgroup.orderOf_dvd_natCard D hd
    have hsup : Nat.card (B ⊔ C : Subgroup A) ≤ p :=
      hrank _ fun e he => (sup_le (hpow B hB) (hpow C hC)) he
    have hBeq : B = B ⊔ C := Subgroup.eq_of_le_of_card_ge le_sup_left (hB ▸ hsup)
    have hCeq : C = B ⊔ C := Subgroup.eq_of_le_of_card_ge le_sup_right (hC ▸ hsup)
    exact hBeq.trans hCeq.symm

theorem noncyclic_abelian_involution_fixed_two {H : Type*} [CommGroup H] [Finite H]
    (hH : IsPGroup 2 H) (hnc : ¬ IsCyclic H) (α : MulAut H) (hα : α ^ 2 = 1)
    (hfix : Nat.card {h : H // α h = h} = 2) :
    Nat.card H = 4 ∧ ∀ h : H, h ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαα : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun f : MulAut H => f h) hα
    simpa [pow_two, MulAut.mul_apply] using this
  obtain ⟨z, hz1, hzfix, hfixz⟩ : ∃ z : H, z ≠ 1 ∧ α z = z ∧ ∀ h, α h = h → h = 1 ∨ h = z := by
    obtain ⟨x, y, hxy, hxyU⟩ := Nat.card_eq_two_iff.mp hfix
    have hmem : ∀ w : {h : H // α h = h}, w = x ∨ w = y := fun w => by
      have : w ∈ ({x, y} : Set _) := hxyU ▸ Set.mem_univ w
      simpa using this
    rcases hmem ⟨1, map_one α⟩ with h1 | h1
    · refine ⟨y.1, fun hy => hxy (Subtype.ext ((congrArg Subtype.val h1).symm.trans hy.symm)),
        y.2, fun h hh => ?_⟩
      rcases hmem ⟨h, hh⟩ with h2 | h2
      · exact Or.inl ((congrArg Subtype.val h2).trans (congrArg Subtype.val h1).symm)
      · exact Or.inr (congrArg Subtype.val h2)
    · refine ⟨x.1, fun hx => hxy (Subtype.ext (hx.trans (congrArg Subtype.val h1))),
        x.2, fun h hh => ?_⟩
      rcases hmem ⟨h, hh⟩ with h2 | h2
      · exact Or.inr (congrArg Subtype.val h2)
      · exact Or.inl ((congrArg Subtype.val h2).trans (congrArg Subtype.val h1).symm)
  have hz2 : z ^ 2 = 1 := by
    rcases hfixz (z ^ 2) (by rw [map_pow, hzfix]) with h | h
    · exact h
    · exact absurd (by simpa [pow_two] using h) hz1
  have hoz : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  let δ : H →* H :=
    { toFun := fun h => h⁻¹ * α h
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [mul_inv, map_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  have hδ : ∀ h, δ h = h⁻¹ * α h := fun h => rfl
  have hker : ∀ h, δ h = 1 ↔ α h = h := fun h => by rw [hδ, inv_mul_eq_one, eq_comm]
  set K := δ.range with hK
  have hcardK : Nat.card K * 2 = Nat.card H := by
    have h1 := Subgroup.card_mul_index δ.ker
    rw [Subgroup.index_ker, ← hK] at h1
    have h2 : Nat.card δ.ker = 2 := by
      rw [← hfix]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun h => (MonoidHom.mem_ker).trans (hker h))
    rw [h2] at h1
    omega
  have hαK : ∀ k ∈ K, α k = k⁻¹ := by
    rintro _ ⟨h, rfl⟩
    rw [hδ, map_mul, map_inv, hαα, mul_inv_rev, inv_inv]
  have hinvK : ∀ k ∈ K, k ^ 2 = 1 → k = 1 ∨ k = z := by
    intro k hk hk2
    apply hfixz
    rw [hαK k hk]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hk2)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hH
  have hm2 : 2 ≤ m := by
    by_contra hlt
    apply hnc
    apply isCyclic_of_card_dvd_prime (p := 2)
    rw [hm]
    interval_cases m <;> norm_num
  have hcardK' : Nat.card K = 2 ^ (m - 1) := by
    have h' : 2 ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hm, h'] at hcardK
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hcardK
  have hzK : z ∈ K := by
    have hK2 : 2 ∣ Nat.card K := by
      rw [hcardK']
      exact dvd_pow_self 2 (by omega)
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 hK2
    have hk2 : (k : H) ^ 2 = 1 := by
      have := pow_orderOf_eq_one k
      rw [hk] at this
      exact congrArg Subtype.val this
    have hk1 : (k : H) ≠ 1 := by
      intro h1
      have : k = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hk
      norm_num at hk
    rcases hinvK k k.2 hk2 with h | h
    · exact absurd h hk1
    · exact h ▸ k.2
  obtain ⟨y, hyK, hy2, hy1⟩ : ∃ y : H, y ∉ K ∧ y ^ 2 = 1 ∧ y ≠ 1 := by
    have hnu := mt (isCyclic_iff_subgroup_card_prime_unique hH).mpr hnc
    push Not at hnu
    obtain ⟨B, C, hB, hC, hBC⟩ := hnu
    by_contra hall
    push Not at hall
    have hsub : ∀ D : Subgroup H, Nat.card D = 2 → D = Subgroup.zpowers z := by
      intro D hD
      apply Subgroup.eq_of_le_of_card_ge _ (by rw [hD, Nat.card_zpowers, hoz])
      intro d hd
      have hd2 : d ^ 2 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, ← hD]
        exact Subgroup.orderOf_dvd_natCard D hd
      by_cases hdK : d ∈ K
      · rcases hinvK d hdK hd2 with h | h
        · exact h ▸ Subgroup.one_mem _
        · exact h ▸ Subgroup.mem_zpowers z
      · exact (hall d hdK hd2) ▸ Subgroup.one_mem _
    exact hBC ((hsub B hB).trans (hsub C hC).symm)
  have hδy : δ y = z := by
    have hsq : δ y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
    rcases hinvK _ ⟨y, rfl⟩ hsq with h | h
    · exfalso
      rcases hfixz y ((hker y).mp h) with h' | h'
      · exact hy1 h'
      · exact hyK (h' ▸ hzK)
    · exact h
  have hαy : α y = y * z := by
    rw [hδ] at hδy
    rw [← hδy, mul_inv_cancel_left]
  have hm_le : m ≤ 2 := by
    by_contra hm3
    push Not at hm3
    obtain ⟨k₀, hk₀K, hk₀z⟩ : ∃ k₀ ∈ K, k₀ ∉ Subgroup.zpowers z := by
      by_contra hall
      push Not at hall
      have hle := Subgroup.card_le_of_le (show K ≤ Subgroup.zpowers z from hall)
      rw [Nat.card_zpowers, hoz, hcardK'] at hle
      have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk₀2 : k₀ ^ 2 ≠ 1 := by
      intro h
      rcases hinvK k₀ hk₀K h with h' | h'
      · exact hk₀z (h' ▸ Subgroup.one_mem _)
      · exact hk₀z (h' ▸ Subgroup.mem_zpowers z)
    obtain ⟨r, hr⟩ := IsPGroup.iff_orderOf.mp hH k₀
    have hr2 : 2 ≤ r := by
      by_contra hlt
      apply hk₀2
      rw [← orderOf_dvd_iff_pow_eq_one, hr]
      interval_cases r <;> norm_num
    set k := k₀ ^ 2 ^ (r - 2) with hkdef
    have hkK : k ∈ K := K.pow_mem hk₀K _
    have hk4 : k ^ 4 = 1 := by
      rw [hkdef, ← pow_mul, show 2 ^ (r - 2) * 4 = 2 ^ r by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hr2], ← hr,
        pow_orderOf_eq_one]
    have hk2ne : k ^ 2 ≠ 1 := by
      rw [hkdef, ← pow_mul, ← pow_succ]
      apply pow_ne_one_of_lt_orderOf (pow_ne_zero _ (by norm_num))
      rw [hr]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hk2z : k ^ 2 = z := by
      have hsq : (k ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hk4
      rcases hinvK _ (K.pow_mem hkK 2) hsq with h | h
      · exact absurd h hk2ne
      · exact h
    have hαk : α k = k * z := by
      rw [hαK k hkK, ← hk2z]
      apply inv_eq_of_mul_eq_one_right
      calc k * (k * k ^ 2) = k ^ 4 := by rw [← pow_succ', ← pow_succ']
        _ = 1 := hk4
    have hfixyk : α (y * k) = y * k := by
      rw [map_mul, hαy, hαk, mul_mul_mul_comm, ← pow_two, hz2, mul_one]
    rcases hfixz _ hfixyk with h | h
    · have hsq : (y * k) ^ 2 = z := by rw [mul_pow, hy2, one_mul, hk2z]
      rw [h, one_pow] at hsq
      exact hz1 hsq.symm
    · apply hyK
      have : y = z * k⁻¹ := by rw [← h, mul_inv_cancel_right]
      rw [this]
      exact K.mul_mem hzK (K.inv_mem hkK)
  have hm4 : m = 2 := le_antisymm hm_le hm2
  refine ⟨by rw [hm, hm4]; norm_num, fun h => ?_⟩
  by_contra hh2
  apply hnc
  obtain ⟨s, hs⟩ := IsPGroup.iff_orderOf.mp hH h
  have hdvd : orderOf h ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 2 ^ m by rw [hm4], ← hm]
    exact orderOf_dvd_natCard h
  rw [hs] at hdvd
  have hs2 : s ≤ 2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hs2' : s = 2 := by
    by_contra hne
    apply hh2
    rw [← orderOf_dvd_iff_pow_eq_one, hs]
    interval_cases s <;> first | exact absurd rfl hne | norm_num
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  exact ⟨h, by rw [hs, hs2', hm, hm4]⟩

end CFSG.RankTwoShapes
