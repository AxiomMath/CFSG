module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
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

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.T3

theorem isCyclic_of_isPGroup {C : Type} [Group C] [Finite C] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hcyc : ∀ y : C, orderOf y = ℓ → IsCyclic ↥(Subgroup.centralizer ({y} : Set C)))
    (A : Subgroup C) (hA : IsPGroup ℓ ↥A) [Nontrivial ↥A] : IsCyclic ↥A := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hZ : Nontrivial ↥(Subgroup.center ↥A) := hA.center_nontrivial
  have hZp : IsPGroup ℓ ↥(Subgroup.center ↥A) := hA.to_subgroup _
  have hdvd : ℓ ∣ Nat.card ↥(Subgroup.center ↥A) := by
    obtain ⟨n, hn0, hn⟩ := hZp.nontrivial_iff_card.mp hZ
    exact hn ▸ dvd_pow_self _ (ne_of_gt hn0)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  set y : C := (((z : ↥(Subgroup.center ↥A)) : ↥A) : C) with hy
  have hyo : orderOf y = ℓ := by
    rw [hy, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have := hcyc y hyo
  refine Subgroup.isCyclic_of_le (H' := Subgroup.centralizer ({y} : Set C)) ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hzc := Subgroup.mem_center_iff.mp z.2 ⟨a, ha⟩
  exact (congrArg Subtype.val hzc).symm

theorem isSolvable_normalizer {C : Type} [Group C] [Finite C] {ℓ : ℕ}
    (hcyc : ∀ y : C, orderOf y = ℓ → IsCyclic ↥(Subgroup.centralizer ({y} : Set C)))
    (Q : Subgroup C) [IsCyclic ↥Q] {y : C} (hyQ : y ∈ Q) (hy : orderOf y = ℓ) :
    Group.IsSolvable ↥(Subgroup.normalizer (Q : Set C)) := by
  have := hcyc y hy
  have hle : Subgroup.centralizer (Q : Set C) ≤ Subgroup.centralizer ({y} : Set C) :=
    Subgroup.centralizer_le (by simpa using hyQ)
  have hcle : Subgroup.centralizer (Q : Set C) ≤ Subgroup.normalizer (Q : Set C) :=
    Subgroup.centralizer_le_normalizer _
  have : IsCyclic ↥(Subgroup.centralizer (Q : Set C)) := Subgroup.isCyclic_of_le hle
  have : IsCyclic ↥((Subgroup.centralizer (Q : Set C)).subgroupOf
      (Subgroup.normalizer (Q : Set C))) :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hcle).symm.surjective
  have : Group.IsSolvable (MulAut ↥Q) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv ↥Q).toMonoidHom) (IsCyclic.mulAutMulEquiv ↥Q).injective
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.subtype ((Subgroup.centralizer (Q : Set C)).subgroupOf
      (Subgroup.normalizer (Q : Set C)))) (Subgroup.normalizerMonoidHom Q) ?_
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.range_subtype]

theorem not_dvd_card_of_nonsolvable_quotient
    {C : Type} [Group C] [Finite C] (E : Subgroup C) [E.Normal] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hcyc : ∀ y : C, orderOf y = ℓ → IsCyclic ↥(Subgroup.centralizer ({y} : Set C)))
    (hns : ¬ Group.IsSolvable (C ⧸ E)) : ¬ ℓ ∣ Nat.card ↥E := by
  intro hdvd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) ℓ hdvd
  have hzp : IsPGroup ℓ ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hyQ : ((y : ↥E) : C) ∈ (P : Subgroup ↥E).map E.subtype :=
    Subgroup.mem_map_of_mem _ (hP (Subgroup.mem_zpowers y))
  have hy0 : orderOf ((y : ↥E) : C) = ℓ := by
    rw [Subgroup.orderOf_coe, hy]
  have hQp : IsPGroup ℓ ↥((P : Subgroup ↥E).map E.subtype) := P.isPGroup'.map E.subtype
  have hne : ((y : ↥E) : C) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy0
    exact hℓ.one_lt.ne hy0
  have : Nontrivial ↥((P : Subgroup ↥E).map E.subtype) :=
    ⟨⟨⟨_, hyQ⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
  have : IsCyclic ↥((P : Subgroup ↥E).map E.subtype) := isCyclic_of_isPGroup hℓ hcyc _ hQp
  have hsolv := isSolvable_normalizer hcyc ((P : Subgroup ↥E).map E.subtype) hyQ hy0
  have hfr := Sylow.normalizer_sup_eq_top P
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' E).comp (Subgroup.normalizer
        (((P : Subgroup ↥E).map E.subtype : Subgroup C) : Set C)).subtype) := by
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have hg : g ∈ Subgroup.normalizer (((P : Subgroup ↥E).map E.subtype : Subgroup C) : Set C)
        ⊔ E := by
      rw [hfr]; trivial
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg
    obtain ⟨n, hn, e, he, rfl⟩ := hg
    refine ⟨⟨n, hn⟩, ?_⟩
    change (QuotientGroup.mk' E) n = ((n * e : C) : C ⧸ E)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff e).mpr he, mul_one]
    rfl
  exact hns (Group.isSolvable_of_surjective hsurj)

theorem exists_conj_mem_zpowers_of_card {G : Type} [Group G] [Finite G] {ℓ m : ℕ}
    (hℓ : ℓ.Prime) (hcard : Nat.card G = m * ℓ) (hm : ¬ ℓ ∣ m) {a b : G}
    (ha : orderOf a = ℓ) (hb : orderOf b = ℓ) :
    ∃ g : G, ∃ k : ℤ, g * a * g⁻¹ = b ^ k := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : Nat.card G ≠ 0 := Nat.card_pos.ne'
    simp [hcard] at this
  have hfac : (Nat.card G).factorization ℓ = 1 := by
    rw [hcard, Nat.factorization_mul hm0 hℓ.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm, hℓ.factorization_self]
  let Sa : Sylow ℓ G :=
    Sylow.ofCard (Subgroup.zpowers a) (by rw [Nat.card_zpowers, ha, hfac, pow_one])
  let Sb : Sylow ℓ G :=
    Sylow.ofCard (Subgroup.zpowers b) (by rw [Nat.card_zpowers, hb, hfac, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Sa Sb
  refine ⟨g, ?_⟩
  have h1 : g * a * g⁻¹ ∈ ((g • Sa : Sylow ℓ G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨a, Subgroup.mem_zpowers a, by simp⟩
  rw [hg] at h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  exact ⟨k, hk.symm⟩

theorem card_comap_zpowers_quotient {C : Type} [Group C] [Finite C] (E : Subgroup C) [E.Normal]
    {ℓ : ℕ} {x : C} (hx : orderOf (x : C ⧸ E) = ℓ) :
    Nat.card ↥((Subgroup.zpowers (x : C ⧸ E)).comap (QuotientGroup.mk' E)) =
      Nat.card ↥E * ℓ := by
  set B := (Subgroup.zpowers (x : C ⧸ E)).comap (QuotientGroup.mk' E) with hB
  have hEB : E ≤ B := fun e he => by
    rw [hB, Subgroup.mem_comap]
    simp [(QuotientGroup.eq_one_iff e).mpr he]
  let f : ↥B →* C ⧸ E := (QuotientGroup.mk' E).domRestrict B
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : Nat.card f.ker = Nat.card E := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv
  have hrange : f.range = Subgroup.zpowers (x : C ⧸ E) := by
    rw [MonoidHom.domRestrict_range, hB,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective E)]
  rw [hker, hrange, Nat.card_zpowers, hx] at h1
  exact h1.symm

theorem exists_lift_of_mem_centralizer_quotient
    {C : Type} [Group C] [Finite C] (E : Subgroup C) [E.Normal] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hE : ¬ ℓ ∣ Nat.card ↥E) {x : C} (hx : orderOf x = ℓ) {c : C ⧸ E}
    (hc : c ∈ Subgroup.centralizer ({(x : C ⧸ E)} : Set (C ⧸ E))) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set C), (g : C ⧸ E) = c := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective c
  have hxo : orderOf (x : C ⧸ E) = ℓ := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h
      have hxmem : x ∈ E := (QuotientGroup.eq_one_iff x).mp h
      apply hE
      have := orderOf_dvd_natCard (⟨x, hxmem⟩ : ↥E)
      rwa [Subgroup.orderOf_mk, hx] at this
  set B := (Subgroup.zpowers (x : C ⧸ E)).comap (QuotientGroup.mk' E) with hB
  have hcard : Nat.card B = Nat.card E * ℓ := card_comap_zpowers_quotient E hxo
  have hcomm : (x : C ⧸ E) * (g₀ : C ⧸ E) = (g₀ : C ⧸ E) * (x : C ⧸ E) :=
    Subgroup.mem_centralizer_iff.mp hc _ (Set.mem_singleton _)
  set x' : C := g₀ * x * g₀⁻¹ with hx'
  have hx'bar : (x' : C ⧸ E) = (x : C ⧸ E) := by
    rw [hx', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hcomm]
    group
  have hox' : orderOf x' = ℓ := by
    rw [← hx]
    exact (MulAut.conj g₀).orderOf_eq x
  have hxB : x ∈ B := by
    rw [hB, Subgroup.mem_comap]
    exact Subgroup.mem_zpowers _
  have hx'B : x' ∈ B := by
    rw [hB, Subgroup.mem_comap]
    show ((x' : C) : C ⧸ E) ∈ _
    rw [hx'bar]
    exact Subgroup.mem_zpowers _
  obtain ⟨b, k, hbk⟩ := exists_conj_mem_zpowers_of_card hℓ hcard hE
    (a := (⟨x, hxB⟩ : ↥B)) (b := (⟨x', hx'B⟩ : ↥B))
    (by rw [Subgroup.orderOf_mk, hx]) (by rw [Subgroup.orderOf_mk, hox'])
  have hbk' : (b : C) * x * (b : C)⁻¹ = x' ^ k := by
    have := congrArg Subtype.val hbk
    simpa using this
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp b.2)
  have hi' : (x : C ⧸ E) ^ i = ((b : C) : C ⧸ E) := hi
  have hcommb : (x : C ⧸ E) * ((b : C) : C ⧸ E) = ((b : C) : C ⧸ E) * (x : C ⧸ E) := by
    rw [← hi']
    exact (Commute.self_zpow _ _).eq
  have h1 : (x : C ⧸ E) ^ k = (x : C ⧸ E) := by
    have h := congrArg (fun y : C => (y : C ⧸ E)) hbk'
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, hx'bar] at h
    rw [← h, ← hcommb]
    group
  have h2 : (x : C ⧸ E) ^ (k - 1) = 1 := by
    rw [zpow_sub_one, h1, mul_inv_cancel]
  have h3 : (ℓ : ℤ) ∣ k - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rwa [hxo] at this
  have h4 : x' ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hox']; exact h3)
  have h5 : x' ^ k = x' := by
    rw [zpow_sub_one, mul_inv_eq_one] at h4
    exact h4
  rw [h5] at hbk'
  have hcent : x * ((b : C)⁻¹ * g₀) = ((b : C)⁻¹ * g₀) * x := by
    calc x * ((b : C)⁻¹ * g₀) = (b : C)⁻¹ * ((b : C) * x * (b : C)⁻¹) * g₀ := by group
      _ = (b : C)⁻¹ * x' * g₀ := by rw [hbk']
      _ = (b : C)⁻¹ * g₀ * x := by rw [hx']; group
  refine ⟨x ^ i * ((b : C)⁻¹ * g₀), ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc x * (x ^ i * ((b : C)⁻¹ * g₀)) = (x * x ^ i) * ((b : C)⁻¹ * g₀) := by rw [mul_assoc]
      _ = (x ^ i * x) * ((b : C)⁻¹ * g₀) := by rw [(Commute.self_zpow x i).eq]
      _ = x ^ i * (x * ((b : C)⁻¹ * g₀)) := by rw [mul_assoc]
      _ = x ^ i * (((b : C)⁻¹ * g₀) * x) := by rw [hcent]
      _ = (x ^ i * ((b : C)⁻¹ * g₀)) * x := (mul_assoc _ _ _).symm
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      hi']
    group

theorem isCyclic_centralizer_quotient {C : Type} [Group C] [Finite C] (E : Subgroup C) [E.Normal]
    {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hcyc : ∀ y : C, orderOf y = ℓ → IsCyclic ↥(Subgroup.centralizer ({y} : Set C)))
    (hE : ¬ ℓ ∣ Nat.card ↥E) {x : C} (hx : orderOf x = ℓ) :
    IsCyclic ↥(Subgroup.centralizer ({(x : C ⧸ E)} : Set (C ⧸ E))) := by
  have := hcyc x hx
  have hmap : (Subgroup.centralizer ({x} : Set C)).map (QuotientGroup.mk' E) =
      Subgroup.centralizer ({(x : C ⧸ E)} : Set (C ⧸ E)) := by
    ext c
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : g ∈ Subgroup.centralizer ({x} : Set C) := hg
      rw [Subgroup.mem_centralizer_iff] at hg' ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have := congrArg (QuotientGroup.mk' E) (hg' x (Set.mem_singleton _))
      simpa using this
    · intro hc
      obtain ⟨g, hg, hgc⟩ := exists_lift_of_mem_centralizer_quotient E hℓ hE hx hc
      exact ⟨g, hg, hgc⟩
  rw [← hmap]
  exact isCyclic_of_surjective _ ((QuotientGroup.mk' E).subgroupMap_surjective _)

theorem false_of_commuting_components
    {C : Type} [Group C] [Finite C] (E : Subgroup C) [E.Normal] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2)
    (hcyc : ∀ y : C, orderOf y = ℓ → IsCyclic ↥(Subgroup.centralizer ({y} : Set C)))
    (L₁ L₂ : Subgroup (C ⧸ E))
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hinf : Nat.card ↥(L₁ ⊓ L₂) = 2)
    (hnonsolv₁ : ¬ Group.IsSolvable ↥L₁)
    (hnonab₂ : ∃ a ∈ L₂, ∃ b ∈ L₂, a * b ≠ b * a)
    (x : C) (hx : orderOf x = ℓ) (hxL : (x : C ⧸ E) ∈ L₁ ⊔ L₂) : False := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hns : ¬ Group.IsSolvable (C ⧸ E) := fun h => hnonsolv₁ inferInstance
  have hE := not_dvd_card_of_nonsolvable_quotient E hℓ hcyc hns
  have hZ := isCyclic_centralizer_quotient E hℓ hcyc hE hx
  set y : C ⧸ E := (x : C ⧸ E) with hy
  have hyℓ : y ^ ℓ = 1 := by
    rw [hy, ← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hLE : L₁ ≤ Subgroup.normalizer (L₂ : Set (C ⧸ E)) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcomm a ha h hh).symm
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ L₁, ∃ b ∈ L₂, a * b = y := by
    have hmem : y ∈ ((L₁ ⊔ L₂ : Subgroup (C ⧸ E)) : Set (C ⧸ E)) := hxL
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L₁ L₂ hLE] at hmem
    obtain ⟨a, ha, b, hb, h⟩ := Set.mem_mul.mp hmem
    exact ⟨a, ha, b, hb, h⟩
  have hcab : a * b = b * a := hcomm a ha b hb
  have hmul : a ^ ℓ * b ^ ℓ = 1 := by
    rw [← (Commute.mul_pow hcab ℓ), hab, hyℓ]
  have hsq : ∀ u ∈ L₁ ⊓ L₂, u ^ 2 = 1 := by
    intro u hu
    have := pow_card_eq_one' (G := ↥(L₁ ⊓ L₂)) (x := ⟨u, hu⟩)
    rw [hinf] at this
    exact congrArg Subtype.val this
  have haℓ : a ^ ℓ ∈ L₁ ⊓ L₂ := by
    rw [Subgroup.mem_inf]
    refine ⟨pow_mem ha ℓ, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hmul]
    exact inv_mem (pow_mem hb ℓ)
  have hbℓ : b ^ ℓ ∈ L₁ ⊓ L₂ := by
    rw [Subgroup.mem_inf]
    refine ⟨?_, pow_mem hb ℓ⟩
    rw [eq_inv_of_mul_eq_one_right hmul]
    exact inv_mem (pow_mem ha ℓ)
  obtain ⟨t, ht⟩ : Odd ℓ := (hℓ.eq_two_or_odd').resolve_left hℓ2
  have hℓ1 : ℓ + 1 = 2 * (t + 1) := by omega
  have hpowℓ : ∀ u : C ⧸ E, u ^ ℓ ∈ L₁ ⊓ L₂ → (u ^ (ℓ + 1)) ^ ℓ = 1 := by
    intro u hu
    have h2 := hsq _ hu
    calc (u ^ (ℓ + 1)) ^ ℓ = (u ^ ℓ) ^ (ℓ + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (u ^ ℓ) ^ (2 * (t + 1)) := by rw [hℓ1]
      _ = 1 := by rw [pow_mul, h2, one_pow]
  set a' := a ^ (ℓ + 1) with ha'def
  set b' := b ^ (ℓ + 1) with hb'def
  have ha' : a' ∈ L₁ := pow_mem ha _
  have hb' : b' ∈ L₂ := pow_mem hb _
  have ha'ℓ : a' ^ ℓ = 1 := hpowℓ a haℓ
  have hb'ℓ : b' ^ ℓ = 1 := hpowℓ b hbℓ
  have hab' : a' * b' = y := by
    rw [ha'def, hb'def, ← Commute.mul_pow hcab, hab, pow_succ, hyℓ, one_mul]
  have hcab' : a' * b' = b' * a' := hcomm a' ha' b' hb'
  have ha'Z : a' ∈ Subgroup.centralizer ({y} : Set (C ⧸ E)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, ← hab']
    calc a' * b' * a' = a' * (b' * a') := mul_assoc _ _ _
      _ = a' * (a' * b') := by rw [← hcab']
  have hb'Z : b' ∈ Subgroup.centralizer ({y} : Set (C ⧸ E)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, ← hab']
    calc a' * b' * b' = b' * a' * b' := by rw [hcab']
      _ = b' * (a' * b') := mul_assoc _ _ _
  by_cases h1 : a' = 1
  · have hyb : y = b' := by rw [← hab', h1, one_mul]
    have hle : L₁ ≤ Subgroup.centralizer ({y} : Set (C ⧸ E)) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh, hyb]
      exact (hcomm u hu b' hb').symm
    have : IsCyclic ↥L₁ := Subgroup.isCyclic_of_le hle
    exact hnonsolv₁ inferInstance
  by_cases h2 : b' = 1
  · have hya : y = a' := by rw [← hab', h2, mul_one]
    have hle : L₂ ≤ Subgroup.centralizer ({y} : Set (C ⧸ E)) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh, hya]
      exact hcomm a' ha' u hu
    have : IsCyclic ↥L₂ := Subgroup.isCyclic_of_le hle
    obtain ⟨u, hu, v, hv, huv⟩ := hnonab₂
    apply huv
    have := (isMulCommutative_iff.mp (inferInstance : IsMulCommutative ↥L₂)) ⟨u, hu⟩ ⟨v, hv⟩
    exact congrArg Subtype.val this
  · have hoa : orderOf a' = ℓ := orderOf_eq_prime ha'ℓ h1
    have hob : orderOf b' = ℓ := orderOf_eq_prime hb'ℓ h2
    let az : ↥(Subgroup.centralizer ({y} : Set (C ⧸ E))) := ⟨a', ha'Z⟩
    let bz : ↥(Subgroup.centralizer ({y} : Set (C ⧸ E))) := ⟨b', hb'Z⟩
    have hcard : Nat.card ↥(Subgroup.zpowers az) = Nat.card ↥(Subgroup.zpowers bz) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hoa, hob]
    have heq := (IsCyclic.subgroup_eq_iff_card_eq
      (G := ↥(Subgroup.centralizer ({y} : Set (C ⧸ E))))).mpr hcard
    have hmem : az ∈ Subgroup.zpowers bz := heq ▸ Subgroup.mem_zpowers az
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : b' ^ k = a' := by
      have := congrArg Subtype.val hk
      simpa using this
    have ha'2 : a' ∈ L₁ ⊓ L₂ := by
      rw [Subgroup.mem_inf]
      refine ⟨ha', ?_⟩
      rw [← hk']
      exact zpow_mem hb' k
    have hsq2 := hsq a' ha'2
    have h3 := orderOf_dvd_of_pow_eq_one hsq2
    rw [hoa] at h3
    exact hℓ2 (le_antisymm (Nat.le_of_dvd (by norm_num) h3) hℓ.two_le)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.T3
