module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

variable {H : Type*} [Group H] [Finite H]

theorem orderOf_mem_of_card_thirty_six (hH : Nat.card H = 36) (h4 : ∀ h : H, orderOf h ≠ 4)
    (h9 : ∀ h : H, orderOf h ≠ 9) (h : H) :
    orderOf h = 1 ∨ orderOf h = 2 ∨ orderOf h = 3 ∨ orderOf h = 6 := by
  have hdvd : orderOf h ∣ 36 := hH ▸ orderOf_dvd_natCard h
  have hmem : orderOf h ∈ ({1, 2, 3, 4, 6, 9, 12, 18, 36} : Finset ℕ) := by
    have : ({1, 2, 3, 4, 6, 9, 12, 18, 36} : Finset ℕ) = Nat.divisors 36 := by decide
    rw [this]
    exact Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hpos : 0 < orderOf h := orderOf_pos h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact absurd h1 (h4 h)
  · exact Or.inr (Or.inr (Or.inr h1))
  · exact absurd h1 (h9 h)
  · exfalso
    apply h4 (h ^ 3)
    rw [orderOf_pow' h (by norm_num), h1]
    norm_num
  · exfalso
    apply h9 (h ^ 2)
    rw [orderOf_pow' h (by norm_num), h1]
    norm_num
  · exfalso
    apply h9 (h ^ 4)
    rw [orderOf_pow' h (by norm_num), h1]
    norm_num

theorem sylow_three_card_of_card_thirty_six (hH : Nat.card H = 36) (V : Sylow 3 H) :
    Nat.card V = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, hH]
  have : (36 : ℕ).factorization 3 = 2 := by
    rw [show (36 : ℕ) = 3 ^ 2 * 4 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 4 by norm_num)]
  rw [this]
  norm_num

section Orbits

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem smul_eq_self_of_card_orbit_eq_two {x : Ω} (hx : Nat.card (MulAction.orbit G x) = 2)
    {g : G} (hg : g ^ 3 = 1) : g • x = x := by
  let σ : G →* Equiv.Perm (MulAction.orbit G x) := MulAction.toPermHom G (MulAction.orbit G x)
  have hfin : Finite (MulAction.orbit G x) := Nat.finite_of_card_ne_zero (by rw [hx]; norm_num)
  have hcardperm : Nat.card (Equiv.Perm (MulAction.orbit G x)) = 2 := by
    rw [Nat.card_perm, hx]
    rfl
  have h3 : orderOf (σ g) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hg, map_one])
  have h2 : orderOf (σ g) ∣ 2 := hcardperm ▸ orderOf_dvd_natCard (σ g)
  have h1 : orderOf (σ g) = 1 := by
    have h := Nat.dvd_gcd h3 h2
    rw [show Nat.gcd 3 2 = 1 by norm_num] at h
    exact Nat.dvd_one.mp h
  rw [orderOf_eq_one_iff] at h1
  have := congrArg (fun τ : Equiv.Perm (MulAction.orbit G x) => (τ ⟨x, MulAction.mem_orbit_self x⟩ :
    Ω)) h1
  exact this

theorem card_orbit_eq_one_of_fixed {x : Ω} (hx : ∀ g : G, g • x = x) :
    Nat.card (MulAction.orbit G x) = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨x, MulAction.mem_orbit_self x⟩, ?_⟩
  rintro ⟨y, g, rfl⟩
  exact Subtype.ext (hx g)

theorem card_orbit_dvd_card [Finite G] (x : Ω) : Nat.card (MulAction.orbit G x) ∣ Nat.card G := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem exists_card_orbit_eq_two [Finite G] [Finite Ω] (hG : Nat.card G = 36)
    (hΩ : Nat.card Ω = 13) {ω₁ ω₂ : Ω} (h12 : ω₁ ≠ ω₂) (hfix₁ : ∀ g : G, g • ω₁ = ω₁)
    (hfix₂ : ∀ g : G, g • ω₂ = ω₂) (hQ : Nat.card (MulAction.orbitRel.Quotient G Ω) ≤ 4) :
    Nat.card (MulAction.orbitRel.Quotient G Ω) = 4 ∧
      ∃ x : Ω, Nat.card (MulAction.orbit G x) = 2 := by
  let _ := Fintype.ofFinite Ω
  let _ : Fintype (MulAction.orbitRel.Quotient G Ω) := Fintype.ofFinite _
  have hQcard : Nat.card (MulAction.orbitRel.Quotient G Ω) =
      (Finset.univ : Finset (MulAction.orbitRel.Quotient G Ω)).card := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  rw [hQcard] at hQ ⊢
  have hsum : ∑ q : MulAction.orbitRel.Quotient G Ω, Nat.card (MulAction.orbit G q.out) = 13 := by
    rw [← hΩ, Nat.card_congr (MulAction.selfEquivSigmaOrbits G Ω), Nat.card_sigma]
  have hsdvd : ∀ q : MulAction.orbitRel.Quotient G Ω, Nat.card (MulAction.orbit G q.out) ∣ 36 :=
    fun q => hG ▸ card_orbit_dvd_card q.out
  have hspos : ∀ q : MulAction.orbitRel.Quotient G Ω, 0 < Nat.card (MulAction.orbit G q.out) :=
    fun q => Nat.card_pos_iff.mpr ⟨⟨⟨q.out, MulAction.mem_orbit_self _⟩⟩, inferInstance⟩
  have hout : ∀ {ω : Ω}, (∀ g : G, g • ω = ω) →
      (Quotient.mk (MulAction.orbitRel G Ω) ω).out = ω := by
    intro ω hω
    have h := Quotient.mk_out (s := MulAction.orbitRel G Ω) ω
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp h
    have hg' : g • ω = (Quotient.mk (MulAction.orbitRel G Ω) ω).out := hg
    rw [← hg', hω]
  set q₁ := Quotient.mk (MulAction.orbitRel G Ω) ω₁ with hq₁
  set q₂ := Quotient.mk (MulAction.orbitRel G Ω) ω₂ with hq₂
  have hs₁ : Nat.card (MulAction.orbit G q₁.out) = 1 := by
    rw [hq₁, hout hfix₁]
    exact card_orbit_eq_one_of_fixed hfix₁
  have hs₂ : Nat.card (MulAction.orbit G q₂.out) = 1 := by
    rw [hq₂, hout hfix₂]
    exact card_orbit_eq_one_of_fixed hfix₂
  have hq12 : q₁ ≠ q₂ := by
    intro h
    have h' := Quotient.exact h
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp h'
    have hg' : g • ω₂ = ω₁ := hg
    rw [hfix₂] at hg'
    exact h12 hg'.symm
  have hmem₂ : q₂ ∈ Finset.univ.erase q₁ := Finset.mem_erase.mpr ⟨hq12.symm, Finset.mem_univ q₂⟩
  have hTsum : ∑ q ∈ (Finset.univ.erase q₁).erase q₂, Nat.card (MulAction.orbit G q.out) = 11 := by
    have h1 := Finset.add_sum_erase Finset.univ (fun q => Nat.card (MulAction.orbit G q.out))
      (Finset.mem_univ q₁)
    have h2 := Finset.add_sum_erase (Finset.univ.erase q₁)
      (fun q => Nat.card (MulAction.orbit G q.out)) hmem₂
    rw [hsum, ← h2, hs₁, hs₂] at h1
    omega
  have hTcard : ((Finset.univ.erase q₁).erase q₂).card + 2 =
      (Finset.univ : Finset (MulAction.orbitRel.Quotient G Ω)).card := by
    rw [Finset.card_erase_of_mem hmem₂, Finset.card_erase_of_mem (Finset.mem_univ q₁)]
    have h2le : 2 ≤ (Finset.univ : Finset (MulAction.orbitRel.Quotient G Ω)).card := by
      rw [← Finset.card_pair hq12]
      exact Finset.card_le_univ _
    omega
  set T := (Finset.univ.erase q₁).erase q₂ with hT
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hTsum
    omega
  rcases Nat.lt_or_ge T.card 2 with hlt | hge
  ·
    have h1 : T.card = 1 := by
      have := hTne.card_pos
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    rw [ha, Finset.sum_singleton] at hTsum
    have := hsdvd a
    rw [hTsum] at this
    norm_num at this
  · have h2 : T.card = 2 := by omega
    obtain ⟨a, b, hab, hTab⟩ := Finset.card_eq_two.mp h2
    rw [hTab, Finset.sum_pair hab] at hTsum
    refine ⟨by omega, ?_⟩
    have ha := hsdvd a
    have hb := hsdvd b
    have hapos := hspos a
    have hbpos := hspos b
    have hcases : Nat.card (MulAction.orbit G a.out) = 2 ∨
        Nat.card (MulAction.orbit G b.out) = 2 := by
      have hale : Nat.card (MulAction.orbit G a.out) ≤ 10 := by omega
      have hbeq : Nat.card (MulAction.orbit G b.out) = 11 - Nat.card (MulAction.orbit G a.out) := by
        omega
      rw [hbeq] at hb
      interval_cases Nat.card (MulAction.orbit G a.out) <;> simp_all
    rcases hcases with h | h
    · exact ⟨a.out, h⟩
    · exact ⟨b.out, h⟩

end Orbits

section Main

theorem card_orderOf_eq_two_of_not_normal (hH : Nat.card H = 36) (h4 : ∀ h : H, orderOf h ≠ 4)
    (V : Sylow 3 H) (hV9 : Nat.card V = 9) (hVcomm : ∀ a b : V, a * b = b * a)
    (hne : ∃ W : Sylow 3 H, W ≠ V) :
    Nat.card {g : H // orderOf g = 2} = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hindexV : (V : Subgroup H).index = 4 := by
    have h := Subgroup.card_mul_index (V : Subgroup H)
    rw [hV9, hH] at h
    omega
  have hcardSyl : Nat.card (Sylow 3 H) = 4 := by
    have hdvd := Sylow.card_dvd_index V
    rw [hindexV] at hdvd
    have hmod := card_sylow_modEq_one 3 H
    have hne1 : Nat.card (Sylow 3 H) ≠ 1 := by
      intro h1
      obtain ⟨W, hW⟩ := hne
      have : Subsingleton (Sylow 3 H) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hW (Subsingleton.elim W V)
    have hle : Nat.card (Sylow 3 H) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 3 H) := Nat.card_pos
    interval_cases h : Nat.card (Sylow 3 H)
    · exact absurd rfl hne1
    · exact absurd hmod (by decide)
    · norm_num at hdvd
    · rfl
  have hnormV : Subgroup.normalizer (V : Set H) = V := by
    have hidx : (Subgroup.normalizer ((V : Subgroup H) : Set H)).index = 4 :=
      (Sylow.card_eq_index_normalizer V).symm.trans hcardSyl
    have h : Nat.card (Subgroup.normalizer ((V : Subgroup H) : Set H)) * 4 = 36 := by
      rw [← hidx, Subgroup.card_mul_index, hH]
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.le_normalizer) ?_).symm
    rw [hV9]
    omega
  have hNC : Subgroup.normalizer (V : Set H) ≤ Subgroup.centralizer (V : Set H) := by
    rw [hnormV]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hVcomm ⟨h, hh⟩ ⟨g, hg⟩)
  obtain ⟨K, hKn, -, hKidx, -, -, -, -, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement V hNC
  have hK4 : Nat.card K = 4 := by
    have h := Subgroup.card_mul_index K
    rw [hKidx, hV9, hH] at h
    omega
  have hinv : ∀ g : H, orderOf g = 2 → g ∈ K := by
    intro g hg
    have hq : Nat.card (H ⧸ K) = 9 := by
      rw [← Subgroup.index_eq_card, hKidx, hV9]
    have h2 : orderOf (QuotientGroup.mk' K g) ∣ 2 := hg ▸ orderOf_map_dvd _ g
    have h9 : orderOf (QuotientGroup.mk' K g) ∣ 9 := hq ▸ orderOf_dvd_natCard _
    have h1 : orderOf (QuotientGroup.mk' K g) = 1 := by
      have h := Nat.dvd_gcd h2 h9
      rw [show Nat.gcd 2 9 = 1 by norm_num] at h
      exact Nat.dvd_one.mp h
    rw [orderOf_eq_one_iff] at h1
    exact (QuotientGroup.eq_one_iff g).mp h1
  have hKinv : ∀ k : H, k ∈ K → k ≠ 1 → orderOf k = 2 := by
    intro k hk hk1
    have hdvd : orderOf k ∣ 4 := by
      have := Subgroup.orderOf_dvd_natCard K hk
      rwa [hK4] at this
    have hle : orderOf k ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos := orderOf_pos k
    have hne1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
    interval_cases hk : orderOf k
    · exact absurd rfl hne1
    · rfl
    · norm_num at hdvd
    · exact absurd hk (h4 k)
  have hequiv : {g : H // orderOf g = 2} ≃ {k : K // k ≠ 1} :=
    { toFun := fun g => ⟨⟨g, hinv g g.2⟩, fun h => by
        have := congrArg Subtype.val h
        have hg1 : (g : H) = 1 := this
        have := g.2
        rw [hg1, orderOf_one] at this
        norm_num at this⟩
      invFun := fun k => ⟨k, hKinv k k.1.2 fun h => k.2 (Subtype.ext h)⟩
      left_inv := fun g => rfl
      right_inv := fun k => rfl }
  rw [Nat.card_congr hequiv]
  have hsub : Nat.card {k : K // k ≠ 1} = Nat.card K - 1 := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  rw [hsub, hK4]

theorem order_thirty_six_action_normal_three_subgroup (hH : Nat.card H = 36)
    (h4 : ∀ h : H, orderOf h ≠ 4) (h9 : ∀ h : H, orderOf h ≠ 9) {Ω : Type*} [MulAction H Ω]
    [Finite Ω] (hΩ : Nat.card Ω = 13)
    (hfix : ∃ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ ∧ ∀ h : H, h • ω₁ = ω₁ ∧ h • ω₂ = ω₂)
    (hfix2 : ∀ h : H, orderOf h = 2 → Nat.card (MulAction.fixedBy Ω h) = 5)
    (hfix3 : ∀ h : H, orderOf h = 3 → Nat.card (MulAction.fixedBy Ω h) = 4)
    (hfix6 : ∀ h : H, orderOf h = 6 → Nat.card (MulAction.fixedBy Ω h) = 2) :
    ∃ V : Sylow 3 H, (∀ W : Sylow 3 H, W = V) ∧ Nat.card V = 9 ∧
      (∀ a b : V, a * b = b * a) ∧ (∀ v : V, v ^ 3 = 1) ∧
      ∀ a b : H, orderOf a = 3 → orderOf b = 3 → a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω₁, ω₂, h12, hω⟩ := hfix
  obtain ⟨V⟩ : Nonempty (Sylow 3 H) := Sylow.nonempty
  have hV9 := sylow_three_card_of_card_thirty_six hH V
  have hVcomm' : IsMulCommutative (V : Subgroup H) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hV9]; norm_num)
  have hVcomm : ∀ a b : V, a * b = b * a := fun a b => hVcomm'.is_comm.comm a b
  have hVexp : ∀ v : V, v ^ 3 = 1 := by
    intro v
    have hdvd : orderOf v ∣ 9 := hV9 ▸ orderOf_dvd_natCard v
    have hne9 : orderOf v ≠ 9 := by
      rw [← Subgroup.orderOf_coe]
      exact h9 v
    have h3 : orderOf v ∣ 3 := by
      have hle : orderOf v ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos := orderOf_pos v
      interval_cases h : orderOf v <;> simp_all
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  have huniq : ∀ W : Sylow 3 H, W = V := by
    by_contra hcon
    obtain ⟨W, hW⟩ := not_forall.mp hcon
    have hN2 := card_orderOf_eq_two_of_not_normal hH h4 V hV9 hVcomm ⟨W, hW⟩
    let _ := Fintype.ofFinite H
    let _ := Fintype.ofFinite Ω
    have horders := orderOf_mem_of_card_thirty_six hH h4 h9
    have hcount : ∀ k : ℕ, Nat.card {g : H // orderOf g = k} =
        (Finset.univ.filter fun g : H => orderOf g = k).card := fun k => by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hN1 : (Finset.univ.filter fun g : H => orderOf g = 1).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨1, ?_⟩
      ext g
      simp [orderOf_eq_one_iff]
    rw [hcount] at hN2
    have htotal : (Finset.univ.filter fun g : H => orderOf g = 1).card +
        (Finset.univ.filter fun g : H => orderOf g = 2).card +
        (Finset.univ.filter fun g : H => orderOf g = 3).card +
        (Finset.univ.filter fun g : H => orderOf g = 6).card = 36 := by
      simp only [Finset.card_filter]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← hH,
        Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun g _ => ?_
      rcases horders g with h | h | h | h <;> simp [h]
    have hfixsum : ∑ g : H, Nat.card (MulAction.fixedBy Ω g) =
        13 * (Finset.univ.filter fun g : H => orderOf g = 1).card +
        5 * (Finset.univ.filter fun g : H => orderOf g = 2).card +
        4 * (Finset.univ.filter fun g : H => orderOf g = 3).card +
        2 * (Finset.univ.filter fun g : H => orderOf g = 6).card := by
      simp only [Finset.card_filter, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rcases horders g with h | h | h | h
      · rw [orderOf_eq_one_iff] at h
        subst h
        have : MulAction.fixedBy Ω (1 : H) = Set.univ := by
          ext x
          simp
        rw [this, Nat.card_coe_set_eq, Set.ncard_univ, hΩ]
        simp
      · rw [hfix2 g h]
        simp [h]
      · rw [hfix3 g h]
        simp [h]
      · rw [hfix6 g h]
        simp [h]
    have hburnside : ∑ g : H, Nat.card (MulAction.fixedBy Ω g) =
        Nat.card (MulAction.orbitRel.Quotient H Ω) * 36 := by
      have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H Ω
      simp only [← Nat.card_eq_fintype_card] at h
      rw [h, hH]
    have hQ4 : Nat.card (MulAction.orbitRel.Quotient H Ω) ≤ 4 := by
      have := hfixsum.symm.trans hburnside
      omega
    obtain ⟨hQ, x, hx⟩ := exists_card_orbit_eq_two (G := H) hH hΩ h12 (fun g => (hω g).1)
      (fun g => (hω g).2) hQ4
    have hN3 : (Finset.univ.filter fun g : H => orderOf g = 3).card = 26 := by
      have := hfixsum.symm.trans hburnside
      rw [hQ] at this
      omega
    have hstab : Nat.card (MulAction.stabilizer H x) = 18 := by
      have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H x
      simp only [← Nat.card_eq_fintype_card] at h
      rw [hx, hH] at h
      omega
    have hle : (Finset.univ.filter fun g : H => orderOf g = 3).card ≤
        Nat.card (MulAction.stabilizer H x) := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
      refine Fintype.card_le_of_injective
        (fun g => ⟨g.1, smul_eq_self_of_card_orbit_eq_two hx
          (orderOf_dvd_iff_pow_eq_one.mp (by rw [(Finset.mem_filter.mp g.2).2]))⟩) ?_
      intro g g' h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      exact h'
    omega
  refine ⟨V, huniq, hV9, hVcomm, hVexp, ?_⟩
  have hmem : ∀ x : H, orderOf x = 3 → x ∈ (V : Subgroup H) := by
    intro x hx
    have hp : IsPGroup 3 (Subgroup.zpowers x) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hx, pow_one]
    obtain ⟨W, hW⟩ := hp.exists_le_sylow
    rw [huniq W] at hW
    exact hW (Subgroup.mem_zpowers x)
  intro a b ha hb
  exact congrArg Subtype.val (hVcomm ⟨a, hmem a ha⟩ ⟨b, hmem b hb⟩)

end Main

end CFSG.Semidihedral.GL2Recognition
