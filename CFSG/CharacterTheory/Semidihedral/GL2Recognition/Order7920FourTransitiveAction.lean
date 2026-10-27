module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.Order7920Profile
public import CFSG.CharacterTheory.Semidihedral.Principal.GL2OddKernelElimination
public import CFSG.CharacterTheory.PermutationCharacterOrbits

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Semidihedral.Principal.GL2ThreeCharacters

namespace Order7920Action

section Gap

variable {G : Type} [Group G] [Fintype G]

theorem permutation_constituents_degree_ten (data : FiniteComplexRepresentation.{0, 0} G)
    (hgap : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ∃ d : ℕ, 10 ≤ d ∧ ψ 1 = d)
    (hone : characterPairing data.character 1 = 1) :
    (data.character 1 ≠ 1 → 11 ≤ (Module.finrank ℂ data.vector : ℕ)) ∧
    ((Module.finrank ℂ data.vector : ℕ) = 11 →
      ∃ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 ∧ ψ 1 = 10 ∧ data.character = 1 + ψ) := by
  obtain ⟨size, summand, hirr, hsum⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum data
  let ψ : Fin size → G → ℂ := fun k => (summand k).character
  have hdecomp : data.character = fun g => ∑ k, (1 : ℂ) * ψ k g := by
    funext g
    simp only [one_mul, ψ]
    exact hsum g
  have hprin := principalFiniteComplexRepresentation_character G
  have hcount : (Finset.univ.filter fun k : Fin size => ψ k = 1).card = 1 := by
    have h := hone
    rw [hdecomp, characterPairing_expansion_left] at h
    have h' : ∑ k : Fin size, (1 : ℂ) * characterPairing (ψ k) 1 =
        ((Finset.univ.filter fun k : Fin size => ψ k = 1).card : ℂ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_mul, ← hprin, characterPairing_irreducible _ _ (hirr k)
        (principalFiniteComplexRepresentation_isIrreducible G)]
      split_ifs <;> simp
    rw [h'] at h
    exact_mod_cast h
  obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp hcount
  have hk₀1 : ψ k₀ = 1 := by
    have : k₀ ∈ Finset.univ.filter fun k : Fin size => ψ k = 1 := by
      rw [hk₀]
      exact Finset.mem_singleton_self k₀
    exact (Finset.mem_filter.mp this).2
  have hother : ∀ k, k ≠ k₀ → ψ k ≠ 1 := by
    intro k hk h
    have : k ∈ Finset.univ.filter fun k : Fin size => ψ k = 1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [hk₀, Finset.mem_singleton] at this
    exact hk this
  let deg : Fin size → ℕ := fun k => Module.finrank ℂ (summand k).vector
  have hdegψ : ∀ k, ψ k 1 = deg k := fun k => by
    simp [ψ, deg, FiniteComplexRepresentation.character, Representation.char_one]
  have hmemIrr : ∀ k, ψ k ∈ CFSG.BlocksIrr G := fun k => by
    rw [CFSG.blocksIrr_eq_irreducible_characters]
    exact ⟨summand k, hirr k, rfl⟩
  have hdeg10 : ∀ k, k ≠ k₀ → 10 ≤ deg k := by
    intro k hk
    obtain ⟨d, hd, hd1⟩ := hgap (ψ k) (hmemIrr k) (hother k hk)
    have h := hdegψ k
    rw [hd1] at h
    have : deg k = d := by exact_mod_cast h.symm
    omega
  have hdim : Module.finrank ℂ data.vector = ∑ k, deg k := by
    have h := congrFun hdecomp 1
    simp only [one_mul] at h
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have : (Module.finrank ℂ data.vector : ℂ) = ((∑ k, deg k : ℕ) : ℂ) := by
      rw [h, Nat.cast_sum]
      exact Finset.sum_congr rfl fun k _ => hdegψ k
    exact_mod_cast this
  have hdegk₀ : deg k₀ = 1 := by
    have h := hdegψ k₀
    rw [hk₀1, Pi.one_apply] at h
    exact_mod_cast h.symm
  have hsplit : ∑ k, deg k = 1 + ∑ k ∈ Finset.univ.erase k₀, deg k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀), hdegk₀]
  constructor
  · intro hne
    rw [hdim, hsplit]
    have hne' : (Finset.univ.erase k₀).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hne
      rw [FiniteComplexRepresentation.character, Representation.char_one, hdim, hsplit,
        hempty, Finset.sum_empty]
      norm_num
    obtain ⟨k₁, hk₁⟩ := hne'
    have h10 := hdeg10 k₁ (Finset.ne_of_mem_erase hk₁)
    have := Finset.single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hk₁
    omega
  · intro h11
    rw [hdim, hsplit] at h11
    have hne' : (Finset.univ.erase k₀).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at h11
      omega
    obtain ⟨k₁, hk₁⟩ := hne'
    have hk₁ne := Finset.ne_of_mem_erase hk₁
    have hrest0 : ∀ k ∈ (Finset.univ.erase k₀).erase k₁, False := by
      intro k hk
      have hk₀' : k ≠ k₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
      have h10 := hdeg10 k hk₀'
      have h10' := hdeg10 k₁ hk₁ne
      have h1 := Finset.add_sum_erase _ deg hk₁
      have := Finset.single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hk
      omega
    have hk₁deg : deg k₁ = 10 := by
      have h := Finset.add_sum_erase _ deg hk₁
      have h10 := hdeg10 k₁ hk₁ne
      omega
    have hempty : (Finset.univ.erase k₀).erase k₁ = ∅ :=
      Finset.eq_empty_of_forall_notMem fun k hk => hrest0 k hk
    have huniv : (Finset.univ : Finset (Fin size)) = {k₀, k₁} := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      by_contra hk
      push Not at hk
      have : k ∈ (Finset.univ.erase k₀).erase k₁ :=
        Finset.mem_erase.mpr ⟨hk.2, Finset.mem_erase.mpr ⟨hk.1, Finset.mem_univ _⟩⟩
      rw [hempty] at this
      exact Finset.notMem_empty _ this
    refine ⟨ψ k₁, hmemIrr k₁, hother k₁ hk₁ne, by rw [hdegψ, hk₁deg]; norm_num, ?_⟩
    rw [hdecomp]
    funext g
    rw [huniv, Finset.sum_pair hk₁ne.symm, one_mul, one_mul, hk₀1]
    rfl

end Gap

section Sums

variable {G : Type} [Group G] [Fintype G]

theorem sum_subgroup_eq {χ : G → ℂ} (hχ1 : χ 1 = 10)
    (h24 : ∀ g, orderOf g = 2 ∨ orderOf g = 4 → χ g = 2) (h5 : ∀ g, orderOf g = 5 → χ g = 0)
    (A : Subgroup G) (hA : ∀ a : A, orderOf a ∈ ({1, 2, 4, 5} : Finset ℕ)) :
    ∑ a : A, χ a =
      10 + 2 * ((Nat.card A : ℂ) - 1 - (Nat.card {a : A // orderOf a = 5} : ℂ)) := by
  have hc : ∀ a : A, χ a =
      (fun d : ℕ => if d = 1 then (10 : ℂ) else if d = 5 then 0 else 2) (orderOf a) := by
    intro a
    have ha := hA a
    have ha' : orderOf (a : G) = orderOf a := Subgroup.orderOf_coe a
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with h | h | h | h
    · rw [orderOf_eq_one_iff.mp h]
      simp [hχ1]
    · simp [h, h24 _ (Or.inl (ha'.trans h))]
    · simp [h, h24 _ (Or.inr (ha'.trans h))]
    · simp [h, h5 _ (ha'.trans h)]
  rw [sum_eq_sum_orders _ _ hA
    (fun d : ℕ => if d = 1 then (10 : ℂ) else if d = 5 then 0 else 2) hc]
  have hcard := card_eq_sum_card_orderOf (G := A) ({1, 2, 4, 5} : Finset ℕ) hA
  have hN1 : Nat.card {a : A // orderOf a = 1} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨1, orderOf_one⟩, fun g => Subtype.ext (orderOf_eq_one_iff.mp g.2)⟩
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, hN1] at hcard ⊢
  have hcardC : (Nat.card A : ℂ) = 1 + (Nat.card {a : A // orderOf a = 2} : ℂ) +
      (Nat.card {a : A // orderOf a = 4} : ℂ) + (Nat.card {a : A // orderOf a = 5} : ℂ) := by
    rw [hcard]
    push_cast
    ring
  rw [hcardC]
  norm_num
  ring

theorem finrank_invariants_eq {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G) {s : ℂ} (hs : ∑ a : A, ρ.character a = s)
    {d : ℕ} (hd : s = (Nat.card A : ℂ) * d) :
    Module.finrank ℂ (Representation.invariants (ρ.comp A.subtype)) = d := by
  have h := CFSG.Semidihedral.GL2Recognition.finrank_invariants_subgroup ρ A
  rw [hs, hd] at h
  have hA : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul] at h
  exact_mod_cast h.symm

end Sums

section Quaternion

variable {G : Type*} [Group G]

theorem exists_quaternion_of_orderOf_eq_four {f : G} (hf : orderOf f = 4)
    (ψ : Subgroup.centralizer ({f ^ 2} : Set G) ≃* G23) :
    ∃ κ : QuaternionGroup 2 →* G, Function.Injective κ ∧ f ∈ κ.range := by
  have hfmem : f ∈ Subgroup.centralizer ({f ^ 2} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [pow_two, mul_assoc])
  set y := ψ ⟨f, hfmem⟩ with hydef
  have hy : orderOf y = 4 := by rw [hydef, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hf]
  set w := GL2Elimination.quatHom (QuaternionGroup.a 1) with hwdef
  have hw : orderOf w = 4 := by
    rw [hwdef, orderOf_injective _ GL2Elimination.quatHom_injective,
      QuaternionGroup.orderOf_a_one]
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_GL2_of_orderOf_eq (hw.trans hy.symm) (Or.inl hw))
  let κ : QuaternionGroup 2 →* G :=
    ((Subgroup.centralizer ({f ^ 2} : Set G)).subtype.comp ψ.symm.toMonoidHom).comp
      ((MulAut.conj c).toMonoidHom.comp GL2Elimination.quatHom)
  have hκ : Function.Injective κ :=
    (Subtype.val_injective.comp ψ.symm.injective).comp
      ((MulAut.conj c).injective.comp GL2Elimination.quatHom_injective)
  refine ⟨κ, hκ, QuaternionGroup.a 1, ?_⟩
  change ((ψ.symm (MulAut.conj c (GL2Elimination.quatHom (QuaternionGroup.a 1))) :
    Subgroup.centralizer ({f ^ 2} : Set G)) : G) = f
  rw [MulAut.conj_apply, ← hwdef, hc, hydef, MulEquiv.symm_apply_apply]

theorem quaternion_eq_or_sq_eq : ∀ q : QuaternionGroup 2, q ≠ 1 →
    q = QuaternionGroup.a 2 ∨ q ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem quaternion_pow_four : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by
  decide

end Quaternion

section OneTwenty

variable {G : Type*} [Group G] [Finite G]

theorem conj_eq_inv_of_involution {P : Subgroup G} (hP : Nat.card P = 5)
    (hCP : Subgroup.centralizer (P : Set G) = P) {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hzN : z ∈ Subgroup.normalizer (P : Set G)) : ∀ p ∈ P, z * p * z⁻¹ = p⁻¹ := by
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  set x : G := (x' : G) with hxdef
  have hx : orderOf x = 5 := by rw [hxdef, Subgroup.orderOf_coe, hx']
  have hPx : P = Subgroup.zpowers x := (Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr x'.2) (by rw [hP, Nat.card_zpowers, hx])).symm
  have hx5 : x ^ (5 : ℕ) = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hmem : z * x * z⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hzN x).mp (hPx ▸
    Subgroup.mem_zpowers x)
  rw [hPx, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  rw [zpow_eq_zpow_emod' k hx5] at hk
  obtain ⟨r, hr⟩ : ∃ r, k % ((5 : ℕ) : ℤ) = r := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg k (by norm_num)
  have hr5 : r < 5 := hr ▸ Int.emod_lt_of_pos k (by norm_num)
  rw [hr] at hk
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have htwice : x = x ^ (r * r) := by
    have h1 : z * (z * x * z⁻¹) * z⁻¹ = x := by
      calc z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z * z)⁻¹ := by group
        _ = x := by rw [hzz]; group
    rw [← hk, ← conj_zpow, ← hk, ← zpow_mul] at h1
    exact h1.symm
  have hz2' : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzP : z ∉ P := fun h => by
    have := Subgroup.orderOf_dvd_natCard P h
    rw [hP, hz2'] at this
    norm_num at this
  have hconj : z * x * z⁻¹ = x⁻¹ := by
    interval_cases r
    · exfalso
      rw [zpow_zero] at hk
      have : x = 1 := by
        calc x = z⁻¹ * (z * x * z⁻¹) * z := by group
          _ = z⁻¹ * 1 * z := by rw [← hk]
          _ = 1 := by group
      rw [this, orderOf_one] at hx
      norm_num at hx
    · exfalso
      apply hzP
      rw [← hCP, hPx, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff]
      rw [zpow_one] at hk
      calc z * x = z * x * z⁻¹ * z := by group
        _ = x * z := by rw [← hk]
    · exfalso
      have h4 : x ^ (3 : ℕ) * x = x := by
        have := htwice.symm
        rw [show (2 : ℤ) * 2 = ((3 + 1 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ] at this
        exact this
      have := orderOf_dvd_of_pow_eq_one (mul_eq_right.mp h4)
      rw [hx] at this
      norm_num at this
    · exfalso
      have h9 : x ^ (8 : ℕ) * x = x := by
        have := htwice.symm
        rw [show (3 : ℤ) * 3 = ((8 + 1 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ] at this
        exact this
      have := orderOf_dvd_of_pow_eq_one (mul_eq_right.mp h9)
      rw [hx] at this
      norm_num at this
    · rw [← hk]
      have : x ^ (4 : ℤ) = x ^ ((5 : ℕ) : ℤ) * x⁻¹ := by
        rw [show (4 : ℤ) = ((5 : ℕ) : ℤ) - 1 by norm_num, zpow_sub_one]
      rw [this, zpow_natCast, hx5, one_mul]
  intro p hp
  rw [hPx, Subgroup.mem_zpowers_iff] at hp
  obtain ⟨j, rfl⟩ := hp
  rw [← conj_zpow, hconj, inv_zpow]

theorem false_of_card_eq_120 {P M Q : Subgroup G} (hP : Nat.card P = 5)
    (hCP : Subgroup.centralizer (P : Set G) = P)
    (hN20 : Nat.card (Subgroup.normalizer (P : Set G)) = 20)
    (hNM : Subgroup.normalizer (P : Set G) ≤ M) (hQM : Q ≤ M) (ψ : Q ≃* QuaternionGroup 2)
    (hM : Nat.card M = 120) : False := by
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPM : P ≤ M := Subgroup.le_normalizer.trans hNM
  have hfac : Nat.factorization 120 5 = 1 := by
    have h : (120 : ℕ) = 5 ^ 1 * 24 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hP' : Nat.card (P.subgroupOf M) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hP]
  let P' : Sylow 5 M := Sylow.ofCard (P.subgroupOf M) (by rw [hP', hM, hfac, pow_one])
  have hNP' : Subgroup.normalizer ((P' : Subgroup M) : Set M) =
      (Subgroup.normalizer (P : Set G)).subgroupOf M :=
    (Subgroup.subgroupOf_normalizer_eq hPM).symm
  have hcardN' : Nat.card (Subgroup.normalizer ((P' : Subgroup M) : Set M)) = 20 := by
    rw [hNP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv, hN20]
  have hn5 : Nat.card (Sylow 5 M) = 6 := by
    have h : Nat.card (Sylow 5 M) = (Subgroup.normalizer ((P' : Subgroup M) : Set M)).index :=
      Sylow.card_eq_index_normalizer P'
    have h2 := (Subgroup.normalizer ((P' : Subgroup M) : Set M)).card_mul_index
    rw [hcardN', hM] at h2
    omega
  have hNS : ∀ S : Sylow 5 M, Nat.card (Subgroup.normalizer ((S : Subgroup M) : Set M)) = 20 :=
      fun S => by
    have h : Nat.card (Sylow 5 M) = (Subgroup.normalizer ((S : Subgroup M) : Set M)).index :=
      Sylow.card_eq_index_normalizer S
    have h2 := (Subgroup.normalizer ((S : Subgroup M) : Set M)).card_mul_index
    rw [← h, hn5, hM] at h2
    omega
  have hcardS : ∀ S : Sylow 5 M, Nat.card (S : Subgroup M) = 5 := fun S => by
    rw [Sylow.card_eq_multiplicity, hM, hfac, pow_one]
  let ι : QuaternionGroup 2 →* M :=
    { toFun := fun q => ⟨((ψ.symm q : Q) : G), hQM (ψ.symm q).2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun q q' => Subtype.ext (by simp) }
  have hιinj : Function.Injective ι := fun q q' h => ψ.symm.injective (Subtype.ext
    (congrArg Subtype.val h :))
  set z : M := ι (QuaternionGroup.a 2) with hzdef
  have hzfix : ∀ S : Sylow 5 M, z • S = S := by
    intro S
    have := Fintype.ofFinite (Sylow 5 M)
    obtain ⟨q, q', hqq', hS⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun q => ι q • S) (by
      rw [← Nat.card_eq_fintype_card, hn5, QuaternionGroup.card]
      norm_num)
    have hr1 : q⁻¹ * q' ≠ 1 := fun h => hqq' (by rw [inv_mul_eq_one] at h; exact h)
    have hrS : ι (q⁻¹ * q') • S = S := by
      rw [map_mul, mul_smul, ← hS, map_inv, ← mul_smul, inv_mul_cancel, one_smul]
    rcases quaternion_eq_or_sq_eq _ hr1 with h | h
    · rw [hzdef, ← h]
      exact hrS
    · rw [hzdef, ← h, map_pow, pow_two, mul_smul, hrS, hrS]
  have hz2 : ((z : M) : G) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hzdef, ← map_pow]
    have : (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 := by decide
    rw [this, map_one, Subgroup.coe_one]
  have hz1 : ((z : M) : G) ≠ 1 := fun h => by
    have h' : z = 1 := Subtype.ext h
    rw [hzdef] at h'
    have : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := hιinj (h'.trans (map_one ι).symm)
    exact absurd this (by decide)
  have hzN : ((z : M) : G) ∈ Subgroup.normalizer (P : Set G) := by
    have h : z ∈ Subgroup.normalizer ((P' : Subgroup M) : Set M) :=
      (Sylow.smul_eq_iff_mem_normalizer).mp (hzfix P')
    rw [hNP', Subgroup.mem_subgroupOf] at h
    exact h
  have hinvP := conj_eq_inv_of_involution hP hCP hz2 hz1 hzN
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  set x : M := ⟨(x' : G), hPM x'.2⟩ with hxdef
  have hx : orderOf x = 5 := by
    rw [hxdef, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx']
  have hxP' : x ∈ (P' : Subgroup M) := Subgroup.mem_subgroupOf.mpr x'.2
  have hzx : z * x * z⁻¹ = x⁻¹ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hinvP x' x'.2)
  have : Nontrivial (Sylow 5 M) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hn5]
    norm_num
  obtain ⟨S, hSP⟩ := exists_ne P'
  have hxS : (x * x) • S = S := by
    have h1 : z • (x • S) = x • S := hzfix (x • S)
    have h2 : z • (x • S) = x⁻¹ • S := by
      rw [← mul_smul, show z * x = x⁻¹ * z by rw [← hzx]; group, mul_smul, hzfix S]
    rw [mul_smul, show x • S = x⁻¹ • S from h1.symm.trans h2, ← mul_smul, mul_inv_cancel,
      one_smul]
  have hxN : x ∈ Subgroup.normalizer ((S : Subgroup M) : Set M) := by
    have h2 : x * x ∈ Subgroup.normalizer ((S : Subgroup M) : Set M) :=
      (Sylow.smul_eq_iff_mem_normalizer).mp hxS
    have hx5 : x ^ 5 = 1 := by rw [← hx, pow_orderOf_eq_one]
    have : x = (x * x) ^ 3 := by
      rw [← pow_two, ← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, hx5, one_mul]
    rw [this]
    exact Subgroup.pow_mem _ h2 3
  have hxS' : x ∈ (S : Subgroup M) := by
    set NS := Subgroup.normalizer ((S : Subgroup M) : Set M) with hNSdef
    have hnorm : ((S : Subgroup M).subgroupOf NS).Normal := Subgroup.normal_in_normalizer
    have hidx : ((S : Subgroup M).subgroupOf NS).index = 4 := by
      have h := ((S : Subgroup M).subgroupOf NS).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv,
        hcardS, hNS] at h
      omega
    let y : NS := ⟨x, hxN⟩
    have hy4 : y ^ 4 ∈ (S : Subgroup M).subgroupOf NS := by
      have hq : ((y : NS ⧸ (S : Subgroup M).subgroupOf NS)) ^ 4 = 1 := by
        rw [← hidx, Subgroup.index]
        exact pow_card_eq_one'
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq
      exact hq
    have hx4 : x ^ 4 ∈ (S : Subgroup M) := by
      have := Subgroup.mem_subgroupOf.mp hy4
      simpa [y] using this
    have hx5 : x ^ 5 = 1 := by rw [← hx, pow_orderOf_eq_one]
    have : x = (x ^ 4) ^ 4 := by
      rw [← pow_mul, show 4 * 4 = 5 * 3 + 1 from rfl, pow_succ, pow_mul, hx5, one_pow, one_mul]
    rw [this]
    exact Subgroup.pow_mem _ hx4 4
  apply hSP
  apply Sylow.ext
  refine (Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcardS, hcardS])).symm
  have hgen : (P' : Subgroup M) = Subgroup.zpowers x := (Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hxP') (by rw [hcardS, Nat.card_zpowers, hx])).symm
  rw [hgen]
  exact Subgroup.zpowers_le.mpr hxS'

end OneTwenty

section Sharp

variable {G : Type*} {X : Type*} [Group G] [MulAction G X] [Finite X]

theorem four_le_card_fixedBy {g : G} {a : Fin 4 → X} (ha : Function.Injective a)
    (hg : ∀ i, g • a i = a i) : 4 ≤ Nat.card (MulAction.fixedBy X g) := by
  have h := Nat.card_le_card_of_injective (fun i : Fin 4 => (⟨a i, hg i⟩ : MulAction.fixedBy X g))
    fun i j hij => ha (congrArg Subtype.val hij)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h

theorem sharply_four_transitive_of_fixed_le_three (hX : Nat.card X = 11)
    (hG : Nat.card G = 7920) (hfix : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) ≤ 3) :
    ∀ a b : Fin 4 → X, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i := by
  classical
  have := Fintype.ofFinite X
  have hone : ∀ g : G, ∀ a : Fin 4 → X, Function.Injective a → (∀ i, g • a i = a i) → g = 1 :=
    fun g a ha hg => by
      by_contra hg1
      have h4 := four_le_card_fixedBy ha hg
      have h3 := hfix g hg1
      omega
  intro a b ha hb
  let F : G → (Fin 4 ↪ X) := fun g =>
    ⟨fun i => g • a i, (MulAction.injective g).comp ha⟩
  have hFinj : Function.Injective F := by
    intro g g' hgg'
    have hi : ∀ i, g • a i = g' • a i := fun i => DFunLike.congr_fun hgg' i
    have h1 : g'⁻¹ * g = 1 := hone _ a ha fun i => by rw [mul_smul, hi i, inv_smul_smul]
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  have hcard : Nat.card G = Nat.card (Fin 4 ↪ X) := by
    rw [hG, Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, hX]
    decide
  have hFbij : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2 ⟨hFinj, hcard⟩
  obtain ⟨g, hg⟩ := hFbij.2 ⟨b, hb⟩
  refine ⟨g, fun i => DFunLike.congr_fun hg i, fun g' hg' => ?_⟩
  apply hFinj
  apply Function.Embedding.ext
  intro i
  exact (hg' i).trans (DFunLike.congr_fun hg i).symm

end Sharp

section Normalizer

variable {G : Type*} [Group G] [Finite G]

theorem card_orderOf_five_normalizer {P : Subgroup G} (hP : Nat.card P = 5)
    (hN20 : Nat.card (Subgroup.normalizer (P : Set G)) = 20) :
    Nat.card {a : Subgroup.normalizer (P : Set G) // orderOf a = 5} = 4 := by
  set N := Subgroup.normalizer (P : Set G) with hNdef
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hnorm : (P.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hidx : (P.subgroupOf N).index = 4 := by
    have h := (P.subgroupOf N).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hP,
      hN20] at h
    omega
  have hmemP : ∀ a : N, orderOf a = 5 → (a : G) ∈ P := by
    intro a ha
    have hq : ((a : N ⧸ P.subgroupOf N)) ^ 4 = 1 := by
      rw [← hidx, Subgroup.index]
      exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq
    have ha4 : (a : G) ^ 4 ∈ P := by
      have := Subgroup.mem_subgroupOf.mp hq
      simpa using this
    have ha5 : a ^ 5 = 1 := by rw [← ha, pow_orderOf_eq_one]
    have ha5' : (a : G) ^ 5 = 1 := by rw [← Subgroup.coe_pow, ha5, Subgroup.coe_one]
    have : (a : G) = ((a : G) ^ 4) ^ 4 := by
      rw [← pow_mul, show 4 * 4 = 5 * 3 + 1 from rfl, pow_succ, pow_mul, ha5', one_pow, one_mul]
    rw [this]
    exact Subgroup.pow_mem _ ha4 4
  have hord : ∀ p : P, p ≠ 1 → orderOf p = 5 := by
    intro p hp
    have hdvd : orderOf p ∣ 5 := hP ▸ orderOf_dvd_natCard p
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp5.out _ hdvd) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hp
    · exact h1
  have he : {a : N // orderOf a = 5} ≃ {p : P // p ≠ 1} :=
    { toFun := fun a => ⟨⟨a.1, hmemP a.1 a.2⟩, fun h => by
        have h' := congrArg Subtype.val h
        have h1 : a.1 = 1 := Subtype.ext h'
        have := a.2
        rw [h1, orderOf_one] at this
        norm_num at this⟩
      invFun := fun p => ⟨⟨p.1, Subgroup.le_normalizer p.1.2⟩, by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
        exact hord p.1 p.2⟩
      left_inv := fun a => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr he]
  have : Fintype P := Fintype.ofFinite P
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card, hP]

end Normalizer

theorem eq_of_dvd_396 {n : ℕ} (hdvd : n ∣ 396) (hmod : n % 5 = 1) (heven : 2 ∣ n) :
    n = 6 ∨ n = 36 ∨ n = 66 ∨ n = 396 := by
  have hmem : n ∈ Nat.divisors 396 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have key : ∀ n ∈ Nat.divisors 396, n % 5 = 1 → 2 ∣ n →
      n = 6 ∨ n = 36 ∨ n = 66 ∨ n = 396 := by decide +kernel
  exact key n hmem hmod heven

end Order7920Action

open Order7920Action in
theorem order7920_produces_sharply_four_transitive_action {G : Type} [Group G] [Fintype G]
    (hG : Nat.card G = 7920)
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (t : G)
    (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3)))
    (χ : G → ℂ) (hχ : χ ∈ CFSG.BlocksIrr G) (hχ1 : χ 1 = 10) (hχt : χ t = 2) :
    ∃ P F Q : Subgroup G, Nat.card P = 5 ∧ IsCyclic F ∧ Nat.card F = 4 ∧
      Nonempty (Q ≃* QuaternionGroup 2) ∧
      Subgroup.normalizer (P : Set G) = P ⊔ F ∧ P ⊓ F = ⊥ ∧ F ≤ Q ∧
      (Subgroup.normalizer (P : Set G) ⊔ Q).index = 11 ∧
      (∀ g : G, (∀ x : G ⧸ (Subgroup.normalizer (P : Set G) ⊔ Q), g • x = x) → g = 1) ∧
      (∀ a b : Fin 4 → G ⧸ (Subgroup.normalizer (P : Set G) ⊔ Q),
        Function.Injective a → Function.Injective b → ∃! g : G, ∀ i, g • a i = b i) ∧
      fixedPointCount G (G ⧸ (Subgroup.normalizer (P : Set G) ⊔ Q)) = 1 + χ := by
  obtain ⟨-, hPfacts, -, hcount, -, χ₀, hχ₀, -, -, huniq, -, hfaith, v24, v3, v58, v611, ψ₂, ψ₃,
    -, -, -, hψ₂χ, hψ₃χ, hψ₂1, hψ₃1, hψ₂t, hψ₃t, hgap⟩ :=
    order7920_local_profile_and_degree_ten_character hG hinv t ht hC
  obtain rfl : χ = χ₀ := huniq χ hχ hχ1 hχt
  obtain ⟨φ⟩ := hC
  have horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 8, 11} : Finset ℕ) := by
    intro g
    by_contra hg
    have h := hcount (orderOf g)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hg
    rw [ite_eq_right hg.1, ite_eq_right hg.2.1, ite_eq_right hg.2.2.1, ite_eq_right hg.2.2.2.1,
      ite_eq_right hg.2.2.2.2.1, ite_eq_right hg.2.2.2.2.2.1, ite_eq_right hg.2.2.2.2.2.2.1,
      ite_eq_right hg.2.2.2.2.2.2.2] at h
    have hpos : 0 < Nat.card {x : G // orderOf x = orderOf g} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨g, rfl⟩⟩, inferInstance⟩
    omega
  have hval2 : ∀ g : G, g ≠ 1 → χ g = 2 ∨ χ g = 1 ∨ χ g = 0 ∨ χ g = -1 := by
    intro g hg1
    have h := horders g
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h | h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1
    · exact Or.inl (v24 g (Or.inl h))
    · exact Or.inr (Or.inl (v3 g h))
    · exact Or.inl (v24 g (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl (v58 g (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (v611 g (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inl (v58 g (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (v611 g (Or.inr h))))
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P₅⟩ : Nonempty (Sylow 5 G) := Sylow.nonempty
  set P : Subgroup G := (P₅ : Subgroup G) with hPdef
  have hfac5 : Nat.factorization 7920 5 = 1 := by
    have h : (7920 : ℕ) = 5 ^ 1 * 1584 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hP : Nat.card P = 5 := by rw [hPdef, Sylow.card_eq_multiplicity, hG, hfac5, pow_one]
  obtain ⟨hCP, F, hFcyc, hF4, hFN, hPF, hNPF, -⟩ := hPfacts P hP
  set N := Subgroup.normalizer (P : Set G) with hNdef
  have hN20 : Nat.card N = 20 := by
    have hcyc : IsCyclic P := isCyclic_of_prime_card hP
    have hCN := Subgroup.centralizer_le_normalizer (P : Set G)
    have hrel : (Subgroup.centralizer (P : Set G)).relIndex N ∣ 4 := by
      have key := Subgroup.card_dvd_of_injective _
        (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
      rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex,
        IsCyclic.card_mulAut, hP, Nat.totient_prime hp5.out] at key
      exact key
    have hCN' : (Subgroup.centralizer (P : Set G)).relIndex N *
        Nat.card (Subgroup.centralizer (P : Set G)) = Nat.card N := by
      have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (P : Set G)) (K := N)
      rwa [inf_of_le_left hCN] at h
    have hc5 : Nat.card (Subgroup.centralizer (P : Set G)) = 5 := by rw [hCP, hP]
    rw [hc5] at hCN'
    have hle := Nat.le_of_dvd (by norm_num) hrel
    have h5 := Subgroup.card_dvd_of_le (Subgroup.le_normalizer : P ≤ N)
    have h4 := Subgroup.card_dvd_of_le hFN
    rw [hP] at h5
    rw [hF4] at h4
    have h20 : 20 ∣ Nat.card N := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h5
    have := Nat.le_of_dvd Nat.card_pos h20
    omega
  obtain ⟨f', hf'⟩ := IsCyclic.exists_generator (α := F)
  set f : G := (f' : G) with hfdef
  have hf : orderOf f = 4 := by
    rw [hfdef, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hf', hF4]
  have hFf : F = Subgroup.zpowers f := (Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr f'.2) (by rw [hF4, Nat.card_zpowers, hf])).symm
  have hu : orderOf (f ^ 2) = 2 := by
    rw [orderOf_pow' f two_ne_zero, hf]
    norm_num
  obtain ⟨ψu⟩ := nonempty_centralizer_involution_mulEquiv hinv ht φ hu
  obtain ⟨κ, hκ, hfκ⟩ := exists_quaternion_of_orderOf_eq_four hf ψu
  set Q := κ.range with hQdef
  have hFQ : F ≤ Q := by
    rw [hFf]
    exact Subgroup.zpowers_le.mpr hfκ
  let eQ : QuaternionGroup 2 ≃* Q := MonoidHom.ofInjective hκ
  have hQ8 : Nat.card Q = 8 := by
    rw [← Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  set M := N ⊔ Q with hMdef
  have hNM : N ≤ M := le_sup_left
  have hQM : Q ≤ M := le_sup_right
  have hχ' := hχ
  obtain ⟨V, _, _, _, ρ, -, hρχ⟩ := hχ'
  have h5val : ∀ g, orderOf g = 5 → χ g = 0 := fun g hg => v58 g (Or.inl hg)
  have hsubord : ∀ (A : Subgroup G) (m : ℕ), Nat.card A = m →
      (∀ d ∈ ({1, 2, 3, 4, 5, 6, 8, 11} : Finset ℕ), d ∣ m → d ∈ ({1, 2, 4, 5} : Finset ℕ)) →
      ∀ a : A, orderOf a ∈ ({1, 2, 4, 5} : Finset ℕ) := by
    intro A m hm hD a
    have hdvd : orderOf a ∣ m := hm ▸ orderOf_dvd_natCard a
    have ha := horders (a : G)
    rw [Subgroup.orderOf_coe] at ha
    exact hD _ ha hdvd
  have hNord := hsubord N 20 hN20 (by decide)
  have hFord := hsubord F 4 hF4 (by decide)
  have hQord : ∀ a : Q, orderOf a ∈ ({1, 2, 4, 5} : Finset ℕ) := by
    intro a
    have h4 : a ^ 4 = 1 := by
      obtain ⟨q, rfl⟩ := eQ.surjective a
      rw [← map_pow, quaternion_pow_four, map_one]
    have hdvd := orderOf_dvd_of_pow_eq_one h4
    have hmem : orderOf a ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have key : ∀ d ∈ Nat.divisors 4, d ∈ ({1, 2, 4, 5} : Finset ℕ) := by decide
    exact key _ hmem
  have hno5 : ∀ (A : Subgroup G), (∀ a : A, orderOf a ∈ ({1, 2, 4, 5} : Finset ℕ)) →
      ¬ 5 ∣ Nat.card A → Nat.card {a : A // orderOf a = 5} = 0 := by
    intro A _ h5
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun a => h5 ?_⟩
    have := orderOf_dvd_natCard a.1
    rwa [a.2] at this
  have hsumN := sum_subgroup_eq hχ1 v24 h5val N hNord
  rw [hN20, card_orderOf_five_normalizer hP hN20] at hsumN
  have hsumF := sum_subgroup_eq hχ1 v24 h5val F hFord
  rw [hno5 F hFord (by rw [hF4]; norm_num), hF4] at hsumF
  have hsumQ := sum_subgroup_eq hχ1 v24 h5val Q hQord
  rw [hno5 Q hQord (by rw [hQ8]; norm_num), hQ8] at hsumQ
  rw [← hρχ] at hsumN hsumF hsumQ
  have hdimN := finrank_invariants_eq ρ N hsumN (d := 2) (by rw [hN20]; norm_num)
  have hdimF := finrank_invariants_eq ρ F hsumF (d := 4) (by rw [hF4]; norm_num)
  have hdimQ := finrank_invariants_eq ρ Q hsumQ (d := 3) (by rw [hQ8]; norm_num)
  have hFN' : F ≤ N := hFN
  have hMpos : 0 < Module.finrank ℂ (Representation.invariants (ρ.comp M.subtype)) := by
    have hle : Representation.invariants (ρ.comp N.subtype) ⊓
        Representation.invariants (ρ.comp Q.subtype) ≤
        Representation.invariants (ρ.comp M.subtype) := invariants_inf_le_sup ρ N Q
    have hsup : Representation.invariants (ρ.comp N.subtype) ⊔
        Representation.invariants (ρ.comp Q.subtype) ≤
        Representation.invariants (ρ.comp F.subtype) :=
      sup_le (invariants_le_of_le ρ hFN') (invariants_le_of_le ρ hFQ)
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (Representation.invariants (ρ.comp N.subtype))
      (Representation.invariants (ρ.comp Q.subtype))
    have h1 := Submodule.finrank_mono hsup
    have h2 := Submodule.finrank_mono hle
    rw [hdimN, hdimQ] at hdim
    rw [hdimF] at h1
    omega
  have hMne : M ≠ ⊤ := by
    intro hMtop
    have hle : Representation.invariants (ρ.comp M.subtype) ≤
        Representation.invariants (ρ.comp (⊤ : Subgroup G).subtype) :=
      invariants_le_of_le ρ (le_of_eq hMtop.symm)
    have hχne : ρ.character ≠ 1 := by
      rw [hρχ]
      intro h
      have := congrFun h 1
      rw [hχ1, Pi.one_apply] at this
      norm_num at this
    have h0 := finrank_invariants_top_eq_zero ρ (hρχ ▸ hχ) hχne
    have := Submodule.finrank_mono hle
    omega
  have h20M : 20 ∣ Nat.card M := hN20 ▸ Subgroup.card_dvd_of_le hNM
  have h8M : 8 ∣ Nat.card M := hQ8 ▸ Subgroup.card_dvd_of_le hQM
  have hMdvd : Nat.card M ∣ 7920 := hG ▸ Subgroup.card_subgroup_dvd_card M
  obtain ⟨n, hn⟩ := h20M
  have hn396 : n ∣ 396 := by
    have h : 20 * n ∣ 20 * 396 := by rw [← hn]; exact hMdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := M)
    omega
  have hn5 : ¬ 5 ∣ n := fun h => by
    have := Nat.dvd_trans h hn396
    norm_num at this
  have hfacM : (Nat.card M).factorization 5 = 1 := by
    have h20 : (20 : ℕ) = 5 ^ 1 * 4 := by norm_num
    rw [hn, Nat.factorization_mul (by norm_num) hn0, Finsupp.add_apply, h20,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), Nat.factorization_eq_zero_of_not_dvd hn5]
  have hPM : P ≤ M := Subgroup.le_normalizer.trans hNM
  have hP' : Nat.card (P.subgroupOf M) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hP]
  let P' : Sylow 5 M := Sylow.ofCard (P.subgroupOf M) (by rw [hP', hfacM, pow_one])
  have hNP' : Subgroup.normalizer ((P' : Subgroup M) : Set M) = N.subgroupOf M :=
    (Subgroup.subgroupOf_normalizer_eq hPM).symm
  have hsyl : Nat.card (Sylow 5 M) = n := by
    have h : Nat.card (Sylow 5 M) = (Subgroup.normalizer ((P' : Subgroup M) : Set M)).index :=
      Sylow.card_eq_index_normalizer P'
    have h2 := (Subgroup.normalizer ((P' : Subgroup M) : Set M)).card_mul_index
    rw [hNP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv, hN20, hn] at h2
    rw [h, hNP']
    omega
  have hmod : n % 5 = 1 := by
    have h := card_sylow_modEq_one 5 M
    rw [hsyl] at h
    exact h
  have heven : 2 ∣ n := by
    rw [hn] at h8M
    omega
  let data : FiniteComplexRepresentation.{0, 0} G :=
    { vector := G ⧸ M → ℂ, representation := permutationRepresentation G (G ⧸ M) }
  have hdatachar : data.character = fixedPointCount G (G ⧸ M) :=
    funext permutationRepresentation_character
  have horbits : Nat.card (MulAction.orbitRel.Quotient G (G ⧸ M)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨Quotient.mk _ (Classical.arbitrary _)⟩⟩
    obtain ⟨i, rfl⟩ := Quotient.exists_rep x
    obtain ⟨j, rfl⟩ := Quotient.exists_rep y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G j i
    exact Quotient.sound ⟨g, hg⟩
  have hone : characterPairing data.character 1 = 1 := by
    rw [hdatachar]
    have h := CFSG.blocksInnerProduct_fixedPointCount_one (W := G) (I := G ⧸ M)
    rw [horbits, Nat.cast_one] at h
    rw [← h]
    simp [characterPairing, CFSG.BlocksInnerProduct]
  have hgap' : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ∃ d : ℕ, 10 ≤ d ∧ ψ 1 = d := by
    intro ψ hψ h1
    by_cases hψχ : ψ = χ
    · exact ⟨10, le_rfl, by rw [hψχ, hχ1]; norm_num⟩
    by_cases hψ2 : ψ = ψ₂
    · exact ⟨10, le_rfl, by rw [hψ2, hψ₂1]; norm_num⟩
    by_cases hψ3 : ψ = ψ₃
    · exact ⟨10, le_rfl, by rw [hψ3, hψ₃1]; norm_num⟩
    obtain ⟨d, hd, hd1⟩ := hgap ψ hψ h1 hψχ hψ2 hψ3
    exact ⟨d, hd.le, hd1⟩
  obtain ⟨hdeg11, hdecomp⟩ := permutation_constituents_degree_ten data hgap' hone
  have hdimdata : Module.finrank ℂ data.vector = M.index := by
    change Module.finrank ℂ (G ⧸ M → ℂ) = M.index
    rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, Subgroup.index]
  have hdata1 : data.character 1 = M.index := by
    rw [FiniteComplexRepresentation.character, Representation.char_one, hdimdata]
  have hidx := M.card_mul_index
  rw [hG, hn] at hidx
  have hidx1 : M.index ≠ 1 := fun h => hMne (Subgroup.index_eq_one.mp h)
  have h11le : 11 ≤ M.index := by
    have h := hdeg11 (by rw [hdata1]; exact_mod_cast hidx1)
    rwa [hdimdata] at h
  have hidx11 : M.index = 11 := by
    rcases eq_of_dvd_396 hn396 hmod heven with h | h | h | h
    · exfalso
      exact false_of_card_eq_120 hP hCP hN20 hNM hQM eQ.symm (by rw [hn, h])
    · rw [h] at hidx
      omega
    · rw [h] at hidx
      omega
    · rw [h] at hidx
      omega
  obtain ⟨ψ, hψ, hψ1, hψdeg, hψdecomp⟩ := hdecomp (by rw [hdimdata, hidx11])
  have hψχ : ψ = χ := by
    by_contra hne
    have ht' : ψ t = -2 := by
      by_cases hψ2 : ψ = ψ₂
      · rw [hψ2, hψ₂t]
      by_cases hψ3 : ψ = ψ₃
      · rw [hψ3, hψ₃t]
      obtain ⟨d, hd, hd1⟩ := hgap ψ hψ hψ1 hne hψ2 hψ3
      rw [hψdeg] at hd1
      have : (d : ℂ) = 10 := hd1.symm
      have : d = 10 := by exact_mod_cast this
      omega
    have hft := congrFun hψdecomp t
    rw [hdatachar, Pi.add_apply, Pi.one_apply, ht', fixedPointCount] at hft
    have hre := congrArg Complex.re hft
    simp at hre
    have : (0 : ℝ) ≤ (Nat.card (MulAction.fixedBy (G ⧸ M) t) : ℝ) := Nat.cast_nonneg _
    linarith
  have hπ : fixedPointCount G (G ⧸ M) = 1 + χ := by
    rw [← hdatachar, hψdecomp, hψχ]
  have hX : Nat.card (G ⧸ M) = 11 := by rw [← Subgroup.index, hidx11]
  have hfixcount : ∀ g : G, (Nat.card (MulAction.fixedBy (G ⧸ M) g) : ℂ) = 1 + χ g := by
    intro g
    have h := congrFun hπ g
    rw [fixedPointCount, Pi.add_apply, Pi.one_apply] at h
    exact h
  have hfix3 : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy (G ⧸ M) g) ≤ 3 := by
    intro g hg1
    have h := hfixcount g
    have hval : ∃ k : ℕ, k ≤ 3 ∧ (1 + χ g : ℂ) = (k : ℂ) := by
      rcases hval2 g hg1 with hv | hv | hv | hv <;> rw [hv]
      · exact ⟨3, le_rfl, by norm_num⟩
      · exact ⟨2, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, by norm_num⟩
      · exact ⟨0, by norm_num, by norm_num⟩
    obtain ⟨k, hk3, hk⟩ := hval
    rw [hk] at h
    have := Nat.cast_injective h
    omega
  refine ⟨P, F, Q, hP, hFcyc, hF4, ⟨eQ.symm⟩, hNPF, hPF, hFQ, hidx11, fun g hg => ?_,
    sharply_four_transitive_of_fixed_le_three hX hG hfix3, hπ⟩
  have hall : MulAction.fixedBy (G ⧸ M) g = Set.univ := Set.eq_univ_of_forall hg
  have h := hfixcount g
  rw [hall, Nat.card_univ, hX] at h
  exact hfaith g (by linear_combination -h)

end CFSG.Semidihedral.GL2Recognition
