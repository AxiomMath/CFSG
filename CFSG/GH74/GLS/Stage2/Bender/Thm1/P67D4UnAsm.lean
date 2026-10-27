module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnTits
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnGroup
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldDef

public section

open scoped Pointwise

namespace CFSG.GH74.BNPair

open CFSG.GH74.GLS.SP

theorem not_isPrimePow_one_add_pow {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p % 3 = 2)
    (hm : 1 ≤ m) : ¬ IsPrimePow (1 + p ^ m) := by
  intro h
  obtain ⟨ℓ, j, hℓ, hj, hN⟩ := (isPrimePow_nat_iff _).1 h
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  have hpm_odd : p ^ m % 2 = 1 := by rw [Nat.pow_mod, hodd]; simp
  have hpm5 : 5 ≤ p ^ m := le_trans hp5 (Nat.le_self_pow (by omega) p)
  have hev : 2 ∣ ℓ ^ j := by rw [hN]; omega
  have hℓ2 : ℓ = 2 := by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hev)
    omega
  subst hℓ2
  rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
  ·
    have h1 : p ^ m % 4 = 1 := by
      have e : p ^ m = p ^ r * p ^ r := by rw [hr, pow_add]
      have : (p ^ r) % 2 = 1 := by rw [Nat.pow_mod, hodd]; simp
      obtain ⟨s, hs⟩ : ∃ s, p ^ r = 2 * s + 1 := ⟨p ^ r / 2, by omega⟩
      rw [e, hs]
      ring_nf
      omega
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have : j = 1 := by omega
      subst this
      omega
    · obtain ⟨c, hc⟩ := pow_dvd_pow 2 hj2
      have : 2 ^ j % 4 = 0 := by rw [hc]; simp [Nat.mul_mod_right]
      omega
  ·
    have h2 : p ^ m % 3 = 2 := by
      have e : p ^ m = (p ^ 2) ^ r * p := by rw [hr, pow_succ, pow_mul]
      have h4 : (p ^ 2) % 3 = 1 := by rw [Nat.pow_mod, hp3]
      rw [e, Nat.mul_mod, Nat.pow_mod, h4, hp3]
      simp
    have h3 : 3 ∣ 2 ^ j := by rw [hN]; omega
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem index_eq_one_add_card_of_cells {G : Type*} [Group G] [Finite G] (B U : Subgroup G)
    (hUB : U ≤ B) (c₀ : G) (hc₀ : c₀ ∉ B)
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u)
    (hinj : ∀ b ∈ B, ∀ b' ∈ B, ∀ u ∈ U, ∀ u' ∈ U, b * c₀ * u = b' * c₀ * u' →
      b = b' ∧ u = u') :
    B.index = 1 + Nat.card U := by
  let e : B ⊕ (B × U) → G :=
    Sum.elim (fun b => (b : G)) fun x => (x.1 : G) * c₀ * (x.2 : G)
  have hnot : ∀ (b b' : B) (u' : U), (b : G) ≠ (b' : G) * c₀ * (u' : G) := by
    intro b b' u' h
    apply hc₀
    have : c₀ = (b' : G)⁻¹ * b * (u' : G)⁻¹ := by
      rw [h]
      group
    rw [this]
    exact B.mul_mem (B.mul_mem (B.inv_mem b'.2) b.2) (B.inv_mem (hUB u'.2))
  have hbij : Function.Bijective e := by
    constructor
    · rintro (b | ⟨b, u⟩) (b' | ⟨b', u'⟩) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact (hnot b b' u' h).elim
      · exact (hnot b' b u h.symm).elim
      · obtain ⟨h1, h2⟩ := hinj b b.2 b' b'.2 u u.2 u' u'.2 h
        exact congrArg Sum.inr (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
    · intro g
      rcases hcell g with hg | ⟨b, hb, u, hu, rfl⟩
      · exact ⟨Sum.inl ⟨g, hg⟩, rfl⟩
      · exact ⟨Sum.inr (⟨b, hb⟩, ⟨u, hu⟩), rfl⟩
  have hcard : Nat.card G = Nat.card B + Nat.card B * Nat.card U := by
    rw [← Nat.card_eq_of_bijective e hbij, Nat.card_sum, Nat.card_prod]
  have hB : 0 < Nat.card B := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hB ?_
  rw [B.card_mul_index, hcard]
  ring

theorem exists_card_eq_pow_of_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (U : Subgroup G) (hU : IsPGroup p U) (hne : U ≠ ⊥) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card U = p ^ m := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hU
  refine ⟨m, Nat.one_le_iff_ne_zero.2 ?_, hm⟩
  rintro rfl
  exact hne (Subgroup.eq_bot_of_card_eq U (by simpa using hm))

namespace RankTwoSystem

section Normalizer

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem conj_mem_U_of_mem_torus {h : X} (hh : h ∈ D.B ⊓ D.N) {u : X} (hu : u ∈ D.U) :
    h * u * h⁻¹ ∈ D.U := by
  have hu' : u ∈ chainProd D.root (intList 1 (n : ℤ)) := by
    rw [← D.roots.carrier_eq]
    exact hu
  refine chainProd_conj_mem D.root D.U h _ (fun k hk y hy => ?_) u hu'
  obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
  exact D.root_le_U hk1 hk2 (D.roots.invariant k ⟨by omega, by omega⟩ h hh y hy)

theorem conj_mem_U_of_mem_B {b : X} (hb : b ∈ D.B) {u : X} (hu : u ∈ D.U) :
    b * u * b⁻¹ ∈ D.U := by
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h, hh, v, hv, rfl⟩ := Set.mem_mul.1 hb'
  have e : h * v * u * (h * v)⁻¹ = h * (v * u * v⁻¹) * h⁻¹ := by group
  rw [e]
  exact D.conj_mem_U_of_mem_torus hh (D.U.mul_mem (D.U.mul_mem hv hu) (D.U.inv_mem hv))

end Normalizer

theorem noAbel_foldFix_of_polarity {X : Type*} [Group X] [Finite X] (D : RankTwoSystem X 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p % 3 = 2) (hUp : IsPGroup p D.U)
    {θ : X ≃* X} (hθ : D.IsPolarity θ) {c₀ : X} (hc₀ : c₀ ∈ dc D.B D.N D.w₀)
    (hc₀f : θ c₀ = c₀) (hnt : ∃ u ∈ D.U, u ≠ 1 ∧ θ u = u)
    (hKC : ∀ k ∈ D.B, θ k = k → (∀ u ∈ D.U, θ u = u → k * u = u * k) → k ∈ D.U)
    (A : Subgroup ↥(foldFix θ)) [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hmemB : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.B :=
    fun g => Subgroup.mem_subgroupOf
  have hmemU : ∀ g : ↥(foldFix θ), g ∈ D.U.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.U :=
    fun g => Subgroup.mem_subgroupOf
  have hw₀ : D.w₀ ≠ 1 := fun h => by
    have := D.rank2.dih.altWord_inj (i := 3) (j := 0) le_rfl (by norm_num)
      (h.trans (altWord_zero D.w₁ D.w₂).symm)
    omega
  have hc₀B : c₀ ∉ D.B := fun h => hw₀ ((D.bw_eq hc₀).symm.trans (D.bw_eq (mem_dc_one.2 h)))
  let c : ↥(foldFix θ) := ⟨c₀, hc₀f⟩
  have hcB : c ∉ D.B.subgroupOf (foldFix θ) := fun h => hc₀B ((hmemB c).1 h)
  have hUB : D.U.subgroupOf (foldFix θ) ≤ D.B.subgroupOf (foldFix θ) := fun g hg =>
    (hmemB g).2 (D.U_le_B ((hmemU g).1 hg))
  have hcell : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ∨
      ∃ b ∈ D.B.subgroupOf (foldFix θ), ∃ u ∈ D.U.subgroupOf (foldFix θ), g = b * c * u := by
    intro g
    rcases hθ.fixed_mem_B_or_top (mem_foldFix.1 g.2) with hg | hg
    · exact Or.inl ((hmemB g).2 hg)
    · obtain ⟨b, hb, hbf, u, hu, huf, hgbu⟩ :=
        hθ.top_decomp hc₀ hg hc₀f (mem_foldFix.1 g.2)
      exact Or.inr ⟨⟨b, hbf⟩, (hmemB _).2 hb, ⟨u, huf⟩, (hmemU _).2 hu, Subtype.ext hgbu⟩
  have hinj : ∀ b ∈ D.B.subgroupOf (foldFix θ), ∀ b' ∈ D.B.subgroupOf (foldFix θ),
      ∀ u ∈ D.U.subgroupOf (foldFix θ), ∀ u' ∈ D.U.subgroupOf (foldFix θ),
      b * c * u = b' * c * u' → b = b' ∧ u = u' := by
    intro b hb b' hb' u hu u' hu' h
    obtain ⟨h1, h2⟩ := top_unique hc₀ ((hmemB b).1 hb) ((hmemB b').1 hb') ((hmemU u).1 hu)
      ((hmemU u').1 hu') (congrArg Subtype.val h)
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  have hindex := index_eq_one_add_card_of_cells (D.B.subgroupOf (foldFix θ))
    (D.U.subgroupOf (foldFix θ)) hUB c hcB hcell hinj
  have hUGp : IsPGroup p (D.U.subgroupOf (foldFix θ)) := by
    refine hUp.of_injective
      (((foldFix θ).subtype.comp (D.U.subgroupOf (foldFix θ)).subtype).codRestrict D.U
        fun g => (hmemU g.1).1 g.2) fun g g' h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hUGne : D.U.subgroupOf (foldFix θ) ≠ ⊥ := by
    obtain ⟨u, hu, hu1, huf⟩ := hnt
    intro h
    have hmem : (⟨u, huf⟩ : ↥(foldFix θ)) ∈ D.U.subgroupOf (foldFix θ) := (hmemU _).2 hu
    rw [h, Subgroup.mem_bot] at hmem
    exact hu1 (congrArg Subtype.val hmem)
  obtain ⟨m, hm1, hm⟩ := exists_card_eq_pow_of_ne_bot _ hUGp hUGne
  have hΩ : ¬ IsPrimePow (D.B.subgroupOf (foldFix θ)).index := by
    rw [hindex, hm]
    exact not_isPrimePow_one_add_pow hp hp2 hp3 hm1
  have hUnorm : ∀ b ∈ D.B.subgroupOf (foldFix θ), ∀ u ∈ D.U.subgroupOf (foldFix θ),
      b * u * b⁻¹ ∈ D.U.subgroupOf (foldFix θ) := fun b hb u hu =>
    (hmemU _).2 (D.conj_mem_U_of_mem_B ((hmemB b).1 hb) ((hmemU u).1 hu))
  have hmeet : ∀ u ∈ D.U.subgroupOf (foldFix θ), c * u * c⁻¹ ∈ D.B.subgroupOf (foldFix θ) →
      u = 1 := fun u hu h => Subtype.ext (U_meet_top hc₀ ((hmemU u).1 hu) ((hmemB _).1 h))
  have hKC' : ∀ k ∈ D.B.subgroupOf (foldFix θ),
      (∀ u ∈ D.U.subgroupOf (foldFix θ), k * u = u * k) → k ∈ D.U.subgroupOf (foldFix θ) := by
    intro k hk hcomm
    refine (hmemU k).2 (hKC k ((hmemB k).1 hk) (mem_foldFix.1 k.2) fun u hu huf => ?_)
    exact congrArg Subtype.val (hcomm ⟨u, huf⟩ ((hmemU _).2 hu))
  exact noAbel_of_two_cells (D.B.subgroupOf (foldFix θ)) (D.U.subgroupOf (foldFix θ)) hUB hUnorm
    c hcB hcell hmeet hΩ hKC' A hA

end RankTwoSystem

end CFSG.GH74.BNPair
