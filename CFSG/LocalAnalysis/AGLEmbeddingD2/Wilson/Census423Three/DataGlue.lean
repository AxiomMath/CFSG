module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.GoodGroup
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.LocalGen

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two

theorem alphaVanishes_of_data {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hZ : Subgroup.center X = ⊥) (hR : Rank2 X)
    (hQ : ∀ d : X, orderOf d = 3 →
      ∃ (S : Type) (_ : Group S), GoodGroup S ∧ Nonempty (↥(qRes d) ≃* S))
    (hS : ∀ D : Subgroup X, (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) → (∀ x ∈ D, x ^ 3 = 1) →
      Nat.card D = 9 → (⊤ : Subgroup X) ≤ Subgroup.closure
        {x : X | ∃ d ∈ D, d ≠ 1 ∧ x ∈ Subgroup.centralizer ({d} : Set X)})
    {D : Subgroup X} (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) : AlphaVanishes X D := by
  refine alphaVanishes_of_good hZ hR hDc hDexp hD9 (fun d hd hd1 => ?_) (hS D hDc hDexp hD9)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, _, hSg, ⟨e⟩⟩ := hQ d (orderOf_eq_prime (hDexp d hd) hd1)
  exact goodAt_of_goodGroup (hSg.of_mulEquiv e.symm)

theorem census423_of_equiv_alpha {X M : Type} [Group X] [Finite X] [Group M] [Finite M]
    (e : X ≃* M)
    (h : ∀ D : Subgroup M, (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → (∀ x ∈ D, x ^ 3 = 1) →
      Nat.card D = 9 → AlphaVanishes M D) : Census423 X := by
  refine census423_of_alphaVanishes fun D hD hD9 => ?_
  have hE : CFSG.Assembly.IsElemAbelian 3 D := hD.prop
  refine alphaVanishes_of_mulEquiv e ?_
  have hE' := isElemAbelian_map' e.toMonoidHom hE
  refine h _ (comm_of_isElemAbelian hE') hE'.2 ?_
  rw [Subgroup.card_map_of_injective e.injective, hD9]

theorem census423_of_data {X M : Type} [Group X] [Finite X] [Group M] [Finite M] [IsSimpleGroup M]
    (e : X ≃* M) (hZ : Subgroup.center M = ⊥) (hR : Rank2 M)
    (hQ : ∀ d : M, orderOf d = 3 →
      ∃ (S : Type) (_ : Group S), GoodGroup S ∧ Nonempty (↥(qRes d) ≃* S))
    (hS : ∀ D : Subgroup M, (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) → (∀ x ∈ D, x ^ 3 = 1) →
      Nat.card D = 9 → (⊤ : Subgroup M) ≤ Subgroup.closure
        {x : M | ∃ d ∈ D, d ≠ 1 ∧ x ∈ Subgroup.centralizer ({d} : Set M)}) :
    Census423 X :=
  census423_of_equiv_alpha e fun _ hDc hDexp hD9 => alphaVanishes_of_data hZ hR hQ hS hDc hDexp hD9

theorem rank2_of_pRank {X : Type} [Group X] [Finite X] (h : CFSG.pRank 3 X ≤ 2) : Rank2 X := by
  intro E hc hexp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := card_pow_three hexp
  have hEA : CFSG.IsElementaryAbelian 3 E :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro g
        exact Subtype.ext (by simpa using hexp g g.2) }
  have hkle : k ≤ CFSG.pRank 3 X := by
    refine le_csSup ⟨Nat.card X, ?_⟩ ⟨E, hEA, hk⟩
    rintro j ⟨F, -, hF⟩
    have h1 : 3 ^ j ≤ Nat.card X := hF ▸ Subgroup.card_le_card_group F
    have h2 : j < 3 ^ j := Nat.lt_pow_self (by norm_num)
    omega
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkle.trans h)
    _ = 9 := by norm_num

theorem rank2_of_mulEquiv {X M : Type} [Group X] [Group M] (e : X ≃* M) (h : Rank2 X) :
    Rank2 M := by
  intro E hc hexp
  have h1 := h (E.map e.symm.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hc a ha b hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, hexp a ha, map_one])
  rwa [Subgroup.card_map_of_injective e.symm.injective] at h1

theorem closure_centralizers_of_map {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (D : Subgroup G)
    (h : Subgroup.closure {k : H | ∃ x ∈ D.map φ.toMonoidHom, x ≠ 1 ∧ k * x = x * k} = ⊤) :
    (⊤ : Subgroup G) ≤ Subgroup.closure
      {x : G | ∃ d ∈ D, d ≠ 1 ∧ x ∈ Subgroup.centralizer ({d} : Set G)} := by
  have h1 := congrArg (Subgroup.comap φ.toMonoidHom) h
  rw [Subgroup.comap_top] at h1
  have hsub : Subgroup.closure {k : H | ∃ x ∈ D.map φ.toMonoidHom, x ≠ 1 ∧ k * x = x * k} ≤
      (Subgroup.closure {x : G | ∃ d ∈ D, d ≠ 1 ∧ x ∈ Subgroup.centralizer ({d} : Set G)}).map
        φ.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro k ⟨_, ⟨d, hd, rfl⟩, hd1, hk⟩
    refine ⟨φ.symm k, Subgroup.subset_closure ⟨d, hd, ?_, ?_⟩, by simp⟩
    · intro h1'
      apply hd1
      simp only [MulEquiv.coe_toMonoidHom]
      rw [h1', map_one]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hk
  intro g _
  have : φ g ∈ Subgroup.closure
      {k : H | ∃ x ∈ D.map φ.toMonoidHom, x ≠ 1 ∧ k * x = x * k} := by rw [h]; trivial
  obtain ⟨g', hg', hg'e⟩ := hsub this
  have : g' = g := φ.injective hg'e
  rwa [← this]

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
