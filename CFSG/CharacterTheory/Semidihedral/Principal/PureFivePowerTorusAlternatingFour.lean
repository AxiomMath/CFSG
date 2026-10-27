module

public import CFSG.CharacterTheory.Semidihedral.Principal.PureFivePowerTorusAlternatingFourSupport

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem perfect_trivial_core_pure_five_power_torus_has_alternating_four_centralizer_quotient
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (a : ℕ) (ha : 1 ≤ a) :
    let q : ℕ := p ^ f
    let e : ℤ := if q % 4 = 1 then 1 else -1
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    ((q : ℤ) + e) / 2 = 5 ^ a →
    IsCyclic W ∧ Nat.card W = 5 ^ a ∧ (CFSG.pPrimeCore 2 K).map K.subtype = W ∧
      Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
      Nat.card K = 12 * 5 ^ a ∧ Nat.card H = 24 * 5 ^ a ∧
      (∃ P : Sylow 5 G, (P : Subgroup G) = W) ∧
      ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 := by
  intro q e s₀ V D W H K hqa
  have := Fintype.ofFinite G
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, -, hWcyc, -, hWm, -, -, -, -, -, -, -, -, -, -, -, -, -, hR, -, -, ⟨hcases, -⟩, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hWcyc : IsCyclic W := hWcyc
  have hWm : (Nat.card W : ℤ) = ((q : ℤ) + e) / 2 := hWm
  have hR : (CFSG.pPrimeCore 2 K).map K.subtype = W := hR
  have hcases : (Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
        Nat.card K = 12 * Nat.card W ∧ Nat.card H = 24 * Nat.card W) ∨
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
        Nat.card K = 60 * Nat.card W ∧ Nat.card H = 120 * Nat.card W) := hcases
  have hW5 : Nat.card W = 5 ^ a := by
    have h : (Nat.card W : ℤ) = 5 ^ a := by rw [hWm, hqa]
    exact_mod_cast h
  have hnotA5 : ¬ Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 5)) :=
    PureFiveAlternatingFour.alternating_five_alternative_false n hn S fS t ht hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hN hY a ha hqa
  have hnotPSL : ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K)
      .PSL 2 5 1 := by
    intro hmod
    obtain ⟨-, F, hF, hFfin, hFcard, ⟨eK⟩⟩ := hmod
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inr (by rw [hFcard]; norm_num))
    exact hnotA5 ⟨eK.trans e5⟩
  obtain ⟨hA4, hK12, hH24⟩ := hcases.resolve_right fun h => hnotPSL h.1
  rw [hW5] at hK12 hH24
  refine ⟨hWcyc, hW5, hR, hA4, hK12, hH24, ?_, hnotPSL⟩
  have hGpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hdvd : 5 ^ a ∣ Nat.card G := hW5 ▸ Subgroup.card_subgroup_dvd_card W
  have hndvd : ¬ 5 ^ (a + 1) ∣ Nat.card G := by
    intro h
    have h' : 5 ^ (a + 1) ∣ Nat.card H := Sylow.prime_pow_dvd_card_normalizer h hW5
    rw [hH24, pow_succ'] at h'
    have h5 := Nat.dvd_of_mul_dvd_mul_right (by positivity : 0 < 5 ^ a) h'
    omega
  have hfact : (Nat.card G).factorization 5 = a := by
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hGpos).mp hdvd
    have h2 : ¬ a + 1 ≤ (Nat.card G).factorization 5 := fun h =>
      hndvd ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hGpos).mpr h)
    omega
  exact ⟨Sylow.ofCard W (by rw [hW5, hfact]), rfl⟩

end CFSG.Semidihedral.Principal
