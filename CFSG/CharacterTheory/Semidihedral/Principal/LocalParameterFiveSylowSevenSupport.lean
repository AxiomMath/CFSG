module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.Principal.QuaternionCosetSixteenBound

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

namespace LocalParameterFiveSylowSeven

section Traces

variable {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]

theorem mapsTo_fixed_of_mem_normalizer (ρ : Representation ℂ G W) (N : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    ∀ v ∈ (⨅ n : N, Module.End.eigenspace (ρ n) 1),
      ρ g v ∈ (⨅ n : N, Module.End.eigenspace (ρ n) 1) := by
  intro v hv
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, one_smul] at hv ⊢
  intro n
  have hn' : g⁻¹ * n * g ∈ N := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) n).mp n.2
    simpa using h
  calc ρ n (ρ g v) = ρ g (ρ (g⁻¹ * n * g) v) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
    _ = ρ g v := by rw [hv ⟨_, hn'⟩]

theorem fixed_eq_invariants (ρ : Representation ℂ G W) (N : Subgroup G) :
    (⨅ n : N, Module.End.eigenspace (ρ n) 1) =
      Representation.invariants (ρ.comp N.subtype : Representation ℂ N W) := by
  ext v
  rw [Representation.mem_invariants]
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, one_smul]
  rfl

theorem trace_restrict_fixed_of_mem_normalizer [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) (N : Subgroup G) [Fintype N] {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    LinearMap.trace ℂ ↥(⨅ n : N, Module.End.eigenspace (ρ n) 1)
        ((ρ g).restrict (mapsTo_fixed_of_mem_normalizer ρ N hg)) =
      (Nat.card N : ℂ)⁻¹ * ∑ n : N, ρ.character (g * n) := by
  let : Invertible (Fintype.card N : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  have hproj : LinearMap.IsProj (⨅ n : N, Module.End.eigenspace (ρ n) 1)
      (Representation.averageMap (ρ.comp N.subtype : Representation ℂ N W)) := by
    rw [fixed_eq_invariants]
    exact Representation.isProj_averageMap _
  rw [QuaternionSixteen.trace_restrict_eq_trace_comp _ (ρ g) _ _ hproj]
  simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
    Representation.asAlgebraHom_of, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype]
  rw [LinearMap.comp_smul, ← Module.End.mul_eq_comp, Finset.mul_sum, map_smul, map_sum,
    smul_eq_mul, invOf_eq_inv, Fintype.card_eq_nat_card]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Representation.character, map_mul ρ]

theorem finrank_add_trace_of_mul_self_eq_one {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (T : Module.End ℂ E) (hT : T * T = 1) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ E ∧
      (Module.finrank ℂ E : ℂ) + LinearMap.trace ℂ E T = 2 * k := by
  set e : Module.End ℂ E := (2 : ℂ)⁻¹ • (1 + T) with hedef
  have he : IsIdempotentElem e := by
    change e * e = e
    have h2 : (1 + T) * (1 + T) = (2 : ℂ) • (1 + T) := by
      rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hT, two_smul]
      abel
    rw [hedef, smul_mul_smul_comm, h2, smul_smul]
    norm_num
  have hproj := LinearMap.IsIdempotentElem.isProj_range e he
  have htr := hproj.trace
  refine ⟨Module.finrank ℂ (LinearMap.range e), Submodule.finrank_le _, ?_⟩
  rw [← htr, hedef, map_smul, map_add, LinearMap.trace_one, smul_eq_mul]
  field_simp

end Traces

section Linear

theorem sum_inv_linear_character {P : Type*} [Group P] [Fintype P] (lam : P →* ℂˣ) :
    ∑ u : P, ((lam u : ℂ))⁻¹ = if lam = 1 then (Nat.card P : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp only [MonoidHom.one_apply, Units.val_one, inv_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
  · have h' : (Units.coeHom ℂ).comp lam⁻¹ ≠ 1 := by
      intro h1
      apply h
      ext u
      have := congrArg (fun f => f u⁻¹) h1
      simpa using this
    have hsum := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp lam⁻¹) h'
    rw [← hsum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp

end Linear

theorem trace_restrict_fixed_of_constant {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) (P : Subgroup G) [Fintype P] {y : G}
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (c : ℂ)
    (hval : ∀ u ∈ P, u ≠ 1 → ρ.character (y * u) = c) :
    LinearMap.trace ℂ ↥(⨅ u : P, Module.End.eigenspace (ρ u) 1)
        ((ρ y).restrict (mapsTo_fixed_of_mem_normalizer ρ P hy)) =
      (Nat.card P : ℂ)⁻¹ * (ρ.character y + ((Nat.card P : ℂ) - 1) * c) := by
  rw [trace_restrict_fixed_of_mem_normalizer ρ P hy]
  congr 1
  have hsplit : ∀ u : P, ρ.character (y * u) =
      (if u = 1 then ρ.character y - c else 0) + c := by
    intro u
    by_cases hu : u = 1
    · subst hu
      simp
    · rw [hval u u.2 (fun h => hu (Subtype.ext h)), ite_eq_right hu, zero_add]
  rw [Finset.sum_congr rfl (fun u _ => hsplit u), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

theorem trace_restrict_isotypic_of_singular {G W : Type*} [Group G] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) (P : Subgroup G) [Fintype P]
    (lam : P →* ℂˣ) {y : G} (hy : ∀ u ∈ P, y * u = u * y)
    (hval : ∀ u ∈ P, u ≠ 1 → ρ.character (y * u) = -1) :
    LinearMap.trace ℂ ↥(⨅ u : P, Module.End.eigenspace (ρ u) (lam u : ℂ))
        ((ρ y).restrict (QuaternionSixteen.mapsTo_isotypic ρ P lam hy)) =
      (Nat.card P : ℂ)⁻¹ * (ρ.character y + 1 - if lam = 1 then (Nat.card P : ℂ) else 0) := by
  rw [QuaternionSixteen.trace_restrict_isotypic ρ P lam hy]
  congr 1
  have hsplit : ∀ u : P, ρ.character (y * u) * ((lam u : ℂ))⁻¹ =
      (if u = 1 then ρ.character y + 1 else 0) - ((lam u : ℂ))⁻¹ := by
    intro u
    by_cases hu : u = 1
    · subst hu
      simp
    · rw [hval u u.2 (fun h => hu (Subtype.ext h)), ite_eq_right hu]
      ring
  rw [Finset.sum_congr rfl (fun u _ => hsplit u), Finset.sum_sub_distrib,
    sum_inv_linear_character]
  simp

theorem eq_one_or_three_of_factorization_le {n : ℕ} (hn : n ≠ 0) (hodd : Odd n)
    (h : ∀ p : ℕ, p.Prime →
      n.factorization p ≤ 2 / (p - 1) + (2 / (p - 1)).factorial.factorization p) :
    n = 1 ∨ n = 3 := by
  have hzero : ∀ p : ℕ, p ≠ 3 → n.factorization p = 0 := by
    intro p hp3
    by_cases hp : p.Prime
    · by_cases hp2 : p = 2
      · subst hp2
        exact Nat.factorization_eq_zero_of_not_dvd (fun h2 => by
          obtain ⟨k, hk⟩ := hodd
          omega)
      · have hp5 : 5 ≤ p := by
          have := hp.two_le
          rcases Nat.lt_or_ge p 5 with hlt | hge
          · interval_cases p
            · exact absurd rfl hp2
            · exact absurd rfl hp3
            · exact absurd hp (by norm_num)
          · exact hge
        have h0 : 2 / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
        have := h p hp
        rw [h0, Nat.factorial_zero, Nat.factorization_one] at this
        simpa using this
    · exact (Nat.factorization_eq_zero_iff n p).mpr (Or.inl hp)
  have hsingle : n.factorization = Finsupp.single 3 (n.factorization 3) := by
    ext p
    by_cases hp : p = 3
    · subst hp
      simp
    · rw [hzero p hp, Finsupp.single_apply, ite_eq_right (Ne.symm hp)]
  have hn3 := Nat.eq_pow_of_factorization_eq_single hn hsingle
  have hle : n.factorization 3 ≤ 1 := by
    have h3 := h 3 Nat.prime_three
    have h1 : (2 / (3 - 1)).factorial.factorization 3 = 0 := by
      norm_num [Nat.factorial]
    rw [h1] at h3
    simpa using h3
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · left
    rw [hn3, h0, pow_zero]
  · right
    rw [hn3, h1, pow_one]

theorem relIndex_centralizer_normalizer_dvd_totient {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) [IsCyclic P] :
    (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) ∣
      (Nat.card P).totient := by
  have key := Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective
    P.normalizerMonoidHom)
  rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex,
    IsCyclic.card_mulAut] at key
  exact key

theorem not_normalizer_le_centralizer {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hPcard : Nat.card (P : Subgroup G) = p) :
    ¬ Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
  intro hNC
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hc := hcomp.card_mul_card
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.transferSylow P hNC).ker with h | h
  · rw [h, Subgroup.card_bot, one_mul, hPcard] at hc
    have : IsCyclic G := isCyclic_of_prime_card hc.symm
    obtain ⟨a, b, hab⟩ := hGnonab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [h, Subgroup.card_top, hPcard] at hc
    have hG0 : 0 < Nat.card G := Nat.card_pos
    have h2 := hp.out.two_le
    have : Nat.card G * 2 ≤ Nat.card G * p := Nat.mul_le_mul_left _ h2
    omega

end LocalParameterFiveSylowSeven

end CFSG.Semidihedral.Principal
