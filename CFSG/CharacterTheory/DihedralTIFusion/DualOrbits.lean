module

public import CFSG.CharacterTheory.DihedralTIFusion.DualOrbitsAction
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Characters

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

open Wreathed BrauerThirdMainTheorem.Helpers

variable {N : Type} [Group N] {K : Subgroup N} [K.Normal]

theorem conj_orbit_subset {k : N} (hk : k ∈ (K : Set N) \ {1}) :
    (Set.range fun n : N => n⁻¹ * k * n) ⊆ (K : Set N) \ {1} := by
  rintro x ⟨n, rfl⟩
  refine ⟨Subgroup.Normal.conj_mem' inferInstance _ hk.1 n, fun h => hk.2 ?_⟩
  have h' : n⁻¹ * k * n = 1 := h
  calc k = n * (n⁻¹ * k * n) * n⁻¹ := by group
    _ = 1 := by rw [h']; group

omit [K.Normal] in
theorem conj_orbit_eq_of_mem {k t : N} (ht : t ∈ Set.range fun n : N => n⁻¹ * k * n) :
    (Set.range fun n : N => n⁻¹ * t * n) = Set.range fun n : N => n⁻¹ * k * n := by
  obtain ⟨m, rfl⟩ := ht
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨m * n, by dsimp only; group⟩
  · rintro ⟨n, rfl⟩
    exact ⟨m⁻¹ * n, by dsimp only; group⟩

theorem character_orbit_subset {μ : K → ℂ} (hμ : μ ∈ BlocksIrr K \ {1}) :
    Set.range (conjugateNormalCharacter K μ) ⊆ BlocksIrr K \ {1} := by
  rintro x ⟨n, rfl⟩
  refine ⟨conjugateNormalCharacter_mem_blocksIrr K hμ.1 n, fun h => hμ.2 ?_⟩
  have h' : conjugateNormalCharacter K μ n = 1 := h
  have hback := conjugateNormalCharacter_mul K μ n⁻¹ n
  rw [inv_mul_cancel, conjugateNormalCharacter_one, h'] at hback
  rw [hback]
  rfl

theorem character_orbit_eq_of_mem {μ ν : K → ℂ}
    (hν : ν ∈ Set.range (conjugateNormalCharacter K μ)) :
    Set.range (conjugateNormalCharacter K ν) = Set.range (conjugateNormalCharacter K μ) := by
  obtain ⟨m, rfl⟩ := hν
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n * m, conjugateNormalCharacter_mul K μ n m⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n * m⁻¹, by rw [← conjugateNormalCharacter_mul, inv_mul_cancel_right]⟩

variable [Fintype N]

theorem natCard_conj_orbits_mul (hab : IsMulCommutative K)
    (hfree : ∀ n : N, n ∉ K → K ⊓ Subgroup.centralizer ({n} : Set N) = ⊥) :
    Nat.card {O : Set N | ∃ k ∈ (K : Set N) \ {1}, O = Set.range fun n : N => n⁻¹ * k * n} *
      K.index = Nat.card K - 1 := by
  have hS : Nat.card ↥((K : Set N) \ {1}) = Nat.card K - 1 := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (one_mem K),
      ← Nat.card_coe_set_eq]
    rfl
  rw [← hS]
  exact natCard_orbits_mul _ _ (fun k hk => conj_orbit_subset hk)
    (fun k _ => ⟨1, by group⟩) (fun k _ t ht => conj_orbit_eq_of_mem ht)
    (fun k hk => natCard_range_conj hab hfree hk.1 hk.2)

theorem natCard_character_orbits_mul (hab : IsMulCommutative K)
    (hfree : ∀ n : N, n ∉ K → K ⊓ Subgroup.centralizer ({n} : Set N) = ⊥) :
    Nat.card {O : Set (K → ℂ) | ∃ μ ∈ BlocksIrr K \ {1},
      O = Set.range (conjugateNormalCharacter K μ)} * K.index = Nat.card K - 1 := by
  have : IsMulCommutative K := hab
  have : Finite ↥(BlocksIrr K \ {1}) :=
    ((BlockSectionOrthogonality.Helpers.irreducibles_finite K).sdiff).to_subtype
  have hS : Nat.card ↥(BlocksIrr K \ {1}) = Nat.card K - 1 := by
    rw [Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem (a := (1 : K → ℂ)) (trivial_mem_irr K),
      ← Nat.card_coe_set_eq, natCard_blocksIrr_of_isMulCommutative]
  rw [← hS]
  exact natCard_orbits_mul _ _ (fun μ hμ => character_orbit_subset hμ)
    (fun μ _ => ⟨1, conjugateNormalCharacter_one K μ⟩)
    (fun μ _ ν hν => character_orbit_eq_of_mem hν)
    (fun μ hμ => natCard_range_conjugateNormalCharacter hab hfree hμ.1 hμ.2)

theorem abelian_normal_subgroup_dual_orbits (hK : K ≠ ⊥) (hab : IsMulCommutative K)
    (hfree : ∀ n : N, n ∉ K → K ⊓ Subgroup.centralizer ({n} : Set N) = ⊥) :
    (∀ k ∈ (K : Set N) \ {1}, ∀ n : N, n⁻¹ * k * n = k ↔ n ∈ K) ∧
      (∀ μ ∈ BlocksIrr K \ {1}, ∀ n : N, conjugateNormalCharacter K μ n = μ ↔ n ∈ K) ∧
      (∀ μ ∈ BlocksIrr K, μ 1 = 1 ∧ ∀ x y : K, μ (x * y) = μ x * μ y) ∧
      Nat.card (BlocksIrr K) = Nat.card K ∧
      (∀ k ∈ (K : Set N) \ {1}, Nat.card (Set.range fun n : N => n⁻¹ * k * n) = K.index) ∧
      (∀ μ ∈ BlocksIrr K \ {1},
        Nat.card (Set.range (conjugateNormalCharacter K μ)) = K.index) ∧
      Nat.card {O : Set N | ∃ k ∈ (K : Set N) \ {1},
        O = Set.range fun n : N => n⁻¹ * k * n} = (Nat.card K - 1) / K.index ∧
      Nat.card {O : Set (K → ℂ) | ∃ μ ∈ BlocksIrr K \ {1},
        O = Set.range (conjugateNormalCharacter K μ)} = (Nat.card K - 1) / K.index ∧
      0 < (Nat.card K - 1) / K.index ∧
      ((Nat.card K - 1) / K.index = 1 ↔
        ∀ k ∈ (K : Set N) \ {1}, ∀ k' ∈ (K : Set N) \ {1}, ∃ n : N, n⁻¹ * k * n = k') := by
  have : IsMulCommutative K := hab
  have he : 0 < K.index := Nat.pos_of_ne_zero K.index_ne_zero_of_finite
  have hK1 : 1 < Nat.card K := (Subgroup.one_lt_card_iff_ne_bot K).mpr hK
  have hconj := natCard_conj_orbits_mul hab hfree
  have hchar := natCard_character_orbits_mul hab hfree
  have hdiv : ∀ r : ℕ, r * K.index = Nat.card K - 1 → (Nat.card K - 1) / K.index = r :=
    fun r hr => Nat.div_eq_of_eq_mul_left he hr.symm
  set r := Nat.card {O : Set N | ∃ k ∈ (K : Set N) \ {1},
    O = Set.range fun n : N => n⁻¹ * k * n} with hr
  refine ⟨fun k hk n => conj_eq_self_iff_mem hab hfree hk.1 hk.2 n,
    fun μ hμ n => conjugateNormalCharacter_eq_self_iff hab hfree hμ.1 hμ.2 n,
    fun μ hμ => blocksIrr_linear hμ, natCard_blocksIrr_of_isMulCommutative K,
    fun k hk => natCard_range_conj hab hfree hk.1 hk.2,
    fun μ hμ => natCard_range_conjugateNormalCharacter hab hfree hμ.1 hμ.2,
    (hdiv _ hconj).symm, (hdiv _ hchar).symm, ?_, ?_⟩
  · rw [hdiv _ hconj]
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hconj
    omega
  · rw [hdiv _ hconj]
    obtain ⟨k₀, hk₀, hk₀1⟩ := (Subgroup.bot_or_exists_ne_one K).resolve_left hK
    have hk₀S : k₀ ∈ (K : Set N) \ {1} := ⟨hk₀, hk₀1⟩
    constructor
    · intro h1 k hk k' hk'
      have hsub : Subsingleton {O : Set N | ∃ k ∈ (K : Set N) \ {1},
          O = Set.range fun n : N => n⁻¹ * k * n} :=
        (Nat.card_eq_one_iff_unique.mp h1).1
      have heq : (Set.range fun n : N => n⁻¹ * k * n) = Set.range fun n : N => n⁻¹ * k' * n :=
        congrArg Subtype.val (Subsingleton.elim (α := {O : Set N | ∃ k ∈ (K : Set N) \ {1},
          O = Set.range fun n : N => n⁻¹ * k * n}) ⟨_, k, hk, rfl⟩ ⟨_, k', hk', rfl⟩)
      have hmem : k' ∈ Set.range fun n : N => n⁻¹ * k' * n := ⟨1, by group⟩
      rw [← heq] at hmem
      exact hmem
    · intro hall
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun O O' => ?_⟩, ⟨⟨_, k₀, hk₀S, rfl⟩⟩⟩
      obtain ⟨O, k, hk, rfl⟩ := O
      obtain ⟨O', k', hk', rfl⟩ := O'
      exact Subtype.ext (conj_orbit_eq_of_mem (hall k' hk' k hk))

end CFSG.DihedralTIFusion
