module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSource

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancingLocal

section Center

variable {H L : Type*} [Group H] [Group L]

theorem mem_center_of_map_mem_center [Group.IsPerfect H] (σ : H →* L) (hσ : σ.ker ≤ center H)
    {x : H} (hx : σ x ∈ center L) : x ∈ center H := by
  have hcomm : ∀ g : H, x * g * x⁻¹ * g⁻¹ ∈ center H := fun g => hσ (by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      (mem_center_iff.mp hx (σ g)).symm]
    group)
  let c : H →* center H :=
    { toFun := fun g => ⟨x * g * x⁻¹ * g⁻¹, hcomm g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by
        have hh := mem_center_iff.mp (hcomm h) g⁻¹
        change x * (g * h) * x⁻¹ * (g * h)⁻¹ =
          x * g * x⁻¹ * g⁻¹ * (x * h * x⁻¹ * h⁻¹)
        calc x * (g * h) * x⁻¹ * (g * h)⁻¹ =
              x * g * x⁻¹ * ((x * h * x⁻¹ * h⁻¹) * g⁻¹) := by group
          _ = x * g * x⁻¹ * (g⁻¹ * (x * h * x⁻¹ * h⁻¹)) := by rw [hh]
          _ = x * g * x⁻¹ * g⁻¹ * (x * h * x⁻¹ * h⁻¹) := by group) }
  have hc : ∀ g, c g = 1 := by
    intro g
    have hg : g ∈ commutator H := Group.IsPerfect.mem_commutator
    exact Abelianization.commutator_subset_ker c hg
  rw [mem_center_iff]
  intro g
  have h1 := congrArg Subtype.val (hc g)
  change x * g * x⁻¹ * g⁻¹ = 1 at h1
  have h2 : x * g = g * x := by
    calc x * g = x * g * x⁻¹ * g⁻¹ * (g * x) := by group
      _ = g * x := by rw [h1, one_mul]
  exact h2.symm

theorem injective_restrict_center [Group.IsPerfect H] (σ : H →* L) (hσ : σ.ker ≤ center H)
    {U : Subgroup H} (hU : U ⊓ center H = ⊥) :
    Function.Injective (((QuotientGroup.mk' (center L)).comp σ).comp U.subtype) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hc : σ u ∈ center L := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hu
    exact hu
  have hu' : (u : H) ∈ U ⊓ center H := ⟨u.2, mem_center_of_map_mem_center σ hσ hc⟩
  rw [hU, mem_bot] at hu'
  exact Subtype.ext hu'

end Center

section Sources

theorem not_prime_cube_dvd {l a : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) :
    ¬ l ^ 3 ∣ 2 ^ a * 3 ^ 2 * 5 * 7 := by
  intro h
  have hdvd : l ∣ 2 ^ a * 3 ^ 2 * 5 * 7 := (dvd_pow_self l (by norm_num)).trans h
  have h3 : l = 3 ∨ l = 5 ∨ l = 7 := by
    rcases (Nat.Prime.dvd_mul hl).mp hdvd with h1 | h7
    · rcases (Nat.Prime.dvd_mul hl).mp h1 with h1 | h5
      · rcases (Nat.Prime.dvd_mul hl).mp h1 with h2 | h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
            (hl.dvd_of_dvd_pow h2)) hl2
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).mp
            (hl.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_five).mp h5))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hl (by norm_num)).mp h7))
  have hodd : ¬ l ^ 3 ∣ 3 ^ 2 * 5 * 7 := by
    rcases h3 with rfl | rfl | rfl <;> norm_num
  apply hodd
  have hcop : Nat.Coprime (l ^ 3) (2 ^ a) :=
    Nat.Coprime.pow 3 a ((Nat.coprime_primes hl Nat.prime_two).mpr hl2)
  rw [show 2 ^ a * 3 ^ 2 * 5 * 7 = 2 ^ a * (3 ^ 2 * 5 * 7) by ring] at h
  exact hcop.dvd_of_dvd_mul_left h

theorem isEmpty_alternating_seven_of_dvd {X : Type} [Group X] {l : ℕ} (hl : l.Prime)
    (hl2 : l ≠ 2) (h : l ^ 3 ∣ Nat.card X) : IsEmpty (X ≃* alternatingGroup (Fin 7)) := by
  refine ⟨fun e => ?_⟩
  rw [Nat.card_congr e.toEquiv, card_alternating_seven,
    show (2520 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 * 7 by norm_num] at h
  exact not_prime_cube_dvd hl hl2 h

theorem not_psl_three_four_of_dvd {X : Type} [Group X] {l : ℕ} (hl : l.Prime)
    (hl2 : l ≠ 2) (h : l ^ 3 ∣ Nat.card X) : ¬ StatedClassicalModel X .PSL 3 2 2 := by
  rintro ⟨-, K, _, _, hK, ⟨e⟩⟩
  rw [Nat.card_congr e.toEquiv, card_psl_three_four K (by rw [hK]; norm_num),
    show (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 * 7 by norm_num] at h
  exact not_prime_cube_dvd hl hl2 h

theorem not_psl_two_odd_of_elementary {X : Type} [Group X] (E : Subgroup X)
    [IsElementaryAbelian 2 E] (hE : 4 < Nat.card E) {p f : ℕ} (hp2 : p ≠ 2) :
    ¬ StatedClassicalModel X .PSL 2 p f := by
  rintro ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩
  have hq : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  exact (not_odd_psl_two_of_elementary E hE hq).false e

theorem not_small_source_of_quotient {X : Type} [Group X] (E : Subgroup X)
    [IsElementaryAbelian 2 E] (hE : 4 < Nat.card E) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hdvd : l ^ 3 ∣ Nat.card X) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel X .PSL 2 p f) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2 :=
  ⟨fun _ _ hp2 => not_psl_two_odd_of_elementary E hE hp2,
    isEmpty_alternating_seven_of_dvd hl hl2 hdvd, not_psl_three_four_of_dvd hl hl2 hdvd⟩

end Sources

section Cover

variable {H : Type*} {L : Type} [Group H] [Group L]

theorem not_small_source_of_cover [Group.IsPerfect H] (σ : H →* L) (hσ : σ.ker ≤ center H)
    (E : Subgroup H) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E) (hEZ : E ⊓ center H = ⊥)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (U : Subgroup H) (hU : l ^ 3 ∣ Nat.card U)
    (hUZ : U ⊓ center H = ⊥) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := by
  have hEi := injective_restrict_center σ hσ hEZ
  have hUi := injective_restrict_center σ hσ hUZ
  set eE := MonoidHom.ofInjective hEi
  set eU := MonoidHom.ofInjective hUi
  have : IsElementaryAbelian 2
      (((QuotientGroup.mk' (center L)).comp σ).comp E.subtype).range :=
    isElementaryAbelian_of_mulEquiv eE
  have hE' : 4 < Nat.card (((QuotientGroup.mk' (center L)).comp σ).comp E.subtype).range := by
    rw [← Nat.card_congr eE.toEquiv]
    omega
  have hU' : l ^ 3 ∣ Nat.card (L ⧸ center L) := by
    refine hU.trans ?_
    rw [Nat.card_congr eU.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact not_small_source_of_quotient _ hE' hl hl2 hU'

end Cover

end CFSG.ComponentClassification.OddSelector
