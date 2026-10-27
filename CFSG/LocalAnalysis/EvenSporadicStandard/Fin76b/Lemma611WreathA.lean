module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.A6Normalizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.A6Dihedral

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem dihedral_four_facts (c : DihedralGroup 4) (hc1 : c ≠ 1) (hcc : ∀ x, c * x = x * c) :
    (∀ x : DihedralGroup 4, (∀ y, x * y = y * x) → x = 1 ∨ x = c) ∧
    (∀ x y : DihedralGroup 4, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = c) ∧
    ∃ y : DihedralGroup 4, y ≠ 1 ∧ y ≠ c := by
  revert c
  decide

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

variable {Γ : Type*} [Group Γ] {N : Subgroup Γ}

theorem card_dvd_eight_of_isPGroup (e : ↥N ≃* alternatingGroup (Fin 6)) {P : Subgroup Γ}
    (hPN : P ≤ N) (hP : IsPGroup 2 P) : Nat.card P ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinN : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have hfin : Finite P := Finite.of_injective _ (Subgroup.inclusion_injective hPN)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have h360 : Nat.card P ∣ 360 := by
    have h1 := card_dvd_of_le hPN
    rwa [Nat.card_congr e.toEquiv, card_alternatingGroup_six] at h1
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    rw [← hn] at h16
    have := h16.trans h360
    norm_num at this
  rw [hn]
  exact (pow_dvd_pow 2 hn3).trans (by norm_num)

theorem nonempty_dihedral_of_le (e : ↥N ≃* alternatingGroup (Fin 6)) {P : Subgroup Γ}
    (hPN : P ≤ N) (hP : Nat.card P = 8) : Nonempty (↥P ≃* DihedralGroup 4) := by
  have h1 : Nat.card (P.subgroupOf N) = 8 := by
    rw [← hP]
    exact Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv
  have h2 : Nat.card ((P.subgroupOf N).map e.toMonoidHom) = 8 := by
    rw [card_map_of_injective e.injective, h1]
  obtain ⟨f⟩ := CFSG.QuasithinUnique.DoubleA3.nonempty_dihedral_of_card_eight _ h2
  exact ⟨((subgroupOfEquivOfLe hPN).symm.trans
    ((P.subgroupOf N).equivMapOfInjective e.toMonoidHom e.injective)).trans f⟩

theorem centralizer_dihedral_facts (e : ↥N ≃* alternatingGroup (Fin 6)) {P : Subgroup Γ}
    (hPN : P ≤ N) (hP : Nat.card P = 8) {c : Γ} (hcP : c ∈ P) (hc1 : c ≠ 1)
    (hcc : ∀ p ∈ P, c * p = p * c) :
    (∀ x ∈ N, (∀ p ∈ P, x * p = p * x) → x = 1 ∨ x = c) ∧
    (∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = c) ∧
    ∃ y ∈ P, y ≠ 1 ∧ y ≠ c := by
  obtain ⟨g⟩ := nonempty_dihedral_of_le e hPN hP
  let c' : ↥P := ⟨c, hcP⟩
  have hgc1 : g c' ≠ 1 := by
    intro h
    exact hc1 (congrArg Subtype.val (g.injective (h.trans (map_one g).symm)))
  have hgcc : ∀ x, g c' * x = x * g c' := by
    intro x
    obtain ⟨y, rfl⟩ := g.surjective x
    rw [← map_mul, ← map_mul]
    exact congrArg g (Subtype.ext (hcc y y.2))
  obtain ⟨h1, h2, y₀, hy1, hyc⟩ := dihedral_four_facts (g c') hgc1 hgcc
  refine ⟨?_, ?_, ?_⟩
  · intro x hxN hx
    have hP' : Nat.card (P.subgroupOf N) = 8 := by
      rw [← hP]
      exact Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv
    have hmem : (⟨x, hxN⟩ : ↥N) ∈ P.subgroupOf N := by
      refine normalizer_le_of_a6 e hP' (isPGroup_mulAut_of_card_eight e hP') ?_
      refine centralizer_le_normalizer _ ?_
      rw [mem_centralizer_iff]
      intro q hq
      exact Subtype.ext (hx q (mem_subgroupOf.1 hq)).symm
    have hxP : x ∈ P := mem_subgroupOf.1 hmem
    have hcent : ∀ y, g ⟨x, hxP⟩ * y = y * g ⟨x, hxP⟩ := by
      intro y
      obtain ⟨y, rfl⟩ := g.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg g (Subtype.ext (hx y y.2))
    rcases h1 _ hcent with h | h
    · left
      exact congrArg Subtype.val (g.injective (h.trans (map_one g).symm))
    · right
      exact congrArg Subtype.val (g.injective h)
  · intro x hx y hy
    have := h2 (g ⟨x, hx⟩) (g ⟨y, hy⟩)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_one g] at this
    rcases this with h | h
    · left
      exact congrArg Subtype.val (g.injective h)
    · right
      exact congrArg Subtype.val (g.injective h)
  · refine ⟨(g.symm y₀ : Γ), (g.symm y₀).2, ?_, ?_⟩
    · intro h
      apply hy1
      have : g.symm y₀ = 1 := Subtype.ext h
      simpa using congrArg g this
    · intro h
      apply hyc
      have : g.symm y₀ = c' := Subtype.ext h
      simpa using congrArg g this

end CFSG.EvenSporadicStandard.Fin76b
