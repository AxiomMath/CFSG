module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem coprime_card_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) {A Y : Subgroup G}
    (hY : IsPGroup p Y) (hA : ¬ p ∣ Nat.card A) : Nat.Coprime (Nat.card A) (Nat.card Y) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hY
  rw [hk]
  exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hA).symm

theorem isSolvable_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hY : IsPGroup p Y) : Group.IsSolvable Y := by
  have : Fact p.Prime := ⟨hp⟩
  have := hY.isNilpotent
  infer_instance

theorem le_inf_centralizer_sup_commutator [Finite G] {A Y : Subgroup G}
    (hAY : A ≤ normalizer (Y : Set G)) (hY : Group.IsSolvable Y)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card Y)) :
    Y ≤ (Y ⊓ centralizer (A : Set G)) ⊔ ⁅Y, A⁆ := by
  have : Subgroup.Normalizes A Y := ⟨hAY⟩
  have h := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime (G := Y)
    (A := A) hY hcop
  have h2 := congrArg (Subgroup.map Y.subtype) h
  rw [Subgroup.map_sup, CFSG.commutatorAction_subgroup_conj_map_eq_commutator Y A hAY,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  have hfix : (CFSG.fixedPointSubgroup A Y).map Y.subtype ≤ Y ⊓ centralizer (A : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u.2, ?_⟩
    show (u : G) ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro s hs
    have h3 : (⟨s, hs⟩ : A) • u = u := hu ⟨s, hs⟩
    have h4 := congrArg Subtype.val h3
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h4
    calc s * (u : G) = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [h4]
  intro x hx
  rw [← h2] at hx
  exact sup_le_sup hfix le_rfl hx

theorem inf_centralizer_sup_commutator_eq [Finite G] {A Y : Subgroup G}
    (hAY : A ≤ normalizer (Y : Set G)) (hY : Group.IsSolvable Y)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card Y)) :
    (Y ⊓ centralizer (A : Set G)) ⊔ ⁅Y, A⁆ = Y :=
  le_antisymm (sup_le inf_le_left (le_normalizer_iff_commutator_le_left.mp hAY))
    (le_inf_centralizer_sup_commutator hAY hY hcop)

theorem exists_mul_inf_centralizer_commutator [Finite G] {A Y : Subgroup G}
    (hAY : A ≤ normalizer (Y : Set G)) (hY : Group.IsSolvable Y)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card Y)) {y : G} (hy : y ∈ Y) :
    ∃ c ∈ Y ⊓ centralizer (A : Set G), ∃ d ∈ ⁅Y, A⁆, y = c * d := by
  have hle := le_inf_centralizer_sup_commutator hAY hY hcop hy
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    (inf_le_left.trans (normalizer_commutator_ge_left Y A)), Set.mem_mul] at hle
  obtain ⟨c, hc, d, hd, rfl⟩ := hle
  exact ⟨c, hc, d, hd, rfl⟩

end CFSG.LocalAnalysis.EvenBN.TwoF4
