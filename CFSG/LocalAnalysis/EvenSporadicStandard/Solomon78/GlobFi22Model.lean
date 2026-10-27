module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi22FinalK
public import CFSG.Monster.B.Fischer.Fi22Primitive

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Schreier CFSG.Monster.B.Fischer CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.FischerOddCore
open CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HypOne
open CFSG.EvenSporadicStandard.HypOne.Fi22

theorem fi22ExtRep_two_mem :
    fi22ExtRep 2 ∈ fi22P :=
  CTUC_Fi22_all_extension_involutions_covered.1 2 (by norm_num)

theorem fi22_centralizer_eq_subgroupOf :
    centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : fi22P)} : Set fi22P) =
      fi22OuterM.subgroupOf fi22P := by
  rw [show (⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : fi22P) = fi22OuterZP from
    Subtype.ext fi22ExtRep_two]
  exact fi22OuterM_subgroupOf_eq.symm

theorem fi22_centralizer_eq_stabilizer :
    centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : fi22P)} : Set fi22P) =
      MulAction.stabilizer fi22P (0 : Fin 3510) := by
  rw [show (⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : fi22P) = fi22OuterZP from
    Subtype.ext fi22ExtRep_two, ← fi22OuterM_subgroupOf_eq]
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, fi22OuterM_eq, Subgroup.mem_inf,
    MulAction.mem_stabilizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem isCoatom_fi22_centralizer :
    IsCoatom (centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : fi22P)} : Set fi22P)) := by
  rw [fi22_centralizer_eq_stabilizer]
  have := fi22P_primitive
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive fi22P (0 : Fin 3510)

theorem fi22_centralizer_twoAdic_lt :
    (Nat.card (centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : fi22P)} : Set fi22P))
      ).factorization 2 < (Nat.card fi22P).factorization 2 := by
  rw [fi22_centralizer_eq_subgroupOf,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22OuterM_le_P).toEquiv, card_fi22OuterM,
    factorization_card_fi22P_two,
    show (18393661440 : ℕ) = 2 ^ 16 * 280665 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem fi22_eq_inf_centralizer
    {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G} (hL : IsSporadic L .Fi22)
    (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcard : 18393661440 ≤ Nat.card K) : K = L ⊓ centralizer ({u} : Set G) := by
  have hKle : K ≤ L ⊓ centralizer ({u} : Set G) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hle : Nat.card K ≤ Nat.card ↥(L ⊓ centralizer ({u} : Set G)) :=
    Subgroup.card_le_of_le hKle
  have h3 : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 18393661440 := by
    rcases fi22_card_inf_centralizer hL hu hu2 with h | h | h <;> omega
  exact Subgroup.eq_of_le_of_card_ge hKle (by omega)

theorem exists_equiv_fi22
    {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G} (hL : IsSporadic L .Fi22)
    (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcard : 18393661440 ≤ Nat.card K) :
    ∃ Φ : ↥L ≃* ↥fi22P, Φ ⟨u, hu⟩ = ⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ ∧
      ∀ x : ↥L, x ∈ K.subgroupOf L ↔
        Φ x ∈ centralizer ({(⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ : fi22P)} : Set fi22P) := by
  have hKeq : K = L ⊓ centralizer ({u} : Set G) :=
    fi22_eq_inf_centralizer hL hu hu2 hKL hKu hcard
  have hcardC : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 18393661440 := by
    have := Subgroup.card_le_of_le (le_of_eq hKeq)
    rcases fi22_card_inf_centralizer hL hu hu2 with h | h | h <;> omega
  obtain ⟨e⟩ := hL
  set E : ↥L ≃* ↥fi22P := e.trans fi22PermEquiv with hE
  set u' : ↥L := ⟨u, hu⟩ with hu'
  have hy2 : orderOf ((E u' : fi22P) : Equiv.Perm (Fin 3510)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hu', Subgroup.orderOf_mk]
    exact hu2
  have h1 : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) =
      Nat.card ↥(centralizerIn fi22P ((E u' : fi22P) : Equiv.Perm (Fin 3510))) :=
    calc Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = Nat.card ↥(centralizerIn L (u' : G)) := rfl
      _ = Nat.card (centralizer ({u'} : Set L)) :=
        (Nat.card_congr (centralizerSubgroupEquiv L u').toEquiv).symm
      _ = Nat.card (centralizer ({E u'} : Set fi22P)) :=
        Nat.card_congr (centralizerEquiv E u').toEquiv
      _ = _ := Nat.card_congr (centralizerSubgroupEquiv fi22P (E u')).toEquiv
  rw [hcardC] at h1
  obtain ⟨r, hr, c, hc, hyc⟩ := cover_P _ (E u').2 hy2
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
  have hk3 : k < 3 := List.mem_range.1 hk
  have h2 : Nat.card ↥(centralizerIn fi22P ((E u' : fi22P) : Equiv.Perm (Fin 3510))) =
      Nat.card ↥(centralizerIn fi22P (fi22ExtRep k)) := by
    rw [hyc]
    exact Nat.card_congr (centralizerInConjEquiv fi22P hc (fi22ExtRep k)).toEquiv.symm
  rw [← h1, card_centralizerIn_P hk3] at h2
  have hk2 : k = 2 := by
    interval_cases k
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
    · rfl
  subst hk2
  set Φ : ↥L ≃* ↥fi22P := E.trans (MulAut.conj (⟨c, hc⟩ : fi22P)⁻¹) with hΦ
  have hΦu : Φ u' = ⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ := by
    apply Subtype.ext
    have h3 : (Φ u' : fi22P) = (⟨c, hc⟩ : fi22P)⁻¹ * E u' * (⟨c, hc⟩ : fi22P)⁻¹⁻¹ := rfl
    rw [h3]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyc]
    group
  refine ⟨Φ, hΦu, fun x => ?_⟩
  rw [Subgroup.mem_subgroupOf, hKeq, Subgroup.mem_inf, ← hΦu, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, hx⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hx
  · intro h
    refine ⟨x.2, ?_⟩
    have := Φ.injective (by rw [map_mul, map_mul]; exact h : Φ (x * u') = Φ (u' * x))
    exact congrArg Subtype.val this

end CFSG.EvenSporadicStandard.Solomon78
