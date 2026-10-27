module

public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.RankThree.PerfectCover
open scoped commutatorElement

theorem isPerfect_of_isSimpleGroup_of_card_not_prime {G : Type*} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hc : ¬ (Nat.card G).Prime) : Group.IsPerfect G := by
  refine Group.isPerfect_def.2 ?_
  rcases hs.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
      have h1 : ⁅a, b⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
    exact hc (IsSimpleGroup.prime_card (α := G))
  · exact h

theorem isPerfect_commutator_of_sup_center_eq_top {X : Type*} [Group X]
    (hsup : commutator X ⊔ center X = ⊤) : Group.IsPerfect ↥(commutator X) := by
  rw [Subgroup.isPerfect_iff]
  have hA : ⁅(⊤ : Subgroup X), commutator X⁆ = ⁅commutator X, commutator X⁆ := by
    conv_lhs => rw [← hsup]
    rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq]
  have hB : ⁅commutator X ⊔ center X, (⊤ : Subgroup X)⁆ = commutator X := by
    rw [hsup]
    exact (commutator_def X).symm
  rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq] at hB
  calc ⁅commutator X, commutator X⁆ = ⁅(⊤ : Subgroup X), commutator X⁆ := hA.symm
    _ = ⁅commutator X, (⊤ : Subgroup X)⁆ := Subgroup.commutator_comm _ _
    _ = commutator X := hB

theorem commutator_cover {Q M : Type} [Group Q] [Finite Q] [Group M] (ρ : Q →* M)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center Q) (hM : Group.IsPerfect M)
    (hmult : Nat.card (hopfMultiplier M) = 1) :
    commutator Q ⊔ ρ.ker = ⊤ ∧ commutator Q ⊓ ρ.ker = ⊥ ∧
      Nat.card ↥(commutator Q) = Nat.card M := by
  have hsup : commutator Q ⊔ ρ.ker = ⊤ := by
    have h1 : (commutator Q).map ρ = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hρ,
        ← commutator_def]
      exact hM.commutator_eq_top
    have h2 := Subgroup.comap_map_eq ρ (commutator Q)
    rw [h1, Subgroup.comap_top] at h2
    exact h2.symm
  have hsup' : commutator Q ⊔ center Q = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← hsup]
    exact sup_le_sup_left hker _
  have hJ := isPerfect_commutator_of_sup_center_eq_top hsup'
  let q : ↥(commutator Q) →* M := ρ.comp (commutator Q).subtype
  have hqs : Function.Surjective q := by
    intro m
    obtain ⟨x, rfl⟩ := hρ m
    have hx : x ∈ commutator Q ⊔ ρ.ker := by
      rw [hsup]
      exact mem_top x
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_normal_right.1 hx
    refine ⟨⟨y, hy⟩, ?_⟩
    show ρ y = ρ (y * z)
    rw [map_mul, MonoidHom.mem_ker.1 hz, mul_one]
  have hkerq : q.ker ≤ center ↥(commutator Q) := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hjc : (j : Q) ∈ center Q := hker (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hj))
    exact Subgroup.mem_center_iff.1 hjc k
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hJ q hqs hkerq
  rw [hmult] at hdvd
  have hqk : q.ker = ⊥ := by
    rw [← Subgroup.card_eq_one]
    exact Nat.dvd_one.1 hdvd
  refine ⟨hsup, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hy.1⟩ : ↥(commutator Q)) ∈ q.ker :=
      MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hy.2)
    rw [hqk, Subgroup.mem_bot] at hy'
    exact Subgroup.mem_bot.2 (by simpa using congrArg Subtype.val hy')
  · have hinj : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).1 hqk
    exact Nat.card_congr (Equiv.ofBijective q ⟨hinj, hqs⟩)

end CFSG.EvenSporadicStandard.Induction.Balance
