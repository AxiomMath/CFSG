module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec6Statements
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6Frame

public section

namespace CFSG.GH74.QTGen4.Leaves.Hyp126Vac

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.S126 CFSG.Open CFSG.GH74
open scoped IsMulCommutative

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.GH74
open scoped IsMulCommutative

theorem card_coreMod_eight : Nat.card (G6.coreMod 8) = 128 := by
  have : Nat.card (G6.coreMod 8) =
      Nat.card {x : G6.PermMod 8 // ∑ i, Multiplicative.toAdd x i = 0} := rfl
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem sq_eq_one_permMod {n : ℕ} (x : G6.PermMod n) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [pow_two, toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem card_ker_le_two :
    Nat.card ↥((Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8).subgroupOf (G6.coreMod 8)) ≤ 2 := by
  have hord : orderOf (G6.allOnes 8) ≤ 2 := by
    apply orderOf_le_of_pow_eq_one (by norm_num)
    exact sq_eq_one_permMod _
  have hz : Nat.card (Subgroup.zpowers (G6.allOnes 8)) ≤ 2 := by
    rw [Nat.card_zpowers]; exact hord
  refine le_trans (Nat.card_le_card_of_injective
    (fun k => (⟨(k.1 : G6.PermMod 8), (Subgroup.mem_subgroupOf.1 k.2).1⟩ :
      Subgroup.zpowers (G6.allOnes 8))) ?_) hz
  intro a b h
  have h1 : ((a.1 : ↥(G6.coreMod 8)) : G6.PermMod 8) = (b.1 : ↥(G6.coreMod 8)) := by
    simpa using congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h1)

theorem not_gen4_onto_coreMod_quot {X : Type} [Group X] [Finite X] (hX : Gen4 X)
    (β : X →* ↥(G6.coreMod 8) ⧸
      (Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8).subgroupOf (G6.coreMod 8))
    (hβ : Function.Surjective β) : False := by
  have hQ := Gen4.of_surjective β hβ hX
  set K := (Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8).subgroupOf (G6.coreMod 8) with hK
  have hel : IsElemAbelian 2 (⊤ : Subgroup (↥(G6.coreMod 8) ⧸ K)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      show a * b = b * a
      induction a using QuotientGroup.induction_on with
      | H m =>
        induction b using QuotientGroup.induction_on with
        | H n =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm m n]
    · intro x _
      induction x using QuotientGroup.induction_on with
      | H m =>
        rw [← QuotientGroup.mk_pow]
        have : m ^ 2 = 1 := Subtype.ext (sq_eq_one_permMod _)
        rw [this]; rfl
  have hle := SectionalTwoRankLE.card_le_of_elementary hQ _ hel
  have h1 : Nat.card ↥(G6.coreMod 8) = Nat.card (↥(G6.coreMod 8) ⧸ K) * Nat.card K :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup K
  rw [card_coreMod_eight] at h1
  have h2 := card_ker_le_two
  have h3 : Nat.card ↥(⊤ : Subgroup (↥(G6.coreMod 8) ⧸ K)) = Nat.card (↥(G6.coreMod 8) ⧸ K) :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [h3] at hle
  have : Nat.card (↥(G6.coreMod 8) ⧸ K) * Nat.card K ≤ 2 ^ 4 * 2 :=
    Nat.mul_le_mul hle h2
  omega

theorem hyp126_gen4_false {G : Type} [Group G] [Finite G] (hG : Gen4 G) {T L V : Subgroup G}
    (h : Hyp126 G T L V) : False := by
  obtain ⟨hc, hmod⟩ := h.module
  obtain ⟨π, -, -, -, -, -, -, -, β, hβ, -, -⟩ := hmod
  exact not_gen4_onto_coreMod_quot
    (Gen4.subgroup _ (Gen4.subgroup V hG)) β hβ

theorem elim126_F4_holds : Elim126_F4 :=
  fun G _ _ _ _ _ h => hyp126_gen4_false (CFSG.GH74.QTGen4.Finite4.gen4 : Gen4 G) h

end CFSG.GH74.QTGen4.Leaves.Hyp126Vac

end
