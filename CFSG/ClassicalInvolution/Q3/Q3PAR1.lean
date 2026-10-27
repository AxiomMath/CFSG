module

public import CFSG.ClassicalInvolution.Q3.Chart
public import CFSG.ClassicalInvolution.Q3.Q3WChain
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport

public section

namespace CFSG.ClassicalInvolution.Q3.Q3PAR

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups

section Finite

theorem swap_back : ∀ A B : SL(2, F3),
    b1 (-1) * b0 A = b0 B * b1 (-1) → b0 (-1) * b1 B = b1 A * b0 (-1) := by
  decide +kernel

theorem exists_swap : ∀ A : SL(2, F3), ∃ B : SL(2, F3), b1 (-1) * b0 A = b0 B * b1 (-1) := by
  decide +kernel

end Finite

section Iota

variable {X : Type} [Group X] {n : ℕ}

theorem eq_iota_neg_one {F : CTFamily F3 X n} {i : Fin n} {K : Subgroup X} {z : X}
    (hr : (F.ι i).range = K) (hi : Function.Injective (F.ι i))
    (hz : Balance.IsCentralInvolution K z) : z = F.ι i (-1) := by
  obtain ⟨A, hA⟩ : z ∈ (F.ι i).range := hr ▸ hz.mem
  have hc : A ∈ Subgroup.center SL(2, F3) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply hi
    rw [map_mul, map_mul, hA]
    exact (hz.central _ (hr ▸ ⟨B, rfl⟩)).symm
  rcases (mem_center_sl2_iff A).mp hc with rfl | rfl
  · exact absurd (by rw [← hA, map_one]) hz.ne_one
  · exact hA.symm

end Iota

section Chain

variable {X : Type} [Group X]

theorem chain_product_centralizes_F3 {K N K₂ : Subgroup X} {z w : X}
    (hz : Balance.IsCentralInvolution K z) (hw : Balance.IsCentralInvolution K₂ w)
    (hKK₂ : ∀ x ∈ K, ∀ y ∈ K₂, x * y = y * x)
    (h1 : ∃ W, LinearBlockStandardPair F3 W K N) (h2 : ∃ W, LinearBlockStandardPair F3 W N K₂) :
    ∀ m ∈ N, (z * w) * m = m * (z * w) := by
  obtain ⟨F, hF⟩ := exists_ctFamily_of_pairs3 (n := 3) (by norm_num) (U := ![K, N, K₂])
    (fun i j hij x hx y hy => by
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd hij (by decide)
        | exact hKK₂ x hx y hy)
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd hij (by decide)
        | exact h1
        | exact h2)
  have hr0 : (F.ι 0).range = K := (hF 0).1
  have hr1 : (F.ι 1).range = N := (hF 1).1
  have hr2 : (F.ι 2).range = K₂ := (hF 2).1
  have hz' : z = F.θ 0 (b0 (-1)) :=
    (eq_iota_neg_one hr0 (hF 0).2 hz).trans (DFunLike.congr_fun (F.left 0 (by decide)) (-1)).symm
  have hw' : w = F.θ 1 (b1 (-1)) :=
    (eq_iota_neg_one hr2 (hF 2).2 hw).trans (DFunLike.congr_fun (F.right 1 (by decide)) (-1)).symm
  have hl : ∀ a, F.ι 1 a = F.θ 1 (b0 a) := fun a =>
    (DFunLike.congr_fun (F.left 1 (by decide)) a).symm
  have hr : ∀ a, F.ι 1 a = F.θ 0 (b1 a) := fun a =>
    (DFunLike.congr_fun (F.right 0 (by decide)) a).symm
  intro m hm
  obtain ⟨a, rfl⟩ : m ∈ (F.ι 1).range := hr1 ▸ hm
  obtain ⟨B, hB⟩ := exists_swap a
  have hwB : w * F.ι 1 a = F.ι 1 B * w := by
    rw [hl a, hl B, hw', ← map_mul, ← map_mul, hB]
  have hzB : z * F.ι 1 B = F.ι 1 a * z := by
    rw [hr a, hr B, hz', ← map_mul, ← map_mul, swap_back a B hB]
  calc z * w * F.ι 1 a = z * (w * F.ι 1 a) := mul_assoc _ _ _
    _ = z * (F.ι 1 B * w) := by rw [hwB]
    _ = (z * F.ι 1 B) * w := (mul_assoc _ _ _).symm
    _ = (F.ι 1 a * z) * w := by rw [hzB]
    _ = F.ι 1 a * (z * w) := mul_assoc _ _ _

theorem nonempty_ringEquiv_zmod_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Nonempty (F ≃+* F3) := by
  have := Fintype.ofFinite F
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card])⟩

theorem chain_product_centralizes3 {K N K₂ : Subgroup X} {z w : X}
    (hz : IsClassicalMember3 K z) (hw : IsClassicalMember3 K₂ w) (hKK₂ : Generic.Commutes K K₂)
    (h1 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K N)
    (h2 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W N K₂) :
    N ≤ Subgroup.centralizer ({z * w} : Set X) := by
  have hcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  obtain ⟨e⟩ := nonempty_ringEquiv_zmod_three hcard
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  exact chain_product_centralizes_F3 hz.isCentralInvolution hw.isCentralInvolution hKK₂
    (h1.imp fun W hW => LinearBlockStandardPair.of_ringEquiv e hW)
    (h2.imp fun W hW => LinearBlockStandardPair.of_ringEquiv e hW) m hm

end Chain

end CFSG.ClassicalInvolution.Q3.Q3PAR
