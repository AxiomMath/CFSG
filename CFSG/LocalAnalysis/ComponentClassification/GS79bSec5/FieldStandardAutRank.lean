module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.EvenBN.LinearThree.ElementaryAbelianCard
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.GS79bSec5

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem card_le_sq_of_mul_self_eq_one_mulAut_projectiveSL_three
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {A : Subgroup (MulAut (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F))}
    (hA : ∀ x ∈ A, x * x = 1) : Nat.card A ≤ Nat.card F ^ 2 := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hncard⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hncard]
  have hn : 2 ≤ (n : ℕ) := by
    have h4 : 2 ^ 2 ≤ 2 ^ (n : ℕ) := by rw [← hcard]; exact hF
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hA x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hA y hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (hA _ (mul_mem hx hy))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hx', hy']
  have hE : Open.IsElemAbelian 2 A :=
    LocalAnalysis.EvenBN.LinearThree.isElemAbelian_of_forall hcomm fun x hx => by
      rw [sq]; exact hA x hx
  by_cases hin : A ≤ (MulAut.conj : LinearFlag.projectiveSL 3 F →*
      MulAut (LinearFlag.projectiveSL 3 F)).range
  · have hinj := RankTwoL3Even.conj_injective_projectiveSL (F := F)
    have hcard' : Nat.card (A.comap (MulAut.conj : LinearFlag.projectiveSL 3 F →*
        MulAut (LinearFlag.projectiveSL 3 F))) = Nat.card A := by
      rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hin]
    rw [← hcard']
    exact LocalAnalysis.EvenBN.LinearThree.card_le_sq_of_mul_self fun a ha =>
      hinj (by rw [map_mul, ← sq, hE.2 _ ha, map_one])
  · calc Nat.card A ≤ 4 * Nat.card F :=
          LocalAnalysis.EvenBN.LinearThree.card_le_of_not_le_range (f := (n : ℕ))
            (by omega) hcard hE hin
      _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul_right _ hF
      _ = Nat.card F ^ 2 := (sq _).symm

theorem pRank_mulAut_le_two_mul_of_lieModel_psl_three {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (hX : Blueprint.LieModel X .PSL 3 2 m) : pRank 2 (MulAut X) ≤ 2 * m := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have hchar : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) fun f g h => MulEquiv.ext (congrFun h)
  have : Finite (MulAut (LinearFlag.projectiveSL 3 K)) :=
    Finite.of_injective (fun f : MulAut (LinearFlag.projectiveSL 3 K) =>
      (f : LinearFlag.projectiveSL 3 K → LinearFlag.projectiveSL 3 K))
      fun f g h => MulEquiv.ext (congrFun h)
  rw [SectionRank.pRank_eq_open_pRank_top,
    SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr e)]
  refine SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  rw [pow_mul', ← hK]
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact card_le_sq_of_mul_self_eq_one_mulAut_projectiveSL_three h4 fun x hx => by
    rw [← sq]; exact hE.2 x hx

end CFSG.ComponentClassification.GS79bSec5
