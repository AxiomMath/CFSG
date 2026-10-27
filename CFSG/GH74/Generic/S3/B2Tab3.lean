module

public import CFSG.GH74.Generic.S3.LxyShape2
public import CFSG.GH74.GLS.TwoThin.G.Section
import CFSG.GH74.Generic.S3.B2Tab1
import CFSG.GH74.Generic.S3.B2Tab2

public section

namespace CFSG.GH74.Generic.S3.B2Tab

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS (InB2 IsDoubleCoverOfAlt IsL34Quotient)
open scoped MatrixGroups

variable {H : Type} [Group H]

theorem involution_unique_of_equiv_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {P : Type} [Group P] (e : P ≃* SL(2, F)) {u v : P} (hu : u * u = 1) (hu1 : u ≠ 1)
    (hv : v * v = 1) (hv1 : v ≠ 1) : u = v := by
  have hu' : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu) hu1
  have hv' : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv) hv1
  rw [(CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e u).1 hu',
    (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e v).1 hv']

theorem false_of_central_pow_four {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {L Λ : Subgroup H} {a : H} (haΛ : a ∈ Λ) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hnc : ∃ l ∈ L, l * a ≠ a * l) (e : ↥Λ ≃* SL(2, F)) {m : ↥Λ} (hm1 : m ≠ 1) (hm4 : m ^ 4 = 1)
    (hmc : ∀ g ∈ L, g * (m : H) = (m : H) * g) : False := by
  obtain ⟨l, hlL, hl⟩ := hnc
  have ha'2 : (⟨a, haΛ⟩ : ↥Λ) * ⟨a, haΛ⟩ = 1 := Subtype.ext ha2
  have ha'1 : (⟨a, haΛ⟩ : ↥Λ) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  by_cases hm2 : m * m = 1
  · have h := involution_unique_of_equiv_sl2 hodd e ha'2 ha'1 hm2 hm1
    apply hl
    have h' : a = (m : H) := congrArg Subtype.val h
    rw [h']
    exact hmc l hlL
  · have hmm : (m * m) * (m * m) = 1 := by
      have : m ^ 4 = (m * m) * (m * m) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
      rw [← this]; exact hm4
    have h := involution_unique_of_equiv_sl2 hodd e ha'2 ha'1 hmm hm2
    apply hl
    have h' : a = (m : H) * (m : H) := congrArg Subtype.val h
    rw [h']
    calc l * ((m : H) * (m : H)) = (l * (m : H)) * (m : H) := by rw [mul_assoc]
      _ = ((m : H) * l) * (m : H) := by rw [hmc l hlL]
      _ = (m : H) * (l * (m : H)) := by rw [mul_assoc]
      _ = (m : H) * ((m : H) * l) := by rw [hmc l hlL]
      _ = ((m : H) * (m : H)) * l := by rw [mul_assoc]

theorem injective_to_quotient {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {L Λ : Subgroup H} (hΛL : Λ ≤ L) {a : H} (haΛ : a ∈ Λ) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hnc : ∃ l ∈ L, l * a ≠ a * l) (e : ↥Λ ≃* SL(2, F)) (hZ : ∀ z : ↥(center ↥L), z ^ 4 = 1) :
    Function.Injective ((QuotientGroup.mk' (center ↥L)).comp (Subgroup.inclusion hΛL)) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  by_contra hm1
  have hmZ : Subgroup.inclusion hΛL m ∈ center ↥L := by
    simpa [QuotientGroup.eq_one_iff] using hm
  have hm4 : m ^ 4 = 1 := by
    apply Subgroup.inclusion_injective hΛL
    rw [map_pow, map_one]
    have h4 := congrArg Subtype.val (hZ ⟨_, hmZ⟩)
    simpa using h4
  refine false_of_central_pow_four hodd haΛ ha2 ha1 hnc e hm1 hm4 ?_
  intro g hg
  have := Subgroup.mem_center_iff.1 hmZ ⟨g, hg⟩
  exact congrArg Subtype.val this


end CFSG.GH74.Generic.S3.B2Tab

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup CFSG.Assembly.LowTwoRank CFSG.GH74.Generic.S3.B2Tab
  CFSG.GH74.GLS.TwoThin
open CFSG.GH74.GLS (InB2)
open scoped MatrixGroups

theorem b2NoncentralTable_proved :
    B2NoncentralTable := by
  intro H _ _ L Λ a hB2 hΛL haΛ ha2 ha1 hac hnc ⟨F, _, _, hodd, h5, ⟨e⟩⟩ _
  rcases inB2_cases hB2 with ⟨F', _, _, hodd', ⟨eL⟩⟩ | ⟨n, hn7, hn11, hD⟩ | ⟨hL34, hexp⟩
  · obtain ⟨l, hlL, hl⟩ := hnc
    exact hl (central_of_involution_of_equiv_sl2 hodd'
      ((specialLinearGroupEquivStatedSL 2 F').trans eL.symm) (hΛL haΛ) ha2 ha1 l hlL)
  · obtain ⟨-, hcard, ⟨eA⟩⟩ := hD
    have hZ4 : ∀ z : ↥(center ↥L), z ^ 4 = 1 := by
      intro z
      have h2 : z ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
      calc z ^ 4 = (z ^ 2) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [h2, one_pow]
    have hinj := injective_to_quotient hodd hΛL haΛ ha2 ha1 hnc e hZ4
    exact sl2_no_perm_embedding_le_eleven hodd h5 hn11
      (((alternatingGroup (Fin n)).subtype.comp eA.toMonoidHom).comp
        (((QuotientGroup.mk' (center ↥L)).comp (Subgroup.inclusion hΛL)).comp e.symm.toMonoidHom))
      (Subtype.val_injective.comp (eA.injective.comp (hinj.comp e.symm.injective)))
  · obtain ⟨-, K, _, _, hcardK, ⟨eP⟩⟩ := stated_of_lieModel_PSL hL34
    have hZ4 : ∀ z : ↥(center ↥L), z ^ 4 = 1 := by
      intro z
      rw [← hexp]
      exact Monoid.pow_exponent_eq_one z
    have hinj := injective_to_quotient hodd hΛL haΛ ha2 ha1 hnc e hZ4
    have : Group.IsPerfect ↥Λ := CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 (by omega) e
    exact false_of_perfect_central_involution_psl34 (F := K) (by rw [hcardK]; norm_num)
      (eP.toMonoidHom.comp ((QuotientGroup.mk' (center ↥L)).comp (Subgroup.inclusion hΛL)))
      (eP.injective.comp hinj) (a := ⟨a, haΛ⟩) (Subtype.ext ha2)
      (fun h => ha1 (congrArg Subtype.val h))
      (fun g => Subtype.ext (hac g g.2))

end CFSG.GH74.Generic.S3
