module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsLinear
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.SLB4A.Basic
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec4.Census
  CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift
  CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks

variable {Q : Type} [Group Q] [Finite Q]

theorem four_le_pRank_of_e8Datum {X : Type} [Group X] {a₁ a₂ a₃ n : X}
    (h : E8Datum a₁ a₂ a₃ n) (e : Q ⧸ center Q ≃* X) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 4 ≤ CFSG.pRank 2 Q := by
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have hkerQ := ker_quotientMap e
  exact h.four_le_pRank (e.surjective.comp (QuotientGroup.mk'_surjective _)) hkerQ.le
    (by rw [← MonoidHom.mem_ker, hkerQ]; exact hzZ) hz1 (by rw [← hz2, pow_orderOf_eq_one])

theorem four_le_pRank_of_alternating {m : ℕ} (hm : 8 ≤ m)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin m)) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 4 ≤ CFSG.pRank 2 Q :=
  four_le_pRank_of_e8Datum (alt8_e8Datum.map (altEmbed hm) (altEmbed_injective hm)) e hzZ hz2

theorem four_le_pRank_of_m22 (e : Q ⧸ center Q ≃* Blueprint.NativeSporadic.M22) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : 4 ≤ CFSG.pRank 2 Q :=
  four_le_pRank_of_e8Datum m22_e8Datum e hzZ hz2

theorem four_le_pRank_of_hs
    (e : Q ⧸ center Q ≃* Blueprint.NativeSporadic.HS) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 4 ≤ CFSG.pRank 2 Q := by
  obtain ⟨a₁, a₂, a₃, n, h⟩ := hs_e8Datum
  exact four_le_pRank_of_e8Datum h e hzZ hz2

theorem four_le_pRank_of_ru
    (e : Q ⧸ center Q ≃* Blueprint.NativeSporadic.Ru) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 4 ≤ CFSG.pRank 2 Q := by
  obtain ⟨a₁, a₂, a₃, n, h⟩ := ru_e8Datum
  exact four_le_pRank_of_e8Datum h e hzZ hz2

open CFSG.LocalAnalysis.ComponentInitial in
theorem pRank_le_one_of_double_cover_alternating_small {n : ℕ} (hn6 : 6 ≤ n) (hn7 : n ≤ 7)
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (hZ : Nat.card (center J) = 2)
    (e : J ⧸ center J ≃* alternatingGroup (Fin n)) : CFSG.pRank 2 J ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have : Group.IsPerfect J := hq.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set η : J →* alternatingGroup (Fin (m + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerη : η.ker = Subgroup.center J := ker_quotientMap e
  have hK : η.ker ≤ Subgroup.center J := hkerη.le
  have hK2 : Nat.card η.ker = 2 := by rw [hkerη, hZ]
  have hKp : IsPGroup 2 η.ker := IsPGroup.of_card (n := 1) (by rw [hK2, pow_one])
  have hlift : ∀ i : Fin m, ∃ x : J, η x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := LocalAnalysis.ComponentInitial.exists_lift_pow_three_eq_one hK hKp
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨x, hx.trans hy, hx3⟩
  choose x hxη hx3 using hlift
  set z := (x ⟨0, by omega⟩ * x ⟨1, by omega⟩) ^ 2 with hz
  have hz1 : z ≠ 1 := sq_lift_ne_one (by omega) η hη hK hK2 hxη hx3
  have hzK : z ∈ η.ker := by
    rw [MonoidHom.mem_ker, hz, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq]
    simp [Fin.ext_iff]
  have hzc : z ∈ Subgroup.center J := hK hzK
  have hk2 : ∀ k ∈ η.ker, k ^ 2 = 1 := fun k hk => by
    have := pow_card_eq_one' (G := η.ker) (x := ⟨k, hk⟩)
    rw [hK2] at this
    exact congrArg Subtype.val this
  set τ := altThreeCycle (n := m) ⟨0, by omega⟩ * altThreeCycle ⟨1, by omega⟩ with hτ
  have hτ2 : τ ^ 2 = 1 := altThreeCycle_mul_sq (by simp [Fin.ext_iff])
  have hτη : η (x ⟨0, by omega⟩ * x ⟨1, by omega⟩) = τ := by rw [map_mul, hxη, hxη]
  have hτ1 : τ ≠ 1 := fun h => hz1 (hk2 _ (by rw [MonoidHom.mem_ker, hτη, h]))
  have hinv : ∀ a : J, a ^ 2 = 1 → a ∈ η.ker := by
    intro a ha
    by_contra hη1
    rw [MonoidHom.mem_ker] at hη1
    have ha2 : η a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_sq_eq_one (by omega) hn7 hτ2 hτ1 ha2 hη1)
    obtain ⟨h, rfl⟩ := hη g
    set y := h * (x ⟨0, by omega⟩ * x ⟨1, by omega⟩) * h⁻¹ with hy
    have hk : y⁻¹ * a ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy, map_mul, map_mul, map_inv, hτη, hg,
        inv_mul_cancel]
    have hkc : Commute y (y⁻¹ * a) := (Subgroup.mem_center_iff.mp (hK hk) y)
    have hy2 : y ^ 2 = z := by
      rw [hy, conj_pow, ← hz, Subgroup.mem_center_iff.mp hzc h, mul_inv_cancel_right]
    apply hz1
    calc z = y ^ 2 := hy2.symm
      _ = y ^ 2 * (y⁻¹ * a) ^ 2 := by rw [hk2 _ hk, mul_one]
      _ = (y * (y⁻¹ * a)) ^ 2 := (hkc.mul_pow 2).symm
      _ = a ^ 2 := by rw [mul_inv_cancel_left]
      _ = 1 := ha
  refine csSup_le' ?_
  rintro r ⟨A, hA, hcard⟩
  have hAK : A ≤ η.ker := fun a ha => hinv a (elemPow_eq_one_of_isElementaryAbelian a ha)
  have h2 : 2 ^ r ≤ 2 ^ 1 := by
    rw [← hcard, pow_one, ← hK2]
    exact Subgroup.card_le_of_le hAK
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

theorem pRank_le_one_of_alternating_small (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    {m : ℕ} (hm6 : 6 ≤ m) (hm7 : m ≤ 7) (e : Q ⧸ center Q ≃* alternatingGroup (Fin m)) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : CFSG.pRank 2 Q ≤ 1 := by
  have : Group.IsPerfect Q := hQ.1
  have hkerQ := ker_quotientMap e
  have hle :=
    LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
    (by omega) _ (e.surjective.comp (QuotientGroup.mk'_surjective _)) hkerQ.le
    (by rw [hkerQ]; exact isPGroup_center_of_pPrimeCore_eq_bot hO)
  rw [hkerQ] at hle
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have hge : 2 ≤ Nat.card (center Q) := by
    have : Nontrivial (center Q) := ⟨⟨⟨z, hzZ⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  exact pRank_le_one_of_double_cover_alternating_small hm6 hm7 hQ (by omega) e

theorem pRank_le_one_of_alternating_five (hQ : IsQuasisimple Q)
    (hO : pPrimeCore 2 Q = ⊥) (e : Q ⧸ center Q ≃* alternatingGroup (Fin 5)) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : CFSG.pRank 2 Q ≤ 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e5⟩ := ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr (Nat.card_zmod 5))
  exact pRank_le_one_of_PSL_two hQ hO hzZ hz2 (K := ZMod 5) (by rw [ZMod.ringChar_zmod_n]; omega)
    (e.trans e5.symm)

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
