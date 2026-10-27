module

import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem l28iv_comm_of_sq_comm {x y : G} {m : ℕ} (hy : y ^ (3 ^ m) = 1)
    (h : y ^ 2 * x * (y ^ 2)⁻¹ = x) : y * x * y⁻¹ = x := by
  have hodd : Odd (3 ^ m) := Odd.pow (by decide)
  obtain ⟨k, hk⟩ := hodd
  have hyk : y = (y ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = 3 ^ m + 1 by omega, pow_succ, hy, one_mul]
  have hc : Commute (y ^ 2) x := by
    rw [Commute, SemiconjBy]
    calc y ^ 2 * x = (y ^ 2 * x * (y ^ 2)⁻¹) * y ^ 2 := by group
      _ = x * y ^ 2 := by rw [h]
  have hc' : Commute y x := by
    rw [hyk]
    exact hc.pow_left (k + 1)
  rw [hc'.eq]
  group

theorem l28iv_le_centralizer {P : Subgroup G} (hP : IsPGroup 3 P) {x u : G} (hxP : x ∈ P)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxu : x ∉ zpowers u) (hu3 : u ^ 3 = 1)
    (hD : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ P ⊓ centralizer ({x} : Set G) →
      g * x * g⁻¹ ∈ zpowers x ∨ g * x * g⁻¹ ∈ zpowers u) :
    P ≤ centralizer ({x} : Set G) := by
  by_contra hnot
  set Q : Subgroup G := P ⊓ centralizer ({x} : Set G) with hQ
  have hlt : Q < P := inf_lt_left.mpr hnot
  have hgrow := CFSG.RankThreeCoreUniqueness.Helpers.pGroup_proper_subgroup_lt_internal_normalizer 3
    Nat.prime_three P Q hP hlt
  obtain ⟨y, hy, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  have hyP : y ∈ P := hy.1
  have hyN : y ∈ normalizer (Q : Set G) := hy.2
  have hxQ : x ∈ Q := ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨m, hm⟩ := hP ⟨y, hyP⟩
  have hym : y ^ (3 ^ m) = 1 := congrArg Subtype.val hm
  have hy2m : (y ^ 2) ^ (3 ^ m) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hym, one_pow]
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hle : ∀ w : G, w * x * w⁻¹ ∈ Q →
      (zpowers x).map (MulAut.conj w).toMonoidHom ≤ Q := fun w hw => by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hw
  have hx1Q : y * x * y⁻¹ ∈ Q := (mem_normalizer_iff.mp hyN x).mp hxQ
  have hx2Q : y ^ 2 * x * (y ^ 2)⁻¹ ∈ Q := by
    have h := (mem_normalizer_iff.mp hyN _).mp hx1Q
    rwa [show y * (y * x * y⁻¹) * y⁻¹ = y ^ 2 * x * (y ^ 2)⁻¹ by rw [pow_two]; group] at h
  have hyx1 : y * x * y⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rw [this, h]
    group
  have hnx : y * x * y⁻¹ ∉ zpowers x := fun h =>
    hyQ ⟨hyP, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (CFSG.LocalAnalysis.RankThreeTheoremC.p34_conj_eq_of_pow hx1 hx3
        hym h))⟩
  rcases hD y (hle y hx1Q) with h1 | h1
  · exact hnx h1
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [zpowers_one_eq_bot, mem_bot] at h1
    exact hyx1 h1
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hzu : zpowers (y * x * y⁻¹) = zpowers u :=
    CFSG.LocalAnalysis.RankThreeTheoremC.p34_zpowers_eq_of_mem huo h1 hyx1
  rcases hD (y ^ 2) (hle _ hx2Q) with h2 | h2
  ·
    have h3 := CFSG.LocalAnalysis.RankThreeTheoremC.p34_conj_eq_of_pow hx1 hx3 hy2m h2
    exact hnx (by rw [l28iv_comm_of_sq_comm hym h3]; exact mem_zpowers x)
  ·
    apply hnx
    have h4 : y * (y * x * y⁻¹) * y⁻¹ ∈ zpowers (y * x * y⁻¹) := by
      rw [hzu, show y * (y * x * y⁻¹) * y⁻¹ = y ^ 2 * x * (y ^ 2)⁻¹ by rw [pow_two]; group]
      exact h2
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h4
    have h5 : y * x * y⁻¹ = x ^ j := by
      have h6 : y * (x ^ j) * y⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by rw [← hj, conj_zpow]
      have h7 : y⁻¹ * (y * (x ^ j) * y⁻¹) * y = y⁻¹ * (y * (y * x * y⁻¹) * y⁻¹) * y := by
        rw [h6]
      rw [show y⁻¹ * (y * x ^ j * y⁻¹) * y = x ^ j by group,
        show y⁻¹ * (y * (y * x * y⁻¹) * y⁻¹) * y = y * x * y⁻¹ by group] at h7
      exact h7.symm
    rw [h5]
    exact zpow_mem (mem_zpowers x) j

end CFSG.LocalAnalysis.RankThreeTheoremC
