module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWCore
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL34a

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

theorem exists_oddPart {N Q : Type*} [Group N] [Finite N] [Group Q] {z : N}
    (hz : ∀ n : N, n * z = z * n) (hz2 : orderOf z = 2) (f : N →* Q)
    (hf : Function.Surjective f) (hker : f.ker = zpowers z) (hQ : Odd (Nat.card Q)) :
    ∃ K : Subgroup N, (∀ n : N, n ∈ K ↔ Odd (orderOf n)) ∧ ∀ n : N, n ∈ K ∨ z * n ∈ K := by
  have hZn : (zpowers z).Normal := by
    rw [← hker]
    infer_instance
  have hcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hidx : (zpowers z).index = Nat.card Q := by
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, card_top]
  have hcop : Nat.Coprime (Nat.card (zpowers z)) (zpowers z).index := by
    rw [hcard, hidx]
    exact Nat.coprime_two_left.mpr hQ
  obtain ⟨K, hK⟩ := exists_right_complement'_of_coprime hcop
  have hKcard : Nat.card K = Nat.card Q := by
    have h := hK.card_mul_card
    have h2 := (zpowers z).index_mul_card
    rw [hcard] at h h2
    rw [hidx] at h2
    omega
  have hzpow : ∀ s ∈ zpowers z, s = 1 ∨ s = z := by
    classical
    intro s hs
    rw [mem_zpowers_iff_mem_range_orderOf, hz2] at hs
    simp only [Finset.mem_image, Finset.mem_range] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    interval_cases k
    · left; rw [pow_zero]
    · right; rw [pow_one]
  have hdecomp : ∀ n : N, ∃ s ∈ zpowers z, ∃ k ∈ K, s * k = n := by
    intro n
    obtain ⟨⟨s, k⟩, hsk, -⟩ := (isComplement'_def.mp hK).existsUnique n
    exact ⟨s, s.2, k, k.2, hsk⟩
  have hodd : ∀ k ∈ K, Odd (orderOf k) := by
    intro k hk
    have hdvd : orderOf k ∣ Nat.card K := by
      rw [← Subgroup.orderOf_mk k hk]
      exact orderOf_dvd_natCard _
    rw [hKcard] at hdvd
    exact hQ.of_dvd_nat hdvd
  refine ⟨K, fun n => ⟨fun hn => hodd n hn, fun hn => ?_⟩, fun n => ?_⟩
  · obtain ⟨s, hs, k, hk, rfl⟩ := hdecomp n
    rcases hzpow s hs with h | h <;> rw [h] at hn ⊢
    · rwa [one_mul]
    · exfalso
      have hc : Commute z k := (hz k).symm
      have hcop' : Nat.Coprime (orderOf z) (orderOf k) := by
        rw [hz2]
        exact Nat.coprime_two_left.mpr (hodd k hk)
      rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime hcop', hz2] at hn
      exact (Nat.not_even_iff_odd.mpr hn) (even_two_mul _)
  · obtain ⟨s, hs, k, hk, rfl⟩ := hdecomp n
    rcases hzpow s hs with h | h <;> rw [h]
    · left; rwa [one_mul]
    · right
      rw [← mul_assoc, ← pow_two, ← hz2, pow_orderOf_eq_one, one_mul]
      exact hk

variable {G : Type} [Group G]

namespace GHSylow

variable (D : GHSylow G)

abbrev OM : Subgroup G := (pPrimeCore 2 ↥D.M).map D.M.subtype

theorem OM_le_M : D.OM ≤ D.M := map_subtype_le _

theorem conj_mem_OM {g o : G} (hg : g ∈ D.M) (ho : o ∈ D.OM) : g * o * g⁻¹ ∈ D.OM := by
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨g, hg⟩ * o' * ⟨g, hg⟩⁻¹, (pPrimeCore_normal (p := 2) (G := ↥D.M)).conj_mem o' ho' _,
    rfl⟩

theorem conj_mem_OM' {g o : G} (hg : g ∈ D.M) (ho : o ∈ D.OM) : g⁻¹ * o * g ∈ D.OM := by
  have := D.conj_mem_OM (inv_mem hg) ho
  rwa [inv_inv] at this

theorem odd_orderOf_of_mem_OM [Finite G] {o : G} (ho : o ∈ D.OM) : Odd (orderOf o) :=
  GrSLit.odd_orderOf_of_mem_map_pPrimeCore ho

theorem odd_card_OM [Finite G] : Odd (Nat.card D.OM) := GrSLit.odd_card_map_pPrimeCore _

theorem le_OM {K : Subgroup G} (hKM : K ≤ D.M) (hnorm : ∀ g ∈ D.M, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hodd : Odd (Nat.card K)) : K ≤ D.OM :=
  GrSLit.le_map_pPrimeCore hKM hnorm hodd

theorem eq_one_of_mem_OM [Finite G] {o : G} (ho : o ∈ D.OM) {a : ℕ} (hoa : o ^ (2 ^ a) = 1) :
    o = 1 := by
  have hodd := D.odd_orderOf_of_mem_OM ho
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hoa)
  rcases b with _ | b
  · rwa [pow_zero, orderOf_eq_one_iff] at hb
  · rw [hb] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, b.succ_ne_zero⟩))

end GHSylow

end CFSG.ComponentClassification.GHarris
