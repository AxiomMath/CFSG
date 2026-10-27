module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import Certificates.Certificate9541
public import Certificates.Certificate9703

public section

namespace CFSG.AGLEmbedding.O8pCent

open CFSG.EvenSmallLie.OmegaEight CFSG.RankThree.PartTwo.Sec4.Item434O8pE9
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (card_subgroupOf_of_le isElemAbelian_subgroupOf)

theorem o8pE9_pg_size : o8pE9.pg.size = 8 := by
  simp [o8pE9, genArrs_size]

theorem o8pE9_pg_mem :
    ∀ l < o8pE9.pg.size, CFSG.Monster.B.Co2.permOfArr o8pE9.n o8pE9.pg[l]! ∈ omegaT := by
  intro l hl
  rw [o8pE9_pg_size] at hl
  have h : o8pE9.pg[l]! = genArrs[l]! := by
    simp only [o8pE9]
    exact extract_getElem! hl (by rw [genArrs_size]; norm_num)
  rw [h]
  exact gen_mem_omegaT hl

theorem o8pE9_qOrd :
    o8pE9.qOrd = 3 ^ (Nat.card omegaT).factorization 3 := by
  have h : o8pE9.qOrd = 3 ^ 5 := by simp [o8pE9]
  rw [h, card_omegaT, show (174182400 : ℕ) = 3 ^ 5 * 716800 by norm_num,
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 5 (by norm_num)]

theorem exists_o8pCentData_omegaT :
    ∃ (Q D : Subgroup omegaT) (g : omegaT), Nat.card Q = 3 ^ (Nat.card omegaT).factorization 3 ∧
      Nat.card Q = 243 ∧ D ≤ Q ∧ IsElemAbelian 3 D ∧ Nat.card D = 81 ∧ g ∈ Q ∧
      ∀ C : Subgroup omegaT, C ≤ D → (∀ c ∈ C, g * c = c * g) → Nat.card C ≤ 9 := by
  obtain ⟨Q, D, g, hQJ, hQcard, hDQ, hDe, hD81, hgQ, hgD, hC⟩ :
      ∃ (Q D : Subgroup (Equiv.Perm (Fin 360))) (g : Equiv.Perm (Fin 360)), Q ≤ omegaT ∧
        Nat.card Q = o8pE9.qOrd ∧ D ≤ Q ∧ IsElemAbelian 3 D ∧ 81 ≤ Nat.card D ∧ g ∈ Q ∧
        g ∉ D ∧ ∀ C : Subgroup (Equiv.Perm (Fin 360)), C ≤ D → (∀ c ∈ C, g * c = c * g) →
          Nat.card C ≤ 9 :=
    centCheck_sound o8pE9 Certificates.certificate9541 [1] 9
      Certificates.certificate9703 omegaT o8pE9_pg_mem
  have hQ243 : Nat.card Q = 243 := hQcard.trans rfl
  have hD81' : Nat.card D = 81 := by
    have hdvd : Nat.card D ∣ 3 ^ 5 := by
      have := Subgroup.card_dvd_of_le hDQ
      rwa [hQ243, show (243 : ℕ) = 3 ^ 5 by norm_num] at this
    obtain ⟨k, hk, hkD⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hne : Nat.card D ≠ 243 := by
      intro h243
      have hDQ' : D = Q :=
        Subgroup.eq_of_le_of_card_ge hDQ (by rw [h243, hQ243])
      exact hgD (hDQ' ▸ hgQ)
    have h5 : k ≠ 5 := by
      rintro rfl
      exact hne (by rw [hkD]; norm_num)
    have h4 : 4 ≤ k := by
      by_contra hlt
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk4 : k = 4 := by omega
    rw [hkD, hk4]
    norm_num
  have hDJ : D ≤ omegaT := hDQ.trans hQJ
  refine ⟨Q.subgroupOf omegaT, D.subgroupOf omegaT, ⟨g, hQJ hgQ⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_subgroupOf_of_le hQJ, hQcard]
    exact o8pE9_qOrd
  · rw [card_subgroupOf_of_le hQJ]
    exact hQ243
  · intro x hx
    exact hDQ hx
  · exact isElemAbelian_subgroupOf omegaT hDe
  · rw [card_subgroupOf_of_le hDJ]
    exact hD81'
  · exact hgQ
  · intro C hCD hCg
    have hmap : C.map omegaT.subtype ≤ D := by
      rintro _ ⟨c, hc, rfl⟩
      exact hCD hc
    have hcomm : ∀ c ∈ C.map omegaT.subtype, g * c = c * g := by
      rintro _ ⟨c, hc, rfl⟩
      exact congrArg Subtype.val (hCg c hc)
    have := hC (C.map omegaT.subtype) hmap hcomm
    rwa [Subgroup.card_map_of_injective omegaT.subtype_injective] at this

end CFSG.AGLEmbedding.O8pCent
