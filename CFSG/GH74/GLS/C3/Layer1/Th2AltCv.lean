module

public import CFSG.GH74.GLS.C3.Layer1.BkL114SEAsm
public import CFSG.GH74.GLS.C3.Layer1.Th2P85AltSE

public section

namespace CFSG.GH74.GLS.Th2.AltCv

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.P85.Alt CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer1.Bk

variable {G : Type} [Group G] [Finite G] {M K : Subgroup G}

omit [Finite G] in
theorem imgM_comm {x : G} (hxM : x ∈ M) (hKx : K ≤ centralizer ({x} : Set G)) :
    ∀ w ∈ imgM M K, w * barMk ↥M (⟨x, hxM⟩ : ↥M) = barMk ↥M (⟨x, hxM⟩ : ↥M) * w := by
  intro w hw
  obtain ⟨m, hm', rfl⟩ := mem_imgM_iff.1 hw
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.1 (hKx hm'))

omit [Finite G] in
theorem five_dvd_centralizer {n : ℕ} (hn' : n = 5 ∨ n = 6 ∨ n = 7) {x : G} (hxM : x ∈ M)
    (hKx : K ≤ centralizer ({x} : Set G))
    (eK : (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ≃* alternatingGroup (Fin n)) :
    5 ∣ Nat.card ↥(centralizer ({barMk ↥M (⟨x, hxM⟩ : ↥M)} : Set (Mb M))) := by
  have hKC : imgM M K ≤ centralizer ({barMk ↥M (⟨x, hxM⟩ : ↥M)} : Set (Mb M)) := fun w hw =>
    mem_centralizer_singleton_iff.2 (imgM_comm hxM hKx w hw)
  have h1 : Nat.card (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ∣ Nat.card ↥(imgM M K) :=
    Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥(imgM M K)))
      (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(imgM M K)))
  have h2 : Nat.card ↥(imgM M K) ∣
      Nat.card ↥(centralizer ({barMk ↥M (⟨x, hxM⟩ : ↥M)} : Set (Mb M))) :=
    Subgroup.card_dvd_of_le hKC
  have h3 : Nat.card (alternatingGroup (Fin n)) =
      Nat.card (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) := (Nat.card_congr eK.toEquiv).symm
  have h4 : 5 ∣ Nat.card (alternatingGroup (Fin n)) := by
    rcases hn' with rfl | rfl | rfl <;>
      (rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide)
  exact h4.trans ((h3 ▸ h1).trans h2)

theorem alt_two_part_six : (Nat.card (alternatingGroup (Fin (6 + 4)))).factorization 2 = 7 := by
  have h : Nat.card (alternatingGroup (Fin (6 + 4))) = 2 ^ 7 * 14175 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 14175 by norm_num)]

theorem two_part_le {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) :
    2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 ≤ 128 := by
  rcases hn with rfl | rfl | rfl
  · rw [alt_two_part_five]; norm_num
  · rw [alt_two_part_six]; norm_num
  · rw [alt_two_part_seven]; norm_num

end CFSG.GH74.GLS.Th2.AltCv

