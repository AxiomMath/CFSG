module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_ncard_conjClassIn [Finite G] (M : Subgroup G) (t : G) :
    (conjClassIn M t).ncard = (M ⊓ centralizer ({t} : Set G)).relIndex M := by
  letI : MulAction ↥M G := MulAction.compHom G (MulAut.conj.comp M.subtype)
  have hstab : MulAction.stabilizer ↥M t = (M ⊓ centralizer ({t} : Set G)).subgroupOf M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    change (↑m * t * ↑m⁻¹ = t) ↔ (↑m ∈ M ∧ ↑m * t = t * ↑m)
    exact ⟨fun h => ⟨m.2, mul_inv_eq_iff_eq_mul.mp h⟩, fun h => mul_inv_eq_iff_eq_mul.mpr h.2⟩
  have horbit : MulAction.orbit ↥M t = conjClassIn M t := by
    ext y
    simp only [MulAction.mem_orbit_iff, conjClassIn, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, m.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  calc (conjClassIn M t).ncard = (MulAction.orbit ↥M t).ncard := by rw [horbit]
    _ = (MulAction.stabilizer ↥M t).index := (MulAction.index_stabilizer ↥M t).symm
    _ = (M ⊓ centralizer ({t} : Set G)).relIndex M := by rw [hstab]; rfl

theorem sec11_relIndex_S_T [Finite G] {M T S : Subgroup G} {t : G} (hT : IsSylow2Of T M)
    (hST : S ≤ T) (hS : IsSylow2Of S (centralizer ({t} : Set G)))
    (h6 : (conjClassIn M t).ncard = 6) : S.relIndex T = 2 := by
  let C : Subgroup G := M ⊓ centralizer ({t} : Set G)
  have hTM : T ≤ M := hT.1
  have hSM : S ≤ M := hST.trans hTM
  have hSC : S ≤ C := le_inf hSM hS.1
  have hCM : C ≤ M := inf_le_left
  have hCZ : C ≤ centralizer ({t} : Set G) := inf_le_right
  have hC6 : C.relIndex M = 6 := by
    have h := sec11_ncard_conjClassIn M t
    rw [h6] at h
    exact h.symm
  have hkey : S.relIndex T * T.relIndex M = S.relIndex C * C.relIndex M := by
    rw [Subgroup.relIndex_mul_relIndex (H := S) (K := T) (L := M) hST hTM,
      Subgroup.relIndex_mul_relIndex (H := S) (K := C) (L := M) hSC hCM]
  have hkey6 : S.relIndex T * T.relIndex M = S.relIndex C * 6 := by
    rw [hkey, hC6]
  have hTodd : Odd (T.relIndex M) :=
    Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact hT.2.2)
  have hZodd : Odd (S.relIndex (centralizer ({t} : Set G))) :=
    Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact hS.2.2)
  have hSCodd : Odd (S.relIndex C) := by
    have hprod : S.relIndex C * C.relIndex (centralizer ({t} : Set G)) =
        S.relIndex (centralizer ({t} : Set G)) :=
      Subgroup.relIndex_mul_relIndex (H := S) (K := C)
        (L := centralizer ({t} : Set G)) hSC hCZ
    have hodd : Odd (S.relIndex C * C.relIndex (centralizer ({t} : Set G))) := by
      rw [hprod]; exact hZodd
    exact (Nat.odd_mul.mp hodd).1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ : ∃ n, Nat.card ↥T = 2 ^ n := hT.2.1.exists_card_eq
  have hdvd : S.relIndex T ∣ 2 ^ n := by
    have h := (S.subgroupOf T).index_dvd_card
    rwa [hn] at h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hkeyk : 2 ^ k * T.relIndex M = S.relIndex C * 6 := by
    rw [← hk]
    exact hkey6
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k
      · exfalso
        rw [pow_zero, one_mul] at hkeyk
        have heven : 2 ∣ T.relIndex M := by
          rw [hkeyk]
          exact ⟨S.relIndex C * 3, by ring⟩
        exact hTodd.not_two_dvd_nat heven
      · rfl
    · exfalso
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have h4dvd : (4 : ℕ) ∣ S.relIndex C * 6 := by
        have h4pow : (4 : ℕ) ∣ 2 ^ (j + 2) := by
          refine ⟨2 ^ j, ?_⟩
          rw [pow_add]
          ring
        have h := dvd_mul_of_dvd_left h4pow (T.relIndex M)
        rw [hkeyk] at h
        exact h
      have h' : 2 * 2 ∣ (S.relIndex C * 3) * 2 := by
        have e : (S.relIndex C * 3) * 2 = S.relIndex C * 6 := by ring
        rw [e]
        exact h4dvd
      have h2dvd : 2 ∣ S.relIndex C * 3 :=
        (mul_dvd_mul_iff_right (show (2 : ℕ) ≠ 0 by norm_num)).mp h'
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2dvd with h | h
      · exact hSCodd.not_two_dvd_nat h
      · norm_num at h
  rw [hk, hk1, pow_one]

end CFSG.OddStandard.SmallF3.Omega
