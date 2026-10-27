module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Centre

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem S_le_centralizer : H.S ≤ centralizer ({H.t} : Set G) := by
  intro s hs
  obtain ⟨x, rfl⟩ := (mem_S H).1 hs
  rw [mem_centralizer_singleton_iff, ← H.psi_tt, ← H.psi_mul, ← H.psi_mul]
  congr 1
  exact SMod.mul_tt_comm x

theorem card_S_mul_index : 32 * H.S.index = Nat.card G := by
  rw [← H.card_S]; exact H.S.card_mul_index

theorem isPGroup_S : IsPGroup 2 H.S :=
  IsPGroup.of_card (n := 5) (by rw [H.card_S]; norm_num)

theorem index_S (n : ℕ) (hn : Nat.card {x : G // IsConj H.t x} = n) :
    H.S.index = n * 495 := by
  have h1 := H.card_S_mul_index
  have h2 := H.card_A_mul
  rw [hn] at h2
  omega

theorem false_case11 (hz : IsConj H.t (H.a ^ 4))
    (hn : Nat.card {x : G // IsConj H.t x} % 4 = 3) : False := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : H.S.index = Nat.card {x : G // IsConj H.t x} * 495 := H.index_S _ rfl
  have hodd : ¬ 2 ∣ H.S.index := by rw [hidx]; omega
  let P : Sylow 2 G := H.isPGroup_S.toSylow hodd
  obtain ⟨c, hc⟩ := isConj_iff.1 hz
  have hxz : H.a ^ 4 ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact (H.W_central H.z_mem_W s hs).symm
  have hyt : c⁻¹ * H.a ^ 4 * c ∈ centralizer (P : Set G) := by
    have : c⁻¹ * H.a ^ 4 * c = H.t := by rw [← hc]; group
    rw [this, mem_centralizer_iff]
    intro s hs
    exact (H.W_central H.t_mem_W s hs).symm
  obtain ⟨n, hn1, hn2⟩ := P.conj_eq_normalizer_conj_of_mem_centralizer (H.a ^ 4) c hxz hyt
  have hct : c⁻¹ * H.a ^ 4 * c = H.t := by rw [← hc]; group
  rw [hct] at hn2
  apply H.conj_t_ne_z (x := n) hn1
  rw [hn2]
  group

end Setting

end CFSG.EvenSporadicStandard.M11Std
