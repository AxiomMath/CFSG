module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

theorem exists_conj_mem_zpowers {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hM : Nat.card M = 3 * 2 ^ 9) {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) :
    ∃ m ∈ M, m * a * m⁻¹ ∈ Subgroup.zpowers b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a' : ↥M := ⟨a, ha⟩
  let b' : ↥M := ⟨b, hb⟩
  have ha3' : orderOf a' = 3 := by rw [← ha3]; exact Subgroup.orderOf_mk a ha
  have hb3' : orderOf b' = 3 := by rw [← hb3]; exact Subgroup.orderOf_mk b hb
  have hsyl : ∀ c : ↥M, orderOf c = 3 →
      ∃ P : Sylow 3 ↥M, (P : Subgroup ↥M) = Subgroup.zpowers c := by
    intro c hc
    have hcard : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc]
    have hp : IsPGroup 3 (Subgroup.zpowers c) :=
      IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
    have hidx : (Subgroup.zpowers c).index = 2 ^ 9 := by
      have h := Subgroup.card_mul_index (Subgroup.zpowers c)
      rw [hcard, hM] at h
      omega
    have hnd : ¬ 3 ∣ (Subgroup.zpowers c).index := by
      rw [hidx]
      intro hd
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
      omega
    exact ⟨hp.toSylow hnd, rfl⟩
  obtain ⟨PA, hPA⟩ := hsyl a' ha3'
  obtain ⟨PB, hPB⟩ := hsyl b' hb3'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) PA PB
  have hmem : g * a' * g⁻¹ ∈ (PB : Subgroup ↥M) := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    exact Subgroup.mem_map.mpr ⟨a', by rw [hPA]; exact Subgroup.mem_zpowers a', rfl⟩
  rw [hPB] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine ⟨(g : G), g.2, Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩⟩
  have := congrArg (fun x : ↥M => (x : G)) hk
  simpa [a', b'] using this

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
