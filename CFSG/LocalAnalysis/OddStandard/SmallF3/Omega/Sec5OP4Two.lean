module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem sec5op4h_mem_commutator_of_mem_closure_odd {X : Type*} [Group X] {x : X}
    (hx : x ∈ Subgroup.closure {y : X | Odd (orderOf y)}) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x ∈ commutator X := by
  have hab : IsMulCommutative (X ⧸ commutator X) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  have hodd : ∀ y ∈ Subgroup.closure {y : X | Odd (orderOf y)},
      Odd (orderOf (QuotientGroup.mk y : X ⧸ commutator X)) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact Odd.of_dvd_nat hy (orderOf_map_dvd (QuotientGroup.mk' _) y)
    | one => rw [QuotientGroup.mk_one, orderOf_one]; exact odd_one
    | mul y z _ _ hy hz =>
      rw [QuotientGroup.mk_mul]
      have hc : Commute (QuotientGroup.mk y : X ⧸ commutator X) (QuotientGroup.mk z) :=
        hab.is_comm.comm _ _
      exact (hy.mul hz).of_dvd_nat hc.orderOf_mul_dvd_mul_orderOf
    | inv y _ hy => rw [QuotientGroup.mk_inv, orderOf_inv]; exact hy
  have h1 : orderOf (QuotientGroup.mk x : X ⧸ commutator X) = 1 := by
    have hdvd : orderOf (QuotientGroup.mk x : X ⧸ commutator X) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one])
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _
      (Nat.coprime_two_right.mpr (hodd x hx))) hdvd
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem sec5op4_twoCore_le_commutator {K : Subgroup G} (hK : twoRes K = K) :
    twoCoreIn K ≤ ⁅K, K⁆ := by
  intro x hx
  have hxK : x ∈ K := by
    have hle : twoCoreIn K ≤ K := by
      unfold twoCoreIn CFSG.inSubgroup
      exact Subgroup.map_subtype_le _
    exact hle hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    have h2 : IsPGroup 2 (twoCoreIn K) := by
      unfold twoCoreIn CFSG.inSubgroup
      exact (CFSG.pCore_isPGroup (G := ↥K) (p := 2)).map K.subtype
    obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg (fun g : ↥(twoCoreIn K) => (g : G)) hk⟩
  have hmap : (Subgroup.closure {y : ↥K | Odd (orderOf y)}).map K.subtype = K := by
    rw [MonoidHom.map_closure]
    have hset : K.subtype '' {y : ↥K | Odd (orderOf y)} =
        {g : G | g ∈ K ∧ Odd (orderOf g)} := by
      ext g
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, ?_⟩
        change Odd (orderOf (y : G))
        rw [Subgroup.orderOf_coe]
        exact hy
      · rintro ⟨hg, hodd⟩
        exact ⟨⟨g, hg⟩, by simpa using hodd, rfl⟩
    rw [hset]
    exact hK
  have hy : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.closure {y : ↥K | Odd (orderOf y)} := by
    have hmem : K.subtype (⟨x, hxK⟩ : ↥K) ∈
        (Subgroup.closure {y : ↥K | Odd (orderOf y)}).map K.subtype := by
      rw [hmap]
      exact hxK
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hmem
    exact (K.subtype_injective hzy) ▸ hz
  have hcomm : (⟨x, hxK⟩ : ↥K) ∈ commutator ↥K :=
    sec5op4h_mem_commutator_of_mem_closure_odd hy (k := k) (by
      apply Subtype.ext
      simpa using hk)
  have hmem : K.subtype (⟨x, hxK⟩ : ↥K) ∈ (commutator ↥K).map K.subtype :=
    Subgroup.mem_map_of_mem _ hcomm
  rw [Subgroup.map_subtype_commutator] at hmem
  simpa using hmem

end CFSG.OddStandard.SmallF3.Omega
