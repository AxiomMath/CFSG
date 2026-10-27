module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Tools2

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_sq_mem {H U : Subgroup G} (hU : IsPGroup 2 U) (hHU : H < U) :
    ∃ s ∈ U, s ∉ H ∧ s ∈ normalizer (H : Set G) ∧ s * s ∈ H := by
  classical
  obtain ⟨u, huU, huH, huN⟩ := exists_mem_normalizer_not_mem_of_lt hU hHU
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU) ⟨u, huU⟩
  rw [Subgroup.orderOf_mk] at hk
  have hex : ∃ j, u ^ (2 ^ j) ∈ H := ⟨k, by rw [← hk, pow_orderOf_eq_one]; exact one_mem _⟩
  have hjH : u ^ (2 ^ Nat.find hex) ∈ H := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := fun h0 => huH (by rw [h0, pow_zero, pow_one] at hjH; exact hjH)
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hiH : u ^ (2 ^ i) ∉ H := Nat.find_min hex (by omega)
  refine ⟨u ^ (2 ^ i), pow_mem huU _, hiH, pow_mem huN _, ?_⟩
  rw [← pow_add, show 2 ^ i + 2 ^ i = 2 ^ (i + 1) by ring, ← hi]
  exact hjH

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem eq_of_le_normalizer_Q {P : Subgroup G} (hP : IsPGroup 2 P) (hSP : S ≤ P)
    (hPQ : P ≤ normalizer (Q : Set G)) : P = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQbot : Q ≠ ⊥ := fun h1 => by
    have h2 := h.zQ
    rw [h1, mem_bot] at h2
    have h3 := h.z2
    rw [h2, orderOf_one] at h3
    omega
  obtain ⟨u, huQ, hu2, huP⟩ := exists_involution_center hP (h.QS.trans hSP) hPQ hQbot
  have hu := h.repoint huQ hu2 fun s hs => huP s (hSP hs)
  have hPN : P ≤ normalizer (footeF L₀ u : Set G) := fun p hp =>
    hu.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr (huP p hp))
  exact hu.sylS.eq_of_le hSP hPN hP

theorem not_mem_normalizer_Q {s : G} (hsT : s ∈ T) (hsS : s ∉ S) :
    s ∉ normalizer (Q : Set G) := by
  intro hsQ
  have hP : IsPGroup 2 ↥(S ⊔ zpowers s) :=
    h.sylT.isPGroup.to_le (sup_le h.ST (zpowers_le.mpr hsT))
  have h1 := h.eq_of_le_normalizer_Q hP le_sup_left
    (sup_le h.S_le_normalizer_Q (zpowers_le.mpr hsQ))
  have h2 : s ∈ S ⊔ zpowers s := mem_sup_right (mem_zpowers s)
  rw [h1] at h2
  exact hsS h2

theorem conj_mem_conjugate_Q {x y q : G} (hx : x ∈ normalizer (S : Set G)) (hy : y ∈ S)
    (hq : q ∈ conjugate Q x) : y * q * y⁻¹ ∈ conjugate Q x := by
  rw [mem_conjugate_iff] at hq ⊢
  have hxy : x * y * x⁻¹ ∈ S := (mem_normalizer_iff.mp hx y).mp hy
  rw [show x * (y * q * y⁻¹) * x⁻¹ = (x * y * x⁻¹) * (x * q * x⁻¹) * (x * y * x⁻¹)⁻¹ by group]
  exact h.conj_mem_Q hxy hq

theorem commute_Q_conjugate {x : G} (hx : x ∈ normalizer (S : Set G))
    (hxQ : x ∉ normalizer (Q : Set G)) {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ conjugate Q x) :
    q * q' = q' * q := by
  have hq'S : q' ∈ S := h.conjugate_Q_le hx hq'
  have h1 : q * q' * q⁻¹ * q'⁻¹ ∈ Q ⊓ conjugate Q x := by
    refine mem_inf.mpr ⟨?_, mul_mem (h.conj_mem_conjugate_Q hx (h.QS hq) hq') (inv_mem hq')⟩
    rw [show q * q' * q⁻¹ * q'⁻¹ = q * (q' * q⁻¹ * q'⁻¹) by group]
    exact mul_mem hq (h.conj_mem_Q hq'S (inv_mem hq))
  rw [h.inf_conjugate_eq_bot hx hxQ, mem_bot] at h1
  calc q * q' = q * q' * q⁻¹ * q'⁻¹ * (q' * q) := by group
    _ = q' * q := by rw [h1, one_mul]

theorem mem_S_of_commute {y : G} (hyT : y ∈ T) (hyz : y * z = z * y) : y ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(S ⊔ zpowers y) :=
    h.sylT.isPGroup.to_le (sup_le h.ST (zpowers_le.mpr hyT))
  have hPN : S ⊔ zpowers y ≤ normalizer (L : Set G) := sup_le h.S_le
    (zpowers_le.mpr (h.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr hyz)))
  have h1 := h.sylS.eq_of_le le_sup_left hPN hP
  have h2 : y ∈ S ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  rwa [h1] at h2

theorem isSylowOf_centralizer_of_center {u : G} (huQ : u ∈ Q) (hu2 : orderOf u = 2)
    (huS : ∀ s ∈ S, s * u = u * s) : IsSylowOf 2 S (centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu := h.repoint huQ hu2 huS
  exact hu.sylS.of_le (fun s hs => mem_centralizer_singleton_iff.mpr (huS s hs))
    hu.centralizer_le_normalizer

end Sec5

end CFSG.ComponentClassification.Foote5
