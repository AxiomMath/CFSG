module

public import CFSG.ClassicalInvolution.Q3.Q3MStruct

public section

namespace CFSG.ClassicalInvolution.Q3.M

open CFSG.Open CFSG.ClassicalInvolution

variable {X : Type} [Group X] [Finite X]

theorem le_of_odd_index (hO : classicalInvolutionOddCore X = ⊥)
    {N T D L Cg : Subgroup X} (hNsub : IsSubnormal N ⊤) (hTN : T ≤ N) (hDN : D ≤ N)
    (hLN : L ≤ N) (hNT : N ≤ Subgroup.normalizer (T : Set X)) (hNTD : N ≤ T ⊔ D)
    (hcomm : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t) (hDconj : ∀ n ∈ N, ∀ d ∈ D, n * d * n⁻¹ ∈ D)
    (hZ2 : ∀ x ∈ T ⊓ D, ∃ j : ℕ, x ^ (2 ^ j) = 1) (hCgN : Cg ≤ N) (hDCg : D ≤ Cg)
    (hLCg : IsSubnormal L Cg) (hodd : Odd (T.relIndex L)) : L ≤ T := by
  set W : Subgroup X := L ⊔ T with hW
  set DL : Subgroup X := D ⊓ W with hDL
  have hLW : L ≤ W := le_sup_left
  have hTW : T ≤ W := le_sup_right
  have hLnorm : L ≤ Subgroup.normalizer (T : Set X) := hLN.trans hNT
  have hCgT : Cg ⊔ T = N :=
    le_antisymm (sup_le hCgN hTN)
      (hNTD.trans (sup_le le_sup_right (hDCg.trans le_sup_left)))
  have hWN : IsSubnormal W N := by
    have h1 := isSubnormal_sup_of_le_normalizer hLCg (hCgN.trans hNT)
    rwa [hCgT] at h1
  have hDLsub : IsSubnormal DL ⊤ := by
    have h2 := isSubnormal_inf hWN D
    rw [inf_eq_right.mpr hDN, inf_comm W D] at h2
    have h3 : IsSubnormal D N :=
      isSubnormal_of_normal_subgroupOf hDN
        ((Subgroup.normal_subgroupOf_iff hDN).mpr fun d n hd hn => hDconj n hn d hd)
    exact isSubnormal_trans (isSubnormal_trans h2 h3) hNsub
  have hWeq : W = T ⊔ DL := by
    refine le_antisymm (sup_le ?_ le_sup_left) (sup_le hTW inf_le_right)
    intro l hl
    obtain ⟨t, ht, d, hd, rfl⟩ := exists_mul_of_mem_sup hcomm (hNTD (hLN hl))
    have hdW : d ∈ W := by
      have : d = t⁻¹ * (t * d) := by group
      rw [this]
      exact W.mul_mem (W.inv_mem (hTW ht)) (hLW hl)
    exact Subgroup.mul_mem_sup ht ⟨hd, hdW⟩
  have hcommDL : ∀ t ∈ T, ∀ d ∈ DL, t * d = d * t := fun t ht d hd => hcomm t ht d hd.1
  have hP1 := card_sup_mul_card_inf_of_le_normalizer hLnorm
  rw [inf_comm L T] at hP1
  have hP2 := card_sup_mul_card_inf hcommDL
  have hTDL : T ⊓ DL = T ⊓ D := by
    ext x
    constructor
    · rintro ⟨hxT, hxD, _⟩
      exact ⟨hxT, hxD⟩
    · rintro ⟨hxT, hxD⟩
      exact ⟨hxT, hxD, hTW hxT⟩
  rw [← hWeq, hTDL] at hP2
  have hZDL : T ⊓ D ≤ DL := fun x hx => ⟨hx.2, hTW hx.1⟩
  have hI1 := card_eq_mul_relIndex hZDL
  have hI2 := card_eq_mul_relIndex (inf_le_right : T ⊓ L ≤ L)
  rw [Subgroup.inf_relIndex_right] at hI2
  have ha : 0 < Nat.card ↥(T ⊓ L) := Nat.card_pos
  have hb : 0 < Nat.card ↥(T ⊓ D) := Nat.card_pos
  have ht : 0 < Nat.card ↥T := Nat.card_pos
  have e1 : Nat.card ↥W = T.relIndex L * Nat.card ↥T := by
    apply Nat.eq_of_mul_eq_mul_left ha
    calc Nat.card ↥(T ⊓ L) * Nat.card ↥W = Nat.card ↥W * Nat.card ↥(T ⊓ L) := mul_comm _ _
      _ = Nat.card ↥L * Nat.card ↥T := hP1
      _ = (Nat.card ↥(T ⊓ L) * T.relIndex L) * Nat.card ↥T := by rw [hI2]
      _ = Nat.card ↥(T ⊓ L) * (T.relIndex L * Nat.card ↥T) := by ring
  have e2 : Nat.card ↥W = Nat.card ↥T * (T ⊓ D).relIndex DL := by
    apply Nat.eq_of_mul_eq_mul_left hb
    calc Nat.card ↥(T ⊓ D) * Nat.card ↥W = Nat.card ↥W * Nat.card ↥(T ⊓ D) := mul_comm _ _
      _ = Nat.card ↥T * Nat.card ↥DL := hP2
      _ = Nat.card ↥T * (Nat.card ↥(T ⊓ D) * (T ⊓ D).relIndex DL) := by rw [hI1]
      _ = Nat.card ↥(T ⊓ D) * (Nat.card ↥T * (T ⊓ D).relIndex DL) := by ring
  have e3 : (T ⊓ D).relIndex DL = T.relIndex L := by
    apply Nat.eq_of_mul_eq_mul_left ht
    rw [← e2, e1]
    ring
  have hodd' : Odd ((T ⊓ D).relIndex DL) := e3 ▸ hodd
  have hcen : ∀ k ∈ DL, ∀ z ∈ T ⊓ D, k * z = z * k := fun k hk z hz =>
    (hcomm z hz.1 k hk.1).symm
  have hDLZ : DL ≤ T ⊓ D := eq_of_odd_index_central hO hDLsub hZDL hcen hZ2 hodd'
  intro l hl
  obtain ⟨t, ht, d, hd, rfl⟩ := exists_mul_of_mem_sup hcomm (hNTD (hLN hl))
  have hdW : d ∈ W := by
    have : d = t⁻¹ * (t * d) := by group
    rw [this]
    exact W.mul_mem (W.inv_mem (hTW ht)) (hLW hl)
  exact T.mul_mem ht (hDLZ ⟨hd, hdW⟩).1

end CFSG.ClassicalInvolution.Q3.M
