module

public import CFSG.GH74.GLS.C3.Layer1.Back112Omega
public import CFSG.GH74.GLS.C3.Layer1.Back112Count

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG

variable {G : Type} [Group G]

theorem card_le_two_of_lt_four {P S : Subgroup G} (hP : Nat.card ↥P = 4) (hS : S ≤ P) (hne : S ≠ P)
    [Finite G] : Nat.card ↥S ≤ 2 := by
  have hlt : S < P := lt_of_le_of_ne hS hne
  have h1 : Nat.card ↥S < Nat.card ↥P := Subgroup.card_lt_of_lt hlt
  have h2 : Nat.card ↥S ∣ Nat.card ↥P := Subgroup.card_dvd_of_le hS
  rw [hP] at h1 h2
  have h3 : Nat.card ↥S ≤ 3 := by omega
  by_contra hgt
  have h4 : Nat.card ↥S = 3 := by omega
  rw [h4] at h2
  omega

theorem omegaZ_T_of_ne [Finite G] {T P Q : Subgroup G} (hPT : P ≤ T) (hQT : Q ≤ T)
    (hPn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P) (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hPQ : P ⊓ Q = ⊥) (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hP4 : Nat.card ↥P = 4) (hQ4 : Nat.card ↥Q = 4)
    (hRab : ∀ a ∈ P ⊔ Q, ∀ b ∈ P ⊔ Q, a * b = b * a) (hR2 : ∀ a ∈ P ⊔ Q, a * a = 1)
    (hR16 : Nat.card ↥(P ⊔ Q) = 16)
    (hno : ∀ u ∈ T, u * u = 1 → u ∈ P ⊔ Q)
    (hidx : Nat.card ↥T ≤ 2 * Nat.card ↥(P ⊔ Q))
    (hnontriv : ∀ y ∈ T, y ∉ P ⊔ Q → ∃ p ∈ P, y * p * y⁻¹ ≠ p)
    (hlt : P ⊔ Q < T) :
    Q ≤ omegaZ T ∧ Nat.card ↥(omegaZ T) ≤ 8 := by
  set R : Subgroup G := P ⊔ Q with hRdef
  have hRT : R ≤ T := sup_le hPT hQT
  have hRn : ∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R := by
    intro t ht r hr
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hr
    have e : t * (p * q) * t⁻¹ = (t * p * t⁻¹) * (t * q * t⁻¹) := by group
    rw [e]
    exact R.mul_mem (Subgroup.mem_sup_left (hPn t ht p hp)) (Subgroup.mem_sup_right (hQn t ht q hq))
  obtain ⟨y, hyT, hyR⟩ := IsConcreteLE.exists_of_lt hlt
  have hy2R : y * y ∈ R := sq_mem_of_card_le_two hRT hidx y hyT
  have hno' : ∀ r ∈ R, (y * r) * (y * r) ≠ 1 := by
    intro r hr h1
    exact hyR (by
      have := R.mul_mem (hno _ (T.mul_mem hyT (hRT hr)) h1) (R.inv_mem hr)
      simpa using this)
  have hsq := card_cent_sq_gt hRab hR2 (fun r hr => hRn y hyT r hr) hy2R hno'
  have hyP : ∀ p ∈ P, y * p * y⁻¹ ∈ P := hPn y hyT
  have hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := hQn y hyT
  have hprod := card_inf_centralizer_le hPQ hcomm hyP hyQ
  obtain ⟨p0, hp0P, hp0⟩ := hnontriv y hyT hyR
  have hCP : Nat.card ↥(P ⊓ centralizer ({y} : Set G)) ≤ 2 := by
    refine card_le_two_of_lt_four hP4 inf_le_left ?_
    intro heq
    apply hp0
    have hmem : p0 ∈ P ⊓ centralizer ({y} : Set G) := by rw [heq]; exact hp0P
    have h1 : y * p0 = p0 * y := by
      have := (Subgroup.mem_centralizer_iff.1 hmem.2) y (Set.mem_singleton y)
      exact this
    calc y * p0 * y⁻¹ = p0 * y * y⁻¹ := by rw [h1]
      _ = p0 := by group
  have hCQ4 : Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) ≤ 4 := by
    rw [← hQ4]; exact Subgroup.card_le_of_le inf_le_left
  have hCQdvd : Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) ∣ 4 := by
    rw [← hQ4]; exact Subgroup.card_dvd_of_le inf_le_left
  have hRC : Nat.card ↥(R ⊓ centralizer ({y} : Set G)) ≤
      2 * Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) :=
    hprod.trans (Nat.mul_le_mul_right _ hCP)
  rw [hR16] at hsq
  have hCQ : Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) = 4 := by
    have hpos : 0 < Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) := Nat.card_pos
    generalize Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) = d at *
    generalize Nat.card ↥(R ⊓ centralizer ({y} : Set G)) = c at *
    interval_cases d <;> first | omega | nlinarith
  have hQy : Q ≤ centralizer ({y} : Set G) := by
    have heq : Q ⊓ centralizer ({y} : Set G) = Q :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hCQ, hQ4])
    rw [← heq]
    exact inf_le_right
  have hRy : R ⊔ Subgroup.zpowers y = T := by
    have hle : R ⊔ Subgroup.zpowers y ≤ T :=
      sup_le hRT ((Subgroup.zpowers_le).2 hyT)
    have hlt' : R < R ⊔ Subgroup.zpowers y := by
      refine lt_of_le_of_ne le_sup_left fun h => hyR ?_
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hd : Nat.card ↥R ∣ Nat.card ↥(R ⊔ Subgroup.zpowers y) := Subgroup.card_dvd_of_le le_sup_left
    have hgt : Nat.card ↥R < Nat.card ↥(R ⊔ Subgroup.zpowers y) := Subgroup.card_lt_of_lt hlt'
    have hRpos : 0 < Nat.card ↥R := Nat.card_pos
    obtain ⟨m, hm⟩ := hd
    have hm2 : 2 ≤ m := by
      by_contra hm1
      push Not at hm1
      interval_cases m <;> omega
    have h2 : 2 * Nat.card ↥R ≤ Nat.card ↥(R ⊔ Subgroup.zpowers y) := by
      rw [hm]
      have := Nat.mul_le_mul_left (Nat.card ↥R) hm2
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (hidx.trans h2)
  have hQz : Q ≤ omegaZ T := by
    intro q hq
    refine ⟨hQT hq, fun t ht => ?_, hR2 q (Subgroup.mem_sup_right hq)⟩
    rw [← hRy] at ht
    have h1 : ∀ r ∈ R, r ∈ centralizer ({q} : Set G) := fun r hr =>
      Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hRab h (Subgroup.mem_sup_right hq) r hr
    have h2 : y ∈ centralizer ({q} : Set G) := Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((Subgroup.mem_centralizer_iff.1 (hQy hq)) y (Set.mem_singleton y)).symm
    have hle : R ⊔ Subgroup.zpowers y ≤ centralizer ({q} : Set G) :=
      sup_le h1 ((Subgroup.zpowers_le).2 h2)
    exact (Subgroup.mem_centralizer_iff.1 (hle ht)) q (Set.mem_singleton q)
  refine ⟨hQz, ?_⟩
  have hZle : omegaZ T ≤ R ⊓ centralizer ({y} : Set G) := by
    intro e he
    refine ⟨hno e he.1 he.2.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (he.2.1 h hyT).symm
  calc Nat.card ↥(omegaZ T) ≤ Nat.card ↥(R ⊓ centralizer ({y} : Set G)) := Subgroup.card_le_of_le hZle
    _ ≤ Nat.card ↥(P ⊓ centralizer ({y} : Set G)) * Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) := hprod
    _ ≤ 2 * 4 := Nat.mul_le_mul hCP hCQ4
    _ = 8 := by norm_num

end CFSG.GH74.GLS.C3.Layer1.Back
