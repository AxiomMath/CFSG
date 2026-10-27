module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyP2Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRowFacts

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Open

section Conj

variable {G : Type*} [Group G]

theorem ovg_orderOf_conj (g y : G) : orderOf (g * y * g⁻¹) = orderOf y := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
  simpa using h

theorem ovg_card_centralizer_conj (g t : G) :
    Nat.card (centralizer ({g * t * g⁻¹} : Set G)) = Nat.card (centralizer ({t} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ * x * g, ?_⟩
      invFun := fun y => ⟨g * y * g⁻¹, ?_⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  · have h := mem_centralizer_singleton_iff.1 x.2
    refine mem_centralizer_singleton_iff.2 ?_
    calc g⁻¹ * (x : G) * g * t = g⁻¹ * ((x : G) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (x : G)) * g := by rw [h]
      _ = t * (g⁻¹ * (x : G) * g) := by group
  · have h := mem_centralizer_singleton_iff.1 y.2
    refine mem_centralizer_singleton_iff.2 ?_
    calc g * (y : G) * g⁻¹ * (g * t * g⁻¹) = g * ((y : G) * t) * g⁻¹ := by group
      _ = g * (t * (y : G)) * g⁻¹ := by rw [h]
      _ = (g * t * g⁻¹) * (g * (y : G) * g⁻¹) := by group

end Conj

theorem babyInv_conj {k : Fin 4} {t : B} (g : B) (h : BabyInv k t) : BabyInv k (g * t * g⁻¹) :=
  ⟨(ovg_orderOf_conj g t).trans h.1, (ovg_card_centralizer_conj g t).trans h.2⟩

theorem babyOrbit_conj {k : Fin 4} {r s h : B} (hh : h ∈ centralizer ({r} : Set B))
    (hs : BabyOrbit k r s) : BabyOrbit k r (h * s * h⁻¹) := by
  have hr : h * r * h⁻¹ = r := by
    have h1 := mem_centralizer_singleton_iff.1 hh
    calc h * r * h⁻¹ = r * h * h⁻¹ := by rw [h1]
      _ = r := by group
  have e : r * (h * s * h⁻¹) = h * (r * s) * h⁻¹ := by
    calc r * (h * s * h⁻¹) = (h * r * h⁻¹) * (h * s * h⁻¹) := by rw [hr]
      _ = h * (r * s) * h⁻¹ := by group
  fin_cases k
  · show BabyInv 1 (r * (h * s * h⁻¹))
    rw [e]
    exact babyInv_conj h hs
  · show BabyInv 3 (r * (h * s * h⁻¹))
    rw [e]
    exact babyInv_conj h hs
  · show orderOf (r * (h * s * h⁻¹)) = 3
    rw [e, ovg_orderOf_conj]
    exact hs
  · show orderOf (r * (h * s * h⁻¹)) = 4 ∧ BabyInv 1 ((r * (h * s * h⁻¹)) ^ 2)
    rw [e, ovg_orderOf_conj, conj_pow]
    exact ⟨hs.1, babyInv_conj h hs.2⟩

theorem ovg_orderOf_babyOrbit {r s : B} {k : Fin 4} (hs : BabyOrbit k r s) :
    orderOf (r * s) = ![2, 2, 3, 4] k := by
  fin_cases k
  · exact hs.1
  · exact hs.1
  · exact hs
  · exact hs.1

theorem babyOvergroups_of_tables [Finite B] (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hsimple : IsSimpleGroup B) {r : B} (hr2 : orderOf r = 2) {K X : Subgroup B} (hKX : K ≤ X)
    (hKr : K ≤ centralizer ({r} : Set B)) (hK : Nat.card K = 2 * ordTwistedE6 2) :
    X ≤ centralizer ({r} : Set B) ∨ X = ⊤ := by
  obtain ⟨k, hk⟩ := hT3.1 r hr2
  have hKC : Nat.card K ≤ Nat.card (centralizer ({r} : Set B)) := Subgroup.card_le_of_le hKr
  have hk0 : k = 0 := eq_zero_of_le_babyCentOrder (by rw [hK, hk.2] at hKC; omega)
  subst hk0
  have hr : BabyInv 0 r := hk
  have hidx : Nat.card (centralizer ({r} : Set B)) = 2 * Nat.card K := by
    rw [hk.2, babyCentOrder_zero, hK]
    ring
  obtain ⟨hcov, htr, hcard⟩ := hT4 r hr
  have hrr : r * r = 1 := by
    have h := pow_orderOf_eq_one r
    rw [hr2, pow_two] at h
    exact h
  have hS : ∀ k : Fin 4, IsSuborbit (centralizer ({r} : Set B)) {s | BabyInv 0 s}
      {s | BabyInv 0 s ∧ BabyOrbit k r s} (babyOrbitSize k) := fun k =>
    { subset := fun s hs => hs.1
      inv := fun h hh s hs => ⟨babyInv_conj h hs.1, babyOrbit_conj hh hs.2⟩
      trans := fun s hs s' hs' => htr k s s' hs.1 hs'.1 hs.2 hs'.2
      ncard := hcard k }
  have hrS : ∀ k : Fin 4, r ∉ {s | BabyInv 0 s ∧ BabyOrbit k r s} := fun k h => by
    have h1 := ovg_orderOf_babyOrbit h.2
    rw [hrr, orderOf_one] at h1
    fin_cases k <;> simp at h1
  have d01 : Disjoint {s | BabyInv 0 s ∧ BabyOrbit 0 r s} {s | BabyInv 0 s ∧ BabyOrbit 1 r s} := by
    refine Set.disjoint_left.2 fun s hs hs' => ?_
    have h0 : BabyInv 1 (r * s) := hs.2
    have h1 : BabyInv 3 (r * s) := hs'.2
    have h2 := h0.2.symm.trans h1.2
    norm_num [babyCentOrder] at h2
  have d02 : Disjoint {s | BabyInv 0 s ∧ BabyOrbit 0 r s} {s | BabyInv 0 s ∧ BabyOrbit 2 r s} := by
    refine Set.disjoint_left.2 fun s hs hs' => ?_
    have h0 : BabyInv 1 (r * s) := hs.2
    have h1 : orderOf (r * s) = 3 := hs'.2
    have h2 := h0.1.symm.trans h1
    omega
  have d03 : Disjoint {s | BabyInv 0 s ∧ BabyOrbit 0 r s} {s | BabyInv 0 s ∧ BabyOrbit 3 r s} := by
    refine Set.disjoint_left.2 fun s hs hs' => ?_
    have h0 : BabyInv 1 (r * s) := hs.2
    have h1 : orderOf (r * s) = 4 ∧ BabyInv 1 ((r * s) ^ 2) := hs'.2
    have h2 := h0.1.symm.trans h1.1
    omega
  have d12 : Disjoint {s | BabyInv 0 s ∧ BabyOrbit 1 r s} {s | BabyInv 0 s ∧ BabyOrbit 2 r s} := by
    refine Set.disjoint_left.2 fun s hs hs' => ?_
    have h0 : BabyInv 3 (r * s) := hs.2
    have h1 : orderOf (r * s) = 3 := hs'.2
    have h2 := h0.1.symm.trans h1
    omega
  have d13 : Disjoint {s | BabyInv 0 s ∧ BabyOrbit 1 r s} {s | BabyInv 0 s ∧ BabyOrbit 3 r s} := by
    refine Set.disjoint_left.2 fun s hs hs' => ?_
    have h0 : BabyInv 3 (r * s) := hs.2
    have h1 : orderOf (r * s) = 4 ∧ BabyInv 1 ((r * s) ^ 2) := hs'.2
    have h2 := h0.1.symm.trans h1.1
    omega
  have d23 : Disjoint {s | BabyInv 0 s ∧ BabyOrbit 2 r s} {s | BabyInv 0 s ∧ BabyOrbit 3 r s} := by
    refine Set.disjoint_left.2 fun s hs hs' => ?_
    have h0 : orderOf (r * s) = 3 := hs.2
    have h1 : orderOf (r * s) = 4 ∧ BabyInv 1 ((r * s) ^ 2) := hs'.2
    have h2 := h0.symm.trans h1.1
    omega
  have hcover : ∀ s ∈ {s | BabyInv 0 s}, s ≠ r →
      s ∈ {s | BabyInv 0 s ∧ BabyOrbit 0 r s} ∨ s ∈ {s | BabyInv 0 s ∧ BabyOrbit 1 r s} ∨
        s ∈ {s | BabyInv 0 s ∧ BabyOrbit 2 r s} ∨ s ∈ {s | BabyInv 0 s ∧ BabyOrbit 3 r s} := by
    intro s hs hsr
    obtain ⟨k, hk⟩ := hcov s hs hsr
    fin_cases k
    · exact Or.inl ⟨hs, hk⟩
    · exact Or.inr (Or.inl ⟨hs, hk⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hs, hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hs, hk⟩))
  exact overgroups_core hKX hKr hidx (V := {s | BabyInv 0 s}) hr
    (fun g s hs => babyInv_conj g hs)
    (fun s hs => by
      obtain ⟨c, hc⟩ := isConj_iff.1 (hT3.2 0 r s hr hs)
      exact ⟨c, hc⟩)
    (hS 0) (hS 1) (hS 2) (hS 3) hcover (hrS 0) (hrS 1) (hrS 2) (hrS 3) d01 d02 d03 d12 d13 d23
    hsimple

end CFSG.EvenSporadicStandard.Induction.Hyp
