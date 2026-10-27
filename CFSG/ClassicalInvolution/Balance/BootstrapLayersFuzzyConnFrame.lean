module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnLink

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames fuzzyVertices card_closure_pair_le_four card_closure_singleton_le_two)

section Classes

variable {G : Type} [Group G] {a : G}

theorem SameClass.symm (ha2 : a * a = 1) {t u : G} (h : SameClass a t u) : SameClass a u t := by
  obtain ⟨n, hn, h | h⟩ := h
  · exact ⟨n⁻¹, inv_mem hn, Or.inl (by rw [h]; group)⟩
  · refine ⟨n⁻¹, inv_mem hn, Or.inr ?_⟩
    calc t = (a * a) * t := by rw [ha2, one_mul]
      _ = a * (a * t * n) * n⁻¹ := by group
      _ = a * u * n⁻¹ := by rw [h]

theorem SameClass.trans (ha2 : a * a = 1) {t u w : G} (h₁ : SameClass a t u)
    (h₂ : SameClass a u w) : SameClass a t w := by
  obtain ⟨n, hn, h₁ | h₁⟩ := h₁ <;> obtain ⟨m, hm, h₂ | h₂⟩ := h₂
  · exact ⟨n * m, mul_mem hn hm, Or.inl (by rw [h₂, h₁]; group)⟩
  · exact ⟨n * m, mul_mem hn hm, Or.inr (by rw [h₂, h₁]; group)⟩
  · exact ⟨n * m, mul_mem hn hm, Or.inr (by rw [h₂, h₁]; group)⟩
  · refine ⟨n * m, mul_mem hn hm, Or.inl ?_⟩
    calc w = a * (a * t * n) * m := by rw [h₂, h₁]
      _ = (a * a) * t * (n * m) := by group
      _ = t * (n * m) := by rw [ha2, one_mul]

variable [Finite G]

theorem eq_one_of_mem_involutionOddCore_of_sq {x : G} (hx : x ∈ involutionOddCore a)
    (hsq : x * x = 1) : x = 1 := by
  rw [involutionOddCore_eq_oddCoreIn] at hx
  have h1 : Odd (orderOf x) :=
    (odd_card_oddCoreIn _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h1
    exact absurd h1 (by decide)

end Classes

section Basis

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)}

theorem exists_vertex_notMem_of_fuzzyFrameOn {A : Subgroup G} (h : FuzzyFrameOn p f 𝒞 A)
    {H : Subgroup G} (hH : Nat.card H < 8) :
    ∃ (J : Subgroup G) (t : G), J ∈ 𝒞 ∧ IsClassicalMember p f J t ∧ t ∈ A ∧ t ∉ H ∧
      A ≤ trivialOnQuot J := by
  obtain ⟨J, z, hJ, hAdef, -, hcard, htriv⟩ := h
  by_contra hcon
  push Not at hcon
  have hle : A ≤ H := by
    rw [hAdef, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    by_contra hnot
    exact hcon (J i) (z i) (hJ i).1 (hJ i).2 (hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩) hnot
      (htriv i)
  have := Subgroup.card_le_of_le hle
  omega

structure FrameBasis (p f : ℕ) [Fact p.Prime] (𝒞 : Set (Subgroup G)) (a : G) (B J : Subgroup G)
    (t : G) (N : Subgroup G) (u : G) : Prop where
  frame : FuzzyFrameOn p f 𝒞 B
  vertex : a ∈ fuzzyVertices p f 𝒞 B
  memJ : J ∈ 𝒞
  clsJ : IsClassicalMember p f J t
  memN : N ∈ 𝒞
  clsN : IsClassicalMember p f N u
  tB : t ∈ B
  uB : u ∈ B
  tqJ : B ≤ trivialOnQuot J
  tqN : B ≤ trivialOnQuot N
  ta : t ≠ a
  uni : u ∉ Subgroup.closure ({a, t} : Set G)

theorem exists_frameBasis {B : Subgroup G} (hB : FuzzyFrameOn p f 𝒞 B) {a : G}
    (haB : a ∈ fuzzyVertices p f 𝒞 B) :
    ∃ (J : Subgroup G) (t : G) (N : Subgroup G) (u : G), FrameBasis p f 𝒞 a B J t N u := by
  have hB' := hB
  obtain ⟨-, -, -, -, hel, -, -⟩ := hB'
  have hcomm : ∀ {x y : G}, x ∈ B → y ∈ B → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hx⟩ : B) ⟨_, hy⟩)
  have hsq : ∀ {x : G}, x ∈ B → x * x = 1 := fun hx => by
    rw [← pow_two]
    exact hel.2 _ hx
  have ha2 : a * a = 1 := hsq haB.1
  obtain ⟨J, t, hJ𝒞, hJ, htB, htH, hBJ⟩ := exists_vertex_notMem_of_fuzzyFrameOn hB
    (H := Subgroup.closure ({a} : Set G)) (by have := card_closure_singleton_le_two ha2; omega)
  have hta : t ≠ a := fun h => htH (h ▸ Subgroup.subset_closure rfl)
  have h4 : Nat.card (Subgroup.closure ({a, t} : Set G)) ≤ 4 :=
    card_closure_pair_le_four ha2 (hsq htB) (hcomm haB.1 htB)
  obtain ⟨N, u, hN𝒞, hN, huB, huH, hBN⟩ := exists_vertex_notMem_of_fuzzyFrameOn hB
    (H := Subgroup.closure ({a, t} : Set G)) (by omega)
  exact ⟨J, t, N, u, ⟨hB, haB, hJ𝒞, hJ, hN𝒞, hN, htB, huB, hBJ, hBN, hta, huH⟩⟩

namespace FrameBasis

variable {B J N : Subgroup G} {a t u : G} (hb : FrameBasis p f 𝒞 a B J t N u)
include hb

theorem comm {x y : G} (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x := by
  obtain ⟨-, -, -, -, hel, -, -⟩ := hb.frame
  exact congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hx⟩ : B) ⟨_, hy⟩)

theorem sq {x : G} (hx : x ∈ B) : x * x = 1 := by
  obtain ⟨-, -, -, -, hel, -, -⟩ := hb.frame
  rw [← pow_two]
  exact hel.2 _ hx

theorem aB : a ∈ B := hb.vertex.1

theorem t_ne_one : t ≠ 1 := hb.clsJ.isCentralInvolution.ne_one

theorem u_ne_one : u ≠ 1 := hb.clsN.isCentralInvolution.ne_one

theorem u_ne_a : u ≠ a := fun h => hb.uni (h ▸ Subgroup.subset_closure (by simp))

theorem u_ne_t : u ≠ t := fun h => hb.uni (h ▸ Subgroup.subset_closure (by simp))

theorem tu_ne_a : t * u ≠ a := by
  intro h
  apply hb.uni
  have hu : u = t * a := by
    calc u = t * (t * u) := by rw [← mul_assoc, hb.sq hb.tB, one_mul]
      _ = t * a := by rw [h]
  rw [hu]
  exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem tu_ne_one : t * u ≠ 1 := by
  intro h
  apply hb.u_ne_t
  calc u = t * (t * u) := by rw [← mul_assoc, hb.sq hb.tB, one_mul]
    _ = t := by rw [h, mul_one]

theorem not_sameClass : ¬ SameClass a t u := by
  rintro ⟨n, hn, h | h⟩
  · have hnB : n = t * u := by
      rw [h, ← mul_assoc, hb.sq hb.tB, one_mul]
    have hn1 := eq_one_of_mem_involutionOddCore_of_sq hn (hb.sq (hnB ▸ mul_mem hb.tB hb.uB))
    rw [hn1, mul_one] at h
    exact hb.u_ne_t h
  · have hnB : n = t * a * u := by
      rw [h]
      calc n = (t * t) * n := by rw [hb.sq hb.tB, one_mul]
        _ = t * (a * a) * (t * n) := by rw [hb.sq hb.aB, mul_one, ← mul_assoc]
        _ = t * a * (a * t * n) := by group
    have hmem : n ∈ B := hnB ▸ mul_mem (mul_mem hb.tB hb.aB) hb.uB
    have hn1 := eq_one_of_mem_involutionOddCore_of_sq hn (hb.sq hmem)
    rw [hn1, mul_one] at h
    exact hb.uni (h ▸ mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))

end FrameBasis

end Basis

end CFSG.ClassicalInvolution.Balance.Bootstrap
