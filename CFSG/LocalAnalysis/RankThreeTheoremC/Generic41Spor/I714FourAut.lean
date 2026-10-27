module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.AGLEmbedding.TwoGenInner (PGoodOut)
open scoped commutatorElement

variable {X : Type*} [Group X] {K : Subgroup X} [K.Normal]

theorem mem_of_conjNormal_mem_inner (hC : Subgroup.centralizer (K : Set X) = ⊥) {x : X}
    (h : MulAut.conjNormal (H := K) x ∈ inner K) : x ∈ K := by
  obtain ⟨k, hk⟩ := h
  have hcomm : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut K => (φ ⟨y, hy⟩ : X)) hk
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at h1
    have h2 : (k : X) * y * (k : X)⁻¹ = x * y * x⁻¹ := by simpa using h1
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
      _ = ((k : X)⁻¹ * x) * y := by group
  rw [hC, Subgroup.mem_bot] at hcomm
  have hx : x = k := by
    calc x = (k : X) * ((k : X)⁻¹ * x) := by group
      _ = k := by rw [hcomm, mul_one]
  rw [hx]
  exact k.2

theorem mem_of_pow_eq_one_of_not_dvd_outer {p : ℕ} (hp : p.Prime)
    (hout : ¬ p ∣ Nat.card (Outer ↥K)) (hC : Subgroup.centralizer (K : Set X) = ⊥) {x : X}
    {m : ℕ} (hx : x ^ (p ^ m) = 1) : x ∈ K := by
  apply mem_of_conjNormal_mem_inner hC
  set α : MulAut ↥K := MulAut.conjNormal (H := K) x with hα
  have hαp : α ^ (p ^ m) = 1 := by rw [hα, ← map_pow, hx, map_one]
  have h1 : (QuotientGroup.mk α : Outer ↥K) ^ (p ^ m) = 1 := by
    rw [← QuotientGroup.mk_pow, hαp]
    rfl
  have hd1 : orderOf (QuotientGroup.mk α : Outer ↥K) ∣ p ^ m := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf (QuotientGroup.mk α : Outer ↥K) ∣ Nat.card (Outer ↥K) :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ m) (Nat.card (Outer ↥K)) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hout)
  have h2 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp h2)

theorem commutator_mem_of_pGoodOut {p : ℕ} (hP : PGoodOut p ↥K)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {x y : X} {m n : ℕ} (hx : x ^ (p ^ m) = 1)
    (hxy : ⁅y, x⁆ ^ (p ^ n) = 1) : ⁅y, x⁆ ∈ K := by
  obtain ⟨D, -, -, hD2, hD3⟩ := hP
  apply mem_of_conjNormal_mem_inner hC
  have hα : (MulAut.conjNormal (H := K) x) ^ (p ^ m) ∈ D := by
    rw [← map_pow, hx, map_one]
    exact D.one_mem
  have hmem : ⁅MulAut.conjNormal (H := K) y, MulAut.conjNormal (H := K) x⁆ ∈ D :=
    hD3 _ _ ⟨m, hα⟩
  rw [← map_commutatorElement] at hmem
  refine hD2 _ hmem n ?_
  rw [← map_pow, hxy, map_one]
  exact (inner K).one_mem

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
