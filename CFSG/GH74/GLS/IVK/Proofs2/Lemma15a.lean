module

public import CFSG.GH74.GLS.IVK.Proofs2.TwoTori
public import CFSG.GH74.GLS.IVK.Proofs2.NoOuter

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

section Xu15a

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem mem_fixedSubgroup_iff' {u : MulAut K} {x : K} : x ∈ fixedSubgroup K u ↔ u x = x := Iff.rfl

omit [Finite K] in
theorem apply_mem_fixedSubgroup_of_commute {u σ : MulAut K} (hc : σ * u = u * σ) {x : K}
    (hx : x ∈ fixedSubgroup K u) : σ x ∈ fixedSubgroup K u := by
  rw [mem_fixedSubgroup_iff'] at hx ⊢
  have h : (u * σ) x = (σ * u) x := by rw [hc]
  rw [MulAut.mul_apply, MulAut.mul_apply, hx] at h
  exact h

theorem apply_mem_xu {u σ : MulAut K} (hc : σ * u = u * σ) {x : K} (hx : x ∈ xu u) : σ x ∈ xu u := by
  obtain ⟨c, hc', rfl⟩ := hx
  let ρ : MulAut ↥(fixedSubgroup K u) :=
    restrictAut σ (fixedSubgroup K u) (fun m hm => apply_mem_fixedSubgroup_of_commute hc hm)
  have hfix := (inferInstance : (pPrimeCore 2 ↥(fixedSubgroup K u)).Characteristic).fixed ρ
  have h2 : c ∈ (pPrimeCore 2 ↥(fixedSubgroup K u)).comap ρ.toMonoidHom := by rw [hfix]; exact hc'
  exact ⟨ρ c, h2, rfl⟩

omit [Finite K] in
theorem xu_le_fixedSubgroup (u : MulAut K) : xu u ≤ fixedSubgroup K u :=
  Subgroup.map_subtype_le _

theorem xu_outer_data (hF : L2Field F) (e : K ≃* L2 F) {v : MulAut K} (hv : v ∈ innDiagSub e)
    (hv' : v ∉ innAut K) (hv2 : orderOf v = 2) :
    IsCyclic ↥(xu v) ∧ Odd (Nat.card ↥(xu v)) ∧ 3 ≤ Nat.card ↥(xu v) ∧
      (2 * Nat.card ↥(xu v) = Nat.card F + 1 ∨ 2 * Nat.card ↥(xu v) + 1 = Nat.card F) := by
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    by_cases h : t % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  have hq5 : 5 ≤ Nat.card F := by
    obtain ⟨⟨t, ht⟩, h3⟩ := hF
    omega
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
    ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3b F hF K e ε hε1 hε d hd v hv hv' hv2).2.1
  have hkodd : Odd k := by
    refine Nat.odd_iff.mpr ?_
    rcases hε1 with rfl | rfl <;> unfold Int.ModEq at hε <;> omega
  have : NeZero k := ⟨by omega⟩
  have hcard : Nat.card ↥(xu v) = k := by
    rw [xu, Subgroup.card_map_of_injective (fixedSubgroup K v).subtype_injective]
    exact pPrimeCore_dihedral_odd hkodd ψ
  refine ⟨(Lemma118.xu_of_dihedral v hk2 hkodd (by omega) dvd_rfl ψ).2, hcard ▸ hkodd, ?_, ?_⟩
  · rw [hcard]
    obtain ⟨j, hj⟩ := hkodd
    omega
  · rw [hcard]
    rcases hε1 with rfl | rfl
    · left
      omega
    · right
      omega

end Xu15a

end CFSG.GH74.GLS.IVK.Proofs2
