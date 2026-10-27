module

public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.TwoWeightData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP

open Subgroup CFSG.GroupTheory.TwoWeights

theorem exists_data_of_model {X G : Type*} [Group X] [Finite X] [Group G] (e : X ≃* G)
    (hconj : ∀ u v : X, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    {m : ℕ} (hfact : (Nat.card X).factorization 2 = m) {a u₁ u₂ u₃ x y : G}
    (ha : orderOf a = 2)
    (D : Data a u₁ u₂ u₃ x y) {A : Subgroup X} (hA : Nat.card ↥A = 2 ^ m) {τ : X}
    (_hτA : τ ∈ A) (hτ2 : orderOf τ = 2) (hτc : ∀ g ∈ A, g * τ = τ * g) :
    ∃ u₁' u₂' u₃' x' y' : X, u₁' ∈ A ∧ u₂' ∈ A ∧ u₃' ∈ A ∧ x' ∈ A ∧ y' ∈ A ∧
      Data τ u₁' u₂' u₃' x' y' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 X := Sylow.ofCard A (by rw [hA, hfact])
  have hSA : (S : Subgroup X) = A := Sylow.coe_ofCard A _
  have hord : orderOf (e.symm a) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha
  obtain ⟨c, hc⟩ := isConj_iff.1 (hconj _ _ hord hτ2)
  let φ : G ≃* X := e.symm.trans (MulAut.conj c)
  have hφa : φ a = τ := hc
  have hB2 : IsPGroup 2 ↥(Subgroup.closure ({u₁, u₂, u₃, a, x, y} : Set G)) :=
    D.isPGroup_closure
  have hB'2 : IsPGroup 2 ↥((Subgroup.closure ({u₁, u₂, u₃, a, x, y} : Set G)).map
      φ.toMonoidHom) := hB2.map φ.toMonoidHom
  have hB'K : (Subgroup.closure ({u₁, u₂, u₃, a, x, y} : Set G)).map φ.toMonoidHom ≤
      Subgroup.centralizer ({τ} : Set X) := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (D.closure_le_centralizer hb)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show φ b * τ = τ * φ b
    rw [← hφa, ← map_mul, ← map_mul, h1]
  have hSK : (S : Subgroup X) ≤ Subgroup.centralizer ({τ} : Set X) := by
    rw [hSA]
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hτc g hg
  obtain ⟨k, hkK, hk⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    (Subgroup.centralizer ({τ} : Set X)) S hSK _ hB'K hB'2
  let ψ : G →* X := ((MulAut.conj k).toMonoidHom).comp φ.toMonoidHom
  have hψ : ∀ g, ψ g = k * φ g * k⁻¹ := fun g => rfl
  have hψa : ψ a = τ := by
    rw [hψ, hφa]
    have h1 : k * τ = τ * k := Subgroup.mem_centralizer_singleton_iff.1 hkK
    rw [h1]
    group
  have hgen : ∀ g ∈ ({u₁, u₂, u₃, a, x, y} : Set G), ψ g ∈ A := by
    intro g hg
    rw [← hSA]
    exact hk ⟨φ g, ⟨g, Subgroup.subset_closure hg, rfl⟩, rfl⟩
  have D' := D.map ψ
  rw [hψa] at D'
  exact ⟨ψ u₁, ψ u₂, ψ u₃, ψ x, ψ y, hgen _ (by simp), hgen _ (by simp), hgen _ (by simp),
    hgen _ (by simp), hgen _ (by simp), D'⟩

theorem card_lt_pow_eight {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {N : ℕ} (hN : Nat.card Y = N) (hnd : ∀ q : ℕ, 3 ≤ q → ¬ q ^ 8 ∣ N) {X : Subgroup Y}
    (hX : IsPGroup p ↥X) : Nat.card ↥X < p ^ 8 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).1 hX
  have hdvd : Nat.card ↥X ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card X
  rw [hk, hN] at hdvd
  rw [hk]
  refine Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt ?_
  by_contra hk8
  have h8 : p ^ 8 ∣ p ^ k := pow_dvd_pow p (by omega)
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  exact hnd p hp3 (h8.trans hdvd)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP
