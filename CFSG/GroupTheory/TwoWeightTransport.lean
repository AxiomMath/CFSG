module

public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.TwoWeightCard

public section

namespace CFSG.GroupTheory.TwoWeights

theorem star_of_model {X G : Type*} [Group X] [Finite X] [Group G] (e : X ≃* G)
    (hconj : ∀ u v : X, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    (hfact : (Nat.card X).factorization 2 = 8) {a u₁ u₂ u₃ x y : G} (ha : orderOf a = 2)
    (D : Data a u₁ u₂ u₃ x y) {A W : Subgroup X} (hA : Nat.card ↥A = 2 ^ 8) {τ : X}
    (hτA : τ ∈ A) (hτ2 : orderOf τ = 2) (hτc : ∀ g ∈ A, g * τ = τ * g)
    (hW : IsPGroup 3 ↥W) (hW1 : W ≠ ⊥) (hAW : A ≤ Subgroup.normalizer (W : Set X))
    (hC : W ⊓ Subgroup.centralizer ({τ} : Set X) = ⊥) : 3 ^ 8 ∣ Nat.card X := by
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
  exact star_core D' (hgen _ (by simp)) (hgen _ (by simp)) (hgen _ (by simp)) hτA
    (hgen _ (by simp)) (hgen _ (by simp)) hW hW1 hAW hC

end CFSG.GroupTheory.TwoWeights
