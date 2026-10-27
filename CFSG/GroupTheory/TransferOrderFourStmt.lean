module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.GroupTheory.TransferOrderFour

@[expose] def TransferCoreStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {A : Type} [CommGroup A] {k : G}, orderOf k = 4 →
    Subgroup.centralizer {k ^ 2} ≤ Subgroup.normalizer (Subgroup.zpowers k : Set G) →
    ∀ {T : Subgroup G}, IsPGroup 2 T → T ≤ Subgroup.centralizer {k ^ 2} →
      Odd (T.relIndex (Subgroup.centralizer {k ^ 2})) → ∀ (hkT : k ∈ T) (ψ : T →* A),
      (∀ (u : G) (hu : u ∈ T), IsConj (k ^ 2) u →
          ψ ⟨u, hu⟩ = 1 ∨ 4 ∣ Nat.card (MulAction.orbit (ConjAct T) (⟨u, hu⟩ : T))) →
      ∀ c : A, c ^ 2 = 1 →
      (∀ (g : G) (h : g⁻¹ * k * g ∈ T), g⁻¹ * k * g ∉ Subgroup.zpowers k → ψ ⟨_, h⟩ = c) →
      Even (Nat.card {X : Subgroup G // (∃ g : G, X = Subgroup.zpowers (g⁻¹ * k * g)) ∧
        X ≤ T ∧ X ≠ Subgroup.zpowers k}) →
      ψ.transfer k = ψ ⟨k, hkT⟩

theorem eq_one_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G] {A : Type*} [CommGroup A]
    (hna : ∃ a b : G, a * b ≠ b * a) (f : G →* A) (g : G) : f g = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    apply (MonoidHom.ker_eq_bot_iff f).mp h
    rw [map_mul, map_mul, mul_comm]
  · exact (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top g)

end CFSG.GroupTheory.TransferOrderFour
