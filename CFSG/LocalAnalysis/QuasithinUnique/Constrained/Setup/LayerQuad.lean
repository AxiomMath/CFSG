module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

@[expose] def QuadBestOffendersNormalize (k : Type*) [Field k] (V : Type v) [AddCommGroup V]
    [Module k V] : Prop :=
  ∀ G A : Subgroup (V ≃ₗ[k] V), A ≤ Subgroup.normalizer (G : Set (V ≃ₗ[k] V)) →
    CFSG.IsElementaryAbelian 2 A → QuadAct (MonoidHom.id (V ≃ₗ[k] V)) A →
    (∀ B : Subgroup (V ≃ₗ[k] V), B ≤ A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A) →
    ∀ L : Subgroup (V ≃ₗ[k] V), IsComponentIn L G → ∀ a ∈ A, conjSub a L = L

variable [CharP k 2] [Finite V]

theorem minimal_best_offenders_normalize_components (hQ : QuadBestOffendersNormalize k V)
    {G A : Subgroup (V ≃ₗ[k] V)} (hAG : A ≤ Subgroup.normalizer (G : Set (V ≃ₗ[k] V)))
    (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[k] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B < weight (MonoidHom.id (V ≃ₗ[k] V)) A) :
    QuadAct (MonoidHom.id (V ≃ₗ[k] V)) A ∧
      ∀ L : Subgroup (V ≃ₗ[k] V), IsComponentIn L G → ∀ a ∈ A, conjSub a L = L := by
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have : Finite ↥A := inferInstance
  have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).2 hAne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax : ∀ B : Subgroup (V ≃ₗ[k] V), B ≤ A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A := by
    intro B hB
    rcases hB.lt_or_eq with hlt | heq
    · by_cases hbot : B = ⊥
      · rw [hbot, weight_bot]
        exact hoff
      · exact (hstrict B (bot_lt_iff_ne_bot.2 hbot) hlt).le
    · rw [heq]
  let ρ : ↥A →* (V ≃ₗ[k] V) := (MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype
  have hab : ∀ x y : ↥A, x * y = y * x := fun x y =>
    (IsMulCommutative.is_comm (M := ↥A)).comm x y
  have hp : IsPGroup 2 ↥A := CFSG.IsElementaryAbelian.isPGroup 2 A
  have hρ : Nat.card V ≤ weight ρ ⊤ := by
    have := weight_comp_subtype (MonoidHom.id (V ≃ₗ[k] V)) A ⊤
    rw [map_subtype_top] at this
    rw [this]
    exact hoff
  obtain ⟨B, hBbot, hw, -, -, hquad, -⟩ := abelian_prime_offender_quadratic_replacement ρ hab hp hρ
  have hBtop : B = ⊤ := by
    by_contra hne
    have hlt : B < ⊤ := lt_top_iff_ne_top.2 hne
    have h1 : ⊥ < B.map A.subtype := by
      rw [bot_lt_iff_ne_bot]
      intro h0
      apply hBbot
      rw [Subgroup.map_eq_bot_iff_of_injective B A.subtype_injective] at h0
      exact h0
    have h2 : B.map A.subtype < A := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le B) ?_
      intro heq
      apply hne
      have : B.map A.subtype = (⊤ : Subgroup ↥A).map A.subtype := by
        rw [map_subtype_top]
        exact heq
      exact Subgroup.map_injective A.subtype_injective this
    have h3 := hstrict _ h1 h2
    have e1 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[k] V)) A B
    have e2 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[k] V)) A ⊤
    rw [map_subtype_top] at e2
    have hw' : weight ρ ⊤ ≤ weight ρ B := hw
    have : weight (MonoidHom.id (V ≃ₗ[k] V)) A ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) (B.map A.subtype) := by
      rw [← e1, ← e2]
      exact hw'
    omega
  subst hBtop
  have hquadA : QuadAct (MonoidHom.id (V ≃ₗ[k] V)) A := by
    intro b hb c hc w
    exact hquad ⟨b, hb⟩ trivial ⟨c, hc⟩ trivial w
  exact ⟨hquadA, fun L hL a ha => hQ G A hAG hAel hquadA hmax L hL a ha⟩

end CFSG.QuasithinUnique.Setup.Layer
