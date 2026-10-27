module

public import CFSG.ClassicalInvolution.Asc77.AscT7XFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

@[expose] def TrivMu {G : Type} [Group G] (Ω : Set (Subgroup G)) (W : Subgroup G) (y : G) :
    Prop :=
  ∀ m ∈ MGrp Ω W, y * m * y⁻¹ * m⁻¹ ∈ W ⊔ OCW W

variable (p f : ℕ) [Fact p.Prime]

@[expose] def H3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp23Setting p f Ω K K' z → Hyp24Data Ω K K' W S R R' z u → Nat.card ↥R = 8 →
    ∀ D : T7X.Frame24 p f Ω W, D.F.ρ.K = K → D.F.ρ'.K = K' → D.F.ρ.R = R → D.F.ρ'.R = R' →
      ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
        R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ D.F.ρ₃.K →
        T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1

@[expose] def NoGraph : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp23Setting p f Ω K K' z → Hyp24Data Ω K K' W S R R' z u → Nat.card ↥R = 8 →
      ∀ y ∈ (S : Subgroup G), TrivMu Ω W y → y ∈ Subgroup.centralizer (W : Set G)

end S24B

end CFSG.ClassicalInvolution.Asc77
