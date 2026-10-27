module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GramClassify
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GramSwitch
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.FixedDiagonal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.Twist

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_normal_vector (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (B : LinearMap.BilinForm (ZMod 2) V)
    (hS : Swap.StdHyp σ) (hF : FormHyp σ B) :
    ∃ (β : A5 ≃* A5) (v : V), v ≠ 0 ∧ (∀ x : A5, twist σ β (x, x) v = v) ∧
      gramF (twist σ β) B v = gramFn b₁ := by
  obtain ⟨v, hv0, S, hSv, hSA⟩ :=
    (irreducible_iff_exists_stabilizer σ hS.inj hS.finrank_eq).mp hS.irr
  obtain ⟨β, hβ⟩ := exists_fixed_graph σ hS v hv0 S hSv hSA
  have hS₁ : Swap.StdHyp (twist σ β) := Swap.StdHyp.twist hS β
  have hF₁ : FormHyp (twist σ β) B := FormHyp.twist hF β
  have hfix : ∀ x : A5, twist σ β (x, x) v = v := by
    intro x
    rw [twist_apply]
    exact hβ x
  have hconj : ∀ x y : A5,
      gramF (twist σ β) B v (y * x * y⁻¹) = gramF (twist σ β) B v x :=
    gramF_conj (twist σ β) B v hF₁ hfix
  have h1 : gramF (twist σ β) B v 1 = 0 := gramF_one (twist σ β) B v hF₁
  have hne : gramF (twist σ β) B v ≠ 0 :=
    gramF_ne_zero (twist σ β) B v hS₁ hF₁ hfix hv0
  have hrank : ∀ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
      (Matrix.of fun i j => gramF (twist σ β) B v ((R i)⁻¹ * C j)) * N ≠ 1 :=
    no_right_inverse (twist σ β) B v hS₁ hF₁
  rcases gram_classify (gramF (twist σ β) B v) hconj h1 hne hrank with hf | hf | hf
  · exact ⟨β, v, hv0, hfix, hf⟩
  · obtain ⟨v', hv'0, hv'fix, hv'F⟩ :=
      gram_switch (twist σ β) B hS₁ hF₁ v hfix hv0 _ (Or.inl rfl) hf
    exact ⟨β, v', hv'0, hv'fix, hv'F⟩
  · obtain ⟨v', hv'0, hv'fix, hv'F⟩ :=
      gram_switch (twist σ β) B hS₁ hF₁ v hfix hv0 _ (Or.inr rfl) hf
    exact ⟨β, v', hv'0, hv'fix, hv'F⟩

end CFSG.EvenSporadicStandard.HNRecog.ML1
