module

public import CFSG.LieType.ChevTwo.OppCl.FormsSplitGraph

public section

namespace CFSG.LieType.ChevTwo.OppCl.FS

open CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V]

theorem exists_graph_diag (Φ : ReflForm F V) (hσ : ∀ c, Φ.σ (Φ.σ c) = c)
    (hsymm : ∀ u v, Φ.β v u = Φ.σ (Φ.β u v)) (W Cc : Submodule F V)
    (hW : Φ.IsTotallyIsotropic W) (hC : IsCompl (Φ.perp W) Cc) {ι : Type} [Fintype ι]
    [LinearOrder ι] (b : Module.Basis ι F Cc) (t : ι → F)
    (ht : ∀ i, t i + Φ.σ (t i) = Φ.β (b i : V) (b i : V)) :
    ∃ s : V →ₗ[F] V, (∀ v, s v ∈ W) ∧ (∀ v ∈ Φ.perp W, s v = 0) ∧
      (∀ i, Φ.β (b i : V) (s (b i : V)) = t i) ∧
      ∀ i j, Φ.β ((b i : V) + s (b i : V)) ((b j : V) + s (b j : V)) = 0 := by
  classical
  let h : ι → ι → F := fun i j =>
    if i = j then t i else if i < j then Φ.β (b i : V) (b j : V) else 0
  obtain ⟨s, hsW, hs0, hsb⟩ := exists_graph_halfform Φ hσ hsymm W Cc hC b h
  refine ⟨s, hsW, hs0, fun i => by simpa [h] using hsb i i, fun i j => ?_⟩
  have hss : Φ.β (s (b i : V)) (s (b j : V)) = 0 := hW (hsW _) _ (hsW _)
  have hsym : Φ.β (s (b i : V)) (b j : V) = Φ.σ (h j i) := by
    rw [hsymm (b j : V) (s (b i : V)), hsb j i]
  have hexp : Φ.β ((b i : V) + s (b i : V)) ((b j : V) + s (b j : V)) =
      Φ.β (b i : V) (b j : V) + h i j + Φ.σ (h j i) := by
    rw [Φ.add_left, Φ.add_right, Φ.add_right, hss, hsb i j, hsym]
    ring
  rw [hexp]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have h1 : h i j = Φ.β (b i : V) (b j : V) := by simp [h, hij.ne, hij]
    have h2 : h j i = 0 := by simp [h, hij.ne', hij.not_gt]
    rw [h1, h2, map_zero, add_zero]
    exact CharTwo.add_self_eq_zero _
  · have h1 : h i i = t i := by simp [h]
    rw [h1, add_assoc, ht i]
    exact CharTwo.add_self_eq_zero _
  · have h1 : h i j = 0 := by simp [h, hji.ne', hji.not_gt]
    have h2 : h j i = Φ.β (b j : V) (b i : V) := by simp [h, hji.ne, hji]
    rw [h1, h2, add_zero, ← hsymm (b j : V) (b i : V)]
    exact CharTwo.add_self_eq_zero _

end CFSG.LieType.ChevTwo.OppCl.FS
