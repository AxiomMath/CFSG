module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2H1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Adapt

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem list_prod_blkN (C : Fin 12 → Mat9) (w : List (Fin 12)) :
    (w.map fun s => blkN (n := 9) (genA s) (C s)).prod =
      blkN (n := 9) (urMat9 C w).1 (urMat9 C w).2 := by
  induction w with
  | nil => exact blkN_one.symm
  | cons s w ih => rw [List.map_cons, List.prod_cons, ih, blkN_mul]; rfl

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {Γ : Type*} [Group Γ]

theorem exists_good_coords18 (π : Γ →* (W →ₗ[ZMod 2] W)) (θ : SL3 →* Γ)
    (τ : W →ₗ[ZMod 2] W) (ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W) (hι : Function.Injective ι)
    (hτι : ∀ u, τ (ι u) = ι u) (hrange : ∀ u, ∃ x, τ x + x = ι u)
    (hW : Nat.card W = 2 ^ (9 + 9)) (hπτ : ∀ g x, τ (π (θ g) x) = π (θ g) (τ x))
    (hπι : ∀ g u, π (θ g) (ι u) = ι (rhoA g *ᵥ u)) :
    ∃ e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2), matOfN e τ = tMN 9 ∧
      ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g) := by
  choose w hw using fun j : Fin 9 => hrange (Pi.single j 1)
  set e₀ := (adaptedEquivN hτι hw hι hW).symm with he₀
  have hblk : ∀ g, matOfN e₀ (π (θ g)) =
      blkN (rhoA g) (urBlockN (matOfN e₀ (π (θ g)))) := fun g =>
    matOfN_eq_blkN hτι hw hι hW (hπι g) (hπτ g)
  set C : Fin 12 → Mat9 := fun s => urBlockN (matOfN e₀ (π (θ (gen3 s)))) with hC
  have hgen : ∀ s, matOfN e₀ (π (θ (gen3 s))) = blkN (genA s) (C s) := fun s => by
    rw [hblk, rhoA_gen3]
  have hrel : ∀ w ∈ h1Rels3, (urMat9 C w).2 = 0 := by
    intro w hw'
    have h1 : (w.map fun s => θ (gen3 s)).prod = 1 := by
      have := congrArg θ (prod_gen3_eq_one hw')
      rwa [map_list_prod, map_one, List.map_map] at this
    have h2 := congrArg (fun g => matHomN e₀ (π g)) h1
    simp only [map_list_prod, map_one, List.map_map] at h2
    have h3 : (w.map fun s => blkN (n := 9) (genA s) (C s)).prod = 1 := by
      rw [← h2]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      exact (hgen s).symm
    rw [list_prod_blkN] at h3
    have := congrArg urBlockN h3
    rw [blkN_urBlockN] at this
    rw [this, urBlockN_one]
  obtain ⟨X, hX⟩ := exists_coboundary9 C hrel
  refine ⟨e₀.trans (shearEquivN X), ?_, ?_⟩
  · rw [matOfN_shear, he₀, matOfN_tau, tMN, blkN_mul, blkN_mul]
    simp only [one_mul, mul_one]
    congr 1
    rw [show X + (1 + X) = (X + X) + 1 by abel, matN_add_self, zero_add]
  · set e := e₀.trans (shearEquivN X) with he
    have hgens : ∀ s, matOfN e (π (θ (gen3 s))) = rhoN (rhoA (gen3 s)) := by
      intro s
      rw [he, matOfN_shear, hgen s, shearN_conj _ _ _ (hX s), rhoA_gen3]
    let f₁ : SL3 →* Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2) :=
      ((matHomN e).comp π).comp θ
    let f₂ : SL3 →* Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2) :=
      { toFun := fun g => rhoN (rhoA g)
        map_one' := by rw [map_one, rhoN_one]
        map_mul' := fun g h => by rw [map_mul, rhoN_mul] }
    have hf : f₁ = f₂ := hom_ext_gen3 hgens
    intro g
    exact DFunLike.congr_fun hf g

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
