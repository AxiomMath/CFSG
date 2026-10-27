module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBEigen

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic (Commutes)

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem negSpace_le_eigenspace_neg_of_fixed (hodd : Odd (Nat.card K)) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hdimE : Module.finrank K ↥(Module.End.eigenspace (g : Module.End K V) 1) = 3)
    {X : Subgroup (V ≃ₗ[K] V)} {iX : V ≃ₗ[K] V} (hX : IsFundamental Q X iX)
    (hfix : ∀ l ∈ X, g * l = l * g) :
    negSpace iX ≤ Module.End.eigenspace (g : Module.End K V) (-1) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  rcases negSpace_le_eigenspace_of_commute h2 hX hgO hg2 hfix with h | h
  · exfalso
    have h1 := Submodule.finrank_mono h
    rw [hdimE, finrank_negSpace hodd hX] at h1
    omega
  · exact h

theorem finrank_negSpace_sup (hodd : Odd (Nat.card K)) {L L' : Subgroup (V ≃ₗ[K] V)}
    {i i' : V ≃ₗ[K] V} (hL : IsFundamental Q L i) (hL' : IsFundamental Q L' i')
    (horth : ∀ x ∈ negSpace i, ∀ y ∈ negSpace i', polar Q x y = 0) :
    Module.finrank K ↥(negSpace i ⊔ negSpace i') = 8 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hdisj : Disjoint (negSpace i) (negSpace i') := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    refine eq_zero_of_polar_negSpace h2 hL hx fun y hy => ?_
    rw [polar_comm]
    exact horth y hy x hx'
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (negSpace i) (negSpace i')
  rw [hdisj.eq_bot, finrank_bot, finrank_negSpace hodd hL, finrank_negSpace hodd hL'] at hsup
  omega

theorem polar_negSpace_of_adj_commute (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {X Y D : Subgroup (V ≃ₗ[K] V)} {iX iY iD : V ≃ₗ[K] V} (hX : IsFundamental Q X iX)
    (hY : IsFundamental Q Y iY) (hD : IsFundamental Q D iD) (hXY : Commutes X Y)
    (hDY : ModelAdj (scalars K V) D Y) (hDX : Commutes D X) :
    ∀ x ∈ negSpace iX, ∀ y ∈ negSpace iY, polar Q x y = 0 :=
  polar_negSpace_of_distinguish hodd hdim hX hY hD hXY
    (fun e => hDY.2.1 (by rw [e]; exact hXY)) hDY.1
    (modelInvComm_of_commutes hodd hD hX hDX) (ModelInvComm.of_adj hDY)
    (fun hiff => hDY.2.1 (hiff.mp hDX))

theorem model_contradiction_of_span (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hdimE : Module.finrank K ↥(Module.End.eigenspace (g : Module.End K V) 1) = 3)
    {S : Submodule K V} (hS : S ≤ Module.End.eigenspace (g : Module.End K V) (-1))
    (hdimS : Module.finrank K V ≤ Module.finrank K ↥S + 7)
    {Y : Fin 3 → Subgroup (V ≃ₗ[K] V)} {iY : Fin 3 → V ≃ₗ[K] V}
    (hY : ∀ k, IsFundamental Q (Y k) (iY k)) (hYinj : Function.Injective Y)
    (hfixY : ∀ k, ∀ l ∈ Y k, g * l = l * g)
    (hYS : ∀ k, ∀ y ∈ negSpace (iY k), ∀ s ∈ S, polar Q y s = 0) : False := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  set Em := Module.End.eigenspace (g : Module.End K V) (-1) with hEm
  have hSig : ∀ s ∈ S, ∀ y ∈ Module.End.eigenspace (g : Module.End K V) 1, polar Q y s = 0 := by
    intro s hs y hy
    have hy' : g y = y := by
      rwa [Module.End.mem_eigenspace_iff, one_smul] at hy
    have hs' : g s = -s := by
      have := hS hs
      rwa [hEm, Module.End.mem_eigenspace_iff, neg_smul, one_smul] at this
    exact polar_eigenspace_orth h2 hgO hy' hs'
  have hcount := finrank_eigen_inf_orth_le hQ h2 hSig
  rw [hdimE] at hcount
  set P := Em ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) S with hP
  have hP4 : Module.finrank K ↥P ≤ 4 := by omega
  have hYP : ∀ k, negSpace (iY k) = P := by
    intro k
    have hle : negSpace (iY k) ≤ P := by
      refine le_inf (negSpace_le_eigenspace_neg_of_fixed hodd hgO hg2 hdimE (hY k) (hfixY k)) ?_
      intro y hy
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro s hs
      show polarBilin Q s y = 0
      rw [polarBilin_apply_apply, polar_comm]
      exact hYS k y hy s hs
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [finrank_negSpace hodd (hY k)]
    exact hP4
  have hii : ∀ k, iY k = iY 0 := fun k =>
    involution_eq_of_negSpace_eq h2 (hY k) (hY 0) (by rw [hYP k, hYP 0])
  obtain ⟨L', hL', hne, -, huniq⟩ := IsFundamental.exists_twin hodd (hY 0)
  have h1 : Y 1 = Y 0 ∨ Y 1 = L' := huniq _ (by rw [← hii 1]; exact hY 1)
  have h2'' : Y 2 = Y 0 ∨ Y 2 = L' := huniq _ (by rw [← hii 2]; exact hY 2)
  have n10 : Y 1 ≠ Y 0 := fun h => by have := hYinj h; simp at this
  have n20 : Y 2 ≠ Y 0 := fun h => by have := hYinj h; simp at this
  have n21 : Y 2 ≠ Y 1 := fun h => by have := hYinj h; simp at this
  rcases h1 with h1 | h1
  · exact n10 h1
  · rcases h2'' with h2'' | h2''
    · exact n20 h2''
    · exact n21 (h2''.trans h1.symm)

end CFSG.ClassicalInvolution.RouteD.Gaps
