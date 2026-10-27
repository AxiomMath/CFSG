module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDUniq
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDEnd
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDRed

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section Final

variable {p n : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]

theorem descent_exists (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (σ : Representation (ZMod p) (SLm F) W)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) (hnt : ∃ g, σ g ≠ 1) :
    ∃ A c : ℕ, A < p ^ n ∧ A ≠ 0 ∧ 0 < c ∧ HasConstituent p F σ A ∧
      Module.finrank (ZMod p) W = c * rotPeriod p n A * digitProd p n A ∧
      (∀ w, σ (T2.negOne F) w = (-1 : ZMod p) ^ A • w) ∧
      (c = 1 → Nat.card (Module.End (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) =
        p ^ rotPeriod p n A) := by
  obtain ⟨N, A, c, hA, hc, ⟨ι⟩, hsimple, htop, hdim, hc1⟩ := descent_data σ hS hp2 hn hF hW
  refine ⟨A, c, hA, ?_, hc, hasConstituent_of_label σ hS hp2 hn hF hA ι, hdim,
    sigma_negOne_eq σ hS hp2 hn hF hA ι htop,
    fun h1 => natCard_end_of_one σ hS hp2 hn hF hA ι hsimple htop (hc1 h1)⟩
  rintro rfl
  obtain ⟨g, hg⟩ := hnt
  exact hg (sigma_trivial_of_label_zero σ hS hp2 hn hF hA ι htop g)

theorem uniq_unbounded (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {W W' : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    [AddCommGroup W'] [Module (ZMod p) W'] [Module.Finite (ZMod p) W']
    (σ : Representation (ZMod p) (SLm F) W) (σ' : Representation (ZMod p) (SLm F) W')
    (hW : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule)
    (hW' : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ'.asModule)
    {A A' : ℕ} (h : HasConstituent p F σ A) (h' : HasConstituent p F σ' A')
    (s : ℕ) (hs : A' = (rot p n)^[s] A) :
    Nonempty (σ.asModule ≃ₗ[MonoidAlgebra (ZMod p) (SLm F)] σ'.asModule) := by
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  have hq : 2 ≤ p ^ n := by
    calc 2 ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
  have hrel : redLabel (p ^ n) A' = (rot p n)^[s] (redLabel (p ^ n) A) := by
    rw [hs]
    exact redLabel_iterate_rot hp hn s A
  exact uniq_of_rot σ σ' hS hp2 hn hF hW hW' (redLabel_lt hq A)
    (hasConstituent_redLabel hF σ h) (hasConstituent_redLabel hF σ' h') s hrel

end Final

theorem mix11c_descent (hS : Mix11cSteinberg) : Mix11cDescent := by
  intro p n _ hp2 hn F _ _ _ hF
  have : CharP F p := charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p
  refine ⟨?_, ?_⟩
  · intro W _ _ _ σ hW hnt
    exact descent_exists hS hp2 hn hF σ hW hnt
  · intro W W' _ _ _ _ _ _ σ σ' hW hW' A A' h h' hs _
    obtain ⟨s, hs⟩ := hs
    exact uniq_unbounded hS hp2 hn hF σ σ' hW hW' h h' s hs

end CFSG.GH74.GLS.Stage4.Rest
