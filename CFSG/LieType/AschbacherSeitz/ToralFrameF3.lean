module

public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrame
public import CFSG.LieType.AschbacherSeitz.RootGroupInvolutionPsi

public section

namespace CFSG.LieType.AschbacherSeitz

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.LieType.Universal

@[expose] def GGRankOneFrame (t : StatedLieTag) (n f : ℕ) {G : Type} [Group G]
    (ψ : (ggU t n f).K →* G) (p : ℕ) (Bs : Subgroup G)
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (F : GGStdForm p Bs ψ.range (ggU (absTag t) 6 f).D S π f) : Prop :=
  ∀ α ∈ (ggU (absTag t) 6 f).D.roots, latPerm π α = α →
    ∃ (δ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K),
      GGRootClass (ggU t n f).D t δ ∧
      Bs ≤ Subgroup.normalizer
        (((ggRankOneSub (ggU t n f).D ψ δ).map (MulAut.conj (ψ u)).toMonoidHom :
          Subgroup G) : Set G) ∧
      ∀ b : Bs,
        ((b : G) ∈ Subgroup.centralizer
          (((ggRankOneSub (ggU t n f).D ψ δ).map (MulAut.conj (ψ u)).toMonoidHom :
            Subgroup G) : Set G) ↔
          latChar p (Multiplicative.toAdd (F.coord b)) α = 0)

theorem ggRootSub_le_rankOneFrame (t : StatedLieTag) (n f : ℕ) {G : Type} [Group G]
    (ψ : (ggU t n f).K →* G) (δ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K) :
    ggRootSub (ggU t n f).D ψ δ u ≤
      (ggRankOneSub (ggU t n f).D ψ δ).map (MulAut.conj (ψ u)).toMonoidHom := by
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨ψ z, ⟨z, Subgroup.mem_sup_left hz, rfl⟩, ?_⟩
  simp [map_mul, map_inv]

theorem f3_of_rankOneFrame (t : StatedLieTag) (n f : ℕ) {G : Type} [Group G]
    (ψ : (ggU t n f).K →* G) (p : ℕ) (Bs : Subgroup G)
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (F : GGStdForm p Bs ψ.range (ggU (absTag t) 6 f).D S π f)
    (hRF : GGRankOneFrame t n f ψ p Bs S π F)
    (hInv : ∀ (γ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K),
      GGRootClass (ggU t n f).D t γ →
        ∃ r ∈ ggRootSub (ggU t n f).D ψ γ u, orderOf r = 2) :
    ∀ α ∈ (ggU (absTag t) 6 f).D.roots, latPerm π α = α →
      ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K),
        GGRootClass (ggU t n f).D t γ ∧
        (∀ b : Bs, latChar p (Multiplicative.toAdd (F.coord b)) α = 0 →
          (b : G) ∈ Subgroup.centralizer (ggRootSub (ggU t n f).D ψ γ u : Set G)) ∧
        ∃ r ∈ ggRootSub (ggU t n f).D ψ γ u, orderOf r = 2 := by
  intro α hα hπ
  obtain ⟨δ, u, hclass, _hN, hC⟩ := hRF α hα hπ
  refine ⟨δ, u, hclass, ?_, hInv δ u hclass⟩
  intro b hb
  have hbJ : (b : G) ∈ Subgroup.centralizer
      (((ggRankOneSub (ggU t n f).D ψ δ).map (MulAut.conj (ψ u)).toMonoidHom :
        Subgroup G) : Set G) := (hC b).mpr hb
  rw [Subgroup.mem_centralizer_iff] at hbJ ⊢
  intro x hx
  exact hbJ x (ggRootSub_le_rankOneFrame t n f ψ δ u hx)

section FullCertificates

theorem f3_of_rankOneFrame_of_central (t : StatedLieTag) (ht : GGExcFive t)
    (n f : ℕ) (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : (ggU t n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    (p : ℕ) (Bs : Subgroup G)
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (F : GGStdForm p Bs ψ.range (ggU (absTag t) 6 f).D S π f)
    (hRF : GGRankOneFrame t n f ψ p Bs S π F) :
    ∀ α ∈ (ggU (absTag t) 6 f).D.roots, latPerm π α = α →
      ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K),
        GGRootClass (ggU t n f).D t γ ∧
        (∀ b : Bs, latChar p (Multiplicative.toAdd (F.coord b)) α = 0 →
          (b : G) ∈ Subgroup.centralizer (ggRootSub (ggU t n f).D ψ γ u : Set G)) ∧
        ∃ r ∈ ggRootSub (ggU t n f).D ψ γ u, orderOf r = 2 :=
  f3_of_rankOneFrame t n f ψ p Bs S π F hRF
    (fun γ u hclass =>
      rootGroupInvolutionPsiAt t ht n f hf ψ hker hclass.1 hclass u)

end FullCertificates

end CFSG.LieType.AschbacherSeitz

end
