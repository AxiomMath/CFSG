module

public import CFSG.GH74.GLS.LU.Local.Conj
public import CFSG.GH74.GLS.LU.Main

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

structure LUEps (G : Type) [Group G] (q : ℕ) (ε : ℤ) (z : G) (K₁ : Subgroup G) (u : G) : Prop where
  eps : ε = 1 ∨ ε = -1
  mod8 : ¬ ((q : ℤ) ≡ ε [ZMOD 8])
  A0_cyc : IsCyclic ↥(A0 z)
  A0_dvd : ((Nat.card ↥(A0 z) : ℕ) : ℤ) ∣ (q : ℤ) - ε
  H_cyc : IsCyclic ↥(K₁ ⊓ centralizer ({u} : Set G))
  H_card : (Nat.card ↥(K₁ ⊓ centralizer ({u} : Set G)) : ℤ) = (q : ℤ) - ε

@[expose] def LUNbhdConcl (G : Type) [Group G] (Gs : Type) [Group Gs] (p f : ℕ) : Prop :=
  ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (z u : G) (Y : Fin 3 → Subgroup G),
        Nat.card K = p ^ f ∧ IsCentralInvolution z ∧ IsLinearA3Neighborhood K z u Y ∧
          Subgroup.centralizer ({z} : Set G) ≤
            Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G)) ∧
    ((p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p) (F : Type) (_ : Field F)
        (_ : Finite F) (z u : G) (Y : Fin 3 → Subgroup G),
        Nat.card K = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧ IsCentralInvolution z ∧
          IsUnitaryA3Neighborhood (p ^ f) K F z u Y ∧
          Subgroup.centralizer ({z} : Set G) ≤
            Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G))

@[expose] def LUMax6AAt (G : Type) [Group G] (Gs : Type) [Group Gs] (p f : ℕ) : Prop :=
  ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f)) →
    ∀ z : G, IsCentralInvolution z → MaxOverCentralizerPSp4 z p f

@[expose] def LUSetupLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (Gs : Type) [Group Gs],
    IsTwoCentralClassicalTypeCompat G Gs → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) →
      ∃ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
        LUComps G (p ^ f) z K₁ K₂ ∧ LUSyl G z S K₁ K₂ t u ∧ LUEps G (p ^ f) 1 z K₁ u) ∧
    ((p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f) →
      ∃ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
        LUComps G (p ^ f) z K₁ K₂ ∧ LUSyl G z S K₁ K₂ t u ∧ LUEps G (p ^ f) (-1) z K₁ u)

@[expose] def LULocalLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G), LUComps G (p ^ f) z K₁ K₂ →
      LUSyl G z S K₁ K₂ t u → MaxOverCentralizerPSp4 z p f →
      (LUEps G (p ^ f) 1 z K₁ u →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (u' : G) (Y : Fin 3 → Subgroup G),
          Nat.card K = p ^ f ∧ IsLinearA3Neighborhood K z u' Y ∧
            Subgroup.centralizer ({z} : Set G) ≤
              Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G)) ∧
      (LUEps G (p ^ f) (-1) z K₁ u →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p) (F : Type) (_ : Field F)
          (_ : Finite F) (u' : G) (Y : Fin 3 → Subgroup G),
          Nat.card K = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧
            IsUnitaryA3Neighborhood (p ^ f) K F z u' Y ∧
            Subgroup.centralizer ({z} : Set G) ≤
              Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G))

theorem LUSyl.isCentralInvolution {G : Type} [Group G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
    {t u : G} (h : LUSyl G z S K₁ K₂ t u) : IsCentralInvolution z :=
  ⟨h.z_inv, S, h.z_mem, fun _ hs => h.comm_z hs⟩

theorem luNeighborhood_at (hT0 : LUSetupLeaf) (hT1 : LULocalLeaf) {G : Type} [Group G] [Finite G]
    (hG : IsKProperSimple G) {Gs : Type} [Group Gs] (hcompat : IsTwoCentralClassicalTypeCompat G Gs)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h6A : LUMax6AAt G Gs p f) :
    LUNbhdConcl G Gs p f := by
  constructor
  · rintro ⟨h8, hL⟩
    obtain ⟨z, S, K₁, K₂, t, u, hc, hs, he⟩ := (hT0 G hG Gs hcompat p f hp hp2 hq).1 ⟨h8, hL⟩
    obtain ⟨K, hK, hKf, u', Y, hKc, hA, hCN⟩ :=
      (hT1 G hG p f hp hp2 hq z S K₁ K₂ t u hc hs
        (h6A (Or.inl ⟨h8, hL⟩) z hs.isCentralInvolution)).1 he
    exact ⟨K, hK, hKf, z, u', Y, hKc, hs.isCentralInvolution, hA, hCN⟩
  · rintro ⟨h8, hU⟩
    obtain ⟨z, S, K₁, K₂, t, u, hc, hs, he⟩ := (hT0 G hG Gs hcompat p f hp hp2 hq).2 ⟨h8, hU⟩
    obtain ⟨K, hK, hKf, hKp, F, hF, hFf, u', Y, hKc, hFc, hA, hCN⟩ :=
      (hT1 G hG p f hp hp2 hq z S K₁ K₂ t u hc hs
        (h6A (Or.inr ⟨h8, hU⟩) z hs.isCentralInvolution)).2 he
    exact ⟨K, hK, hKf, hKp, F, hF, hFf, z, u', Y, hKc, hFc, hs.isCentralInvolution, hA, hCN⟩

theorem luNeighborhood_of_6A (hT0 : LUSetupLeaf) (hT1 : LULocalLeaf) (h6A : LUMax6A) :
    LUNeighborhood := by
  intro G _ _ hG Gs _ hcompat p f hp hp2 hq
  exact luNeighborhood_at hT0 hT1 hG hcompat hp hp2 hq
    (fun hc z hz => h6A G hG Gs hcompat p f hp hp2 hq hc z hz)

end CFSG.GH74.GLS.LU.Local
