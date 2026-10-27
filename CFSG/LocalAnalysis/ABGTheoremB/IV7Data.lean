module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

namespace Setting

variable {G : Type u} [Group G] (σ : Setting G)

structure HypIV7 [Finite G] (r : ℕ) : Prop where
  prime : r.Prime
  dvd_ON : r ∣ Nat.card σ.ON
  dvd_CL : r ∣ Nat.card (σ.C ⊓ σ.L : Subgroup G)
  exceptional : σ.Exceptional r

structure IV7Data [Finite G] (r : ℕ) where
  P : Subgroup G
  P_sylow : IsSylowOf r P σ.C
  P_D : σ.D ≤ Subgroup.normalizer (P : Set G)
  R : Subgroup G
  R_sylow : IsSylowOf r R σ.ON
  R_D : σ.D ≤ Subgroup.normalizer (R : Set G)
  R_P : P ≤ Subgroup.normalizer (R : Set G)
  Q : Subgroup G
  Q_ne_bot : Q ≠ ⊥
  Q_le : Q ≤ P
  Q_characteristic : (Q.subgroupOf P).Characteristic
  Nstar : Subgroup G
  Nstar_qgroup : IsQGroup Nstar
  Nstar_constrained : PConstrainedWithin r Nstar (CFSG.solvableRadical Nstar)
  Nstar_covers : (σ.L : Set G) ⊆ (Nstar : Set G) * (σ.ON : Set G)
  D_le_Nstar : σ.D ≤ Nstar
  Q_le_Nstar : Q ≤ Nstar
  Cstar_covers : ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
    ((σ.C ⊓ Nstar ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) *
      ((σ.C ⊓ solvRadIn σ.L : Subgroup G) : Set G)
  Rstar : Subgroup G
  Rstar_sylow : IsSylowOf r Rstar (pPrimePCoreIn r Nstar)
  Rstar_D : σ.D ≤ Subgroup.normalizer (Rstar : Set G)
  Rstar_Q : Q ≤ Subgroup.normalizer (Rstar : Set G)
  centralizer_le : σ.C ⊓ Subgroup.centralizer ((Q ⊔ Rstar ⊓ Subgroup.centralizer (Q : Set G) :
      Subgroup G) : Set G) ≤ σ.C ⊓ Nstar ⊓ Subgroup.normalizer (Q : Set G)
  cases : σ.C ⊓ Nstar ⊓ Subgroup.normalizer (Q : Set G) = σ.C ⊓ Subgroup.normalizer (Q : Set G) ∨
    (Q = centerOf P ∧ Nstar = Subgroup.normalizer (R : Set G) ∧
      Q ≤ Subgroup.centralizer (R : Set G))

variable {σ}

@[expose] def IV7Data.Cstar [Finite G] {r : ℕ} (d : σ.IV7Data r) : Subgroup G :=
  σ.C ⊓ d.Nstar ⊓ Subgroup.normalizer (d.Q : Set G)

@[expose] def IV7Data.Qstar [Finite G] {r : ℕ} (d : σ.IV7Data r) : Subgroup G :=
  d.Q ⊔ d.Rstar ⊓ Subgroup.centralizer (d.Q : Set G)

@[expose] def IV7Data.familyM [Finite G] {r : ℕ} (d : σ.IV7Data r) : Set (Subgroup G) :=
  {H | IsPLocal r H ∧ σ.D ≤ H ∧ d.Qstar ≤ H ∧ automizerIndex (σ.T.subgroupOf H) = 6 ∧
    ((d.Cstar ⊓ σ.L : Subgroup G) : Set G) ⊆
      ((d.Cstar ⊓ H : Subgroup G) : Set G) * ((d.Cstar ⊓ solvRadIn σ.L : Subgroup G) : Set G) ∧
    d.Cstar ⊓ pPrimeCoreIn r H ≤ solvRadIn σ.L}

variable (σ)

@[expose] def familyMstar [Finite G] (r : ℕ) : Set (Subgroup G) :=
  {K | IsPLocal r K ∧ σ.D ≤ K ∧ IsDGroupWrt (σ.T.subgroupOf K) ∧
    Odd (Nat.card (pPrimeCoreIn r K))}

end Setting

end CFSG.ABGTheoremB
