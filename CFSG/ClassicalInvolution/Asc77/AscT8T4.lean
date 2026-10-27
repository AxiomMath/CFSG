module

import CFSG.ClassicalInvolution.Asc77.AscT8T4Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8Eight
public import CFSG.ClassicalInvolution.Asc77.AscT8Y1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8T

section Lift

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem exists_mul_mem_sigmaNorm_of_centralizer (hs : Std8 p f Ω K J S R T W z t)
    (hconn : T3.DStarConnected (T8.layerFamQ Ω (z * t))) (hcomp : dComp Ω K = dstarComp Ω K)
    {c : G} (hc : c ∈ Subgroup.centralizer ({z * t} : Set G)) :
    ∃ ν ∈ oddCoreOf (T8.layerJoin Ω (z * t)), ν * c ∈ sigmaNorm Ω K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := T8.xMem_zt hs
  have hcz : c ∈ T8.cenZ (z * t) := by
    rw [T8.cenZ_eq_centralizer]
    exact hc
  have hKc : T8.XMem Ω (z * t) (conjSub c K) := hKx.conj hΩ hcz
  obtain ⟨ν, hν, hνK⟩ := T8.exists_oddCore_conj_mem_dstarComp hp hq hΩ hx hKx hconn hKc
  refine ⟨ν, hν, ?_⟩
  rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hs.stand.mem, conjSub_mul, hcomp]
  exact hνK

end Lift

section Const

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_AlphaConst : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω →
      (∃ W ∈ WSet Ω, (∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) ∧
        ¬ MuIsoE4 Ω W) →
      ∀ z : G, IsUniqueInvolution K z → ∀ J₁ ∈ omegaNbr Ω K, ∀ J₂ ∈ omegaNbr Ω K,
        ∀ t₁ t₂ : G, IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
          alphaOf (Subgroup.closure ({t₁, z} : Set G)) =
            alphaOf (Subgroup.closure ({t₂, z} : Set G))

end Const

section Sigma

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem alphaOf_eq_of_mem_dComp [IsSimpleGroup G] (hA : C27_AlphaConst p f)
    (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hμ : ∃ W' ∈ WSet Ω, (∀ x ∈ muGroup Ω W', ∀ y ∈ muGroup Ω W', x * y = y * x) ∧
      ¬ MuIsoE4 Ω W') {L : Subgroup G} (hL : L ∈ dComp Ω K) :
    L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y → IsUniqueInvolution L' y' →
      alphaOf (Subgroup.closure ({y', y} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact alphaOf_eq_of_mem_dCompE
    (fun hA' hB' h => T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hA' hB' h)
    (fun hA' => hΩ.exists_uniqueInvolution hp hq hA')
    (fun c hcΩ z' hz' J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2 =>
      hA G Ω c (hs.stand.of_mem hcΩ) (hnt c hcΩ) hdisc hμ z' hz' J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2)
    hs.stand.mem hs.hz hs.hJ hs.ht hL

end Sigma

end T8T

end CFSG.ClassicalInvolution.Asc77
