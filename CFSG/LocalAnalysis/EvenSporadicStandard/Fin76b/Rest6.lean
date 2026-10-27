module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.SwapE
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.CentE
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaSq
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup
public import CFSG.Sporadic.Schreier.PairJ2Faithful

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)
open CFSG.Sporadic.Schreier (j3P j3PermEquiv card_j3P j2P j2PermEquiv)
open CFSG.Sporadic.SmallOddCore (ctuc_j3_full_automorphism_permutation_model)

@[expose] def Fin76bInnerRest₆ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G) (Q : Sylow 2 G)
    (x β : G) (B : Subgroup G), StdHyp G L → (IsSporadic L .J2 ∨ IsSporadic L .J3) →
    (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) → InnerConfig G L z t T₀ →
    EConfig L T₀ E t →
    (∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ T₀ ⊔ zpowers z →
      E.map (MulAut.conj g).toMonoidHom = E) →
    (∀ y ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G), y ∈ normalizer (E : Set G)) →
    (∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
      z ∈ S → S = zpowers z ⊔ zpowers t ∨
        (∃ k : ℕ, 2 ≤ k ∧ Nonempty (S ≃* DihedralGroup (2 ^ k))) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (S ≃* CFSG.Open.SemidihedralGroup n)) →
    T₀ ⊔ zpowers z ≤ (Q : Subgroup G) → x ∈ (Q : Subgroup G) → x ∉ T₀ ⊔ zpowers z →
    x ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G) →
    x * z * x⁻¹ = z * t → x * t * x⁻¹ = t → (∀ q ∈ (Q : Subgroup G), q * t = t * q) →
    B ≤ L → B ≤ centralizer ({t} : Set G) → Nonempty (↥B ≃* alternatingGroup (Fin 5)) →
    β ∈ B → orderOf β = 3 →
    (∃ hz : z ∈ centralizer ({β} : Set G),
      Lemma64Conclusion ↥(centralizer ({β} : Set G))
        (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))))) → False

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_rest₆ (hSol : SolomonZ2A6) (hR : Fin76bInnerRest₆) (h : StdHyp G L)
    (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hinner : normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G))
    {X : Type*} [Group X] [Finite X] (φ : X ≃* L) (hX : SylowEData X) (hB : BetaDataSqB X)
    (hZ : center L = ⊥) : False := by
  obtain ⟨z, t, T₀, E, Q, x, hcfg, hE, hTQ, hxQ, hxT, hxN, hxz, hxt⟩ :=
    inner_swap_of_sylowEData h φ hX hZ hS hinner
  have hzt : ∃ y : G, y * z * y⁻¹ = z * t := ⟨x, hxz⟩
  obtain ⟨B, β, hBL, hBt, hBiso, hβB, hβ3, h64⟩ := lemma64_of_betaDataSqB hSol
    (fun _ hβ => h.isKGroupCat_centralizer_of_orderOf (by norm_num) hβ) hcfg φ hB
  exact hR G L z t T₀ E Q x β B h hJ hS hinner hcfg hE
    (fun g hg => EConfig.map_conj_eq_of_le hcfg hE hzt hg)
    (fun y hy => EConfig.mem_normalizer_of_mem_normalizer hcfg hE hzt hy)
    (fun S hS2 hSC hSmax hzS => EConfig.sylow_centralizer_shape hcfg hE hS2 hSC hSmax hzS)
    hTQ hxQ hxT hxN hxz hxt (EConfig.t_central_Q hcfg hE Q.isPGroup' hTQ hxQ hxz hxt)
    hBL hBt hBiso hβB hβ3 h64

end CFSG.EvenSporadicStandard.Fin76b
