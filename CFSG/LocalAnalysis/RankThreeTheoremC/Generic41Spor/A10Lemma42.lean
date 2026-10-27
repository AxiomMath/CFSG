module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma42I
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWrapPrime
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointX
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointTypes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC GenericComponentClass)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_D_facts {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hB : A10StageB P x J ψ)
    (hTcard : Nat.card (u3T P x J) = 5 ^ 2) (hxJ : x ∉ J) :
    (conjLines x (P : Subgroup G)).ncard ≤ 3 ∧
      ∀ W : Subgroup G, W ≤ (P : Subgroup G) → Nat.card W = 5 ^ 2 →
        (∀ A ∈ conjLines x (P : Subgroup G), A ≤ W) →
          conjLines x (P : Subgroup G) = {Subgroup.zpowers x} := by
  obtain ⟨-, hB2⟩ := hB
  rcases hB2 with h1 | ⟨A₁, A₂, hne, hA₁, hA₂, h3⟩
  · refine ⟨by rw [h1, Set.ncard_singleton]; omega, fun _ _ _ _ => h1⟩
  · obtain ⟨hA₁T, hA₁c, -⟩ := hA₁
    obtain ⟨hA₂T, hA₂c, -⟩ := hA₂
    refine ⟨?_, fun W hWP hWc hall => ?_⟩
    · rw [h3]
      have e1 := Set.ncard_insert_le (Subgroup.zpowers x) ({A₁, A₂} : Set (Subgroup G))
      have e2 := Set.ncard_insert_le A₁ ({A₂} : Set (Subgroup G))
      have e3 := Set.ncard_singleton A₂
      omega
    · exfalso
      have hxW : Subgroup.zpowers x ≤ W := hall _ (by rw [h3]; exact Or.inl rfl)
      have hA₁W : A₁ ≤ W := hall _ (by rw [h3]; exact Or.inr (Or.inl rfl))
      have hA₂W : A₂ ≤ W := hall _ (by rw [h3]; exact Or.inr (Or.inr rfl))
      have hsupT : A₁ ⊔ A₂ ≤ u3T P x J := sup_le hA₁T hA₂T
      have hdvd : Nat.card (A₁ ⊔ A₂ : Subgroup G) ∣ 5 ^ 2 := by
        rw [← hTcard]
        exact Subgroup.card_dvd_of_le hsupT
      have hgt : 5 < Nat.card (A₁ ⊔ A₂ : Subgroup G) := by
        by_contra hle
        have hle1 : Nat.card A₁ ≤ Nat.card (A₁ ⊔ A₂ : Subgroup G) := Subgroup.card_le_of_le le_sup_left
        have hEq : A₁ = A₁ ⊔ A₂ :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
        have hA₂A₁ : A₂ ≤ A₁ := hEq ▸ le_sup_right
        exact hne (Subgroup.eq_of_le_of_card_ge hA₂A₁ (by omega)).symm
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
      have hi2 : i = 2 := by
        interval_cases i <;> simp_all
      have hcardsup : Nat.card (A₁ ⊔ A₂ : Subgroup G) = Nat.card (u3T P x J) := by
        rw [hi', hi2, hTcard]
      have hTeq : A₁ ⊔ A₂ = u3T P x J := Subgroup.eq_of_le_of_card_ge hsupT (by omega)
      have hTW : u3T P x J ≤ W := hTeq ▸ sup_le hA₁W hA₂W
      have hWT : W = u3T P x J := (Subgroup.eq_of_le_of_card_ge hTW (by omega)).symm
      apply hxJ
      have hxT : x ∈ u3T P x J := hWT ▸ hxW (Subgroup.mem_zpowers x)
      exact hxT.2

theorem a10_lemma42 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hClass : GenericComponentClass G) (hTits : TitsFacts) (hX : A10Facts)
    (hMcL : ExtraFacts IsMcLType 5 McLShape) (hJ4 : ExtraFacts IsJ4Type 11 J4Shape)
    (hSz : Sz32Facts) (hSz' : Sz32OpenFacts) (hdata : Sz32DataFacts) (hXe : A10Ext)
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) (hB : A10StageB P x J ψ) {U : Subgroup G} (hU : IIPlane 5 P x J U)
    (hγ : A10PlaneShape J (u3T P x J) ψ U) :
    ∀ a ∈ U, a ∉ Subgroup.zpowers x → Subgroup.centralizer ({a} : Set G) ≤ M := by
  intro a ha hax
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hTcard, hTel, hxJ⟩ := plane_T_structure hX.sylow hc
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := plane_S_decomp hX.sylow hX.noOuter hc
  have hxC : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := hB.1
  have hSP : u3S P x = (P : Subgroup G) := inf_eq_left.2 hxC
  haveI : IsMulCommutative (u3T P x J) := hTel.1
  haveI : IsCyclic Z := hZcyc
  have hPab : IsMulCommutative (P : Subgroup G) := by
    rw [← hSP, ← hsup]
    exact plane_sup_comm (fun a ha b hb => (hZT b hb a ha).symm)
  obtain ⟨hD₁, hD₂⟩ := a10_D_facts ψ hB hTcard hxJ
  have ha1 : a ≠ 1 := fun h => hax (h ▸ Subgroup.one_mem _)
  refine lemma42_routeW' hS hU0 hD1 hClass (by norm_num) hc.sigma hc.core hc.fail hc.larger
    hc.generic.1 hc.generic.2.1.2.1 hc.generic.2.1.2.2.1 hxC hD₁ hD₂ (fun _ => hPab)
    (plane_x_not_mem_commutator hX.sylow hX.noOuter hc hxC)
    (fun y hy _ => plane_three_le_pRank_centralizer hX.sylow hX.noOuter hc hxC hy)
    (fun Q _ _ hQ hz => secondPointFacts_of_class (by norm_num) hQ hz hTits hX hMcL hJ4)
    (fun Q _ _ hQ _ => spw_normalizerPowers_of_class (by norm_num) hQ hTits hX hXe hMcL hJ4)
    (fun _ => sz32_second_point_false hS hU0 hD1 hSz hSz' hdata hc.core hc.sigma
      hc.generic.2.1.2.2.1 hc.generic.2.1.2.1 hxC (hsup.trans hSP) hZT hTZ hTel.2 hZcyc hxZ)
    a ((hU.le ha).1) ha1 (hU.elem.2 a ha) ?_
  rintro ⟨g, hg, -⟩
  have hle : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ U :=
    hg ▸ Subgroup.zpowers_le.2 ha
  have hwc := a10_lemma42_i ψ hB hU hγ g hle
  apply hax
  have hzz : Subgroup.zpowers a = Subgroup.zpowers x := hg.trans hwc
  rw [← hzz]
  exact Subgroup.mem_zpowers a

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
