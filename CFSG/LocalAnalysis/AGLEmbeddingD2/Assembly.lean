module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Component
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduction

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

structure D2AlmostSimple (p : ℕ) (X : Type*) [Group X] [Finite X] (R : Sylow p X)
    (A X₀ K : Subgroup X) : Prop extends D2Reduced p X R A X₀ where
  component : IsComponentOf K ⊤
  normal : K.Normal
  unique : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K
  center_eq_bot : Subgroup.center K = ⊥
  centralizer_eq_bot : Subgroup.centralizer (K : Set X) = ⊥
  not_le : ¬ K ≤ X₀
  dvd : p ∣ Nat.card K
  catalog : IsCatalogGroup K

theorem D2Escape.almostSimple_of {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Open.IsKProper G) {p : ℕ}
    {P : Sylow p G} {M A H R : Subgroup G} (h : D2Escape p P M A H R) :
    ∃ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K := by
  have := hsimple
  obtain ⟨Rbar, hRbar, hred⟩ := h.reduced
  have hHtop : H ≠ ⊤ := twoLocal_ne_top hnonab h.maxTwoLocal_H.1
  have hncon : ¬ HasPrimeConstraint (G := H) p := by
    rintro ⟨N, hNn, hNp, hNC⟩
    have hN : N ≤ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) := le_sSup ⟨hNn, hNp⟩
    rw [hred.pCore_eq_bot, le_bot_iff] at hN
    subst hN
    apply hred.ne_top
    have htop : (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.centralizer (((⊥ : Subgroup (H ⧸ primeComplementCore (G := H) p))) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
      rw [hy, one_mul, mul_one]
    rw [eq_top_iff]
    exact (htop.trans hNC).trans bot_le
  obtain ⟨K, hK, -, -, hdvd, -, hcat⟩ :=
    isKProper_not_hasPrimeConstraint_catalog_component hK H hHtop p h.prime hncon
  have hcenter := hred.center_eq_bot hK
  refine ⟨Rbar, K, hRbar,
    { toD2Reduced := hred
      component := hK
      normal := hred.normal_of_isComponentOf hK
      unique := fun L hL => hred.eq_of_isComponentOf hL hK
      center_eq_bot := hcenter
      centralizer_eq_bot := hred.centralizer_eq_bot_of_isComponentOf hK
      not_le := hred.not_le_of_isComponentOf hK
      dvd := hdvd
      catalog := IsCatalogGroup.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
        hcat }⟩

theorem D2Escape.almostSimple {G : Type} [Group G] [Finite G] (hglob : AGLGlobal G) {p : ℕ}
    {P : Sylow p G} {M A H R : Subgroup G} (h : D2Escape p P M A H R) :
    ∃ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K :=
  h.almostSimple_of hglob.simple hglob.nonab hglob.kProper

@[expose] def D2ComponentCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) (P : Sylow p G) (M A H R : Subgroup G), D2Escape p P M A H R →
    D2EscapeMax p P M R → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K → False

theorem d2EscapeCase_of_componentCase (hcomp : D2ComponentCase) {G : Type} [Group G] [Finite G]
    (hglob : D2Global G) (hD1 : D1For G) : D2EscapeCase G := by
  intro p hβ P M A H R h hmax
  obtain ⟨Rbar, K, hRbar, hK⟩ := h.almostSimple hglob.toAGLGlobal
  exact hcomp G hglob hD1 p P M A H R h hmax hβ Rbar K hRbar hK

theorem d2_of_componentCase (hcomp : D2ComponentCase) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : IsKProper G)
    (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G) (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G)
    (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G) (P : Sylow p G) (M : Subgroup G)
    (hM : GLBIsMaxTwoLocal M) (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G)
    (hQ : IsPGroup p Q) (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M :=
  d2_of_escapeCase hD1
    (d2EscapeCase_of_componentCase hcomp ⟨inferInstance, hnonab, hK, hchar, he, hδ₁, hδ₂⟩ hD1)
    p hp P M hM hPM Q hQ hQrank hQM H hH hQH

end CFSG.AGLEmbeddingD2
