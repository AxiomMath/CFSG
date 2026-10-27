module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
import CFSG.LocalAnalysis.AGLEmbeddingD2.CompetitorR

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def D2HeisBorelFor {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M A R : Subgroup G) (i : TauCeti.CFSGIndex) : Prop :=
  ∀ H : Subgroup G, D2Escape p P M A H R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* i.Group) →
      D2HeisBorel p Rbar (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K

theorem D2HeisBorelAt.for {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop} (h : D2HeisBorelAt i Pp)
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : Pp p) {P : Sylow p G} {M A R : Subgroup G} :
    D2HeisBorelFor p P M A R i :=
  fun _ _ Rbar K _ hK he => h _ p hp Rbar _ _ K hK he

theorem D2IndexCaseFor.heisBorelFor {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M A R : Subgroup G} {i : TauCeti.CFSGIndex} (h : D2IndexCaseFor p P M A R i) :
    D2HeisBorelFor p P M A R i :=
  fun H hesc Rbar K hRbar hK he => (h H hesc Rbar K hRbar hK he).elim

@[expose] def D2HeisLocalEqAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* i.Group) → ∀ p, Pp p →
    ∀ R : Sylow p X, ¬ p ∣ Nat.card (Outer K) ∧ Nat.card (R : Subgroup X) = p ^ 3 ∧
      Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R ∧
      Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
        Subgroup X) = p ∧
      ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
        (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ∧
      (∀ r ∈ (R : Subgroup X), r ^ p = 1) ∧
      Group.IsSolvable (Subgroup.normalizer ((R : Subgroup X) : Set X)) ∧
      ∃ t, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
        ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
        (∀ x ∈ (R : Subgroup X),
          ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
            t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
        (∀ x ∈ (R : Subgroup X),
          ∃ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X),
            t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
        ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup X,
          (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ F →
            F ≤ (R : Subgroup X) → F.relIndex (R : Subgroup X) = p →
              t ^ j ∉ Subgroup.normalizer (F : Set X)

theorem D2HeisLocalAt.toEq {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop} (h : D2HeisLocalAt i Pp) :
    D2HeisLocalEqAt i Pp := by
  intro X _ _ K hKn hC he p hp R
  obtain ⟨hout, hcard, -, hrest⟩ := h X K hKn hC he p hp R
  exact ⟨hout, hcard, hrest⟩

theorem D2HeisLocalEqAt.heisBorel {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : D2HeisLocalEqAt i Pp) {X : Type} [Group X] [Finite X] {p : ℕ} (hp : Pp p)
    {R : Sylow p X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K)
    (he : Nonempty (K ≃* i.Group)) (hX₀ : X₀ = Subgroup.normalizer ((R : Subgroup X) : Set X)) :
    D2HeisBorel p R X₀ K := by
  obtain ⟨hout, hcard, hC, hZ, hcomm, hexp, hsolv, hlines⟩ :=
    h X K hK.normal hK.centralizer_eq_bot he p hp R
  exact hK.heisBorel_of_local_of_eq hout hcard hX₀ hC hZ hcomm hexp hsolv hlines

theorem D2Escape.aglJConfig_of_heisBorelFor {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M A H R : Subgroup G} (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hKU : UnitaryBorelKFacts)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex, IsD2SeitzException p d.1 →
      D2HeisBorelFor p P M A R (.lie d))
    (hSpor : ∀ s : TauCeti.SporadicName, D2HeisBorelFor p P M A R (.sporadic s))
    (hglob : AGLGlobal G) (h : D2Escape p P M A H R) (hp5 : 5 ≤ p) (hcard : Nat.card R = p ^ 3)
    (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal) : AGLJConfig p M H R R := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine h.aglJConfig_of_cases hrank hL3 hKU hglob hp5 hcard hRQ
    (fun Rbar K hRbar hK s hi =>
      h.aglJConfig_of_borel hglob hRbar (hSpor s H h Rbar K hRbar hK hi) hRQ)
    fun Rbar K hRbar hK d hchar ⟨e⟩ => ?_
  by_cases hexcp : IsD2SeitzException p d.1
  · exact h.aglJConfig_of_borel hglob hRbar (hexc d hexcp H h Rbar K hRbar hK ⟨e⟩) hRQ
  · exact (hK.false_of_seitzCross hS d e hchar hexcp).elim

theorem D2Escape.false_of_heisBorelFor' {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M A H R : Subgroup G} (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hKU : UnitaryBorelKFacts)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex, IsD2SeitzException p d.1 →
      D2HeisBorelFor p P M A R (.lie d))
    (hSpor : ∀ s : TauCeti.SporadicName, D2HeisBorelFor p P M A R (.sporadic s))
    (hCGT : AschbacherLocalCGTBlock) (hglob : AGLGlobal G) (hD1p : D1At G p)
    (hX : NoXBlockFor G) (h : D2Escape p P M A H R) (hmax : D2EscapeMax p P M R) (hp5 : 5 ≤ p)
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hB : D2HeisBorel p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal) : False := by
  have hcard : Nat.card R = p ^ 3 := by
    rw [← h.card_map_eq le_rfl, ← hRbar]
    exact hB.card
  refine false_of_agljCompetitorsOn (p := p) (M := M) (R := R) (X := R)
    (C := fun H' => D2Escape p P M A H' R ∧ (⊥ : Subgroup G) ≤ nclIn H' R) ?_
    (agljCompetitorsOn_d2Escape hmax hglob hD1p) ⟨h, bot_le⟩ hCGT hX
  rintro H' ⟨h', -⟩
  exact h'.aglJConfig_of_heisBorelFor hrank hL3 hS hKU hexc hSpor hglob hp5 hcard hRQ

end CFSG.AGLEmbeddingD2
