module

public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

structure A3pInSitu {Y : Type} [Group Y] (p : ℕ) (T B Y₀ : Subgroup Y) : Prop where
  primeCore : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    p.Coprime (Nat.card W) → W = ⊥
  normal_dichotomy : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    W = ⊥ ∨ B ≤ W
  centralizer_le : Y₀ ⊓ Subgroup.centralizer (B : Set Y) ≤ T

@[expose] def KFactA3pLocal (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    Nonempty (K ≃* alternatingGroup (Fin (3 * p))) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow p Y) (B Y₀ : Subgroup Y),
      B ≤ T → IsElemAbelian p B → Nat.card B = p ^ 3 →
      GLBWeakCore p (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ → A3pInSitu p (T : Subgroup Y) B Y₀

@[expose] def StmtA3pSocleData (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T : Type} [Group T] {P : Sylow p G} {M H R X : Subgroup G},
    D1SocleConfig T p P M H R R → Nonempty (T ≃* alternatingGroup (Fin (3 * p))) →
    X ≤ R → IsElemAbelian p X → Nat.card X = p ^ 3 → D1SurvivorData p P M H R X

theorem stmtA3pSocleData_of {p : ℕ} [Fact p.Prime] (hK : KFactA3pLocal p) :
    StmtA3pSocleData p := by
  intro G _ _ T _ P M H R X h eT hXR hXel hXc
  have hp : p.Prime := Fact.out
  obtain ⟨K, hKn, ⟨eK⟩, hC, -⟩ := h.socle
  obtain ⟨eT⟩ := eT
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.toD1Escape.reducedNongeneration
  have hXp : IsPGroup p X := h.ext.isPGroup.to_le hXR
  have hXH : X ≤ H := hXR.trans h.ext.le_H
  have hXp' : IsPGroup p (X.subgroupOf H) := hXp.comap_subtype
  have hcard : Nat.card ((X.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))) = p ^ 3 := by
    rw [card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hXp',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXc]
  have hXRb : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hRbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hXR)
  have hXe : IsElemAbelian p ((X.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))) := by
    refine elementary_abelian_map p ?_ _
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := (isMulCommutative_iff.mp hXel.1) ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩
      simpa using congrArg Subtype.val this
    · exact Subtype.ext (hXel.2 _ (Subgroup.mem_subgroupOf.mp hx))
  have hS := hK _ K hKn ⟨eK.trans eT⟩ hC Rbar _ _ hXRb hXe hcard hred.weakCore_le hred.ne_top
  have hX1 : X ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card (⊥ : Subgroup G) = p ^ 3 := hXc
    rw [Subgroup.card_bot] at h1
    have := Nat.one_lt_pow (by norm_num : (3 : ℕ) ≠ 0) hp.one_lt
    omega
  refine h.ext.survivorData_of_map h.glob hXR hX1 (fun W hW hWn hWc => ?_)
    hS.normal_dichotomy (hS.centralizer_le.trans ?_)
  · exact hS.primeCore W hW ((Subgroup.normal_subgroupOf_iff_le_normalizer hW).mp hWn) hWc
  · rw [hRbar]

@[expose] def StmtA3pTarget (p a b : ℕ) [Fact p.Prime] : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* alternatingGroup (Fin (3 * p))) →
    JStarTarget p b L ∧ JStarTargetCard p a b L ∧
      ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer L)

@[expose] def KFactJStarElimA3p (p b : ℕ) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* alternatingGroup (Fin (3 * p))) →
    JStarElimOf p b L

end CFSG.AGLEmbedding
