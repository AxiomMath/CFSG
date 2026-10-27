module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section J3

variable {G : Type} [Group G] [Finite G]

@[expose] def blockCentralizer (M L : Subgroup G) : Subgroup G :=
  ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype

@[expose] def KFactBlockThreeSolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L N₀ B : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    N₀ ≤ B → B ≤ M ⊓ Subgroup.normalizer (S : Set G) →
    M ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (N₀ : Set G) →
    M ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (B : Set G) →
    Nat.Coprime 3 (Nat.card N₀) → (∀ b ∈ B, ∃ e : ℕ, b ^ 3 ^ e ∈ N₀) →
    (∀ k ∈ M ⊓ Subgroup.normalizer (S : Set G), ∃ e : ℕ, k ^ 2 ^ e ∈ B) →
    (∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        U ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
        (∀ u ∈ U, ∃ e : ℕ, u ^ 3 ^ e ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →
        ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
      ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        U ≤ barM M (Subgroup.normalizer (S : Set G)) →
        U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup 3 U →
        (U ⊓ (barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))).relIndex
          U ≤ 3

@[expose] def StmtBlockInnerNormalizer : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G},
    D1PhaseThree p P M H R → Asc81bEightFour → Asc81bEightSix → D1NoXBlock →
    IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ l ∈ barM M L,
      (∀ s ∈ barM M (pCoreOf 2 H), ∃ s' ∈ barM M (pCoreOf 2 H), ∀ y ∈ barM M L,
        (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹ = s' * y * s'⁻¹) →
      l ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)

end J3

section J3MSide

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

omit [Finite G] in
theorem blockCentralizer_le (M L : Subgroup G) : blockCentralizer M L ≤ M :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem mem_blockCentralizer_iff {M L : Subgroup G} (m : M) :
    (m : G) ∈ blockCentralizer M L ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  constructor
  · rintro ⟨m', hm', hmm'⟩
    rwa [show m' = m from Subtype.ext hmm'] at hm'
  · exact fun hm => ⟨m, hm, rfl⟩

omit [Finite G] in
theorem D1J3Data.mem_normalizer_inner {L : Subgroup G} {t : G} (htM : t ∈ M)
    (htR : t ∈ Subgroup.normalizer (R : Set G)) (htL : t ∈ Subgroup.normalizer (L : Set G)) :
    t ∈ Subgroup.normalizer ((R ⊓ (L ⊔ blockCentralizer M L) : Subgroup G) : Set G) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Cb := Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hL' : L.map (MulAut.conj t).toMonoidHom = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp htL
  have hLbar : (barM M L).map (MulAut.conj (mk ⟨t, htM⟩)).toMonoidHom = barM M L := by
    rw [← barM_map_conj htM, hL']
  have hNC : Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have htN : mk ⟨t, htM⟩ ∈ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hNC (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLbar)
  have key : ∀ (g : M), mk g ∈ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ∀ c ∈ blockCentralizer M L, (g : G) * c * (g : G)⁻¹ ∈ blockCentralizer M L := by
    rintro g hg _ ⟨m, hm, rfl⟩
    refine ⟨g * m * g⁻¹, ?_, by simp⟩
    show mk (g * m * g⁻¹) ∈ Cb
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hm
  have htC : t ∈ Subgroup.normalizer (blockCentralizer M L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key ⟨t, htM⟩ htN c, fun hc => ?_⟩
    have h1 := key (⟨t, htM⟩)⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ htN) _ hc
    simpa [mul_assoc] using h1
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨htR, Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨htL, htC⟩⟩

end J3MSide

end CFSG.AGLEmbedding
