module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieChar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltPerm
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

namespace AltDegree

theorem map_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (g : G) :
    (Subgroup.centralizer ({g} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e g} : Set H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using congrArg e hx')
  · intro hy
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine ⟨e.symm y, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
    apply e.injective
    simpa using hy'

theorem three_le_pRank_of_mulEquiv_alternating {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 3 * p ≤ n) (e : K ≃* alternatingGroup (Fin n)) : 3 ≤ Open.pRank p K := by
  have h1 := three_le_pRank_alternatingGroup hp hp2 hn
  have h2 : Open.pRank p ((⊤ : Subgroup (alternatingGroup (Fin n))).map e.symm.toMonoidHom) =
      Open.pRank p (⊤ : Subgroup (alternatingGroup (Fin n))) :=
    pRank_map_of_injective p hp _ e.symm.injective _
  rw [Subgroup.map_top_of_surjective _ e.symm.surjective] at h2
  have h3 : Open.pRank p ((⊤ : Subgroup K).map K.subtype) = Open.pRank p (⊤ : Subgroup K) :=
    pRank_map_of_injective p hp _ K.subtype_injective _
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3
  omega

end AltDegree

theorem D2AlmostSimple.sylow_le_of_alternating (h : D2AlmostSimple p X R A X₀ K) {n : ℕ}
    (hn : 5 ≤ n) (e : K ≃* alternatingGroup (Fin n)) : (R : Subgroup X) ≤ K := by
  refine h.sylow_le_of_not_dvd_card_outer ?_
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact not_dvd_card_outer_alternatingGroup n hn p h.prime h.ne_two

theorem D2AlmostSimple.eq_two_mul_of_alternating (h : D2AlmostSimple p X R A X₀ K) {n : ℕ}
    (hn : 5 ≤ n) (e : K ≃* alternatingGroup (Fin n)) : n = 2 * p := by
  have hp := h.prime
  have hp2 := h.ne_two
  have hRK : (R : Subgroup X) ≤ K := h.sylow_le_of_alternating hn e
  have hAK : A ≤ K := h.A_le.trans hRK
  have h3 : n < 3 * p := by
    by_contra hge
    have h3K := AltDegree.three_le_pRank_of_mulEquiv_alternating hp hp2 (not_lt.mp hge) e
    have hmono : Open.pRank p K ≤ Open.pRank p (⊤ : Subgroup X) :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_top
    have hR : Open.pRank p (⊤ : Subgroup X) = 2 := by
      rw [← pRank_sylow_eq_globalRank p hp R]
      exact h.pRank_eq
    omega
  have hĀ : IsElemAbelian p ((A.subgroupOf K).map e.toMonoidHom) :=
    elementary_abelian_map p (isElemAbelian_subgroupOf h.elem K) _
  have hĀcard : Nat.card ((A.subgroupOf K).map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, h.card_A]
  have hE : IsElemAbelian p (((A.subgroupOf K).map e.toMonoidHom).map
      (alternatingGroup (Fin n)).subtype) := elementary_abelian_map p hĀ _
  have hEcard : Nat.card (((A.subgroupOf K).map e.toMonoidHom).map
      (alternatingGroup (Fin n)).subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective, hĀcard]
  obtain ⟨b₁, hb₁E, b₂, hb₂E, O₁, O₂, hO₁, hO₂, hd, hb₁, hb₂⟩ :=
    exists_cycles_of_isElemAbelian hp hp2 h3 hE hEcard
  have h2p : 2 * p ≤ n := by
    have hu := Finset.card_union_of_disjoint hd
    have hle := Finset.card_le_univ (O₁ ∪ O₂)
    simp only [Fintype.card_fin] at hle
    omega
  rcases h2p.eq_or_lt with heq | hlt
  · omega
  · exfalso
    have key : ∀ b ∈ ((A.subgroupOf K).map e.toMonoidHom).map (alternatingGroup (Fin n)).subtype,
        ∃ k : K, (k : X) ∈ A ∧ ((e k : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = b := by
      rintro b ⟨ã, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, Subgroup.mem_subgroupOf.mp hk, rfl⟩
    obtain ⟨k₁, hk₁A, rfl⟩ := key b₁ hb₁E
    obtain ⟨k₂, hk₂A, rfl⟩ := key b₂ hb₂E
    have hne : ∀ (k : K) (O : Finset (Fin n)), O.card = p →
        (∀ x, ((e k : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) x ≠ x ↔ x ∈ O) → k ≠ 1 := by
      intro k O hO hk hk1
      obtain ⟨x, hx⟩ : O.Nonempty := Finset.card_pos.mp (hO ▸ hp.pos)
      exact (hk x).2 hx (by simp [hk1])
    have htop : Subgroup.centralizer ({k₁} : Set K) ⊔ Subgroup.centralizer ({k₂} : Set K) = ⊤ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_sup, AltDegree.map_centralizer_singleton_mulEquiv,
        AltDegree.map_centralizer_singleton_mulEquiv,
        closure_centralizers_eq_top hp hp2 hlt (e k₁) (e k₂) O₁ O₂ hO₁ hO₂ hd hb₁ hb₂,
        Subgroup.map_top_of_surjective _ e.surjective]
    have hC : ∀ k : K, (k : X) ∈ A → k ≠ 1 →
        (Subgroup.centralizer ({k} : Set K)).map K.subtype ≤ X₀ := by
      intro k hkA hk1
      rintro _ ⟨g, hg, rfl⟩
      have hg' : (g : X) ∈ Subgroup.centralizer ({(k : X)} : Set X) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
      refine h.normalizer_le_of_le_A (Subgroup.zpowers (k : X)) (Subgroup.zpowers_le.mpr hkA) ?_
        (centralizer_singleton_le_normalizer_zpowers _ hg')
      rw [Ne, Subgroup.zpowers_eq_bot]
      exact fun h1 => hk1 (Subtype.ext h1)
    apply h.not_le
    intro g hg
    have hgtop : (⟨g, hg⟩ : K) ∈ Subgroup.centralizer ({k₁} : Set K) ⊔
        Subgroup.centralizer ({k₂} : Set K) := htop ▸ Subgroup.mem_top _
    have hmem : g ∈ (Subgroup.centralizer ({k₁} : Set K) ⊔
        Subgroup.centralizer ({k₂} : Set K)).map K.subtype := ⟨_, hgtop, rfl⟩
    rw [Subgroup.map_sup] at hmem
    exact sup_le (hC k₁ hk₁A (hne k₁ O₁ hO₁ hb₁)) (hC k₂ hk₂A (hne k₂ O₂ hO₂ hb₂)) hmem

theorem d2AltCase_of_twoMul
    (h : ∀ (p : ℕ) (hp : 5 ≤ 2 * p), D2IndexCase (.alternating (2 * p) hp)) : D2AltCase := by
  intro n hn G _ _ hglob hD1 p P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  have hn2 : n = 2 * p := hK.eq_two_mul_of_alternating hn e
  subst hn2
  exact h p hn G hglob hD1 p P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩

end CFSG.AGLEmbeddingD2
