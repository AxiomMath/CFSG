module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGlue
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGroup
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBIrrGlue
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideBlocksThree
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KFactParabolicAutomizerIrrPB : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L J U Z : Subgroup X) (y : X) (p r : ℕ),
    IsComponentOf L ⊤ → IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J →
    J ≠ L → (∀ T : Subgroup X, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set X)) →
    p.Prime → p ≠ 2 → PerfectCyclicSylow p J →
    U ≤ Subgroup.normalizer (L : Set X) → U ≤ Subgroup.normalizer (J : Set X) → IsPGroup p U →
    ⁅U, U⁆ = Z → Z ≤ Subgroup.centralizer (U : Set X) → (∀ u ∈ U, u ^ p ∈ Z) →
    p ^ 3 ≤ Z.relIndex U → U ⊓ Subgroup.centralizer (L : Set X) ≤ Z →
    y ∈ Subgroup.normalizer (L : Set X) → y ∈ Subgroup.normalizer (J : Set X) →
    y ∈ Subgroup.normalizer (U : Set X) →
    r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p → ¬ r ∣ p - 1 →
    (∀ u ∈ U, y ^ r * u * (y ^ r)⁻¹ * u⁻¹ ∈ Z) → (∃ u ∈ U, y * u * y⁻¹ * u⁻¹ ∉ Z) →
    (∀ V : Subgroup X, Z ≤ V → V ≤ U → y ∈ Subgroup.normalizer (V : Set X) → V = Z ∨ V = U) →
    False

section Glue

variable {G : Type} [Group G] [Finite G]

theorem false_of_nineThreeTwo_irr (hK1 : KFactParabolicAutomizerIrrPB) {M S L Y Z : Subgroup G}
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h2 : NineThreeTwo M S L) {p r : ℕ} {t : G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    (hYK : Y ≤ M ⊓ Subgroup.normalizer (S : Set G)) (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (hYp : IsPGroup p Y) (hYZ : ⁅Y, Y⁆ = Z) (hZc : Z ≤ Subgroup.centralizer (Y : Set G))
    (hYpow : ∀ y ∈ Y, y ^ p ∈ Z) (hidx : p ^ 3 ≤ Z.relIndex Y)
    (hCZ : Y ⊓ blockCentralizer M L ≤ Z) (htK : t ∈ M ⊓ Subgroup.normalizer (S : Set G))
    (htL : t ∈ Subgroup.normalizer (L : Set G)) (htY : t ∈ Subgroup.normalizer (Y : Set G))
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrp : r ≠ p) (hrp1 : ¬ r ∣ p - 1)
    (htr : ∀ y ∈ Y, t ^ r * y * (t ^ r)⁻¹ * y⁻¹ ∈ Z) (htnt : ∃ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∉ Z)
    (hirr : ∀ V : Subgroup G, Z ≤ V → V ≤ Y → t ∈ Subgroup.normalizer (V : Set G) →
      V = Z ∨ V = Y) : False := by
  have hYM : Y ≤ M := hYK.trans inf_le_left
  have hZY : Z ≤ Y := hYZ ▸ Subgroup.commutator_le_self Y
  have htM : t ∈ M := htK.1
  have hNJ : ∀ g ∈ M ⊓ Subgroup.normalizer (S : Set G), g ∈ Subgroup.normalizer (L : Set G) →
      g ∈ Subgroup.normalizer ((Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) : Set G) :=
    fun g hg hgL => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg.2, hgL⟩
  have hcomm : ⁅barM M Y, barM M Y⁆ = barM M Z := by
    have hY : (Y.subgroupOf M).map M.subtype = Y := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hYM]
    have h1 : ⁅Y, Y⁆.subgroupOf M = ⁅Y.subgroupOf M, Y.subgroupOf M⁆ := by
      change Subgroup.comap M.subtype ⁅Y, Y⁆ = _
      conv_lhs => rw [← hY, ← Subgroup.map_commutator]
      exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [← hYZ]
    unfold barM
    rw [h1, Subgroup.map_commutator]
  rw [← relIndex_barM_of_pGroup hp hp2 hYM hYp hZY] at hidx
  exact hK1 _ (barM M L) _ (barM M Y) (barM M Z) _ p r hL.component h2.1 h2.2.1
    (barM_normalizer_inf_ne_of_asc81bHyp hA hL) (ne_inf_normalizer_of_asc81bHyp hA hL hS h2) hp
    hp2 hJ (barM_le_normalizer_barM hYL)
    (barM_le_normalizer_barM fun y hy => hNJ y (hYK hy) (hYL hy)) (isPGroup_barM hYp) hcomm
    (barM_le_centralizer_barM hZc) (pow_mem_barM hYpow) hidx (barM_inf_centralizer_le hCZ)
    (mem_normalizer_barM htM htL) (mem_normalizer_barM htM (hNJ t htK htL))
    (mem_normalizer_barM htM htY) hr hr2 hr3 hrp hrp1 (conj_commutator_mem_barM htM htr)
    (exists_conj_commutator_not_mem_barM hp hp2 hYM hYp hZY htM htY htnt)
    (eq_or_eq_barM_of_irreducible hYM hZY htM htY hirr)

end Glue

theorem stmtLemmaBRelCyc_of_irrPB (h93 : Asc81bNineThree) (hK1 : KFactParabolicAutomizerIrrPB)
    (hK2 : KFactAltSixSevenAut) (hK3 : CitedBlockTransvectionCyclic)
    (hK4 : CitedBlockAltNormalizer) : StmtLemmaBRelCyc := by
  intro G _ _ M S L Y Z p r t hK hA hL hX1 hS hp hp2 hcyc hYK hYL hYp hYZ hZc hYpow hidx htK
    htL htY hr hr2 hr3 hrp hrp1 htr htnt hirr
  subst hYZ
  have hYM : Y ≤ M := hYK.trans inf_le_left
  have htM : t ∈ M := htK.1
  have hJ := perfectCyclicSylow_barM hL.le hp hcyc
  have htC : t ∈ Subgroup.normalizer ((Y ⊓ blockCentralizer M L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htY, mem_normalizer_blockCentralizer htM htL⟩
  have htZ : t ∈ Subgroup.normalizer ((⁅Y, Y⁆ : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (by rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp htY])
  have hV := hirr (Y ⊓ blockCentralizer M L ⊔ ⁅Y, Y⁆) le_sup_right
    (sup_le inf_le_left Y.commutator_le_self)
    (Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨htC, htZ⟩)
  rcases hV with hV | hV
  · exfalso
    have hCZ : Y ⊓ blockCentralizer M L ≤ ⁅Y, Y⁆ := hV ▸ le_sup_left
    have hp3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    have hsmall : (Y ⊓ blockCentralizer M L).relIndex Y ≤ p ^ 2 → False := by
      intro h
      have hdvd := Subgroup.relIndex_dvd_of_le_left Y hCZ
      have hpos : (Y ⊓ blockCentralizer M L).relIndex Y ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd
      omega
    rcases h93 G M S L hK hA hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · exact hX1 h1
    · exact false_of_nineThreeTwo_irr hK1 hA hL hS h2 hp hp2 hJ hYK hYL hYp rfl hZc hYpow hidx
        hCZ htK htL htY hr hr2 hr3 hrp hrp1 htr htnt hirr
    · obtain ⟨u, hu, hcov⟩ := hK3 G M S L p hK hA hL hX1 hS h3 hp hp2 hJ Y hYK hYL hYp
      have hcov' : ∀ x ∈ Y, ∃ k : ℕ, x * (u ^ k)⁻¹ ∈ ⁅Y, Y⁆ := by
        intro x hx
        obtain ⟨k, hk⟩ := hcov x hx
        exact ⟨k, hCZ ⟨Y.mul_mem hx (Y.inv_mem (Y.pow_mem hu k)), hk⟩⟩
      have hle := relIndex_le_of_cyclic_mod_central hp.pos hu hZc (hYpow u hu) hcov'
      have hp1 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      rw [pow_one] at hp1
      omega
    · apply hsmall
      rw [relIndex_blockCentralizer_eq hYM]
      exact hK2 _ (barM M L) (barM M Y) p hL.component (Or.inl h4.2.2.1) hp hp2
        (barM_le_normalizer_barM hYL) (isPGroup_barM hYp)
    · apply hsmall
      rw [relIndex_blockCentralizer_eq hYM]
      exact hK2 _ (barM M L) (barM M Y) p hL.component (Or.inr h5.2.1) hp hp2
        (barM_le_normalizer_barM hYL) (isPGroup_barM hYp)
    · exact hsmall (hK4 G M S L p hK hA hL hX1 hS (Or.inl h6) hp hp2 hJ Y hYK hYL hYp)
    · exact hsmall (hK4 G M S L p hK hA hL hX1 hS (Or.inr (Or.inl h7)) hp hp2 hJ Y hYK hYL hYp)
    · exact hsmall (hK4 G M S L p hK hA hL hX1 hS (Or.inr (Or.inr h8)) hp hp2 hJ Y hYK hYL hYp)
  · have hYC := le_of_sup_eq_of_central inf_le_left rfl hZc hV
    exact (barM_mono (hYC.trans inf_le_right)).trans (barM_blockCentralizer_le M L)

end CFSG.AGLEmbedding
