module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25G2.BenderBorel MulAction
open CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem le_normalizer_of_bender {X : Type} [Group X] [Finite X] [hs : IsSimpleGroup X]
    (hB : fusionIsBenderGroup X) (Q : Sylow 2 X) {M : Subgroup X}
    (hQM : (Q : Subgroup X) ≤ M) (hM : M ≠ ⊤) :
    M ≤ Subgroup.normalizer ((Q : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, _, hq4, hBor⟩ := exists_borel_of_bender hB
  obtain ⟨-, ⟨D, hDcyc, -, -, hsup⟩, -, hZcard, -⟩ := hBor Q
  have hsolvN := isSolvable_normalizer_of_sup_cyclic Q.isPGroup' hDcyc hsup
  have hreg := regular_of_borel (isSimpleBenderGroup_of_fusion hB) Q hsolvN
  set N := Subgroup.normalizer ((Q : Subgroup X) : Set X) with hN
  have hQN : (Q : Subgroup X) ≤ N := Subgroup.le_normalizer
  have hQne : (Q : Subgroup X) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (Subgroup.center (Q : Subgroup X)) = 1 := by
      have : Subsingleton (↥(Q : Subgroup X)) := by
        rw [hbot]
        infer_instance
      have : Subsingleton (Subgroup.center (Q : Subgroup X)) :=
        (Subgroup.center (Q : Subgroup X)).subtype_injective.subsingleton
      exact Nat.card_unique
    omega
  by_contra hnot
  obtain ⟨m₀, hm₀M, hm₀N⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hconj : ∀ g : X, ∀ x ∈ (Q : Subgroup X), g * x * g⁻¹ ∈ M := by
    intro g x hx
    have hex : ∃ m ∈ M, m⁻¹ * g ∈ N := by
      by_cases hg : g ∈ N
      · exact ⟨1, M.one_mem, by simpa using hg⟩
      · have hα : (QuotientGroup.mk m₀ : X ⧸ N) ≠ QuotientGroup.mk 1 := by
          intro h
          apply hm₀N
          have := QuotientGroup.eq.mp h
          simpa using N.inv_mem this
        have hβ : (QuotientGroup.mk g : X ⧸ N) ≠ QuotientGroup.mk 1 := by
          intro h
          apply hg
          have := QuotientGroup.eq.mp h
          simpa using N.inv_mem this
        obtain ⟨⟨r, hr⟩, hrβ, -⟩ := hreg hα hβ
        refine ⟨r * m₀, M.mul_mem (hQM hr) hm₀M, ?_⟩
        have h1 : (QuotientGroup.mk (r * m₀) : X ⧸ N) = QuotientGroup.mk g := by
          have : (⟨r, hr⟩ : ↥(Q : Subgroup X)) • (QuotientGroup.mk m₀ : X ⧸ N) =
              QuotientGroup.mk g := hrβ
          simpa [MulAction.Quotient.smul_mk] using this
        exact QuotientGroup.eq.mp h1
    obtain ⟨m, hmM, hmN⟩ := hex
    have hgn : g = m * (m⁻¹ * g) := by group
    set n := m⁻¹ * g with hn
    have hnx : n * x * n⁻¹ ∈ (Q : Subgroup X) := by
      have := (Subgroup.mem_normalizer_iff.mp hmN) x
      exact this.mp hx |> fun h => by simpa using h
    have hmem : m * (n * x * n⁻¹) * m⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hmM (hQM hnx)) (M.inv_mem hmM)
    have heq : g * x * g⁻¹ = m * (n * x * n⁻¹) * m⁻¹ := by rw [hgn]; group
    rw [heq]
    exact hmem
  have hcl : Subgroup.normalClosure ((Q : Subgroup X) : Set X) ≤ M := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hay
    exact hconj g a ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ((Q : Subgroup X) : Set X)) with h | h
  · apply hQne
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ Subgroup.normalClosure ((Q : Subgroup X) : Set X) :=
      Subgroup.subset_normalClosure hx
    rw [h] at this
    exact this
  · apply hM
    rw [eq_top_iff]
    rw [h] at hcl
    exact hcl

theorem overgroups_of_bender {X : Type} [Group X] [Finite X] (hB : fusionIsBenderGroup X) :
    Overgroups X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup X := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  refine Overgroups.of_sylow (Q : Subgroup X) (isSylowTwoOf_top_of_sylow Q) fun Y hQY hY => ?_
  obtain ⟨_, _, _, hBor⟩ := exists_borel_of_bender hB
  obtain ⟨hSE, ⟨D, hDcyc, -, -, hsup⟩, -, -, -⟩ := hBor Q
  have hsolvN := isSolvable_normalizer_of_sup_cyclic Q.isPGroup' hDcyc hsup
  have hYN := le_normalizer_of_bender hB Q hQY hY
  have hQle : (Q : Subgroup X) ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQY hYN Q.isPGroup'
  intro x hx
  have hxN : x ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X) := hYN hx.1
  have hc : ∀ r ∈ (Q : Subgroup X), x * r = r * x := fun r hr =>
    ((Subgroup.mem_centralizer_iff.mp hx.2) r (hQle hr)).symm
  exact hQle (centralizer_le_of_borel (isSimpleBenderGroup_of_fusion hB) Q hsolvN hSE.1 hxN hc)

theorem overgroups_isPSL_two {X : Type} [Group X] [Finite X] {f : ℕ} (h : IsPSL 2 2 f X) :
    Overgroups X :=
  overgroups_of_bender (A5.C25.fusionIsBenderGroup_of_isPSL h)

theorem overgroups_isSz {X : Type} [Group X] [Finite X] {f : ℕ} (h : IsSz f X) : Overgroups X :=
  overgroups_of_bender (A5.C25.fusionIsBenderGroup_of_isSz h)

theorem overgroups_isPSU_three {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : IsPSU 3 2 f X) : Overgroups X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
  exact overgroups_of_bender
    (Or.inr (Or.inl ⟨f, hf, ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)⟩⟩))

end CFSG.QuasithinUnique.Bridge.Over
