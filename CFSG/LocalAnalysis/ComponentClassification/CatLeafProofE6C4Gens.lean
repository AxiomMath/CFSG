module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Frame
public import CFSG.LieType.Chevalley.E6SignedGraphLongRoot

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ClassicalInvolution.WeakCT (range_le_of_tv)
open scoped MatrixGroups Matrix commutatorElement

variable {K : Type} [Field K]

theorem orbitFixed_singleton_eq_bot
    (hK : ringChar K ≠ 2) {ε : E6Vec} (hε : IsRoot TwistTag.E6.tag ε) (hρ : rho ε = ε)
    (hodd : ¬ Even (ε ⟨1, by decide⟩)) : orbitFixed K {ε} = ⊥ := by
  have hO : TwistTag.E6.diagramOrbit ε = {ε} := by
    rw [diagramOrbit_eq, hρ, Finset.pair_eq_singleton]
  refine orbitFixed_eq_bot_of_not_mem hK ⟨ε, hε, hO⟩ fun h => ?_
  rcases h.2 with h2 | ⟨-, he⟩
  · rw [Finset.card_singleton] at h2
    exact absurd h2 (by decide)
  · exact hodd (he ε (Finset.mem_singleton_self ε))

theorem commutator_pinnedX_mul_mem
    {α β γ δ ε : E6Vec} (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β)
    (hγ : IsRoot TwistTag.E6.tag γ) (hδ : IsRoot TwistTag.E6.tag δ)
    (hε : IsRoot TwistTag.E6.tag ε) (hαδ : α + δ = ε) (hβγ : β + γ = ε)
    (h1 : α ≠ δ ∧ α ≠ -δ) (h2 : β ≠ γ ∧ β ≠ -γ)
    (h3 : α ≠ γ ∧ α ≠ -γ ∧ ¬ IsRoot TwistTag.E6.tag (α + γ))
    (h4 : β ≠ δ ∧ β ≠ -δ ∧ ¬ IsRoot TwistTag.E6.tag (β + δ))
    (h5 : ε ≠ α ∧ ε ≠ -α ∧ ¬ IsRoot TwistTag.E6.tag (ε + α))
    (h6 : ε ≠ δ ∧ ε ≠ -δ ∧ ¬ IsRoot TwistTag.E6.tag (ε + δ))
    (h7 : γ ≠ δ ∧ γ ≠ -δ ∧ ¬ IsRoot TwistTag.E6.tag (γ + δ)) (s t u v : K) :
    ⁅pinnedX TwistTag.E6.tag K α s * pinnedX TwistTag.E6.tag K β t,
      pinnedX TwistTag.E6.tag K γ u * pinnedX TwistTag.E6.tag K δ v⁆ ∈
      rootSubgroup TwistTag.E6.tag K ε := by
  have hform : ∀ {x y : E6Vec}, IsRoot TwistTag.E6.tag x → IsRoot TwistTag.E6.tag y → x ≠ y →
      x ≠ -y → IsRoot TwistTag.E6.tag (x + y) → ∀ c d : K,
      ∃ e : K, ⁅pinnedX TwistTag.E6.tag K x c, pinnedX TwistTag.E6.tag K y d⁆ =
        pinnedX TwistTag.E6.tag K (x + y) e := fun hx hy hne hne' hxy c d =>
    ⟨_, ((simply_laced_root_commutator_unit TwistTag.E6.tag simplyLaced_E6 hx hy hne hne').1
      hxy).2 K c d⟩
  rw [commute_pinnedX_of_not_isRoot hγ hδ h7.1 h7.2.1 h7.2.2 u v]
  obtain ⟨e₁, he₁⟩ := hform hα hδ h1.1 h1.2 (hαδ ▸ hε) s v
  obtain ⟨e₂, he₂⟩ := hform hβ hγ h2.1 h2.2 (hβγ ▸ hε) t u
  rw [hαδ] at he₁
  rw [hβγ] at he₂
  rw [commutatorElement_mul_mul_of_commute he₁ he₂
    (commute_pinnedX_of_not_isRoot hβ hδ h4.1 h4.2.1 h4.2.2 t v)
    (commute_pinnedX_of_not_isRoot hα hγ h3.1 h3.2.1 h3.2.2 s u)
    (commute_pinnedX_of_not_isRoot hε hα h5.1 h5.2.1 h5.2.2 e₂ s)
    (commute_pinnedX_of_not_isRoot hε hδ h6.1 h6.2.1 h6.2.2 e₂ v)]
  exact mul_mem (mem_rootSubgroup.2 ⟨e₁, rfl⟩) (mem_rootSubgroup.2 ⟨e₂, rfl⟩)

theorem conj_mul_eq {G : Type*} [Group G] (n x y : G) :
    n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by
  group

theorem e6C4Rho_zero_gens
    (c : K) :
    (∃ t₁ t₂ : K, e6C4Rho K 0 (tv 0 1 c) =
      pinnedX TwistTag.E6.tag K (simpleRoot 0) t₁ *
        pinnedX TwistTag.E6.tag K (rho (simpleRoot 0)) t₂) ∧
    ∃ t₁ t₂ : K, e6C4Rho K 0 (tv 1 0 c) =
      pinnedX TwistTag.E6.tag K (-simpleRoot 0) t₁ *
        pinnedX TwistTag.E6.tag K (-rho (simpleRoot 0)) t₂ := by
  obtain ⟨ε₂, -, hx₂⟩ := canonicalRep_conj_xUnit (K := K) e6C4Word ⟨2, by decide⟩
  obtain ⟨ε₄, -, hx₄⟩ := canonicalRep_conj_xUnit (K := K) e6C4Word ⟨4, by decide⟩
  obtain ⟨η₂, -, hy₂⟩ := canonicalRep_conj_yUnit (K := K) e6C4Word ⟨2, by decide⟩
  obtain ⟨η₄, -, hy₄⟩ := canonicalRep_conj_yUnit (K := K) e6C4Word ⟨4, by decide⟩
  obtain ⟨hw₂, hw₄⟩ := e6C4Word_smul
  have hp : TwistTag.E6.perm (TwistTag.E6.orbitMin ⟨1, by decide⟩) ≠
      TwistTag.E6.orbitMin ⟨1, by decide⟩ := by decide
  have hm : TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hq : TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide
  refine ⟨⟨ε₂ * c, ε₄ * ((orbitSign K e6C4Word ⟨1, by decide⟩ : K) * c), ?_⟩,
    ⟨η₂ * c, η₄ * ((orbitSign K e6C4Word ⟨1, by decide⟩ : K) * c), ?_⟩⟩
  · change orbitSL2 K e6C4Word ⟨1, by decide⟩ (tv 0 1 c) = _
    rw [tv_zero_one_eq_uSL, orbitSL2_uSL_pair e6C4Word hp, hm, hq, conj_mul_eq, hx₂, hx₄, hw₂,
      hw₄]
  · change orbitSL2 K e6C4Word ⟨1, by decide⟩ (tv 1 0 c) = _
    rw [tv_one_zero_eq_vSL, orbitSL2_vSL_pair e6C4Word hp, hm, hq, conj_mul_eq, hy₂, hy₄,
      smul_neg, smul_neg, hw₂, hw₄]

theorem e6C4Rho_mem_fixedGroup
    (k : Fin 4) (M : SL(2, K)) : e6C4Rho K k M ∈ fixedGroup K := by
  have hs1 : ∀ a : Fin TwistTag.E6.foldedTag.rank, TwistTag.E6.orbitMin a ≠ ⟨1, by decide⟩ →
      orbitSign K 1 a = 1 := fun a ha => by
    rw [orbitSign, one_smul, Pi.single_eq_of_ne (Ne.symm ha), zpow_zero]
  fin_cases k
  · exact orbitSL2_mem_fixedGroup e6C4Word_mem (fun h => absurd h (by decide)) M
  · exact orbitSL2_mem_fixedGroup (one_mem _) (fun h => absurd h (by decide)) M
  · exact orbitSL2_mem_fixedGroup (one_mem _) (fun h => absurd h (by decide)) M
  · exact orbitSL2_mem_fixedGroup (one_mem _) (fun _ => hs1 _ (by decide)) M

theorem e6C4Rho_two_gens
    (c : K) :
    e6C4Rho K 2 (tv 0 1 c) = pinnedX TwistTag.E6.tag K (Pi.single ⟨2, by decide⟩ 1) c *
        pinnedX TwistTag.E6.tag K (Pi.single ⟨4, by decide⟩ 1) c ∧
      e6C4Rho K 2 (tv 1 0 c) = pinnedX TwistTag.E6.tag K (-Pi.single ⟨2, by decide⟩ 1) c *
        pinnedX TwistTag.E6.tag K (-Pi.single ⟨4, by decide⟩ 1) c := by
  rw [(e6C4Rho_eq_e6F4Rho K).2.1]
  refine ⟨?_, ?_⟩
  · change simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩ (tv 0 1 c) *
      simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩ (tv 0 1 c) = _
    rw [simpleRootSL2_tv01, simpleRootSL2_tv01, pinnedX_single, pinnedX_single]
  · change simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩ (tv 1 0 c) *
      simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩ (tv 1 0 c) = _
    rw [simpleRootSL2_tv10, simpleRootSL2_tv10, pinnedX_neg_single, pinnedX_neg_single]

theorem e6C4_roots
    :
    IsRoot TwistTag.E6.tag (simpleRoot 0) ∧ IsRoot TwistTag.E6.tag (rho (simpleRoot 0)) ∧
      IsRoot TwistTag.E6.tag (simpleRoot 0 + Pi.single ⟨4, by decide⟩ 1) ∧
      IsRoot TwistTag.E6.tag (simpleRoot 0 + -Pi.single ⟨2, by decide⟩ 1) := by
  have ha := isRoot_simpleRoot 0
  have hb : IsRoot TwistTag.E6.tag (rho (simpleRoot 0)) := by
    rw [← e6C4Word_smul.2]
    exact IsRoot.smul (isRoot_single _ _) _
  have hg := IsRoot.reflect ⟨4, by decide⟩ ha
  have hd := IsRoot.reflect ⟨2, by decide⟩ ha
  rw [show reflect TwistTag.E6.tag ⟨4, by decide⟩ (simpleRoot 0) =
    simpleRoot 0 + Pi.single ⟨4, by decide⟩ 1 by decide] at hg
  rw [show reflect TwistTag.E6.tag ⟨2, by decide⟩ (simpleRoot 0) =
    simpleRoot 0 + -Pi.single ⟨2, by decide⟩ 1 by decide] at hd
  exact ⟨ha, hb, hg, hd⟩

end CFSG.ComponentClassification.CatLeafProof
