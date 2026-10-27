module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcGraph
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTw
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InOuter
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6C4Rig
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6F4

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank

theorem outerCoreTrivAt_twistedE6_graph
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    OuterCoreTrivAt (fieldActor (t := TwistTag.E6) σ σ) := by
  classical
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (show 1 ≤ f * 2 by omega) (by rw [hK, ← pow_mul])
    rw [ringChar.eq K p]
    exact hp2
  obtain ⟨-, -, -, -, -, -, -, -, -, hσP, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC₀
  have hMC₀ := Burgoyne.E2.twE6F4Image_le_graphFixedRootGroup σ
  have hF : ∀ g : C₀, fieldActor (t := TwistTag.E6) σ σ g = g ↔
      diagramMap TwistTag.E6 K * (g : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * diagramMap TwistTag.E6 K := by
    intro g
    rw [← Subtype.coe_inj, hσP, mul_inv_eq_iff_eq_mul]
  have hJq : CFSG.IsQuasisimple ((Burgoyne.E2.twE6F4Image σ).subgroupOf C₀) := by
    obtain ⟨hsimp, hnab⟩ := Burgoyne.E2.isSimpleGroup_twE6F4Image hK2 σ
    exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMC₀).symm
      (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  refine outerCoreTrivAt_of_normal_quasisimple (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    (fun j hj => (hF j).2
      (mem_twistedFixedGroup_id_iff.1 (Burgoyne.E2.twE6F4Image_le σ hj).1).2)
    (fun g hg j hj => ?_) hJq fun β hβ hfix =>
      Burgoyne.E2.eq_one_of_odd_fix_twE6F4Image hp hp2 hf hK σ hσ hβ fun x hx => hfix x hx
  have hgP := (hF g).1 hg
  have hgC : (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le _ _ _ g.2).1
  have hgσ : Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.E6.tag K) = g := by
    have h := (graphFixedRootGroup_le _ _ _ g.2).2
    change twistHom TwistTag.E6 K σ.toRingHom g = g at h
    rw [twistHom_apply] at h
    have hPg : diagramMap TwistTag.E6 K * (g : ModGL TwistTag.E6.tag K) *
        (diagramMap TwistTag.E6 K)⁻¹ = g := by rw [hgP, mul_inv_cancel_right]
    exact mul_left_cancel (mul_right_cancel (h.trans hPg.symm))
  have hgY : (g : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) ⊓
      entrywiseFixedGroup TwistTag.E6.tag σ :=
    ⟨mem_twistedFixedGroup_id_iff.2 ⟨hgC, hgP⟩, mem_entrywiseFixedGroup.2 ⟨hgC, hgσ⟩⟩
  have hjM : ((j : C₀) : ModGL TwistTag.E6.tag K) ∈ Burgoyne.E2.twE6F4Image σ := hj
  have h := (Burgoyne.E2.twE6F4Image_normal σ).conj_mem ⟨_, Burgoyne.E2.twE6F4Image_le σ hjM⟩ hjM
    ⟨_, hgY⟩
  rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact h

theorem outerCoreTrivAt_twistedE6_signedGraph
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    OuterCoreTrivAt (Burgoyne.E2.twE6SignAut σ) := by
  classical
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (show 1 ≤ f * 2 by omega) (by rw [hK, ← pow_mul])
    rw [ringChar.eq K p]
    exact hp2
  have hq : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨μ, hμq⟩ := Burgoyne.E2.exists_unit_pow_sub_one_eq_neg_one hq hK
  have hμ : σ (μ : K) = -μ := by
    have hq1 : 1 ≤ p ^ f := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero)
    rw [hσ, show p ^ f = p ^ f - 1 + 1 by omega, pow_succ, ← Units.val_pow_eq_pow_val, hμq,
      Units.val_neg, Units.val_one, neg_one_mul]
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC₀
  have hJC := Burgoyne.E2.twE6C4Sub_le_graphFixedRootGroup hK2 σ hμ
  have hF : ∀ g : C₀, Burgoyne.E2.twE6SignAut σ g = g ↔
      E6SignedGraph.twistA K * (g : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * E6SignedGraph.twistA K := by
    intro g
    rw [← Subtype.coe_inj, Burgoyne.E2.coe_twE6SignAut hp hp2 hf hK σ hσ, mul_inv_eq_iff_eq_mul]
  have hJq : CFSG.IsQuasisimple ((Burgoyne.E2.twE6C4Sub σ μ).subgroupOf C₀) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm
      (Burgoyne.E2.isQuasisimple_twE6C4Sub hK2 σ μ)
  refine outerCoreTrivAt_of_normal_quasisimple (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    (fun j hj => (hF j).2 (Burgoyne.E2.twE6C4Sub_commute σ μ hj)) (fun g hg j hj => ?_) hJq
    fun β hβ hfix =>
      Burgoyne.E2.eq_one_of_odd_fix_twE6C4Sub hp hp2 hf hK σ hσ hμ hβ fun x hx => hfix x hx
  rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Burgoyne.E2.twE6C4Sub_conj_mem hK2 σ hμ g.2 ((hF g).1 hg) hj

theorem twistedE6GraphCoreInput :
    TwistedE6GraphCoreInput := by
  intro p f hp hp2 hf K _ _ hK σ hσ g u hα
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hαo : MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor (t := TwistTag.E6) σ σ ∉ twistedE6Inn K σ := by
    intro hin
    have h1 := hΘ _ g u σ rfl
    have h2 : MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
        fieldActor (t := TwistTag.E6) σ σ ∈ Θ.ker := by
      rw [hker]
      exact Subgroup.mem_sup_left hin
    rw [MonoidHom.mem_ker, h1] at h2
    have hKo : Nat.card K = (p ^ f) ^ TwistTag.E6.order := hK
    obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 hp hf K hKo
    have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
    rw [hσσ', h2, orderOf_one] at hord
    exact absurd hord (by decide)
  obtain ⟨ψ, hψ | hψ⟩ :=
    Burgoyne.E2.TwE6In.twE6_outer_involution_conj hp hp2 hf K hK σ hσ _ hα hαo
  · exact outerCoreAt_of_conj hψ (outerCoreTrivAt_twistedE6_graph hp hp2 hf hK σ hσ).outerCoreAt
  · exact outerCoreAt_of_conj hψ
      (outerCoreTrivAt_twistedE6_signedGraph hp hp2 hf hK σ hσ).outerCoreAt

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
