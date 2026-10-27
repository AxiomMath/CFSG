module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolBackward
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm29

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_isSolomonMember_of_top (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) {K : Subgroup G}
    (hK2 : IsTwoComponentIn K (⊤ : Subgroup G)) (hKm : IsSolomonMember K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GeneralizedFitting.subgroup G with hF
  have hO := Sol76.pPrimeCore_eq_bot_of_fStar hsF hnF
  have hZF : center F = ⊥ := Sol76.center_eq_bot_of_simple_nonab hnF
  obtain ⟨-, T, hT, -, hTC, -⟩ := hKm
  have hKp : IsPComponent 2 K := isPComponent_subgroupOf_top_iff'.mp hK2.2
  obtain ⟨hsub, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 K).mp hKp
  have hOK : pPrimeCore 2 ↥K = ⊥ := by
    have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hsub
    rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h1
    exact h1
  have hKq : IsQuasisimple ↥K := LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot) hq
  have hKcomp : CFSG.Open.IsComponentOf K ⊤ :=
    ⟨le_top, Sol76.open_isSubnormal_top hsub, Group.isPerfect_def.mp hKq.1, hKq.2.1⟩
  have hKF : K ≤ F := (Layer.component_le hKcomp).trans le_sup_right
  have hFq : IsQuasisimple ↥F := (LocalCores.isQuasisimple_of_isSimpleGroup hnF).1
  have hKne : K ≠ ⊥ := Sol78.ne_bot_of_isPComponent' hKp
  have hKeq : K = F := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hFq
        (hsub.subgroupOf (K := F)) with h | h
    · refine le_antisymm hKF fun x hx => ?_
      have : (⟨x, hx⟩ : F) ∈ K.subgroupOf F := by rw [h]; trivial
      exact mem_subgroupOf.mp this
    · exfalso
      rw [hZF, le_bot_iff] at h
      apply hKne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hKF hx⟩ : F) ∈ K.subgroupOf F := mem_subgroupOf.mpr hx
      rw [h, mem_bot] at this
      exact mem_bot.mpr (congrArg Subtype.val this)
  apply hT
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨-, hxK⟩ := hTC hx
  have hxc : x ∈ centralizer (F : Set G) := by
    rw [mem_centralizer_iff]
    intro f hf
    have h1 := hxK f (hKeq ▸ hf)
    rw [hOK, Subgroup.map_bot, mem_bot] at h1
    calc f * x = x * (f * (f⁻¹ * x⁻¹ * f * x)) := by group
      _ = x * f := by rw [h1, mul_one]
  have hxF : x ∈ F :=
    ((GeneralizedFitting.centralizer_le_fitting G).trans le_sup_left) hxc
  have hxZ : (⟨x, hxF⟩ : F) ∈ center F := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp hxc) g g.2)
  rw [hZF, mem_bot] at hxZ
  exact mem_bot.mpr (congrArg Subtype.val hxZ)

theorem false_of_solomonLt_bot (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) {X Y : Subgroup G}
    (hX : IsSolomonMember X) (hY : IsSolomonMember Y)
    (hYc : IsTwoComponentIn Y (conjClosure
      (twoLayerIn (X ⊓ centralizer (((⊥ : Subgroup G) : Subgroup G) : Set G)))
      (twoLayerIn (centralizer (((⊥ : Subgroup G) : Subgroup G) : Set G))))) : False := by
  have hstar := star_of_isSolomonMember hX (IsPGroup.of_bot) bot_le
  obtain ⟨hYC, -⟩ := isTwoComponentIn_of_conjClosure hstar hYc
  have h1 : centralizer (((⊥ : Subgroup G) : Subgroup G) : Set G) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => mem_centralizer_iff.mpr fun y hy => ?_
    rw [SetLike.mem_coe, mem_bot] at hy
    rw [hy, one_mul, mul_one]
  rw [h1] at hYC
  exact not_isSolomonMember_of_top hsF hnF hYC hY

theorem mirrorGood_of_reflTransGen (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) {a : G} {J K : Subgroup G}
    (ha : orderOf a = 2) (hJ : IsTwoComponentIn J (centralizer ({a} : Set G)))
    (hML : GSMirrorMaximal J) (h : Relation.ReflTransGen SolomonLink J K) :
    MirrorGood J K ∧ IsSolomonMember K := by
  induction h with
  | refl => exact ⟨mirrorGood_self ha hJ, isSolomonMember_of_isTwoComponentAt ha hJ⟩
  | tail _ hlink ih =>
    obtain ⟨hgood, hmem⟩ := ih
    obtain ⟨⟨e⟩, hlt | hlt⟩ := hlink
    · obtain ⟨-, hK'm, T, hT2, hTQ, hK'⟩ := hlt
      by_cases hT : T = ⊥
      · subst hT
        exact (false_of_solomonLt_bot hsF hnF hmem hK'm hK').elim
      · obtain ⟨hstar, hfw⟩ := forward hML hgood hT2 hT hTQ
        obtain ⟨hK'C, hmv⟩ := isTwoComponentIn_of_conjClosure hstar hK'
        exact ⟨hfw _ hK'C hmv, hK'm⟩
    · obtain ⟨hK'm, -, T, hT2, hTQ, hK⟩ := hlt
      by_cases hT : T = ⊥
      · subst hT
        exact (false_of_solomonLt_bot hsF hnF hK'm hmem hK).elim
      · exact ⟨backward hML hK'm hT2 hT hTQ hK ⟨e.symm⟩ hgood, hK'm⟩

theorem isSolomonMaximal_of_gsMirrorMaximal (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) {a : G} {J : Subgroup G}
    (ha : orderOf a = 2) (hJ : IsTwoComponentIn J (centralizer ({a} : Set G)))
    (hML : GSMirrorMaximal J) : IsSolomonMaximal J := by
  refine ⟨isSolomonMember_of_isTwoComponentAt ha hJ, fun K K₁ hK hlt => ?_⟩
  obtain ⟨hgood, hmem⟩ := mirrorGood_of_reflTransGen hsF hnF ha hJ hML hK.2
  have hlt' := hlt
  obtain ⟨-, hK₁m, T, hT2, hTQ, hK₁⟩ := hlt'
  by_cases hT : T = ⊥
  · subst hT
    exact (false_of_solomonLt_bot hsF hnF hmem hK₁m hK₁).elim
  obtain ⟨hstar, hfw⟩ := forward hML hgood hT2 hT hTQ
  obtain ⟨hK₁C, hmv⟩ := isTwoComponentIn_of_conjClosure hstar hK₁
  obtain ⟨-, ⟨e₁⟩, -⟩ := hfw K₁ hK₁C hmv
  obtain ⟨-, ⟨e⟩, -⟩ := hgood
  exact ⟨hK.1, hK.2.tail ⟨⟨e.trans e₁.symm⟩, Or.inl hlt⟩⟩

end CFSG.ComponentClassification.Foote5.SolMax
