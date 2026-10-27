module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1ReeAct
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Tr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1BT
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Types
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FRee
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Ree CFSG.AGLEmbedding

section Native

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem ree_bruhat (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∃ w : ↥(ReeTag.G2.reeGamma K a), w ∉ ReeModel.stdB a K ∧
      ∀ g : ↥(ReeTag.G2.reeGamma K a), g ∉ ReeModel.stdB a K →
        ∃ u ∈ ReeModel.stdU a K, ∃ m ∈ ReeModel.stdB a K, g = u * w * m := by
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨hn, hηξ, -, -, -, -, hreg, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  have hcoset : ∀ g g' : ↥(ReeTag.G2.reeGamma K a),
      (QuotientGroup.mk g : ↥(ReeTag.G2.reeGamma K a) ⧸
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) = QuotientGroup.mk g' ↔
        g⁻¹ * g' ∈ ReeModel.stdB a K := fun g g' => QuotientGroup.eq
  refine ⟨⟨_, hn⟩, ?_, ?_⟩
  · intro hnB
    apply hηξ
    rw [hcoset]
    simpa using (ReeModel.stdB a K).inv_mem hnB
  · intro g hg
    have hgξ : (QuotientGroup.mk g : ↥(ReeTag.G2.reeGamma K a) ⧸
        (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) ≠
          QuotientGroup.mk 1 := by
      intro h
      apply hg
      rw [hcoset] at h
      simpa using (ReeModel.stdB a K).inv_mem h
    obtain ⟨u, hu, -⟩ := hreg _ _ hηξ hgξ
    have hu' : (QuotientGroup.mk ((u : ↥(ReeTag.G2.reeGamma K a)) * ⟨_, hn⟩) :
        ↥(ReeTag.G2.reeGamma K a) ⧸
          (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) =
        QuotientGroup.mk g := by
      rw [← hu, MulAction.Quotient.smul_mk]
      rfl
    refine ⟨(u : ↥(ReeTag.G2.reeGamma K a)), u.2, _, (hcoset _ _).1 hu', ?_⟩
    group

theorem ree_core (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∀ c : ↥(ReeTag.G2.reeGamma K a),
      (∀ x : ↥(ReeTag.G2.reeGamma K a), x⁻¹ * c * x ∈ ReeModel.stdB a K) → c = 1 := by
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨_, _, hfaith, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  intro c hc
  refine hfaith.eq_of_smul_eq_smul fun ω => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ω
  rw [one_smul, MulAction.Quotient.smul_mk, QuotientGroup.eq]
  have h1 := (ReeModel.stdB a K).inv_mem (hc x)
  have h2 : (x⁻¹ * c * x)⁻¹ = (c * x)⁻¹ * x := by group
  rw [h2] at h1
  exact h1

theorem aut_eq_one_ree (hK : Nat.card K = 3 ^ (2 * a + 1))
    (b : MulAut ↥(ReeTag.G2.reeGamma K a)) (hb : ¬ 3 ∣ orderOf b)
    (hfix : ∀ u ∈ ReeModel.stdU a K, b u = u) : b = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨P, hP⟩, hNU, -, -⟩ := ReeModel.std_facts hK
  obtain ⟨w, hw, hbr⟩ := ree_bruhat hK
  have hUp : IsPGroup 3 ↥(ReeModel.stdU a K) := by
    rw [← hP]
    exact P.isPGroup'
  exact aut_eq_one_of_bruhat b hb hNU hUp hfix hw hbr (ree_core hK)

theorem e1Core_ree_native (hK : Nat.card K = 3 ^ (2 * a + 1))
    (hBT : LieType.BorelTits.Holds ↥(ReeTag.G2.reeGamma K a) 3) :
    E1Core 3 ↥(ReeTag.G2.reeGamma K a) := by
  intro b hb1 hbr hHH E hE hinv
  by_contra hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥(ReeTag.G2.reeGamma K a) := Subtype.finite
  obtain ⟨M, S, hM, hS, hR⟩ := e1_engine hBT b hHH hE hinv hne
  obtain ⟨⟨P, hP⟩, hNU, hco, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq (MulEquiv.refl ↥(ReeTag.G2.reeGamma K a)) S P
  have h1 : (normalizer ((S : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a))).map e'.toMonoidHom = ReeModel.stdB a K := by
    rw [Subgroup.map_equiv_normalizer_eq, he', hP, hNU]
  have h2 : normalizer ((S : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a)) = (ReeModel.stdB a K).comap e'.toMonoidHom := by
    rw [← h1, Subgroup.comap_map_eq_self_of_injective e'.injective]
  have hcoS : IsCoatom (normalizer ((S : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a))) := h2 ▸ (Subgroup.isCoatom_comap e').2 hco
  have hMN : M = normalizer ((S : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a)) := by
    rcases hcoS.le_iff.1 hS with h | h
    · exact absurd h hM.1
    · exact h
  have hbS : ∀ x ∈ (S : Subgroup ↥(ReeTag.G2.reeGamma K a)), b x = x :=
    hR S S.isPGroup' (Subgroup.le_normalizer.trans hS) hMN.le
  set b' : MulAut ↥(ReeTag.G2.reeGamma K a) :=
    (e' : MulAut ↥(ReeTag.G2.reeGamma K a)) * b * (e' : MulAut ↥(ReeTag.G2.reeGamma K a))⁻¹
    with hb'
  have hfix : ∀ u ∈ ReeModel.stdU a K, b' u = u := by
    intro u hu
    have hu' : u ∈ (S : Subgroup ↥(ReeTag.G2.reeGamma K a)).map e'.toMonoidHom := by
      rw [he', hP]
      exact hu
    obtain ⟨s, hs, hsu⟩ := hu'
    have hsu' : e' s = u := hsu
    subst hsu'
    have h3 : (e' : MulAut ↥(ReeTag.G2.reeGamma K a))⁻¹ (e' s) = s := e'.symm_apply_apply s
    have h4 : b' (e' s) = e' (b ((e' : MulAut ↥(ReeTag.G2.reeGamma K a))⁻¹ (e' s))) := rfl
    rw [h4, h3, hbS s hs]
  have hb'ord : ¬ 3 ∣ orderOf b' := by
    have : orderOf b' = orderOf b := by
      refine (SemiconjBy.orderOf_eq (e' : MulAut ↥(ReeTag.G2.reeGamma K a)) ?_).symm
      show (e' : MulAut ↥(ReeTag.G2.reeGamma K a)) * b = b' * (e' : MulAut _)
      rw [hb']
      group
    rw [this]
    exact hbr
  have hb'1 := aut_eq_one_ree hK b' hb'ord hfix
  apply hb1
  have h4 : b = (e' : MulAut ↥(ReeTag.G2.reeGamma K a))⁻¹ * b' * (e' : MulAut _) := by
    rw [hb']
    group
  rw [h4, hb'1]
  group

end Native

section Top


theorem e1_ree : E1Type FReed := by
  intro r Y _ _ hr hr2 hF b hb1 hbr hHH E hE hinv
  obtain ⟨hp3, f, hf, hm⟩ := hF
  subst hp3
  obtain ⟨f', hR⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.reeTitsModel_of_FRee (Y := Y) ⟨f, hf, hm⟩
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.ree_model_data_pos hR
  have hBT : LieType.BorelTits.Holds Y 3 := holds_of_lieModel hm (by decide)
  have hBT' : LieType.BorelTits.Holds ↥(ReeTag.G2.reeGamma K a) 3 :=
    LieType.BorelTits.Holds.of_mulEquiv e hBT
  exact E1Core.of_mulEquiv e (e1Core_ree_native hK hBT') b hb1 hbr hHH E hE hinv

end Top

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
