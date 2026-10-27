module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Spin
public import CFSG.ClassicalInvolution.RouteD.TWEB6Layer
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBLocal
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutDiagC
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBRecognition
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}


theorem exists_bridges_group [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (hshape : LocalShapeT p f 0 .POmegaOdd 7 Ω x) {M : Subgroup G} (nd : DNodes p f 6 Ω M)
    (hx : ∀ a, nd.J a ∈ centralizingMembers Ω {x}) :
    ∃ N₁ ∈ centralizingMembers Ω {x}, ∃ N₂ ∈ centralizingMembers Ω {x},
      (∀ a : Fin 6, a.val < 4 → Commutes N₁ (nd.J a) ∧ Commutes N₂ (nd.J a)) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨4, by norm_num⟩) N₁) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨5, by norm_num⟩) N₁) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨4, by norm_num⟩) N₂) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨5, by norm_num⟩) N₂) ∧
      ¬ Commutes N₁ N₂ ∧ N₁ ≠ N₂ := by
  classical
  obtain ⟨e⟩ := Layer0.of_shape hΩ hex (by decide) (by decide) hshape
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 7 p f := ⟨Fact.out, hf1, by norm_num, hp2⟩
  have hY : YData p f .POmegaOdd 7 := yData_odd (by norm_num) hadm (by omega)
  have hF := orthFacts_odd (m := 7) hp2 (by norm_num) hq
  have cq := centralQuot_odd (m := 7) hp2 (by norm_num) hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hQ : (polarBilin (quadOdd 7 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 7 _ h2
  have hdim : 15 ≤ Module.finrank (GaloisField p f)
      (Fin 7 ⊕ Fin 7 ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
  have hmem : ∀ a : Fin 6, ∃ R ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd 7 p f Fact.out).D, locImg Ω x (nd.J a) = R.map e.φ :=
    fun a => e.mem _ (hx a)
  choose R hRf hLR using hmem
  let jn : ℕ → Fin 6 := fun a => ⟨min a 5, by omega⟩
  have hjn : ∀ a, a < 6 → (jn a).val = a := fun a h => by
    simp only [jn]
    omega
  have hadjn : ∀ a, a < 4 → DNodes.Adj (jn a) (jn (a + 1)) := fun a h => by
    rw [DNodes.adj_def, hjn a (by omega), hjn (a + 1) (by omega)]
    omega
  have hnadj : ∀ a b, a + 1 < b → b ≤ 4 → ¬ DNodes.Adj (jn a) (jn b) := fun a b hab hb => by
    rw [DNodes.adj_def, hjn a (by omega), hjn b (by omega)]
    omega
  have hne : ∀ a b, a < 6 → b < 6 → a ≠ b → jn a ≠ jn b := fun a b ha hb hab h => by
    have := congrArg Fin.val h
    rw [hjn a ha, hjn b hb] at this
    exact hab this
  have h4 : jn 4 = ⟨4, by norm_num⟩ := Fin.ext (hjn 4 (by omega))
  have h5 : jn 5 = ⟨5, by norm_num⟩ := Fin.ext (hjn 5 (by omega))
  have hcommR : ∀ a b : ℕ, a < 6 → b < 6 → Commutes (nd.J (jn a)) (nd.J (jn b)) →
      Commutes (R (jn a)) (R (jn b)) := fun a b ha hb hc =>
    (e.commutes_iff hY hΩ hP1 (hx _) (hx _) (hRf _) (hLR _) (hLR _)).mp hc
  have hadjR : ∀ a b : ℕ, a < 6 → b < 6 → DNodes.Adj (jn a) (jn b) →
      ModelAdj (Subgroup.center (modelUniv .POmegaOdd 7 p f Fact.out).K) (R (jn a)) (R (jn b)) :=
    fun a b ha hb hab =>
      e.modelAdj hY hΩ hP1 (hx _) (hx _) (hRf _) (hRf _) (hLR _) (hLR _) (nd.cl _) (nd.cl _)
        (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _)
        (nd.conjSub_w h2 hab)
  have hlinR : ∀ a b : ℕ, a < 6 → b < 6 → DNodes.Adj (jn a) (jn b) →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (R (jn a)) (R (jn b)) :=
    fun a b ha hb hab => by
      obtain ⟨W, hW⟩ := nd.pair_of_adj hab
      exact e.pair_to_model hF hP1 (hx _) (hx _) (hRf _) (hRf _) (hLR _) (hLR _) hW
  have hadj35 : DNodes.Adj (jn 3) (jn 5) := by
    rw [DNodes.adj_def, hjn 3 (by omega), hjn 5 (by omega)]
    omega
  have hn45 : ¬ DNodes.Adj (jn 4) (jn 5) := by
    rw [DNodes.adj_def, hjn 4 (by omega), hjn 5 (by omega)]
    omega
  have hnadjtw : ∀ a, a ≤ 2 → ¬ DNodes.Adj (jn a) (jn 5) := fun a ha => by
    rw [DNodes.adj_def, hjn a (by omega), hjn 5 (by omega)]
    omega
  have hne54 : R (jn 5) ≠ R (jn 4) := fun h =>
    nd.ne_J hΩ (hne 5 4 (by omega) (by omega) (by omega))
      (locImg_injOn hΩ hP1 (hx _) (hx _) (by rw [hLR, hLR, h]))
  obtain ⟨T₁, hT₁, T₂, hT₂, hc, s₁, t₁, s₂, t₂, hnc, hT12⟩ := exists_bridges_spin
    (R := fun a => R (jn a)) (Rtw := R (jn 5)) hp2 hq hQ hdim cq
    (fun A hA B hB h => hF.lift (spinAction (quadOdd 7 (GaloisField p f))) cq.ker_le A hA B hB h)
    (fun a ha => hRf _) (hRf _)
    (fun a ha => hadjR a (a + 1) (by omega) (by omega) (hadjn a ha))
    (fun a ha => hlinR a (a + 1) (by omega) (by omega) (hadjn a ha))
    (fun a b hab hb => hcommR a b (by omega) (by omega)
      (nd.commutes_of_not_adj (hne a b (by omega) (by omega) (by omega)) (hnadj a b hab hb)))
    (hadjR 3 5 (by omega) (by omega) hadj35)
    (fun a ha => hcommR a 5 (by omega) (by omega)
      (nd.commutes_of_not_adj (hne a 5 (by omega) (by omega) (by omega)) (hnadjtw a ha)))
    (hcommR 4 5 (by omega) (by omega)
      (nd.commutes_of_not_adj (hne 4 5 (by omega) (by omega) (by omega)) hn45))
    hne54
  obtain ⟨N₁, hN₁, hNT₁⟩ := e.comp T₁ hT₁
  obtain ⟨N₂, hN₂, hNT₂⟩ := e.comp T₂ hT₂
  have hjnfin : ∀ a : Fin 6, jn a.val = a := fun a => Fin.ext (hjn a.val a.isLt)
  have back : ∀ {N : Subgroup G} {T : Subgroup (modelUniv .POmegaOdd 7 p f Fact.out).K},
      N ∈ centralizingMembers Ω {x} → T ∈ fundamentalSubgroups .POmegaOdd
        (modelUniv .POmegaOdd 7 p f Fact.out).D → locImg Ω x N = T.map e.φ →
      ∀ a : Fin 6, Commutes T (R (jn a.val)) → Commutes N (nd.J a) := by
    intro N T hN hT hNT a hTa
    rw [hjnfin a] at hTa
    exact (e.commutes_iff hY hΩ hP1 hN (hx a) hT hNT (hLR a)).mpr hTa
  have pairs : ∀ {N : Subgroup G} {T : Subgroup (modelUniv .POmegaOdd 7 p f Fact.out).K},
      N ∈ centralizingMembers Ω {x} → locImg Ω x N = T.map e.φ → ∀ k : ℕ, k < 6 →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (R (jn k)) T) →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J (jn k)) N := by
    intro N T hN hNT k hk ⟨W, hW⟩
    exact e.pair_of_model hq hΩ hP1 (hx _) hN (hLR _) hNT hW
  refine ⟨N₁, hN₁, N₂, hN₂, fun a ha => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact back hN₁ hT₁ hNT₁ a (hc a.val ha).1
  · exact back hN₂ hT₂ hNT₂ a (hc a.val ha).2
  · rw [← h4]
    exact pairs hN₁ hNT₁ 4 (by omega) s₁
  · rw [← h5]
    exact pairs hN₁ hNT₁ 5 (by omega) t₁
  · rw [← h4]
    exact pairs hN₂ hNT₂ 4 (by omega) s₂
  · rw [← h5]
    exact pairs hN₂ hNT₂ 5 (by omega) t₂
  · intro h
    exact hnc ((e.commutes_iff hY hΩ hP1 hN₁ hN₂ hT₁ hNT₁ hNT₂).mp h)
  · intro h
    refine hT12 (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect e.φ e.ker_le
      (cq.perf T₁ hT₁) (cq.perf T₂ hT₂) ?_)
    rw [← hNT₁, ← hNT₂, h]

end CFSG.ClassicalInvolution.RouteD.TWE.B6
