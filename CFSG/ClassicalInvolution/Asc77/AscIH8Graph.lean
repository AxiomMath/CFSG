module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.RouteD.MultiModelFactsFinal
public import CFSG.ClassicalInvolution.SmallCases.DSplitDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Disconnected

@[expose] def SmallModel (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSL ∧ n ≤ 4) ∨ (t = .PSU ∧ n ≤ 4) ∨ (t = .PSp ∧ n = 2) ∨ (t = .POmegaOdd ∧ n = 3) ∨
    (t = .POmegaPlus ∧ n = 4) ∨ (t = .POmegaMinus ∧ n = 4)

theorem ih8_tag_cases {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    CommFamilyConnected (ModelFund p t n e) ∨ SmallModel t n := by
  by_cases hg : ConnGeneric t n
  · exact Or.inl (commFamilyConnected_of_generic hp2 hadm hg)
  by_cases hs : ConnShort t n
  · exact Or.inl (commFamilyConnected_of_short hp2 hadm hs)
  by_cases hx : ConnExotic t n
  · exact Or.inl (modelConnExotic t n e hfund hadm hp2 hq hx)
  exact Or.inr (small_model_cases hfund hadm hG2 hD4 hg hs hx)

theorem ih8_exists_edge_of_connected {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ}
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hnA1 : ¬ (t = .PSL ∧ n = 2))
    (hconn : CommFamilyConnected (ModelFund p t n e))
    {R : Subgroup (modelUniv t n p e Fact.out).K} (hR : R ∈ ModelFund p t n e) :
    ∃ S ∈ ModelFund p t n e, S ≠ R ∧ Commutes R S := by
  obtain ⟨S, hS, hSR, -⟩ := Exotic.exists_fund_not_commuting hfund hadm hnA1 hR
  rcases (hconn R hR S hS).cases_head with h | ⟨c, ⟨-, hc, hRc⟩, -⟩
  · exact absurd h.symm hSR
  · refine ⟨c, hc, fun hcR => ?_, hRc⟩
    exact not_commutes_self_modelFund hp2 hfund hq hadm hR (hcR ▸ hRc)

theorem ih8_commutes_map {K G : Type} [Group K] [Group G] (ψ : K →* G) {U V : Subgroup K}
    (h : Commutes U V) : Commutes (U.map ψ) (V.map ψ) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  rw [← map_mul, ← map_mul, h u hu v hv]

namespace Ih8Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {t : StatedLieTag}
  {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem dAdj_of_commutes (hp2 : p ≠ 2) (hD4 : t ≠ .trialityD4) (hq : 5 ≤ p ^ f)
    {R S : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (hRS : R ≠ S) (hc : Commutes R S) : dAdj Ω (R.map M.ψ) (S.map M.ψ) := by
  refine Disconnected.dAdj_of_commutes (M.map_mem hS) (fun h => hRS ?_) (ih8_commutes_map M.ψ hc)
  exact ih8_eq_of_map_eq M.ψ M.ker_le_center (M.cls_perfect hp2 hD4 hq hR)
    (M.cls_perfect hp2 hD4 hq hS) h

theorem not_dEdgeless_of_commutes (hp2 : p ≠ 2) (hD4 : t ≠ .trialityD4) (hq : 5 ≤ p ^ f)
    {R S : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (hRS : R ≠ S) (hc : Commutes R S) : ¬ DEdgeless Ω :=
  fun h => h _ (M.map_mem hR) _ (M.map_mem hS) (M.dAdj_of_commutes hp2 hD4 hq hR hS hRS hc)

theorem dConnected_of_connected (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hconn : CommFamilyConnected (ModelFund p t k e)) : DConnected Ω := by
  have hcls := M.fund_eq_cls hne hG2 hD4
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  intro K hK J hJ
  obtain ⟨A, hA, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨B, hB, rfl⟩ := (M.mem_iff J).mp hJ
  have h := hconn A (M.cls_sub hA) B (M.cls_sub hB)
  refine Relation.ReflTransGen.lift (fun U : Subgroup (modelUniv t k p e Fact.out).K =>
    U.map M.ψ) ?_ A B h
  rintro U V ⟨hU, hV, hc⟩
  have hU' : U ∈ M.cls := hcls ▸ hU
  have hV' : V ∈ M.cls := hcls ▸ hV
  refine ⟨M.map_mem hV', M.dAdj_of_commutes hp2 hD4 hq hU' hV' (fun h => ?_) hc⟩
  subst h
  exact not_commutes_self_modelFund hp2 M.isFundTag hq' M.admissible hU hc

end Ih8Model

end CFSG.ClassicalInvolution.Asc77
