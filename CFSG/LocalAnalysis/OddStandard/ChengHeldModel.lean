module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelStruct4
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelStruct2
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelAutOK
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelGAut
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelTrans4
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelTrans2
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelTransAut
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelTransG
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupNormalizer
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelQS
public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartG

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model
open CFSG.OddStandard.ChengHeld.M1b (evalE evalE_pw)
open CFSG.Sporadic.Recognition.PresentedWords

theorem chProps_parts (h : chPropsOK = true) :
    struct4OK 0 = true ∧ struct4OK 1 = true ∧ struct2OK = true ∧ autOK 0 = true ∧
      autOK 1 = true ∧ autOK 2 = true ∧ gAutOK 0 = true ∧ gAutOK 1 = true ∧
      gAutOK 2 = true := by
  simp only [chPropsOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem struct4OK_of {α : ℕ} (hα : α ≤ 1) (h : chPropsOK = true) : struct4OK α = true := by
  obtain ⟨h1, h2, -⟩ := chProps_parts h
  interval_cases α
  · exact h1
  · exact h2

theorem autOK_of {α : ℕ} (hα : α ≤ 2) (h : chPropsOK = true) : autOK α = true := by
  obtain ⟨-, -, -, h1, h2, h3, -⟩ := chProps_parts h
  interval_cases α
  · exact h1
  · exact h2
  · exact h3

theorem gAutOK_of {α : ℕ} (hα : α ≤ 2) (h : chPropsOK = true) : gAutOK α = true := by
  obtain ⟨-, -, -, -, -, -, h1, h2, h3⟩ := chProps_parts h
  interval_cases α
  · exact h1
  · exact h2
  · exact h3

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

theorem Chart4.exists_rep {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) :
    ∃ R : Rep (mkReg α) ↥d.S, ∀ j : Fin 7, R.pt (c.fam j) = (mkReg α).g j.val := by
  have hrel : ∀ w ∈ regRelWords α, wprod c.fam w = 1 := by
    intro w hw
    have : regRelWords α = relWords4 α := by simp [regRelWords, show α ≠ 2 by omega]
    rw [this] at hw
    exact c.wprod_fam w hw
  exact Model.exists_rep (by omega) hP c.fam hrel c.closure_fam (by
    rw [c.card_S hα h hP]; simp [regN, show α ≠ 2 by omega])

theorem Chart2.exists_rep (c : Chart2 d) (h : Hyp G A) (hP : chPresOK = true) :
    ∃ R : Rep (mkReg 2) ↥d.S, ∀ j : Fin 7, R.pt (c.fam j) = (mkReg 2).g j.val := by
  have hrel : ∀ w ∈ regRelWords 2, wprod c.fam w = 1 := by
    intro w hw
    have : regRelWords 2 = relWords2 := by simp [regRelWords]
    rw [this] at hw
    exact c.wprod_fam w hw
  exact Model.exists_rep (by omega) hP c.fam hrel c.closure_fam (by
    rw [c.card_S h hP]; simp [regN])

theorem Chart4.sFacts {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) : c.SFacts := by
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  exact c.sFacts_of (struct4_facts hα (struct4OK_of hα hQ) c.fam R hR) (c.card_S hα h hP)

section GRels

variable {E : Type*} [Group E]

attribute [local simp] evalE evalE_pw vt vpi vtau vmu vlam vze vxi Tm.prod

theorem rels_of_gact (α : ℕ) (hα : α ≤ 2) (σ : ℕ → E) (g : E)
    (h : GAct α (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) g) :
    ∀ e ∈ gRels α, cj (σ e.1) g = evalE σ e.2 := by
  intro e he
  interval_cases α <;>
    simp (config := {decide := true}) only [GAct, gRels, ite_true, ite_false,
      List.mem_cons, List.mem_nil_iff, or_false] at h he <;>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mul_assoc, *]

end GRels

omit [Finite G] in
theorem coe_evalE_natFam (S : Subgroup G) (x : Fin 7 → ↥S) :
    ∀ τ : Tm, ((evalE (natFam x) τ : ↥S) : G) = evalE (natFam (fun j => ((x j : ↥S) : G))) τ
  | .var i => rfl
  | .one => rfl
  | .mul a b => by
    simp only [evalE, Subgroup.coe_mul]
    rw [coe_evalE_natFam S x a, coe_evalE_natFam S x b]
  | .inv a => by
    simp only [evalE, Subgroup.coe_inv]
    rw [coe_evalE_natFam S x a]

theorem Chart4.autFactsG {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (k : Kind) {y : G} (hy : y ∈ d.X)
    (hact : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    AutFactsG d.S c.famG α (kind0 k) y := by
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  have hT := treeSpec_mkReg (α := α) (by omega) hP
  have hy' : ∀ s ∈ d.S, y⁻¹ * s * y ∈ d.S := fun s hs => by
    simpa using d.conj_mem_S (d.X.inv_mem hy) hs
  have key := autFactsG_of c.fam hy' (α := α) (k := kind0 k)
    (fun σ hσ => autOK_facts (by omega) (autOK_of (by omega) hQ) c.fam R hR hT
      (by cases k <;> decide) σ hσ)
    (by
      intro e he
      have hg : tableRels α (kind0 k) = actRels α (kind0 k) := by
        simp [tableRels, show α ≠ 2 by omega]
      rw [hg] at he
      have := rels_of_act α hα k (natFam c.famG) y hact e he
      rw [coe_evalE_natFam d.S c.fam]
      have hf : (fun j => ((c.fam j : ↥d.S) : G)) = c.famG := funext c.subtype_fam
      have hn : ∀ i, ((natFam c.fam i : ↥d.S) : G) = natFam c.famG i := fun i => by
        simp only [natFam]; exact c.subtype_fam _
      rw [hn, hf]
      exact this)
  have hf : (fun j => ((c.fam j : ↥d.S) : G)) = c.famG := funext c.subtype_fam
  rwa [hf] at key

theorem Chart2.sFacts (c : Chart2 d) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) : c.SFacts := by
  obtain ⟨R, hR⟩ := c.exists_rep h hP
  obtain ⟨-, -, h3, -⟩ := chProps_parts hQ
  exact c.sFacts_of (struct2_facts h3 c.fam R hR) (c.card_S h hP)

theorem Chart2.autFactsG (c : Chart2 d) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) (k : Kind) {y : G} (hy : y ∈ d.X)
    (hact : k.Act2 d.q c.pi c.tau c.mu c.lam c.ze c.xi y) :
    AutFactsG d.S c.famG 2 (kind0 k) y := by
  obtain ⟨R, hR⟩ := c.exists_rep h hP
  have hT := treeSpec_mkReg (α := 2) (by omega) hP
  have hy' : ∀ s ∈ d.S, y⁻¹ * s * y ∈ d.S := fun s hs => by
    simpa using d.conj_mem_S (d.X.inv_mem hy) hs
  have key := autFactsG_of c.fam hy' (α := 2) (k := kind0 k)
    (fun σ hσ => autOK_facts (by omega) (autOK_of (by omega) hQ) c.fam R hR hT
      (by cases k <;> decide) σ hσ)
    (by
      intro e he
      have hg : tableRels 2 (kind0 k) = act2Rels (kind0 k) := by simp [tableRels]
      rw [hg] at he
      have := rels_of_act2 k (natFam c.famG) y hact e he
      rw [coe_evalE_natFam d.S c.fam]
      have hf : (fun j => ((c.fam j : ↥d.S) : G)) = c.famG := funext c.subtype_fam
      have hn : ∀ i, ((natFam c.fam i : ↥d.S) : G) = natFam c.famG i := fun i => by
        simp only [natFam]; exact c.subtype_fam _
      rw [hn, hf]
      exact this)
  have hf : (fun j => ((c.fam j : ↥d.S) : G)) = c.famG := funext c.subtype_fam
  rwa [hf] at key

theorem Chart4.gFactsG {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S)
    (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g) :
    GFactsG d.S c.famG α g := by
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  have hT := treeSpec_mkReg (α := α) (by omega) hP
  have key := gFactsG_of c.fam hg (α := α)
    (fun γ hγ => gAutOK_facts (by omega) (gAutOK_of (by omega) hQ) c.fam R hR hT γ hγ)
    (by
      intro e he
      have := rels_of_gact α (by omega) (natFam c.famG) g hact e he
      rw [coe_evalE_natFam d.S c.fam]
      have hf : (fun j => ((c.fam j : ↥d.S) : G)) = c.famG := funext c.subtype_fam
      have hn : ∀ i, ((natFam c.fam i : ↥d.S) : G) = natFam c.famG i := fun i => by
        simp only [natFam]; exact c.subtype_fam _
      rw [hn, hf]
      exact this)
  have hf : (fun j => ((c.fam j : ↥d.S) : G)) = c.famG := funext c.subtype_fam
  rwa [hf] at key

theorem Chart4.involutions_in_S' {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {i : G} (hi : i ∈ d.QS)
    (hi2 : i * i = 1) : i ∈ d.S :=
  c.involutions_in_S h (c.sFacts hα h hP hQ) hc hi hi2

theorem Chart4.X_sylow_G_of_facts
    {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) : CFSG.ABGLocalTools.IsSylowOf 2 d.X (⊤ : Subgroup G) :=
  c.X_sylow_G h (c.sFacts hα h hP hQ).center.le

theorem Chart4.centralizer_X_S_le_Q
    {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) : d.X ⊓ centralizer (d.S : Set G) ≤ d.Q := by
  have hS := c.sFacts hα h hP hQ
  refine (d.inf_centralizer_S_le h).trans (sup_le ?_ le_rfl)
  rw [hS.center]
  exact zpowers_le.2 c.t_mem.1

theorem Chart2.centralizer_X_S_le
    (c : Chart2 d) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true) :
    d.X ⊓ centralizer (d.S : Set G) ≤ c.D ⊔ d.Q := by
  have hS := c.sFacts h hP hQ
  refine (d.inf_centralizer_S_le h).trans (sup_le_sup_right ?_ _)
  rw [hS.center]

end CFSG.OddStandard.ChengHeld
