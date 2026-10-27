module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealB
public import Certificates.Data.ChengHeldCover

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open CFSG.OddStandard.ChengHeldData
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

section Eval

variable {E : Type*} [Group E]

@[expose] def evalE (σ : ℕ → E) : Tm → E
  | .var i => σ i
  | .one => 1
  | .mul a b => evalE σ a * evalE σ b
  | .inv a => (evalE σ a)⁻¹

@[simp] theorem evalE_pw (σ : ℕ → E) (a : Tm) (n : ℕ) : evalE σ (Tm.pw a n) = evalE σ a ^ n := by
  induction n with
  | zero => simp [Tm.pw, evalE]
  | succ n ih => rw [Tm.pw, evalE, ih, pow_succ]

@[simp] theorem evalE_cj (σ : ℕ → E) (a b : Tm) :
    evalE σ (Tm.cj a b) = cj (evalE σ a) (evalE σ b) := by
  simp [Tm.cj, evalE, cj, mul_assoc]

@[simp] theorem evalE_cm (σ : ℕ → E) (a b : Tm) :
    evalE σ (Tm.cm a b) = cm (evalE σ a) (evalE σ b) := by
  simp [Tm.cm, evalE, cm, mul_assoc]

end Eval

section Model

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem evalM_lt
    (σ : ℕ → MElt) (hσ : ∀ i, (σ i).1 < 64) : ∀ τ : Tm, (τ.evalM σ).1 < 64
  | .var i => hσ i
  | .one => by simp only [Tm.evalM, oneM]; decide
  | .mul a b => mulM_lt (evalM_lt σ hσ a) (evalM_lt σ hσ b)
  | .inv a => invM_lt (evalM_lt σ hσ a)

theorem nfM_evalM
    (h : IsQSetting q l) (σ : ℕ → MElt) (hσ : ∀ i, (σ i).1 < 64) :
    ∀ τ : Tm, nfM l (τ.evalM σ) = evalE (fun i => nfM l (σ i)) τ
  | .var i => rfl
  | .one => nfM_one
  | .mul a b => by
      rw [Tm.evalM, evalE, ← nfM_evalM h σ hσ a, ← nfM_evalM h σ hσ b,
        nfM_mul h (evalM_lt σ hσ a) (evalM_lt σ hσ b)]
  | .inv a => by
      rw [Tm.evalM, evalE, ← nfM_evalM h σ hσ a, nfM_inv h (evalM_lt σ hσ a)]

theorem eqN2_iff
    (h : IsQSetting q l)
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ j.val % 2 = 0)
    {x y : MElt} (hx : x.1 < 64) (hy : y.1 < 64) : eqN2 x y = true ↔ nfM l x = nfM l y := by
  rw [nfM, nfM, nf_eq_iff h hx hy, hκ, eqN2, Bool.and_eq_true, beq_iff_eq]
  simp only [beq_iff_eq]

theorem eval_eq_of_relsOK
    (h : IsQSetting q l) {eqf : MElt → MElt → Bool}
    (hf : ∀ x y : MElt, x.1 < 64 → y.1 < 64 → (eqf x y = true ↔ nfM l x = nfM l y))
    {σ : ℕ → MElt} (hσ : ∀ i, (σ i).1 < 64) {rels : List (Tm × Tm)}
    (hr : relsOK eqf σ rels = true) :
    ∀ e ∈ rels, evalE (fun i => nfM l (σ i)) e.1 = evalE (fun i => nfM l (σ i)) e.2 := by
  intro e he
  rw [relsOK, List.all_eq_true] at hr
  have h1 := (hf _ _ (evalM_lt σ hσ e.1) (evalM_lt σ hσ e.2)).1 (hr e he)
  rwa [nfM_evalM h σ hσ, nfM_evalM h σ hσ] at h1

theorem act_of_actOK
    (h : IsQSetting q l) {eqf : MElt → MElt → Bool}
    (hf : ∀ x y : MElt, x.1 < 64 → y.1 < 64 → (eqf x y = true ↔ nfM l x = nfM l y))
    {σ : ℕ → MElt} (hσ : ∀ i, (σ i).1 < 64) {β : E ≃* E} {i : ℕ} (hi : i < 36)
    (hβ : ∀ w, β (l (cv w)) = l (cv (substWord (aut i) w))) {rels : List (ℕ × Tm)}
    (hr : actOK eqf σ i rels = true) :
    ∀ e ∈ rels, β (nfM l (σ e.1)) = evalE (fun i => nfM l (σ i)) e.2 := by
  intro e he
  rw [actOK, List.all_eq_true] at hr
  have h1 := (hf _ _ (betaRepM_lt hi (hσ e.1)) (evalM_lt σ hσ e.2)).1 (hr e he)
  rw [nfM_evalM h σ hσ] at h1
  rw [← h1]
  exact beta_nf h hi (hσ e.1) hβ _ _

end Model

section Struct

variable {E : Type*} [Group E]

attribute [local simp] evalE evalE_pw evalE_cj evalE_cm vt vpi vtau vmu vlam vze vxi

theorem frame4_of_rels (α : ℕ) (σ : ℕ → E)
    (h : ∀ e ∈ frame4Rels α, evalE σ e.1 = evalE σ e.2) :
    Frame4 α (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) := by
  have key : ∀ a b : Tm, (a, b) ∈ frame4Rels α → evalE σ a = evalE σ b := fun a b hab => h _ hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simpa using key (Tm.pw vt 4) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.pw vpi 2) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.pw vtau 4) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.pw vmu 2) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.pw vlam 2) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.pw vze 2) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.pw vxi 2) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.pw vtau 2) (Tm.pw vt 2) (by simp [frame4Rels])
  · simpa using key (Tm.cm vpi vtau) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.cj vpi vmu) (Tm.mul (Tm.pw vt 2) vpi) (by simp [frame4Rels])
  · simpa using key (Tm.cj vpi vlam) (Tm.mul (Tm.pw vt 2) vpi) (by simp [frame4Rels])
  · simpa using key (Tm.cj vpi vze) (Tm.mul (Tm.pw vt 2) vpi) (by simp [frame4Rels])
  · simpa using key (Tm.cj vpi (Tm.mul vmu vlam)) vpi (by simp [frame4Rels])
  · simpa using key (Tm.cj vpi vxi) vpi (by simp [frame4Rels])
  · simpa using key (Tm.cj vtau vxi) (Tm.mul (Tm.pw vt 2) vtau) (by simp [frame4Rels])
  · simpa using key (Tm.cj vtau vlam) (Tm.mul (Tm.pw vt 2) vtau) (by simp [frame4Rels])
  · simpa using key (Tm.cj vtau vze) (Tm.mul (Tm.pw vt 2) vtau) (by simp [frame4Rels])
  · simpa using key (Tm.cm vtau vmu) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.cm vmu vlam) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.cm vze vxi) Tm.one (by simp [frame4Rels])
  · simpa using key (Tm.cm vmu vxi) (Tm.mul vpi vtau) (by simp [frame4Rels])
  · simpa using key (Tm.cm vmu vze) (Tm.mul vt vpi) (by simp [frame4Rels])
  · simpa using key (Tm.cm vlam vxi) vtau (by simp [frame4Rels])
  · simpa using key (Tm.cm vlam vze) (Tm.mul (Tm.mul (Tm.mul vt (Tm.pw vt (2 * α))) vpi) vtau)
      (by simp [frame4Rels])

theorem frame2_of_rels (σ : ℕ → E) (h : ∀ e ∈ frame2Rels, evalE σ e.1 = evalE σ e.2) :
    Frame2 (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) := by
  have key : ∀ a b : Tm, (a, b) ∈ frame2Rels → evalE σ a = evalE σ b := fun a b hab => h _ hab
  have c : ∀ a b : Tm, (a, b) ∈ frame2Rels → evalE σ a = evalE σ b ∧ evalE σ b = evalE σ a :=
    fun a b hab => ⟨key a b hab, (key a b hab).symm⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using key (Tm.pw vt 2) Tm.one (by simp [frame2Rels])
  · simpa using key (Tm.pw vpi 2) Tm.one (by simp [frame2Rels])
  · simpa using key (Tm.pw vtau 2) Tm.one (by simp [frame2Rels])
  · simpa using key (Tm.pw vmu 2) Tm.one (by simp [frame2Rels])
  · simpa using key (Tm.pw vlam 2) Tm.one (by simp [frame2Rels])
  · simpa using key (Tm.pw vze 2) Tm.one (by simp [frame2Rels])
  · simpa using key (Tm.pw vxi 2) Tm.one (by simp [frame2Rels])
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using key (Tm.mul vt vpi) (Tm.mul vpi vt) (by simp [frame2Rels])
    · simpa using key (Tm.mul vt vtau) (Tm.mul vtau vt) (by simp [frame2Rels])
    · simpa using key (Tm.mul vt vmu) (Tm.mul vmu vt) (by simp [frame2Rels])
    · simpa using key (Tm.mul vt vlam) (Tm.mul vlam vt) (by simp [frame2Rels])
    · simpa using key (Tm.mul vt vze) (Tm.mul vze vt) (by simp [frame2Rels])
    · simpa using key (Tm.mul vt vxi) (Tm.mul vxi vt) (by simp [frame2Rels])
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    have e12 := (c (Tm.mul vpi vtau) (Tm.mul vtau vpi) (by simp [frame2Rels]))
    have e13 := (c (Tm.mul vpi vmu) (Tm.mul vmu vpi) (by simp [frame2Rels]))
    have e14 := (c (Tm.mul vpi vlam) (Tm.mul vlam vpi) (by simp [frame2Rels]))
    have e23 := (c (Tm.mul vtau vmu) (Tm.mul vmu vtau) (by simp [frame2Rels]))
    have e24 := (c (Tm.mul vtau vlam) (Tm.mul vlam vtau) (by simp [frame2Rels]))
    have e34 := (c (Tm.mul vmu vlam) (Tm.mul vlam vmu) (by simp [frame2Rels]))
    simp only [evalE, vpi, vtau, vmu, vlam] at e12 e13 e14 e23 e24 e34
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | rfl | exact e12.1 | exact e12.2 | exact e13.1 | exact e13.2 | exact e14.1 |
        exact e14.2 | exact e23.1 | exact e23.2 | exact e24.1 | exact e24.2 | exact e34.1 |
        exact e34.2
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    have e12 := (c (Tm.mul vpi vtau) (Tm.mul vtau vpi) (by simp [frame2Rels]))
    have e15 := (c (Tm.mul vpi vze) (Tm.mul vze vpi) (by simp [frame2Rels]))
    have e16 := (c (Tm.mul vpi vxi) (Tm.mul vxi vpi) (by simp [frame2Rels]))
    have e25 := (c (Tm.mul vtau vze) (Tm.mul vze vtau) (by simp [frame2Rels]))
    have e26 := (c (Tm.mul vtau vxi) (Tm.mul vxi vtau) (by simp [frame2Rels]))
    have e56 := (c (Tm.mul vze vxi) (Tm.mul vxi vze) (by simp [frame2Rels]))
    simp only [evalE, vpi, vtau, vze, vxi] at e12 e15 e16 e25 e26 e56
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | rfl | exact e12.1 | exact e12.2 | exact e15.1 | exact e15.2 | exact e16.1 |
        exact e16.2 | exact e25.1 | exact e25.2 | exact e26.1 | exact e26.2 | exact e56.1 |
        exact e56.2
  · simpa using key (Tm.cm vmu vxi) (Tm.mul vpi vtau) (by simp [frame2Rels])
  · simpa using key (Tm.cm vlam vxi) vtau (by simp [frame2Rels])
  · simpa using key (Tm.cm vmu vze) (Tm.mul vt vpi) (by simp [frame2Rels])
  · simpa [mul_assoc] using key (Tm.cm vlam vze) (Tm.mul (Tm.mul vt vpi) vtau)
      (by simp [frame2Rels])

theorem act_field_of_rels (α : ℕ) (hα : α ≤ 1) (σ : ℕ → E) (y : E)
    (h : ∀ e ∈ actRels α 0, cj (σ e.1) y = evalE σ e.2) :
    Kind.field.Act α (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) y := by
  have key : ∀ i τ, (i, τ) ∈ actRels α 0 → cj (σ i) y = evalE σ τ := fun i τ hm => h _ hm
  interval_cases α
  · simp only [Kind.Act]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using key 0 vt (by simp [actRels])
    · simpa using key 1 vpi (by simp [actRels])
    · simpa using key 2 (Tm.mul vpi vtau) (by simp [actRels])
    · simpa using key 3 (Tm.mul (Tm.pw vt 2) vlam) (by simp [actRels])
    · simpa using key 4 (Tm.mul (Tm.pw vt 2) vmu) (by simp [actRels])
    · simpa using key 5 (Tm.mul vze vxi) (by simp [actRels])
    · simpa using key 6 vxi (by simp [actRels])
  · simp only [Kind.Act]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using key 0 (Tm.inv vt) (by simp [actRels])
    · simpa using key 1 vpi (by simp [actRels])
    · simpa using key 2 (Tm.mul vpi vtau) (by simp [actRels])
    · simpa using key 3 (Tm.mul (Tm.pw vt 2) vlam) (by simp [actRels])
    · simpa using key 4 (Tm.mul (Tm.pw vt 2) vmu) (by simp [actRels])
    · simpa using key 5 (Tm.mul (Tm.mul (Tm.pw vt 2) vze) vxi) (by simp [actRels])
    · simpa using key 6 vxi (by simp [actRels])

theorem act_graph_of_rels (α : ℕ) (hα : α ≤ 1) (σ : ℕ → E) (y : E)
    (h : ∀ e ∈ actRels α 1, cj (σ e.1) y = evalE σ e.2) :
    Kind.graph.Act α (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) y := by
  have key : ∀ i τ, (i, τ) ∈ actRels α 1 → cj (σ i) y = evalE σ τ := fun i τ hm => h _ hm
  interval_cases α
  · simp only [Kind.Act]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using key 0 (Tm.inv vt) (by simp [actRels])
    · simpa using key 1 vpi (by simp [actRels])
    · simpa using key 2 (Tm.inv vtau) (by simp [actRels])
    · simpa using key 3 (Tm.mul (Tm.mul (Tm.pw vt 2) vze) vxi) (by simp [actRels])
    · simpa using key 4 vze (by simp [actRels])
    · simpa using key 5 vlam (by simp [actRels])
    · simpa using key 6 (Tm.mul (Tm.mul (Tm.pw vt 2) vmu) vlam) (by simp [actRels])
  · simp only [Kind.Act]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using key 0 vt (by simp [actRels])
    · simpa using key 1 vpi (by simp [actRels])
    · simpa using key 2 vtau (by simp [actRels])
    · simpa using key 3 (Tm.mul vze vxi) (by simp [actRels])
    · simpa using key 4 vze (by simp [actRels])
    · simpa using key 5 vlam (by simp [actRels])
    · simpa using key 6 (Tm.mul vmu vlam) (by simp [actRels])

theorem act_unitary_of_rels (α : ℕ) (hα : α ≤ 1) (σ : ℕ → E) (y : E)
    (h : ∀ e ∈ actRels α 2, cj (σ e.1) y = evalE σ e.2) :
    Kind.unitary.Act α (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) y := by
  have key : ∀ i τ, (i, τ) ∈ actRels α 2 → cj (σ i) y = evalE σ τ := fun i τ hm => h _ hm
  interval_cases α
  · simp only [Kind.Act]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using key 0 (Tm.inv vt) (by simp [actRels])
    · simpa using key 1 vpi (by simp [actRels])
    · simpa using key 2 (Tm.mul vpi (Tm.inv vtau)) (by simp [actRels])
    · simpa using key 3 (Tm.mul (Tm.pw vt 2) vze) (by simp [actRels])
    · simpa using key 4 (Tm.mul vze vxi) (by simp [actRels])
    · simpa using key 5 (Tm.mul (Tm.pw vt 2) vmu) (by simp [actRels])
    · simpa using key 6 (Tm.mul (Tm.mul (Tm.pw vt 2) vmu) vlam) (by simp [actRels])
  · simp only [Kind.Act]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using key 0 (Tm.inv vt) (by simp [actRels])
    · simpa using key 1 vpi (by simp [actRels])
    · simpa using key 2 (Tm.mul vpi vtau) (by simp [actRels])
    · simpa using key 3 (Tm.mul (Tm.pw vt 2) vze) (by simp [actRels])
    · simpa using key 4 (Tm.mul (Tm.mul (Tm.pw vt 2) vze) vxi) (by simp [actRels])
    · simpa using key 5 (Tm.mul (Tm.pw vt 2) vmu) (by simp [actRels])
    · simpa using key 6 (Tm.mul vmu vlam) (by simp [actRels])

theorem act2_field_of_rels (σ : ℕ → E) (y : E)
    (h : ∀ e ∈ act2Rels 0, cj (σ e.1) y = evalE σ e.2) :
    Kind.field.Act2 (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) y := by
  have key : ∀ i τ, (i, τ) ∈ act2Rels 0 → cj (σ i) y = evalE σ τ := fun i τ hm => h _ hm
  simp only [Kind.Act2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using key 0 vt (by simp [act2Rels])
  · simpa using key 1 vpi (by simp [act2Rels])
  · simpa using key 2 (Tm.mul vpi vtau) (by simp [act2Rels])
  · simpa using key 3 vlam (by simp [act2Rels])
  · simpa using key 4 vmu (by simp [act2Rels])
  · simpa using key 5 (Tm.mul vze vxi) (by simp [act2Rels])
  · simpa using key 6 vxi (by simp [act2Rels])

theorem act2_graph_of_rels (σ : ℕ → E) (y : E)
    (h : ∀ e ∈ act2Rels 1, cj (σ e.1) y = evalE σ e.2) :
    Kind.graph.Act2 (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) y := by
  have key : ∀ i τ, (i, τ) ∈ act2Rels 1 → cj (σ i) y = evalE σ τ := fun i τ hm => h _ hm
  simp only [Kind.Act2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using key 0 vt (by simp [act2Rels])
  · simpa using key 1 vpi (by simp [act2Rels])
  · simpa using key 2 vtau (by simp [act2Rels])
  · simpa using key 3 (Tm.mul vze vxi) (by simp [act2Rels])
  · simpa using key 4 vze (by simp [act2Rels])
  · simpa using key 5 vlam (by simp [act2Rels])
  · simpa using key 6 (Tm.mul vmu vlam) (by simp [act2Rels])

theorem act2_unitary_of_rels (σ : ℕ → E) (y : E)
    (h : ∀ e ∈ act2Rels 2, cj (σ e.1) y = evalE σ e.2) :
    Kind.unitary.Act2 (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) (σ 6) y := by
  have key : ∀ i τ, (i, τ) ∈ act2Rels 2 → cj (σ i) y = evalE σ τ := fun i τ hm => h _ hm
  simp only [Kind.Act2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using key 0 vt (by simp [act2Rels])
  · simpa using key 1 vpi (by simp [act2Rels])
  · simpa using key 2 (Tm.mul vpi vtau) (by simp [act2Rels])
  · simpa using key 3 vze (by simp [act2Rels])
  · simpa using key 4 (Tm.mul vze vxi) (by simp [act2Rels])
  · simpa using key 5 vmu (by simp [act2Rels])
  · simpa using key 6 (Tm.mul vmu vlam) (by simp [act2Rels])

end Struct

end CFSG.OddStandard.ChengHeld.M1b
