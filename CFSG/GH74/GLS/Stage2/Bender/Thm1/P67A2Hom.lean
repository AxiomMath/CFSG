module

public import CFSG.LieType.Steinberg.RankTwo.Statement
public import CFSG.LieType.Steinberg.RankTwo.G2Comm
public import CFSG.LieType.Steinberg.RankTwo.G2CommCheck
public import CFSG.Timmesfeld.RankTwo.ModelG2Comm
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.Steinberg.Adjoint.Group
public import CFSG.LieType.Chevalley.NativeMonomial
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LinearAlgebra.LinearGroups.Elementary
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.RankTwo
open scoped MatrixGroups commutatorElement

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

local notation "F2" => rootOperatorFamily Tag.G2

@[expose] def A2l : List (ℤ × ℤ) := [(1, 0), (0, 1), (1, 1), (-1, 0), (0, -1), (-1, -1)]

@[expose] def a2pos (p : ℤ × ℤ) : ℕ :=
  if p = (1, 0) then 0 else if p = (0, 1) then 3 else if p = (1, 1) then 7
  else if p = (-1, 0) then 2 else if p = (0, -1) then 6 else 10

@[expose] def a2idx (p : ℤ × ℤ) : Fin 3 × Fin 3 :=
  if p = (1, 0) then (0, 1) else if p = (0, 1) then (1, 2) else if p = (1, 1) then (0, 2)
  else if p = (-1, 0) then (1, 0) else if p = (0, -1) then (2, 1) else (2, 0)

@[expose] def a2sign (p q : ℤ × ℤ) : ℤ := if (a2idx p).2 = (a2idx q).1 then 1 else -1

@[expose] def a2add (p q : ℤ × ℤ) : ℤ × ℤ := (p.1 + q.1, p.2 + q.2)

theorem a2pos_lt : ∀ p ∈ A2l, a2pos p < 12 := by decide +kernel

theorem a2_chain_cases : ∀ p ∈ A2l, ∀ q ∈ A2l, a2add p q ∈ A2l →
    (((a2pos p, a2pos q), [(1, 1, a2pos (a2add p q), a2sign p q)]) ∈ g2CommPairs) ∨
    (((a2pos q, a2pos p), [(1, 1, a2pos (a2add p q), -a2sign p q)]) ∈ g2CommPairs) := by
  decide +kernel

theorem a2_nil_cases : ∀ p ∈ A2l, ∀ q ∈ A2l, p ≠ q → a2add p q ≠ (0, 0) → a2add p q ∉ A2l →
    g2CommDet (a2pos p) (a2pos q) ≠ 0 ∧ g2CommComplete (a2pos p) (a2pos q) [] = true := by
  decide +kernel

theorem a2_e1_cases : (g2CommDet 7 1 ≠ 0 ∧ g2CommComplete 7 1 [] = true) ∧
    (g2CommDet 10 1 ≠ 0 ∧ g2CommComplete 10 1 [] = true) := by
  decide +kernel

theorem a2pos_10 : a2pos ((1 : ℤ), (0 : ℤ)) = 0 := by decide

theorem a2pos_n10 : a2pos ((-1 : ℤ), (0 : ℤ)) = 2 := by decide

theorem a2pos_11 : a2pos ((1 : ℤ), (1 : ℤ)) = 7 := by decide

theorem a2pos_n11 : a2pos ((-1 : ℤ), (-1 : ℤ)) = 10 := by decide

theorem root0 : (g2CommRoot 0 : Fin (Tag.rank .G2) → ℤ) = Pi.single ⟨0, by decide⟩ 1 := by
  decide +kernel

theorem root2 : (g2CommRoot 2 : Fin (Tag.rank .G2) → ℤ) = -Pi.single ⟨0, by decide⟩ 1 := by
  decide +kernel

theorem root1 : (g2CommRoot 1 : Fin (Tag.rank .G2) → ℤ) = Pi.single ⟨1, by decide⟩ 1 := by
  decide +kernel

theorem cartan_e1 : (∑ j : Fin (Tag.rank .G2), (Tag.G2).cartan ⟨0, by decide⟩ j *
    (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .G2)) (1 : ℤ) :
      Fin (Tag.rank .G2) → ℤ) j) = -1 := by
  decide +kernel

theorem mem_rootsA2 {γ : Fin 2 → ℤ} : γ ∈ RA2 ↔
    γ = ![1, 0] ∨ γ = ![0, 1] ∨ γ = ![1, 1] ∨ γ = ![-1, 0] ∨ γ = ![0, -1] ∨
      γ = ![-1, -1] := by
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
  have inj := CFSG.LieType.Universal.SpecialLinear.toStd_injective 2
  constructor
  · rintro ⟨i, j, hij, h⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Or.inl (inj (h.trans (by decide)))
    · exact Or.inr (Or.inr (Or.inl (inj (h.trans (by decide)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (inj (h.trans (by decide))))))
    · exact absurd rfl hij
    · exact Or.inr (Or.inl (inj (h.trans (by decide))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (inj (h.trans (by decide)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inj (h.trans (by decide)))))))
    · exact absurd rfl hij
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, by decide⟩
    · exact ⟨1, 2, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide⟩
    · exact ⟨1, 0, by decide, by decide⟩
    · exact ⟨2, 1, by decide, by decide⟩
    · exact ⟨2, 0, by decide, by decide⟩

theorem mem_RA2_iff {γ : Fin 2 → ℤ} : γ ∈ RA2 ↔ (γ 0, γ 1) ∈ A2l := by
  rw [mem_rootsA2]
  have key : ∀ a b : ℤ, γ = ![a, b] ↔ (γ 0, γ 1) = (a, b) := fun a b => by
    constructor
    · rintro rfl
      simp
    · intro h
      obtain ⟨h0, h1⟩ := Prod.mk.inj h
      funext i
      fin_cases i <;> simp [h0, h1]
  simp only [A2l, List.mem_cons, List.not_mem_nil, or_false, key]

theorem pairOf_eq_a2idx {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) :
    CFSG.LieType.Steinberg.SL.pairOf 2 γ = a2idx (γ 0, γ 1) := by
  rcases mem_rootsA2.1 hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact CFSG.LieType.Steinberg.SL.pairOf_eq (by decide) (by decide)
  · exact CFSG.LieType.Steinberg.SL.pairOf_eq (by decide) (by decide)
  · exact CFSG.LieType.Steinberg.SL.pairOf_eq (by decide) (by decide)
  · exact CFSG.LieType.Steinberg.SL.pairOf_eq (by decide) (by decide)
  · exact CFSG.LieType.Steinberg.SL.pairOf_eq (by decide) (by decide)
  · exact CFSG.LieType.Steinberg.SL.pairOf_eq (by decide) (by decide)

section Pure

variable {K : Type} [Field K]

theorem mem_commOrder_list_iff
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)))
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (p : ℕ × ℕ) :
    p ∈ O.list α β ↔ p = (1, 1) ∧ α + β ∈ RA2 := by
  have hα' : α ∈ (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)).roots := by
    rw [CFSG.LieType.Steinberg.SL.Φ_roots]
    exact hα
  have hβ' : β ∈ (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)).roots := by
    rw [CFSG.LieType.Steinberg.SL.Φ_roots]
    exact hβ
  rw [O.mem_iff α hα' β hβ' hαβ p]
  constructor
  · intro hp
    obtain ⟨rfl, -⟩ := (CFSG.LieType.Steinberg.SL.mem_expPairs_iff (F := K) hα hβ hαβ p).1 hp
    obtain ⟨-, -, h⟩ := hp
    rw [CFSG.LieType.Steinberg.SL.Φ_roots] at h
    exact ⟨rfl, by simpa using h⟩
  · rintro ⟨rfl, h⟩
    refine ⟨one_pos, one_pos, ?_⟩
    rw [CFSG.LieType.Steinberg.SL.Φ_roots]
    simpa using h

theorem commOrder_list_eq_singleton
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)))
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (h : α + β ∈ RA2) :
    O.list α β = [(1, 1)] :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup (O.nodup α β)
    (List.nodup_singleton _)).2 fun p => by
      rw [mem_commOrder_list_iff O hα hβ hαβ, List.mem_singleton, and_iff_left h])

theorem commOrder_list_eq_nil
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K)))
    {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hαβ : α + β ≠ 0) (h : α + β ∉ RA2) :
    O.list α β = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun p hp => h ((mem_commOrder_list_iff O hα hβ hαβ p).1 hp).2

theorem commC_eq {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (p : ℕ × ℕ) :
    CFSG.LieType.Steinberg.SL.commC (m := 2) α β p = a2sign (α 0, α 1) (β 0, β 1) := by
  unfold CFSG.LieType.Steinberg.SL.commC a2sign
  rw [pairOf_eq_a2idx hα, pairOf_eq_a2idx hβ]

@[expose] noncomputable def wSL {i j : Fin 3} (hij : i ≠ j) (t : K) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection hij t *
    Matrix.SpecialLinearGroup.transvection hij.symm (-t⁻¹) *
      Matrix.SpecialLinearGroup.transvection hij t

theorem coe_wSL_mul_neg_one {i j : Fin 3} (hij : i ≠ j) {t : K} (ht : t ≠ 0) :
    ((wSL hij t * wSL hij (-1) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun k => if k = i then t else if k = j then t⁻¹ else 1) := by
  have h := (CFSG.LinearGroups.elementary_diagonal_factorization hij ht).2.2.2.1
  rw [h]
  rfl

end Pure

section A


variable {K : Type} [Field K]

@[expose] noncomputable def a2y (γ : Fin 2 → ℤ) (c : K) : ↥(adjointGroup .G2 K) :=
  xPar (rootOperatorFamily .G2) (g2CommRoot (a2pos (γ 0, γ 1))) c

theorem a2y_add (γ : Fin 2 → ℤ) (c d : K) : a2y γ (c + d) = a2y γ c * a2y γ d :=
  xPar_add _ _ _

theorem a2y_comm_self (γ : Fin 2 → ℤ) (c d : K) : ⁅a2y γ c, a2y γ d⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute]
  show _ * _ = _ * _
  rw [← a2y_add, ← a2y_add, add_comm]

theorem weylElement_neg_inv (i : Fin (Tag.rank .G2)) (t : Kˣ) :
    CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily .G2) (K := K)) i (-t) =
      (CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily .G2) (K := K)) i t)⁻¹ := by
  simp only [CFSG.LieType.Steinberg.weylElement, mul_inv_rev, xPar_neg, Units.val_neg,
    Units.val_inv_eq_inv_val, inv_neg, neg_neg, mul_assoc]

theorem torus_conj_e1 (t : Kˣ) :
    torusElement .G2 K (⟨0, by decide⟩ : Fin (Tag.rank .G2)) t * xPar F2 (g2CommRoot 1) 1 *
        (torusElement .G2 K (⟨0, by decide⟩ : Fin (Tag.rank .G2)) t)⁻¹ =
      xPar F2 (g2CommRoot 1) (((t⁻¹ : Kˣ)) : K) := by
  have hroot : IsRoot .G2 (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .G2)) (1 : ℤ)) :=
    isRoot_single .G2 _
  rw [root1, xPar_of_isRoot hroot, xPar_of_isRoot hroot]
  have h := (rootOperatorFamily Tag.G2).torusElement_mul_eltElement_mul_inv
    (K := K) ⟨0, by decide⟩ t ⟨_, hroot⟩ 1
  rw [h]
  simp only [cartan_e1, zpow_neg, zpow_one, mul_one]

theorem g2_comm_stored (e : (ℕ × ℕ) × List CFSG.LieType.Chevalley.RootOps.Factor)
    (he : e ∈ g2CommPairs) (s t : K) :
    ⁅xPar F2 (g2CommRoot e.1.1) s, xPar F2 (g2CommRoot e.1.2) t⁆ =
      (e.2.map fun f => xPar F2 (g2CommRoot f.2.2.1)
        ((f.2.2.2 : K) * s ^ f.1 * t ^ f.2.1)).prod :=
  CFSG.Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2)
    (List.all_eq_true.1 g2CommPairs_check e he) s t

theorem a2y_comm_chain {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hs : α + β ∈ RA2)
    (c d : K) :
    ⁅a2y α c, a2y β d⁆ = a2y (α + β) (((a2sign (α 0, α 1) (β 0, β 1) : ℤ) : K) * c * d) := by
  have hp : (α 0, α 1) ∈ A2l := mem_RA2_iff.1 hα
  have hq : (β 0, β 1) ∈ A2l := mem_RA2_iff.1 hβ
  have hpq : a2add (α 0, α 1) (β 0, β 1) ∈ A2l := by
    simpa [a2add] using mem_RA2_iff.1 hs
  rcases a2_chain_cases _ hp _ hq hpq with h | h
  · have h' := g2_comm_stored _ h c d
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] at h'
    exact h'
  · have h' := g2_comm_stored _ h d c
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] at h'
    have h'' := congrArg (fun x => x⁻¹) h'
    simp only [commutatorElement_inv, xPar_neg] at h''
    refine h''.trans ?_
    show xPar _ _ _ = xPar _ _ _
    congr 1
    push_cast
    ring

section Phi

variable (φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →* ↥(adjointGroup .G2 K))
  (hφ : ∀ γ ∈ RA2, ∀ c : K, φ (CFSG.LieType.Steinberg.SL.x 2 K γ c) = a2y γ c)

include hφ

theorem phi_T01 (c : K) :
    φ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c) =
      xPar F2 (Pi.single ⟨0, by decide⟩ 1) c := by
  rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (γ := ![1, 0]) (show (0 : Fin 3) ≠ 1 by decide)
    (by decide) c, hφ _ (mem_rootsA2.2 (Or.inl rfl)) c, ← root0]
  simp [a2y, a2pos_10]

theorem phi_T10 (c : K) :
    φ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c) =
      xPar F2 (-Pi.single ⟨0, by decide⟩ 1) c := by
  rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (γ := ![-1, 0]) (show (1 : Fin 3) ≠ 0 by decide)
    (by decide) c, hφ _ (mem_rootsA2.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) c, ← root2]
  simp [a2y, a2pos_n10]

theorem phi_T02 (c : K) :
    φ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c) =
      xPar F2 (g2CommRoot 7) c := by
  rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (γ := ![1, 1]) (show (0 : Fin 3) ≠ 2 by decide)
    (by decide) c, hφ _ (mem_rootsA2.2 (Or.inr (Or.inr (Or.inl rfl)))) c]
  simp [a2y, a2pos_11]

theorem phi_T20 (c : K) :
    φ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c) =
      xPar F2 (g2CommRoot 10) c := by
  rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (γ := ![-1, -1]) (show (2 : Fin 3) ≠ 0 by decide)
    (by decide) c, hφ _ (mem_rootsA2.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) c]
  simp [a2y, a2pos_n11]

theorem phi_wSL01 (t : Kˣ) :
    φ (wSL (show (0 : Fin 3) ≠ 1 by decide) (t : K)) =
      CFSG.LieType.Steinberg.weylElement (xPar F2) (⟨0, by decide⟩ : Fin (Tag.rank .G2)) t := by
  simp only [wSL, map_mul, phi_T01 φ hφ, phi_T10 φ hφ, CFSG.LieType.Steinberg.weylElement,
    Units.val_inv_eq_inv_val]

theorem phi_D01 (t : Kˣ) :
    φ (wSL (show (0 : Fin 3) ≠ 1 by decide) (t : K) *
        wSL (show (0 : Fin 3) ≠ 1 by decide) (-1)) =
      torusElement .G2 K (⟨0, by decide⟩ : Fin (Tag.rank .G2)) t := by
  have h1 : wSL (show (0 : Fin 3) ≠ 1 by decide) (-1 : K) =
      wSL (show (0 : Fin 3) ≠ 1 by decide) (((-1 : Kˣ) : Kˣ) : K) := by simp
  rw [map_mul, h1, phi_wSL01 φ hφ, phi_wSL01 φ hφ, weylElement_neg_inv, weylElement_xPar,
    weylElement_xPar]
  have h2 : torusElement .G2 K (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1 = 1 :=
    Subtype.ext (torusElt_one _)
  rw [h2, one_mul, mul_inv_cancel_right]

end Phi

end A

section B


variable {K : Type} [Field K]

theorem a2y_comm_of_not_mem {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2) (hne : α ≠ β)
    (hs0 : α + β ≠ 0) (hs : α + β ∉ RA2) (c d : K) : ⁅a2y α c, a2y β d⁆ = 1 := by
  have hp : (α 0, α 1) ∈ A2l := mem_RA2_iff.1 hα
  have hq : (β 0, β 1) ∈ A2l := mem_RA2_iff.1 hβ
  have hne' : (α 0, α 1) ≠ (β 0, β 1) := by
    intro e
    apply hne
    funext i
    fin_cases i
    · exact (Prod.mk.inj e).1
    · exact (Prod.mk.inj e).2
  have hz : a2add (α 0, α 1) (β 0, β 1) ≠ (0, 0) := by
    intro e
    apply hs0
    funext i
    fin_cases i
    · exact (Prod.mk.inj e).1
    · exact (Prod.mk.inj e).2
  have hn : a2add (α 0, α 1) (β 0, β 1) ∉ A2l := by
    intro e
    exact hs (mem_RA2_iff.2 (by simpa [a2add] using e))
  obtain ⟨hd, hcomp⟩ := a2_nil_cases _ hp _ hq hne' hz hn
  exact commutator_g2CommRoot_eq_one (by simpa using a2pos_lt _ hp)
    (by simpa using a2pos_lt _ hq) hd hcomp c d

theorem a2y_commutatorFormula
    (O : CFSG.LieType.Steinberg.CommOrder (CFSG.LieType.Steinberg.SL.Φ (m := 2) (F := K))) :
    CFSG.LieType.Steinberg.CommutatorFormula (fun γ c => a2y (K := K) γ c) O
      (CFSG.LieType.Steinberg.SL.commC (m := 2)) := by
  intro α hα β hβ hαβ c d
  have hα' : α ∈ RA2 := by rw [← CFSG.LieType.Steinberg.SL.Φ_roots (F := K)]; exact hα
  have hβ' : β ∈ RA2 := by rw [← CFSG.LieType.Steinberg.SL.Φ_roots (F := K)]; exact hβ
  by_cases h : α + β ∈ RA2
  · rw [commOrder_list_eq_singleton O hα' hβ' hαβ h]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_smul,
      pow_one]
    rw [a2y_comm_chain hα' hβ' h, commC_eq hα' hβ']
  · rw [commOrder_list_eq_nil O hα' hβ' hαβ h]
    simp only [List.map_nil, List.prod_nil]
    by_cases hab : α = β
    · subst hab
      exact a2y_comm_self _ _ _
    · exact a2y_comm_of_not_mem hα' hβ' hab hαβ h c d

theorem commute_pos_e1 {a : ℕ} (ha : a = 7 ∨ a = 10) (c u : K) :
    Commute (xPar (rootOperatorFamily .G2) (g2CommRoot a) c)
      (xPar (rootOperatorFamily .G2) (g2CommRoot 1) u) := by
  rcases ha with rfl | rfl
  · exact commutatorElement_eq_one_iff_commute.1 (commutator_g2CommRoot_eq_one (by norm_num)
      (by norm_num) a2_e1_cases.1.1 a2_e1_cases.1.2 c u)
  · exact commutatorElement_eq_one_iff_commute.1 (commutator_g2CommRoot_eq_one (by norm_num)
      (by norm_num) a2_e1_cases.2.1 a2_e1_cases.2.2 c u)

section Phi

variable (φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →* ↥(adjointGroup .G2 K))
  (hφ : ∀ γ ∈ RA2, ∀ c : K, φ (CFSG.LieType.Steinberg.SL.x 2 K γ c) = a2y γ c)

include hφ

theorem commute_phi_D02 (t u : K) :
    Commute (φ (wSL (show (0 : Fin 3) ≠ 2 by decide) t *
        wSL (show (0 : Fin 3) ≠ 2 by decide) (-1))) (xPar F2 (g2CommRoot 1) u) := by
  have h7 := commute_pos_e1 (K := K) (a := 7) (Or.inl rfl)
  have h10 := commute_pos_e1 (K := K) (a := 10) (Or.inr rfl)
  simp only [wSL, map_mul, phi_T02 φ hφ, phi_T20 φ hφ]
  exact (((h7 _ u).mul_left (h10 _ u)).mul_left (h7 _ u)).mul_left
    (((h7 _ u).mul_left (h10 _ u)).mul_left (h7 _ u))

theorem phi_scalar_ne_one {r : K} (hr1 : r ≠ 1) (hr3 : r ^ 3 = 1)
    (A : Matrix.SpecialLinearGroup (Fin (2 + 1)) K)
    (hA : Matrix.scalar (Fin 3) r = (A : Matrix (Fin 3) (Fin 3) K)) : φ A ≠ 1 := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr3
  set t : Kˣ := (Units.mk0 r hr0)⁻¹ with ht
  have htv : (t : K) = r⁻¹ := by simp [ht]
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have hA' : A = (wSL (show (0 : Fin 3) ≠ 1 by decide) (t : K) *
        wSL (show (0 : Fin 3) ≠ 1 by decide) (-1)) *
      (wSL (show (0 : Fin 3) ≠ 2 by decide) (t : K) *
        wSL (show (0 : Fin 3) ≠ 2 by decide) (-1)) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_wSL_mul_neg_one _ ht0,
      coe_wSL_mul_neg_one _ ht0, Matrix.diagonal_mul_diagonal, ← hA]
    have hr2 : r⁻¹ * r⁻¹ = r := by
      field_simp
      linear_combination -hr3
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.scalar_apply, htv, hr2]
  intro h1
  rw [hA', map_mul, phi_D01 φ hφ t] at h1
  have hM : φ (wSL (show (0 : Fin 3) ≠ 2 by decide) (t : K) *
        wSL (show (0 : Fin 3) ≠ 2 by decide) (-1)) =
      (torusElement .G2 K (⟨0, by decide⟩ : Fin (Tag.rank .G2)) t)⁻¹ :=
    eq_inv_of_mul_eq_one_right h1
  have hc := commute_phi_D02 φ hφ (t : K) 1
  rw [hM] at hc
  have hc' : Commute (torusElement .G2 K (⟨0, by decide⟩ : Fin (Tag.rank .G2)) t)
      (xPar F2 (g2CommRoot 1) 1) := by simpa using hc.inv_left
  have h2 := hc'.eq
  have h3 := torus_conj_e1 (K := K) t
  rw [h2, mul_inv_cancel_right] at h3
  have hroot : IsRoot .G2 (g2CommRoot 1) := by rw [root1]; exact isRoot_single .G2 _
  have h4 := xPar_injective hroot h3
  apply hr1
  rw [Units.val_inv_eq_inv_val, htv, inv_inv] at h4
  exact h4.symm

theorem a2Hom_injective : Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple (F := K) 2 le_rfl
  have hroot : IsRoot .G2 (g2CommRoot 0) := by rw [root0]; exact isRoot_single .G2 _
  have hnt : ∃ k, φ k ≠ 1 := by
    refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1, ?_⟩
    rw [phi_T01 φ hφ, ← root0]
    intro h
    have h' := xPar_injective hroot (h.trans (xPar_zero (F := F2) (g2CommRoot 0)).symm)
    exact one_ne_zero h'
  have hc := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hnt hg
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  by_cases hr1 : r = 1
  · subst hr1
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hr]
    simp
  · exact absurd (MonoidHom.mem_ker.1 hg) (phi_scalar_ne_one φ hφ hr1 (by simpa using hr3) g hr)

end Phi

end B

section C


variable {K : Type} [Field K] [Finite K]

theorem exists_a2Hom_injective :
    ∃ φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →* ↥(adjointGroup .G2 K),
      Function.Injective φ ∧
        ∀ γ ∈ RA2, ∀ c : K, φ (CFSG.LieType.Steinberg.SL.x 2 K γ c) = a2y γ c := by
  obtain ⟨⟨-, ⟨O⟩, -⟩, -, huniv, -⟩ := sl3_rankTwoPresentation K
  obtain ⟨φ, hφ, -⟩ := huniv O (CFSG.LieType.Steinberg.SL.commC (m := 2))
    (CFSG.LieType.Steinberg.SL.commutatorFormula O) (↥(adjointGroup .G2 K))
    (fun γ c => a2y γ c) (fun γ _ c d => a2y_add γ c d) (a2y_commutatorFormula O)
  exact ⟨φ, a2Hom_injective φ hφ, hφ⟩

end C

end CFSG.GH74.GLS.Stage2.Bender.Thm1
