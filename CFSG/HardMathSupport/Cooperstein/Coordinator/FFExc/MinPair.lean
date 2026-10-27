module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinLead
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairTransfer
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairDataE6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairDataE7
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairGraph
public import CFSG.LieType.Steinberg.Minuscule.Form
public import CFSG.Blueprint.ChevalleyRootArtifact
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate129090
import Certificates.Data.Kernel.PairBnb
import CFSG.Certificates.Kernel.PairBnbSound
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.EachTrue

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley Matrix

@[expose] def fWt (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun γ := ∑ i : Fin n, 7 ^ (i : ℕ) * γ i
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

@[expose] def horner (l : List ℤ) : ℤ := l.foldr (fun x acc => x + 7 * acc) 0

theorem horner_ofFn : ∀ (n : ℕ) (γ : Fin n → ℤ), horner (List.ofFn γ) = fWt n γ
  | 0, γ => by simp [horner, fWt]
  | n + 1, γ => by
    rw [List.ofFn_succ, horner, List.foldr_cons, ← horner, horner_ofFn n]
    simp only [fWt, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
      one_mul, Fin.val_succ, pow_succ, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

structure PosData (τ : Tag) (R : List (List ℤ)) : Prop where
  inj : ∀ γ δ : Fin τ.rank → ℤ, IsRoot τ γ → IsRoot τ δ → fWt τ.rank γ = fWt τ.rank δ → γ = δ
  pos : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (0 < fWt τ.rank γ ↔ 0 < ht γ)
  mem : ∀ γ : Fin τ.rank → ℤ, (IsRoot τ γ ∧ 0 < ht γ) ↔ List.ofFn γ ∈ R

theorem posData_of (τ : Tag) (R : List (List ℤ))
    (hinj : ∀ l ∈ τ.artifactRoots, ∀ l' ∈ τ.artifactRoots, horner l = horner l' → l = l')
    (hpos : ∀ l ∈ τ.artifactRoots, (0 < horner l ↔ 0 < l.sum))
    (hR1 : ∀ l ∈ R, l ∈ τ.artifactRoots ∧ 0 < l.sum)
    (hR2 : ∀ l ∈ τ.artifactRoots, 0 < l.sum → l ∈ R) : PosData τ R where
  inj γ δ hγ hδ h := by
    refine List.ofFn_injective (hinj _ (isRoot_iff_mem_artifactRoots.1 hγ) _
      (isRoot_iff_mem_artifactRoots.1 hδ) ?_)
    rw [horner_ofFn, horner_ofFn]; exact h
  pos γ hγ := by
    have := hpos _ (isRoot_iff_mem_artifactRoots.1 hγ)
    rw [horner_ofFn] at this
    rw [this, ht, List.sum_ofFn]
  mem γ := by
    have hs : (List.ofFn γ).sum = ht γ := by rw [ht, List.sum_ofFn]
    constructor
    · rintro ⟨h1, h2⟩
      exact hR2 _ (isRoot_iff_mem_artifactRoots.1 h1) (by rw [hs]; exact h2)
    · intro h
      obtain ⟨h1, h2⟩ := hR1 _ h
      exact ⟨isRoot_iff_mem_artifactRoots.2 h1, by rw [← hs]; exact h2⟩

theorem posData_E6 : PosData .E6 e6R :=
  posData_of .E6 e6R (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem posData_E7 : PosData .E7 e7R :=
  posData_of .E7 e7R (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem e6W_eq : e6W = (List.range e6Data.d).map fun a => List.ofFn (e6Data.wt a) := by
  decide +kernel

theorem e7W_eq : e7W = (List.range e7Data.d).map fun a => List.ofFn (e7Data.wt a) := by
  decide +kernel

theorem e6_27_numbers (X : Finset (Fin Tag.E6.rank → ℤ)) (Y : Finset (Fin e6Data.d))
    (hX : X.Nonempty) (hXP : ∀ γ ∈ X, IsRoot .E6 γ ∧ 0 < ht γ)
    (hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot .E6 (γ + δ))
    (hXY : ∀ γ ∈ X, ∀ a ∈ Y, ¬ (e6Data.wt a ⬝ᵥ γ = -1)) :
    X.card + Y.card ≤ 26 ∧ 2 * X.card + Y.card ≤ 42 := by
  have h1 := pair_transfer (d := e6Data.d) e6R e6W e6Nb e6O1 1 1 25 e6Data.wt
    (fun γ => IsRoot .E6 γ ∧ 0 < ht γ) e6_nb e6_chk1 posData_E6.mem e6W_eq X Y hX hXP
    (fun γ hγ δ hδ h => hXX γ hγ δ hδ h.1) hXY
  have h2 := pair_transfer (d := e6Data.d) e6R e6W e6Nb e6O2 2 1 40 e6Data.wt
    (fun γ => IsRoot .E6 γ ∧ 0 < ht γ) e6_nb e6_chk2 posData_E6.mem e6W_eq X Y hX hXP
    (fun γ hγ δ hδ h => hXX γ hγ δ hδ h.1) hXY
  omega

theorem e7_56_numbers (X : Finset (Fin Tag.E7.rank → ℤ)) (Y : Finset (Fin e7Data.d))
    (hX : X.Nonempty) (hXP : ∀ γ ∈ X, IsRoot .E7 γ ∧ 0 < ht γ)
    (hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot .E7 (γ + δ))
    (hXY : ∀ γ ∈ X, ∀ a ∈ Y, ¬ (e7Data.wt a ⬝ᵥ γ = -1)) :
    X.card + Y.card ≤ 45 ∧ 2 * X.card + Y.card ≤ 55 := by
  obtain ⟨hnb, hc1, hc2⟩ : e7Check := Certificates.certificate129090
  have h1 := pair_transfer (d := e7Data.d) e7R e7W e7Nb e7O1 1 1 44 e7Data.wt
    (fun γ => IsRoot .E7 γ ∧ 0 < ht γ) hnb hc1 posData_E7.mem e7W_eq X Y hX hXP
    (fun γ hγ δ hδ h => hXX γ hγ δ hδ h.1) hXY
  have h2 := pair_transfer (d := e7Data.d) e7R e7W e7Nb e7O2 2 1 53 e7Data.wt
    (fun γ => IsRoot .E7 γ ∧ 0 < ht γ) hnb hc2 posData_E7.mem e7W_eq X Y hX hXP
    (fun γ hγ δ hδ h => hXX γ hγ δ hδ h.1) hXY
  omega

theorem e6_abelian_card_le (X : Finset (Fin Tag.E6.rank → ℤ))
    (hXP : ∀ γ ∈ X, IsRoot .E6 γ ∧ 0 < ht γ) (hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot .E6 (γ + δ)) :
    X.card ≤ 16 :=
  abelian_transfer e6R e6rNb e6rO1 16 (fun γ => IsRoot .E6 γ ∧ 0 < ht γ) e6r_nb e6r_chk
    posData_E6.mem X hXP (fun γ hγ δ hδ h => hXX γ hγ δ hδ h.1)

theorem e7_abelian_card_le (X : Finset (Fin Tag.E7.rank → ℤ))
    (hXP : ∀ γ ∈ X, IsRoot .E7 γ ∧ 0 < ht γ) (hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot .E7 (γ + δ)) :
    X.card ≤ 27 :=
  abelian_transfer e7R e7rNb e7rO1 27 (fun γ => IsRoot .E7 γ ∧ 0 < ht γ) e7r_nb e7r_chk
    posData_E7.mem X hXP (fun γ hγ δ hδ h => hXX γ hγ δ hδ h.1)

section Group

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) {R : List (List ℤ)}

@[expose] def posUnip (k : Type*) [Field k] : Subgroup (hV.minGroup k) :=
  ⨆ γ ∈ {γ | IsRoot τ γ ∧ 0 < ht γ}, hV.rootGroup k γ

theorem lvlU_one_eq (hPD : PosData τ R) (k : Type*) [Field k] :
    lvlU hV k (fWt τ.rank) 1 = posUnip hV k := by
  have h : {γ | γ ∈ posRoots (fWt τ.rank) ∧ 1 ≤ fWt τ.rank γ} =
      {γ | IsRoot τ γ ∧ 0 < ht γ} := by
    ext γ
    simp only [posRoots, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩
      exact ⟨h1, (hPD.pos γ h1).1 h2⟩
    · rintro ⟨h1, h2⟩
      have := (hPD.pos γ h1).2 h2
      exact ⟨⟨h1, this⟩, by omega⟩
  unfold lvlU lvl posUnip
  rw [h]

variable {hV} in
theorem pair_group_bound (hPD : PosData τ R)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (hc0 : 0 < τ.cartan.det) {k : Type*} [Field k]
    [Finite k] (N1 N2 : ℕ)
    (hnum : ∀ (X : Finset (Fin τ.rank → ℤ)) (Y : Finset (Fin D.d)), X.Nonempty →
      (∀ γ ∈ X, IsRoot τ γ ∧ 0 < ht γ) → (∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot τ (γ + δ)) →
      (∀ γ ∈ X, ∀ a ∈ Y, ¬ (D.wt a ⬝ᵥ γ = -1)) →
      X.card + Y.card ≤ N1 ∧ 2 * X.card + Y.card ≤ N2)
    {A : Subgroup (hV.minGroup k)} (hAU : A ≤ posUnip hV k)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (fixedSub (hV := hV) (k := k) A) ≤ Nat.card k ^ N1 ∧
      Nat.card A ^ 2 * Nat.card (fixedSub (hV := hV) (k := k) A) ≤ Nat.card k ^ N2 := by
  rw [← lvlU_one_eq hV hPD k] at hAU
  obtain ⟨X, Y, hXr, hXX, hXY, hAc', hCc, hne⟩ :=
    exists_leading_data (hV := hV) (k := k) hc0 (fun γ δ hγ hδ h => hPD.inj γ δ hγ hδ h) hAU hAc
  have hX := hne hA
  have hXP : ∀ γ ∈ X, IsRoot τ γ ∧ 0 < ht γ := fun γ hγ =>
    ⟨(hXr γ hγ).1, (hPD.pos γ (hXr γ hγ).1).1 (hXr γ hγ).2⟩
  have hXY' : ∀ γ ∈ X, ∀ a ∈ Y, ¬ (D.wt a ⬝ᵥ γ = -1) := by
    intro γ hγ a ha h
    have := (hV.rootOp_single_ne_zero_iff (R := k) hsymm (hXP γ hγ).1 a).2 h
    exact this (hXY γ hγ a ha)
  obtain ⟨hn1, hn2⟩ := hnum X Y hX hXP hXX hXY'
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  have e1 : Nat.card A * Nat.card (fixedSub (hV := hV) (k := k) A) ≤ Nat.card k ^ (X.card + Y.card) := by
    rw [pow_add]; exact Nat.mul_le_mul hAc' hCc
  have e2 : Nat.card A ^ 2 * Nat.card (fixedSub (hV := hV) (k := k) A) ≤
      Nat.card k ^ (2 * X.card + Y.card) := by
    rw [pow_add, pow_mul']
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hAc' 2) hCc
  exact ⟨e1.trans (Nat.pow_le_pow_right hq hn1), e2.trans (Nat.pow_le_pow_right hq hn2)⟩

end Group

variable (k : Type*) [Field k] [Finite k]

theorem e6_27_pair_bound {A : Subgroup (e6Data_valid.minGroup k)}
    (hAU : A ≤ posUnip e6Data_valid k) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (fixedSub (hV := e6Data_valid) (k := k) A) ≤ Nat.card k ^ 26 ∧
      Nat.card A ^ 2 * Nat.card (fixedSub (hV := e6Data_valid) (k := k) A) ≤ Nat.card k ^ 42 :=
  pair_group_bound posData_E6 (cartan_symm posDef_cartan_E6) (MinData.det_cartan_pos posDef_cartan_E6)
    26 42 (fun X Y hX hXP hXX hXY => e6_27_numbers X Y hX hXP hXX hXY) hAU hAc hA

theorem e7_56_pair_bound {A : Subgroup (e7Data_valid.minGroup k)}
    (hAU : A ≤ posUnip e7Data_valid k) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (fixedSub (hV := e7Data_valid) (k := k) A) ≤ Nat.card k ^ 45 ∧
      Nat.card A ^ 2 * Nat.card (fixedSub (hV := e7Data_valid) (k := k) A) ≤ Nat.card k ^ 55 :=
  pair_group_bound posData_E7 (cartan_symm posDef_cartan_E7) (MinData.det_cartan_pos posDef_cartan_E7)
    45 55 (fun X Y hX hXP hXX hXY => e7_56_numbers X Y hX hXP hXX hXY) hAU hAc hA

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
