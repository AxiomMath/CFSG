module

public import CFSG.Certificates.Kernel.PermCent.L33RepTwinSound
public import CFSG.GH74.GLS.Prop27.LocBalReps
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallInner

public section

namespace CFSG.Certificates.Kernel.PkCV.L33R

open Subgroup CFSG.GH74.GLS.Prop27 CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups CFSG.Sporadic.Schreier

section Inv

variable {G : Type} [Group G]

@[expose] def OddCoreAtP (P A : Subgroup G) (τ : G) : Prop :=
  ∀ x ∈ A, x * τ = τ * x → x ≠ 1 → Odd (orderOf x) →
    ∃ c ∈ P, c * τ = τ * c ∧ Even (orderOf (x * c * x⁻¹ * c⁻¹))

theorem oddCoreAtP_conj {P A : Subgroup G} (hnorm : ∀ g ∈ A, ∀ y ∈ P, g * y * g⁻¹ ∈ P)
    {g r : G} (hg : g ∈ A) (h : OddCoreAtP P A r) : OddCoreAtP P A (g * r * g⁻¹) := by
  intro x hx hxτ hx1 hxodd
  have hx' : g⁻¹ * x * g ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hg) hx) hg
  have hx'r : (g⁻¹ * x * g) * r = r * (g⁻¹ * x * g) := (conj_comm_iff g x r).1 hxτ
  have hx'1 : g⁻¹ * x * g ≠ 1 := by
    intro e
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [e, mul_one, mul_inv_cancel]
  have hx'odd : Odd (orderOf (g⁻¹ * x * g)) := by
    have h1 := orderOf_conj_eq g⁻¹ x
    rw [inv_inv] at h1
    rw [h1]
    exact hxodd
  obtain ⟨c', hc'P, hc'r, hc'even⟩ := h _ hx' hx'r hx'1 hx'odd
  refine ⟨g * c' * g⁻¹, hnorm g hg c' hc'P, ?_, ?_⟩
  · have h1 : (g * c' * g⁻¹) * (g * r * g⁻¹) = g * (c' * r) * g⁻¹ := by group
    have h2 : (g * r * g⁻¹) * (g * c' * g⁻¹) = g * (r * c') * g⁻¹ := by group
    rw [h1, h2, hc'r]
  · have h1 : x * (g * c' * g⁻¹) * x⁻¹ * (g * c' * g⁻¹)⁻¹ =
        g * ((g⁻¹ * x * g) * c' * (g⁻¹ * x * g)⁻¹ * c'⁻¹) * g⁻¹ := by group
    rw [h1, orderOf_conj_eq]
    exact hc'even

theorem oddCoreAtP_of_conj {P A : Subgroup G} (hnorm : ∀ g ∈ A, ∀ y ∈ P, g * y * g⁻¹ ∈ P)
    {g x : G} (hg : g ∈ A) (h : OddCoreAtP P A (g * x * g⁻¹)) : OddCoreAtP P A x := by
  have h1 := oddCoreAtP_conj hnorm (A.inv_mem hg) h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem goodOrInnerPred_map {Y : Type} [Group Y] {N : Subgroup Y} (φ : Y ≃* Y)
    (hN : ∀ y, φ y ∈ N ↔ y ∈ N) {t : Y} (h : GoodOrInnerPred N (φ t)) : GoodOrInnerPred N t := by
  obtain ⟨h1, h2⟩ := h
  have hC : ∀ c, c ∈ centralizer ({t} : Set Y) ↔ φ c ∈ centralizer ({φ t} : Set Y) := by
    intro c
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      φ.injective.eq_iff]
  have hC' : ∀ c, c ∈ centralizer ({φ t} : Set Y) → φ.symm c ∈ centralizer ({t} : Set Y) := by
    intro c hc
    rw [hC, MulEquiv.apply_symm_apply]
    exact hc
  have hconj : ∀ c a : Y, c * φ a * c⁻¹ = φ (φ.symm c * a * (φ.symm c)⁻¹) := by
    intro c a
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  refine ⟨fun o ho hne hodd => ?_, fun a b haa hbb hba hnorm => ?_⟩
  · obtain ⟨c, hc, he⟩ := h1 (φ o) ((hC o).1 ho) (fun e => hne (φ.injective (by rw [e, map_one])))
      (by rwa [MulEquiv.orderOf_eq φ o])
    refine ⟨φ.symm c, hC' c hc, ?_⟩
    rw [← MulEquiv.orderOf_eq φ, map_mul, ← hconj]
    exact he
  · have hq : q8List (φ t) (φ a) (φ b) = (q8List t a b).map φ := by
      simp [q8List, map_mul]
    have hnorm' : ∀ c ∈ centralizer ({φ t} : Set Y),
        c * φ a * c⁻¹ ∈ q8List (φ t) (φ a) (φ b) ∧ c * φ b * c⁻¹ ∈ q8List (φ t) (φ a) (φ b) := by
      intro c hc
      obtain ⟨ha', hb'⟩ := hnorm _ (hC' c hc)
      rw [hq, hconj, hconj]
      exact ⟨List.mem_map_of_mem ha', List.mem_map_of_mem hb'⟩
    rcases h2 (φ a) (φ b) (by rw [← map_mul, haa]) (by rw [← map_mul, hbb])
        (by rw [← map_mul, ← map_mul, ← map_mul, hba]) hnorm' with
      ⟨ha, hb⟩ | ⟨x, hx, hx3, hmv, hcomm⟩
    · exact Or.inl ⟨(hN a).1 ha, (hN b).1 hb⟩
    · refine Or.inr ⟨φ.symm x, hC' x hx, φ.injective ?_, fun ⟨e1, e2⟩ => hmv ⟨?_, ?_⟩,
        fun y hy hya hyb => φ.injective ?_⟩
      · rw [map_pow, MulEquiv.apply_symm_apply, hx3, map_one]
      · have e := congrArg φ e1
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at e
      · have e := congrArg φ e2
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at e
      · rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hcomm (φ y) ((hC y).1 hy) (by rw [← map_mul, ← map_mul, hya])
          (by rw [← map_mul, ← map_mul, hyb])

theorem goodOrInnerPred_of_conj {P A : Subgroup G} (hnorm : ∀ g ∈ A, ∀ y ∈ P, g * y * g⁻¹ ∈ P)
    {g x : G} (hg : g ∈ A)
    (h : ∀ hx : g * x * g⁻¹ ∈ A, GoodOrInnerPred (P.subgroupOf A) ⟨g * x * g⁻¹, hx⟩) :
    ∀ hx : x ∈ A, GoodOrInnerPred (P.subgroupOf A) ⟨x, hx⟩ := by
  intro hx
  refine goodOrInnerPred_map (MulAut.conj (⟨g, hg⟩ : A)) (fun y => ?_) ?_
  · rw [MulAut.conj_apply, mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    constructor
    · intro hy
      have h1 := hnorm g⁻¹ (A.inv_mem hg) _ hy
      have e : g⁻¹ * (g * (y : G) * g⁻¹) * g⁻¹⁻¹ = y := by group
      rwa [e] at h1
    · exact hnorm g hg y
  · exact h (A.mul_mem (A.mul_mem hg hx) (A.inv_mem hg))

end Inv

section Rep

variable {n : Nat} [Small n]

theorem oddCoreRep_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) (hPA : QP.originalSubgroup ≤ QA.originalSubgroup) {a m : ℕ}
    (hm : Odd m) (hcard : Nat.card QA.originalSubgroup = 2 ^ a * m) {τ : CV n}
    (h : oddCoreRepC m (elemsC QA) (elemsC QP) τ = true) :
    OddCoreAtP QP.originalSubgroup QA.originalSubgroup (ev τ) :=
  oddCoreAt_sound QA QP hQA hQP hPA hm hcard
    (by rw [elemsT_eq_elemsC, elemsT_eq_elemsC, oddCoreRep_C]; exact h)

theorem goodAt_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) {B : ℕ} {t : CV n} (ht : ev t ∈ QA.originalSubgroup)
    (h : goodAtC B (elemsC QP) (elemsC QA) t = true) :
    GoodOrInnerPred (QP.originalSubgroup.subgroupOf QA.originalSubgroup) ⟨ev t, ht⟩ := by
  rw [← goodAt_C, ← elemsT_eq_elemsC, ← elemsT_eq_elemsC, Bool.and_eq_true] at h
  have hι : Function.Injective QA.originalSubgroup.subtype := Subtype.val_injective
  have hL : ∀ m, m ∈ elemsT QA ↔ ∃ y, QA.originalSubgroup.subtype y = m := fun m => by
    rw [mem_elemsT QA hQA m]
    exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  have hLN : ∀ y, QA.originalSubgroup.subtype y ∈ elemsT QP ↔
      y ∈ QP.originalSubgroup.subgroupOf QA.originalSubgroup := fun y => by
    rw [mem_elemsT QP hQP, mem_subgroupOf]
    rfl
  exact ⟨noOddNormalAt_of_noOddB hι hL h.1, fun a b haa hbb hba hnorm =>
    witness_of_pairsN hι hL hLN h.2 a b haa hbb hba hnorm⟩

end Rep

end CFSG.Certificates.Kernel.PkCV.L33R

end
