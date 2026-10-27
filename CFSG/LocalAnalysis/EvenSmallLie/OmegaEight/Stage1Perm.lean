module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bits
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem perm_apply_inv (σ : Equiv.Perm V6) (x : V6) : σ (σ⁻¹ x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem perm_inv_apply (σ : Equiv.Perm V6) (x : V6) : σ⁻¹ (σ x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

@[expose] def linGroup : Subgroup (Equiv.Perm V6) where
  carrier := {σ | ∀ a b, σ (a + b) = σ a + σ b}
  one_mem' a b := rfl
  mul_mem' {σ τ} hσ hτ a b := by
    simp only [Set.mem_ofPred_eq, Equiv.Perm.coe_mul, Function.comp_apply] at *
    rw [hτ, hσ]
  inv_mem' {σ} hσ a b := by
    simp only [Set.mem_ofPred_eq] at *
    apply σ.injective
    rw [hσ, perm_apply_inv, perm_apply_inv, perm_apply_inv]

@[expose] def orthGroup (ε : Eps) : Subgroup (Equiv.Perm V6) where
  carrier := {σ | σ ∈ linGroup ∧ ∀ v, qfV ε (σ v) = qfV ε v}
  one_mem' := ⟨linGroup.one_mem, fun v => rfl⟩
  mul_mem' {σ τ} hσ hτ := ⟨linGroup.mul_mem hσ.1 hτ.1, fun v => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ.2, hτ.2]⟩
  inv_mem' {σ} hσ := ⟨linGroup.inv_mem hσ.1, fun v => by
    conv_rhs => rw [← perm_apply_inv σ v]
    rw [hσ.2]⟩

@[expose] def affGroup (ε : Eps) : Subgroup (Equiv.Perm V6) where
  carrier := {σ | (∀ v, qfV ε (σ v) = qfV ε v) ∧ ∀ a b c, σ (a + b + c) = σ a + σ b + σ c}
  one_mem' := ⟨fun v => rfl, fun a b c => rfl⟩
  mul_mem' {σ τ} hσ hτ := ⟨fun v => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ.1, hτ.1], fun a b c => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hτ.2, hσ.2]⟩
  inv_mem' {σ} hσ := ⟨fun v => by
    conv_rhs => rw [← perm_apply_inv σ v]
    rw [hσ.1], fun a b c => by
    apply σ.injective
    rw [hσ.2, perm_apply_inv, perm_apply_inv, perm_apply_inv,
      perm_apply_inv]⟩

theorem map_zero_of_mem_linGroup {σ : Equiv.Perm V6} (hσ : σ ∈ linGroup) : σ 0 = 0 := by
  have h := hσ 0 0
  rw [add_zero] at h
  exact (left_eq_add.1 h)

@[expose] def basisVec (j : ℕ) : V6 := toVec 6 (2 ^ j)

@[expose] def colsF (f : V6 → V6) : List ℕ :=
  (List.range 6).map fun j => vecBits (f (basisVec j))

@[expose] def colsOf (σ : Equiv.Perm V6) : List ℕ := colsF σ

theorem colsF_length (f : V6 → V6) : (colsF f).length = 6 := by simp [colsF]

theorem colsF_getD (f : V6 → V6) {j : ℕ} (hj : j < 6) :
    (colsF f).getD j 0 = vecBits (f (basisVec j)) := by
  simp [colsF, List.getD_eq_getElem?_getD, hj]

theorem colsOf_length (σ : Equiv.Perm V6) : (colsOf σ).length = 6 := colsF_length σ

theorem colsOf_getD (σ : Equiv.Perm V6) {j : ℕ} (hj : j < 6) :
    (colsOf σ).getD j 0 = vecBits (σ (basisVec j)) := colsF_getD σ hj

theorem eq_sum_basisVec (v : V6) : v = ∑ j : Fin 6, v j • basisVec j := by
  ext i
  simp only [basisVec, toVec_two_pow', Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem map_sum_of_mem_linGroup {σ : Equiv.Perm V6} (hσ : σ ∈ linGroup) (v : V6) :
    σ v = ∑ j : Fin 6, v j • σ (basisVec j) := by
  have hadd : ∀ (s : Finset (Fin 6)) (f : Fin 6 → V6), σ (∑ j ∈ s, f j) = ∑ j ∈ s, σ (f j) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simpa using map_zero_of_mem_linGroup hσ
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hσ, ih]
  have hsmul : ∀ (c : ZMod 2) (w : V6), σ (c • w) = c • σ w := by
    intro c w
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
    · rw [zero_smul, zero_smul, map_zero_of_mem_linGroup hσ]
    · rw [one_smul, one_smul]
  conv_lhs => rw [eq_sum_basisVec v]
  rw [hadd]
  simp only [hsmul]

theorem eq_of_colsOf_eq {σ τ : Equiv.Perm V6} (hσ : σ ∈ linGroup) (hτ : τ ∈ linGroup)
    (h : colsOf σ = colsOf τ) : σ = τ := by
  have hb : ∀ j : Fin 6, σ (basisVec j) = τ (basisVec j) := by
    intro j
    have := congrArg (fun l => l.getD j 0) h
    simp only [colsOf_getD _ j.isLt] at this
    rw [← toVec_vecBits (σ _), this, toVec_vecBits]
  ext1 v
  rw [map_sum_of_mem_linGroup hσ, map_sum_of_mem_linGroup hτ]
  simp only [hb]

@[expose] def ColsValid (ε : Eps) (l : List ℕ) : Prop :=
  ∀ j < 6, l.getD j 0 < 64 ∧ qfB ε (l.getD j 0) = qfB ε (2 ^ j) ∧
    ∀ i < j, bfB ε (l.getD i 0) (l.getD j 0) = bfB ε (2 ^ i) (2 ^ j)

theorem mem_oColsAux (ε : Eps) (ds : List ℕ) :
    ∀ cs : List ℕ, cs.length + ds.length = 6 → ColsValid ε (cs ++ ds) →
      cs ++ ds ∈ oColsAux ε ds.length cs := by
  induction ds with
  | nil => intro cs _ _; simp [oColsAux]
  | cons d ds ih =>
    intro cs hlen hval
    have hk : cs.length < 6 := by simp at hlen; omega
    obtain ⟨h1, h2, h3⟩ := hval cs.length hk
    have hd : (cs ++ d :: ds).getD cs.length 0 = d := by simp [List.getD_eq_getElem?_getD]
    have hcs : ∀ i < cs.length, (cs ++ d :: ds).getD i 0 = cs.getD i 0 := by
      intro i hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    rw [hd] at h1 h2 h3
    simp only [List.length_cons, oColsAux, List.mem_flatMap]
    refine ⟨d, ?_, ?_⟩
    · simp only [extendCols, List.mem_filter, List.mem_range, h1, true_and, Bool.and_eq_true,
        beq_iff_eq, h2, List.all_eq_true]
      intro i hi
      rw [← hcs i hi]
      exact h3 i hi
    · have := ih (cs ++ [d]) (by simp at hlen ⊢; omega) (by simpa using hval)
      simpa using this

theorem mem_oCols {ε : Eps} {l : List ℕ} (hl : l.length = 6) (hv : ColsValid ε l) :
    l ∈ oCols ε := by
  have := mem_oColsAux ε l [] (by simp [hl]) (by simpa using hv)
  simpa [oCols, hl] using this

theorem bz_injective {x y : Bool} (h : bz x = bz y) : x = y := by
  cases x <;> cases y <;> simp_all [bz]

theorem vecBits_basisVec (j : ℕ) (hj : j < 6) : vecBits (basisVec j) = 2 ^ j := by
  rw [basisVec, vecBits_toVec]
  calc 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hj
    _ = 64 := rfl

theorem colsValid_colsOf {ε : Eps} {σ : Equiv.Perm V6} (hσ : σ ∈ orthGroup ε) :
    ColsValid ε (colsOf σ) := by
  have hq : ∀ v, qfB ε (vecBits (σ v)) = qfB ε (vecBits v) := fun v => bz_injective (hσ.2 v)
  intro j hj
  rw [colsOf_getD σ hj]
  refine ⟨vecBits_lt _, by rw [hq, vecBits_basisVec j hj], fun i hi => ?_⟩
  rw [colsOf_getD σ (hi.trans hj), bfB, bfB, ← vecBits_add, ← hσ.1, hq, hq, hq, vecBits_add,
    vecBits_basisVec i (hi.trans hj), vecBits_basisVec j hj]

theorem colsOf_mem_oCols {ε : Eps} {σ : Equiv.Perm V6} (hσ : σ ∈ orthGroup ε) :
    colsOf σ ∈ oCols ε :=
  mem_oCols (colsOf_length σ) (colsValid_colsOf hσ)

@[expose] noncomputable def zeroSet (ε : Eps) : Finset V6 :=
  Finset.univ.filter fun v => qfV ε v = 0

theorem mem_orthGroup_of_mem_affGroup {ε : Eps} {σ : Equiv.Perm V6} (hσ : σ ∈ affGroup ε)
    (h0 : σ 0 = 0) : σ ∈ orthGroup ε := by
  refine ⟨fun a b => ?_, hσ.1⟩
  have := hσ.2 a b 0
  rwa [add_zero, h0, add_zero] at this

theorem affB_lt (d : Array ℕ × ℕ) (hd : d.2 < 64) (x : ℕ) : affB d x < 64 :=
  Nat.xor_lt_two_pow (n := 6) (bmulVec_lt _ _) hd

theorem toVec_affB (d : Array ℕ × ℕ) (v : V6) :
    toVec 6 (affB d (vecBits v)) = toMat 6 6 d.1 *ᵥ v + toVec 6 d.2 := by
  rw [affB, toVec_xor, ← mulVec_toVec, toVec_vecBits]

@[expose] def affPerm (d d' : Array ℕ × ℕ) (hd : d.2 < 64) (hd' : d'.2 < 64)
    (h1 : ∀ x < 64, affB d' (affB d x) = x) (h2 : ∀ x < 64, affB d (affB d' x) = x) :
    Equiv.Perm V6 where
  toFun v := toVec 6 (affB d (vecBits v))
  invFun v := toVec 6 (affB d' (vecBits v))
  left_inv v := by
    simp only
    rw [vecBits_toVec (affB_lt d hd _), h1 _ (vecBits_lt v), toVec_vecBits]
  right_inv v := by
    simp only
    rw [vecBits_toVec (affB_lt d' hd' _), h2 _ (vecBits_lt v), toVec_vecBits]

theorem affPerm_apply {d d' : Array ℕ × ℕ} {hd : d.2 < 64} {hd' : d'.2 < 64}
    {h1 : ∀ x < 64, affB d' (affB d x) = x} {h2 : ∀ x < 64, affB d (affB d' x) = x} (v : V6) :
    affPerm d d' hd hd' h1 h2 v = toVec 6 (affB d (vecBits v)) := rfl

theorem affPerm_inv_apply {d d' : Array ℕ × ℕ} {hd : d.2 < 64} {hd' : d'.2 < 64}
    {h1 : ∀ x < 64, affB d' (affB d x) = x} {h2 : ∀ x < 64, affB d (affB d' x) = x} (v : V6) :
    (affPerm d d' hd hd' h1 h2)⁻¹ v = toVec 6 (affB d' (vecBits v)) := rfl

theorem affPerm_mem {ε : Eps} {d d' : Array ℕ × ℕ} {hd : d.2 < 64} {hd' : d'.2 < 64}
    {h1 : ∀ x < 64, affB d' (affB d x) = x} {h2 : ∀ x < 64, affB d (affB d' x) = x}
    (hq : ∀ x < 64, qfB ε (affB d x) = qfB ε x) : affPerm d d' hd hd' h1 h2 ∈ affGroup ε := by
  refine ⟨fun v => ?_, fun a b c => ?_⟩
  · rw [affPerm_apply, qfV_toVec ε (affB_lt d hd _), hq _ (vecBits_lt v), qfV]
  · simp only [affPerm_apply, toVec_affB, mulVec_add]
    have key : ∀ x y z w : V6, x + y + z + w = x + w + (y + w) + (z + w) := by
      intro x y z w
      ext i
      simp only [Pi.add_apply]
      exact (by decide : ∀ a b c e : ZMod 2, a + b + c + e = a + e + (b + e) + (c + e)) _ _ _ _
    exact key _ _ _ _

end CFSG.EvenSmallLie.OmegaEight.Stage1
