module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverWords
public import CFSG.RankThree.Asc83Table.E27
public import CFSG.Certificates.CosetTableRelations
public import CFSG.Certificates.CosetTableShort
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverSetup
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestNative

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.Asc83Table Subgroup

structure J3Pkg {X : Type*} [Group X] (k : Fin 6 → X) : Prop where
  eqs : ∀ u ∈ eqWords, evalW k u = 1
  moves : ∀ u ∈ moveWords, evalW k u ≠ 1
  zc : evalW k zw ∈ center X

section Alg

variable {X : Type*} [Group X] (k : Fin 6 → X)

theorem evalW_powW (i : Fin 6) (n : ℕ) : evalW k (powW i n) = k i ^ n := by
  induction n with
  | zero => simp [powW, evalW]
  | succ n ih =>
    have : powW i (n + 1) = (i, true) :: powW i n := rfl
    rw [this, evalW_cons, ih, pow_succ']
    rfl

theorem evalW_zeta_pow (n : ℕ) : evalW k (List.replicate n zw).flatten = (evalW k zw) ^ n := by
  induction n with
  | zero => simp [evalW]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, evalW_append, ih, pow_succ']

@[expose] def xB : Fin 4 → X := ![k 3, k 4, k 5, evalW k zw]

theorem basisProd_xB (a : Fin 4 → ZMod 3) :
    basisProd (xB k) a =
      k 3 ^ (a 0).val * (k 4 ^ (a 1).val * (k 5 ^ (a 2).val * (evalW k zw) ^ (a 3).val)) := by
  simp [basisProd, List.ofFn_succ, xB]

theorem evalW_toWordB (a : Fin 4 → ZMod 3) : evalW k (toWordB a) = basisProd (xB k) a := by
  rw [basisProd_xB, toWordB, evalW_append, evalW_append, evalW_append, evalW_powW, evalW_powW,
    evalW_powW, evalW_zeta_pow, mul_assoc, mul_assoc]

theorem mem_moveWords {a : Fin 4 → ZMod 3} (ha : a ≠ 0) : toWordB a ∈ moveWords := by
  have h : a ∈ allVecs := by
    revert a; decide
  unfold moveWords
  exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨h, by simpa using ha⟩, rfl⟩

end Alg

theorem mem_eqWords_powW3 (i : Fin 6) (hi : i = 3 ∨ i = 4 ∨ i = 5) : powW i 3 ∈ eqWords := by
  rcases hi with rfl | rfl | rfl <;> simp [eqWords]

namespace J3Pkg

variable {X : Type*} [Group X] {k : Fin 6 → X} (h : J3Pkg k)
include h

theorem pow_three (i : Fin 6) (hi : i = 3 ∨ i = 4 ∨ i = 5) : k i ^ 3 = 1 := by
  have := h.eqs _ (mem_eqWords_powW3 i hi)
  rwa [evalW_powW] at this

theorem zeta_pow_three : (evalW k zw) ^ 3 = 1 := by
  have := h.eqs ((List.replicate 3 zw).flatten) (by simp [eqWords])
  rwa [evalW_zeta_pow] at this

theorem comm_zeta (g : X) : g * evalW k zw = evalW k zw * g := Subgroup.mem_center_iff.1 h.zc g

theorem commute_of_eval {a b : Fin 6} (hw : [(a, true), (b, true), (a, false), (b, false)] ∈ eqWords) :
    Commute (k a) (k b) := by
  have := h.eqs _ hw
  simp only [evalW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Bool.cond_true, Bool.cond_false] at this
  have e : k a * k b * (k a)⁻¹ * (k b)⁻¹ = 1 :=
    (show k a * k b * (k a)⁻¹ * (k b)⁻¹ = k a * (k b * ((k a)⁻¹ * (k b)⁻¹)) by group).trans this
  have h2 : k a * k b = k b * k a := by
    calc k a * k b = (k a * k b * (k a)⁻¹ * (k b)⁻¹) * (k b * k a) := by group
      _ = k b * k a := by rw [e, one_mul]
  exact h2

theorem x_pow (i : Fin 4) : xB k i ^ 3 = 1 := by
  fin_cases i
  · exact h.pow_three 3 (by simp)
  · exact h.pow_three 4 (by simp)
  · exact h.pow_three 5 (by simp)
  · exact h.zeta_pow_three

theorem x_comm (i j : Fin 4) : Commute (xB k i) (xB k j) := by
  have h34 : Commute (k 3) (k 4) := h.commute_of_eval (by simp [eqWords])
  have h35 : Commute (k 3) (k 5) := h.commute_of_eval (by simp [eqWords])
  have h45 : Commute (k 4) (k 5) := h.commute_of_eval (by simp [eqWords])
  have hz : ∀ g : X, Commute g (evalW k zw) := fun g => h.comm_zeta g
  fin_cases i <;> fin_cases j <;>
    first
    | exact Commute.refl _
    | exact h34 | exact h34.symm | exact h35 | exact h35.symm | exact h45 | exact h45.symm
    | exact hz _ | exact (hz _).symm

theorem basisProd_ne_one {a : Fin 4 → ZMod 3} (ha : a ≠ 0) : basisProd (xB k) a ≠ 1 := by
  rw [← evalW_toWordB]
  exact h.moves _ (mem_moveWords ha)

theorem basisProd_injective : Function.Injective (basisProd (xB k)) := by
  intro a b hab
  have hx := h.x_pow
  have hc := h.x_comm
  have h1 : basisHom hx hc (Multiplicative.ofAdd a) = basisHom hx hc (Multiplicative.ofAdd b) :=
    Subtype.ext (by rw [coe_basisHom, coe_basisHom]; exact hab)
  have h2 : basisHom hx hc (Multiplicative.ofAdd (a - b)) = 1 := by
    rw [ofAdd_sub, div_eq_mul_inv, map_mul, map_inv, h1, mul_inv_cancel]
  have h3 : basisProd (xB k) (a - b) = 1 := by
    have := congrArg Subtype.val h2
    rwa [coe_basisHom, toAdd_ofAdd] at this
  by_contra hne
  exact h.basisProd_ne_one (sub_ne_zero.2 hne) h3

theorem act_lt (i j : Fin 3) :
    k ⟨i.val, by omega⟩ * k ⟨3 + j.val, by omega⟩ * (k ⟨i.val, by omega⟩)⁻¹ =
      basisProd (xB k) fun r => actMat ⟨i.val, by omega⟩ r j.castSucc := by
  have hm : actWord ⟨i.val, by omega⟩ j ∈ eqWords := by
    simp only [eqWords, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
      true_and]
    exact Or.inr ⟨i, j, rfl⟩
  have := h.eqs _ hm
  rw [actWord, evalW_append, evalW_invW, evalW_toWordB] at this
  have h1 : evalW k [((⟨i.val, by omega⟩ : Fin 6), true), (⟨3 + j.val, by omega⟩, true),
      (⟨i.val, by omega⟩, false)] = k ⟨i.val, by omega⟩ * k ⟨3 + j.val, by omega⟩ *
        (k ⟨i.val, by omega⟩)⁻¹ := by
    simp [evalW, mul_assoc]
  rw [h1] at this
  exact mul_inv_eq_one.1 this

theorem act (i : Fin 6) (j : Fin 4) :
    k i * xB k j * (k i)⁻¹ = basisProd (xB k) fun r => actMat i r j := by
  by_cases hj : j = 3
  · subst hj
    have hz : k i * xB k 3 * (k i)⁻¹ = xB k 3 := by
      have := h.comm_zeta (k i)
      change k i * evalW k zw * (k i)⁻¹ = evalW k zw
      rw [this]; group
    rw [hz]
    fin_cases i <;> (rw [basisProd_xB]; simp [actMat, xB, show (1 : ZMod 3).val = 1 from rfl])
  · obtain ⟨j', rfl⟩ : ∃ j' : Fin 3, j = j'.castSucc := by
      refine ⟨⟨j.val, by omega⟩, ?_⟩
      · apply Fin.ext; simp
    have hxj : xB k j'.castSucc = k ⟨3 + j'.val, by omega⟩ := by
      fin_cases j' <;> rfl
    rw [hxj]
    by_cases hi : i.val < 3
    · have := h.act_lt ⟨i.val, hi⟩ j'
      simpa using this
    · have hc : Commute (k i) (k ⟨3 + j'.val, by omega⟩) := by
        have hi3 : i = 3 ∨ i = 4 ∨ i = 5 := by
          fin_cases i <;> simp_all
        have e : ∀ m : Fin 3, xB k m.castSucc = k ⟨3 + m.val, by omega⟩ := by
          intro m; fin_cases m <;> rfl
        rcases hi3 with rfl | rfl | rfl
        · have := h.x_comm 0 j'.castSucc; rw [hxj] at this; exact this
        · have := h.x_comm 1 j'.castSucc; rw [hxj] at this; exact this
        · have := h.x_comm 2 j'.castSucc; rw [hxj] at this; exact this
      rw [hc.eq, mul_inv_cancel_right]
      have hmat : actMat i = 1 := by
        fin_cases i <;> simp_all [actMat]
      rw [hmat, basisProd_xB]
      fin_cases j' <;>
        simp [xB, Matrix.one_apply, Fin.ext_iff, show (1 : ZMod 3).val = 1 from rfl]

end J3Pkg

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
