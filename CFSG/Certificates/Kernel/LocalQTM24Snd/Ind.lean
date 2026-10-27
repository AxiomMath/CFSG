module

public import Certificates.Data.Kernel.LocalQT.M24L
public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.Elt
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.KC.LQT CFSG.KC.LQT.Syl.CoreSnd

variable {n : ℕ}

private theorem aux_ind_idxK_cons (x y : ℕ) (l : List ℕ) :
    CFSG.KC.LQT.M24.idxK x (y :: l) =
      Bool.rec (motive := fun _ => ℕ) (Nat.succ (CFSG.KC.LQT.M24.idxK x l)) 0 (Nat.beq y x) :=
  rfl

private theorem aux_ind_idxK_get : ∀ (l : List ℕ), l.Nodup → ∀ (j x : ℕ), l[j]? = some x →
    CFSG.KC.LQT.M24.idxK x l = j
  | [], _, j, x, h => by simp at h
  | y :: l, _, 0, x, h => by
    have hxy : y = x := by simpa using h
    subst hxy
    rw [aux_ind_idxK_cons, Nat.beq_refl]
  | y :: l, hnd, j + 1, x, h => by
    have h' : l[j]? = some x := h
    have hx : x ∈ l := List.mem_of_getElem? h'
    have hne : x ≠ y := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hx)
    have hb : Nat.beq y x = false := by
      cases hc : Nat.beq y x
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hc).symm hne
    rw [aux_ind_idxK_cons, hb]
    have := aux_ind_idxK_get l (List.nodup_cons.1 hnd).2 j x h'
    show Nat.succ (CFSG.KC.LQT.M24.idxK x l) = j + 1
    omega

theorem idxK_of_getElem? {l : List ℕ} (hl : l.Nodup) {j x : ℕ} (h : l[j]? = some x) :
    CFSG.KC.LQT.M24.idxK x l = j :=
  aux_ind_idxK_get l hl j x h

private theorem aux_ind_getK : ∀ (l : List ℕ) (i : ℕ),
    CFSG.KC.LQT.S.getK l i = l.getD i 0
  | [], i => by cases i <;> rfl
  | _ :: _, 0 => rfl
  | x :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact aux_ind_getK l i

private theorem aux_ind_getD_inj {B : List (Perm (Fin n))} (hB : EFacts B) {a b : ℕ}
    (ha : a < 16) (hb : b < 16) (e : (lst B).getD a 1 = (lst B).getD b 1) : a = b := by
  have ha' : a < (lst B).length := by have := lst_length B; omega
  have hb' : b < (lst B).length := by have := lst_length B; omega
  rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at e
  exact (List.Nodup.getElem_inj_iff hB.nodup).1 e

private theorem aux_ind_map_getElem? {B : List (Perm (Fin n))} {j : ℕ} (hj : j < 16) :
    ((lst B).map P.code)[j]? = some (P.code ((lst B).getD j 1)) := by
  have hj' : j < (lst B).length := by have := lst_length B; omega
  rw [List.getElem?_map, List.getElem?_eq_getElem hj', List.getD_eq_getElem _ _ hj']
  rfl

theorem indK_spec (hn : n ≤ 32) {B : List (Perm (Fin n))} (hB : EFacts B) (g : Perm (Fin n))
    (hg : g ∈ Subgroup.normalizer
      ((Subgroup.closure {b | b ∈ B} : Subgroup (Perm (Fin n))) : Set (Perm (Fin n)))) :
    ∃ τ : Perm (Fin 16), CFSG.KC.LQT.M24.indK n ((lst B).map P.code) (P.code g) = P.code τ ∧
      ∀ i : Fin 16, (lst B).getD (τ i) 1 = g * (lst B).getD i 1 * g⁻¹ := by
  have hmem : ∀ i : ℕ, i < 16 → g * (lst B).getD i 1 * g⁻¹ ∈ lst B := by
    intro i hi
    have hi' : i < (lst B).length := by have := lst_length B; omega
    have hx : (lst B).getD i 1 ∈ lst B := by
      rw [List.getD_eq_getElem _ _ hi']
      exact List.getElem_mem hi'
    have hE : (lst B).getD i 1 ∈ Subgroup.closure {b | b ∈ B} :=
      (mem_closure_iff_lst hB _).2 hx
    have hc : g * (lst B).getD i 1 * g⁻¹ ∈ Subgroup.closure {b | b ∈ B} :=
      SetLike.mem_coe.1 ((Subgroup.mem_normalizer_iff.1 hg _).1 (SetLike.mem_coe.2 hE))
    exact (mem_closure_iff_lst hB _).1 hc
  have hidx : ∀ i : Fin 16, ∃ j : Fin 16,
      (lst B).getD j 1 = g * (lst B).getD i 1 * g⁻¹ := by
    intro i
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.1 (hmem i i.isLt)
    have hj16 : j < 16 := by have := lst_length B; omega
    refine ⟨⟨j, hj16⟩, ?_⟩
    show (lst B).getD j 1 = _
    rw [List.getD_eq_getElem _ _ hj]
    exact hjx
  choose f hf using hidx
  have finj : Function.Injective f := by
    intro i i' e
    have h3 : g * (lst B).getD i 1 * g⁻¹ = g * (lst B).getD i' 1 * g⁻¹ := by
      rw [← hf i, ← hf i', e]
    have h4 : (lst B).getD i 1 = (lst B).getD i' 1 :=
      mul_left_cancel (mul_right_cancel h3)
    exact Fin.ext (aux_ind_getD_inj hB i.isLt i'.isLt h4)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 finj), ?_, fun i => hf i⟩
  have hEl : ((lst B).map P.code).Nodup :=
    List.Nodup.map (fun a b hab => P.code_inj hn hab) hB.nodup
  have hgetK : ∀ i : ℕ, i < 16 →
      CFSG.KC.LQT.S.getK ((lst B).map P.code) i = P.code ((lst B).getD i 1) := by
    intro i hi
    have hi' : i < ((lst B).map P.code).length := by
      have := lst_length B
      simp only [List.length_map]
      omega
    have hi'' : i < (lst B).length := by have := lst_length B; omega
    rw [aux_ind_getK, List.getD_eq_getElem _ _ hi', List.getElem_map,
      List.getD_eq_getElem _ _ hi'']
  have hkey : ∀ i : Fin 16,
      CFSG.KC.LQT.M24.idxK (CFSG.KC.LQT.P.conj n (P.code g)
        (CFSG.KC.LQT.S.getK ((lst B).map P.code) i)) ((lst B).map P.code) = (f i : ℕ) := by
    intro i
    rw [hgetK i i.isLt, P.conj_code hn, ← hf i]
    apply idxK_of_getElem? hEl
    exact aux_ind_map_getElem? (f i).isLt
  unfold CFSG.KC.LQT.M24.indK
  rw [CFSG.KC.LQT.P.ofFn_eq]
  refine CFSG.KC.LQT.P.code_of_vals _ (fun i hi => ?_)
  have h1 := hkey ⟨i, hi⟩
  have h2 : CFSG.KC.LQT.P.vals (Equiv.ofBijective f (Finite.injective_iff_bijective.1 finj)) i
      = (f ⟨i, hi⟩ : ℕ) :=
    CFSG.KC.LQT.P.vals_fin _ ⟨i, hi⟩
  rw [h2]
  exact h1

theorem indK_unique {B : List (Perm (Fin n))} (hB : EFacts B) (g : Perm (Fin n))
    (τ τ' : Perm (Fin 16))
    (h : ∀ i : Fin 16, (lst B).getD (τ i) 1 = g * (lst B).getD i 1 * g⁻¹)
    (h' : ∀ i : Fin 16, (lst B).getD (τ' i) 1 = g * (lst B).getD i 1 * g⁻¹) : τ = τ' := by
  refine Equiv.ext fun i => Fin.ext ?_
  exact aux_ind_getD_inj hB (τ i).isLt (τ' i).isLt ((h i).trans (h' i).symm)

end CFSG.KC.LQT.M24Snd

end
