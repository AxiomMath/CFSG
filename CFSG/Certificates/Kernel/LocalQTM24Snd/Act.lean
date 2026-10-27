module

public import CFSG.Certificates.Kernel.LocalQTSimsSound
public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.Elt

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.KC.LQT CFSG.KC.LQT.Syl.CoreSnd

private theorem aux_act_getD_mem {n : ℕ} {B : List (Perm (Fin n))} (hB : EFacts B) (i : Fin 16) :
    (lst B).getD i 1 ∈ Subgroup.closure {b | b ∈ B} := by
  rw [mem_closure_iff_lst hB]
  have hi : i.val < (lst B).length := by rw [lst_length]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

private theorem aux_act_inj {n : ℕ} {B : List (Perm (Fin n))} (hB : EFacts B) :
    Function.Injective (fun i : Fin 16 =>
      (⟨(lst B).getD i 1, aux_act_getD_mem hB i⟩ : Subgroup.closure {b | b ∈ B})) := by
  intro i j hij
  have hi : i.val < (lst B).length := by rw [lst_length]; exact i.isLt
  have hj : j.val < (lst B).length := by rw [lst_length]; exact j.isLt
  have h1 : (lst B).getD i.val 1 = (lst B).getD j.val 1 := congrArg Subtype.val hij
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h1
  exact Fin.ext ((hB.nodup.getElem_inj_iff).1 h1)

private theorem aux_act_surj {n : ℕ} {B : List (Perm (Fin n))} (hB : EFacts B) :
    Function.Surjective (fun i : Fin 16 =>
      (⟨(lst B).getD i 1, aux_act_getD_mem hB i⟩ : Subgroup.closure {b | b ∈ B})) := by
  rintro ⟨y, hy⟩
  obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.1 ((mem_closure_iff_lst hB y).1 hy)
  have hk16 : k < 16 := by rw [lst_length] at hk; exact hk
  refine ⟨⟨k, hk16⟩, Subtype.ext ?_⟩
  show (lst B).getD k 1 = y
  rw [List.getD_eq_getElem _ _ hk, hky]

theorem exists_equiv {n : ℕ} {B : List (Perm (Fin n))} (hB : EFacts B) :
    ∃ e : Perm (Subgroup.closure {b | b ∈ B}) ≃* Perm (Fin 16),
      ∀ (p : Perm (Subgroup.closure {b | b ∈ B})) (i : Fin 16)
        (x : Subgroup.closure {b | b ∈ B}), (x : Perm (Fin n)) = (lst B).getD i 1 →
        (lst B).getD (e p i) 1 = ((p x : Subgroup.closure {b | b ∈ B}) : Perm (Fin n)) := by
  obtain ⟨ι, hι⟩ : ∃ ι : Fin 16 ≃ Subgroup.closure {b | b ∈ B},
      ∀ j : Fin 16, ((ι j : Subgroup.closure {b | b ∈ B}) : Perm (Fin n)) = (lst B).getD j 1 :=
    ⟨Equiv.ofBijective (fun i : Fin 16 =>
      (⟨(lst B).getD i 1, aux_act_getD_mem hB i⟩ : Subgroup.closure {b | b ∈ B}))
      ⟨aux_act_inj hB, aux_act_surj hB⟩, fun j => rfl⟩
  refine ⟨ι.symm.permCongrHom, ?_⟩
  intro p i x hx
  have hix : ι i = x := Subtype.ext (by rw [hι i, hx])
  have key : ι.symm.permCongrHom p i = ι.symm (p x) := by
    rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_symm, hix]
  rw [key, ← hι (ι.symm (p x)), Equiv.apply_symm_apply]

theorem range_eq_closure {G K : Type*} [Group G] [Group K] (nG : List G)
    (ρ : Subgroup.closure {g | g ∈ nG} →* K) :
    ρ.range = Subgroup.closure {t | ∃ g : G, ∃ hg : g ∈ nG,
      t = ρ ⟨g, Subgroup.subset_closure hg⟩} := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := {g | g ∈ nG}),
    MonoidHom.map_closure]
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, hy, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, Subgroup.subset_closure hg⟩, hg, rfl⟩

private theorem aux_act_pow_mem {G : Type*} [Group G] (T : List G) (P : Set G)
    (hP : ∀ x ∈ P, ∀ t ∈ T, x * t ∈ P) {y : G} (hy : y ∈ T) (m : ℕ) :
    ∀ x ∈ P, x * y ^ m ∈ P := by
  induction m with
  | zero => intro x hx; simpa using hx
  | succ m ih =>
    intro x hx
    rw [pow_succ, ← mul_assoc]
    exact hP _ (ih x hx) y hy

theorem closure_le_of_closed {G : Type*} [Group G] [Finite G] (T : List G) (P : Set G)
    (h1 : (1 : G) ∈ P) (hP : ∀ x ∈ P, ∀ t ∈ T, x * t ∈ P) :
    ∀ σ ∈ Subgroup.closure {t | t ∈ T}, σ ∈ P := by
  intro σ hσ
  induction hσ using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right x hx y hy ih =>
    have hyT : y ∈ T := hy
    exact hP x ih y hyT
  | mul_inv_cancel x hx y hy ih =>
    have hyT : y ∈ T := hy
    have e : y⁻¹ = y ^ (orderOf y - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos y),
        pow_orderOf_eq_one]
    rw [e]
    exact aux_act_pow_mem T P hP hyT _ x ih

theorem card_closure_of_grpS {m : ℕ} (hm : m ≤ 32) {C : List CFSG.KC.LQT.L.Lvl}
    (hok : CFSG.KC.LQT.L.chainOK m C = true) (hI : CFSG.KC.LQT.L.chainInj m C = true)
    (Tl : List (Perm (Fin m))) {W : List (List (List ℕ))} {d : ℕ}
    (h : CFSG.KC.LQT.PH.grpS m C (CFSG.KC.LQT.L.chainF C) (Tl.map CFSG.KC.LQT.P.code) W d =
      true) :
    Nat.card (Subgroup.closure {t | t ∈ Tl}) = CFSG.KC.LQT.L.chainF C := by
  obtain ⟨h1, -⟩ := CFSG.KC.LQT.CM.grpS_sound hm hok hI Tl h
  rw [← CFSG.KC.LQT.CM.card_inC hm hok hI]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => (h1 σ).symm)

end CFSG.KC.LQT.M24Snd

end
