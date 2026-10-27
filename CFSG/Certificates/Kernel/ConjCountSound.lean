module

public import Certificates.Data.Kernel.ConjCountL
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.KC.ConjCount

open CFSG.QuasithinUnique.K1.SporadicPerm

section Group

variable {G : Type} [Group G] [Finite G]

theorem no_orderOf_fifteen {H : Subgroup G} {m : ℕ} (hH : Nat.card H = 5 * m) (hm : ¬ 5 ∣ m)
    {t : G} (htH : t ∈ H) (ht : orderOf t = 5) (gs : List G) (hgs : ∀ g ∈ gs, g ∈ H)
    (hd : (gs.map fun g => g * t * g⁻¹).Nodup) (hlen : Nat.card H < 15 * gs.length) :
    ∀ z ∈ H, orderOf z ≠ 15 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro z hz hz15
  set T : H := ⟨t, htH⟩ with hTdef
  set Z : H := ⟨z, hz⟩ with hZdef
  have hT5 : orderOf T = 5 := by rw [← Subgroup.orderOf_coe]; exact ht
  have hZ15 : orderOf Z = 15 := by rw [← Subgroup.orderOf_coe]; exact hz15
  set C := MulAction.stabilizer (ConjAct H) T with hC
  have hmemC : ∀ x : H, x * T * x⁻¹ = T → ConjAct.toConjAct x ∈ C := by
    intro x hx
    rw [hC, MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul]
    exact hx
  have : Finite (ConjAct H) := Finite.of_equiv H ConjAct.toConjAct.toEquiv
  have hcard : Nat.card C * Nat.card (MulAction.orbit (ConjAct H) T) = Nat.card H := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, Subgroup.card_mul_index]
    exact Nat.card_congr (ConjAct.toConjAct (G := H)).toEquiv.symm
  have hL : gs.length ≤ Nat.card (MulAction.orbit (ConjAct H) T) := by
    classical
    let f : G → G := fun g => g * t * g⁻¹
    have hsub : ((gs.map f).toFinset : Set G) ⊆
        (H.subtype '' (MulAction.orbit (ConjAct H) T) : Set G) := by
      intro y hy
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      refine ⟨ConjAct.toConjAct (⟨g, hgs g hg⟩ : H) • T, MulAction.mem_orbit _ _, ?_⟩
      rw [ConjAct.toConjAct_smul]
      rfl
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hd, List.length_map,
      Set.ncard_image_of_injective _ H.subtype_injective, ← Nat.card_coe_set_eq] at h1
    exact h1
  have hC15 : Nat.card C < 15 := by
    have hpos : 0 < gs.length := by
      rcases Nat.eq_zero_or_pos gs.length with h | h
      · rw [h] at hlen; omega
      · exact h
    by_contra hge
    have : 15 * gs.length ≤ Nat.card H := by
      rw [← hcard]
      exact Nat.mul_le_mul (not_lt.mp hge) hL
    omega
  have hidx : ∀ P : Subgroup H, Nat.card P = 5 → ¬ 5 ∣ P.index := by
    intro P hP h5
    have h := P.card_mul_index
    rw [hP, hH] at h
    have h' : P.index = m := by omega
    exact hm (h' ▸ h5)
  have hp5 : ∀ P : Subgroup H, Nat.card P = 5 → IsPGroup 5 P := fun P hP =>
    IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  set a := Z ^ 3 with ha
  have ha5 : orderOf a = 5 := by
    rw [ha, orderOf_pow_of_dvd (by norm_num) (by rw [hZ15]; norm_num), hZ15]
  have hPc : Nat.card (Subgroup.zpowers T) = 5 := by rw [Nat.card_zpowers, hT5]
  have hQc : Nat.card (Subgroup.zpowers a) = 5 := by rw [Nat.card_zpowers, ha5]
  let PS : Sylow 5 H := (hp5 _ hPc).toSylow (hidx _ hPc)
  let QS : Sylow 5 H := (hp5 _ hQc).toSylow (hidx _ hQc)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H QS PS
  have hPeq : Subgroup.zpowers T = (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • QS : Sylow 5 H) : Subgroup H) = (PS : Subgroup H) := by rw [hg]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1.symm
  rw [MonoidHom.map_zpowers] at hPeq
  set y := g * Z * g⁻¹ with hy
  have hy3 : (MulAut.conj g).toMonoidHom a = y ^ 3 := by
    rw [hy, conj_pow, ha]
    rfl
  rw [hy3] at hPeq
  have hTy : T ∈ Subgroup.zpowers (y ^ 3) := hPeq ▸ Subgroup.mem_zpowers T
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hTy
  have hcomm : y ^ 5 * T * (y ^ 5)⁻¹ = T := by
    rw [← hk]
    have hc : Commute (y ^ 5) ((y ^ 3) ^ k) := ((Commute.refl y).pow_pow 5 3).zpow_right k
    rw [hc.eq, mul_inv_cancel_right]
  have hy5 : orderOf (y ^ 5) = 3 := by
    rw [hy, conj_pow]
    have h := MulEquiv.orderOf_eq (MulAut.conj g) (Z ^ 5)
    rw [MulAut.conj_apply] at h
    rw [h, orderOf_pow_of_dvd (by norm_num) (by rw [hZ15]; norm_num), hZ15]
  have h3 : 3 ∣ Nat.card C := by
    have h := Subgroup.orderOf_dvd_natCard C (hmemC _ hcomm)
    rwa [MulEquiv.orderOf_eq, hy5] at h
  have h5 : 5 ∣ Nat.card C := by
    have h := Subgroup.orderOf_dvd_natCard C (hmemC T (by group))
    rwa [MulEquiv.orderOf_eq, hT5] at h
  have h15 : 15 ∣ Nat.card C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3 h5
  have hpos : 0 < Nat.card C := Nat.card_pos
  have := Nat.le_of_dvd hpos h15
  omega

end Group

section Tables

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

@[expose] def evalL (E : List Γ) (w : List ℕ) : Γ := (w.map fun l => E.getD l 1).prod

theorem evalL_append (E : List Γ) (u v : List ℕ) : evalL E (u ++ v) = evalL E u * evalL E v := by
  simp [evalL, List.prod_append]

theorem evalL_mem {H : Subgroup Γ} {E : List Γ} (hE : ∀ x ∈ E, x ∈ H) (w : List ℕ) :
    evalL E w ∈ H := by
  induction w with
  | nil => simp [evalL, H.one_mem]
  | cons l w ih =>
    have h1 : E.getD l 1 ∈ H := by
      rcases Nat.lt_or_ge l E.length with hl | hl
      · rw [List.getD_eq_getElem _ _ hl]; exact hE _ (List.getElem_mem hl)
      · rw [List.getD_eq_default _ _ hl]; exact H.one_mem
    have : evalL E (l :: w) = E.getD l 1 * evalL E w := by simp [evalL]
    rw [this]
    exact H.mul_mem h1 ih

theorem tab_length (g : Γ) : (tab n g).length = n := by simp [tab]

theorem tab_getD_act (g : Γ) (p : ℕ) : (tab n g).getD p 0 = act n g p := rfl

theorem tab_ext {x : List ℕ} {g : Γ} (hx : x.length = n) (h : ∀ p < n, x.getD p 0 = act n g p) :
    x = tab n g := by
  apply List.ext_getElem (by rw [hx, tab_length])
  intro p h1 h2
  have hp : p < n := hx ▸ h1
  have e1 := h p hp
  rw [List.getD_eq_getElem _ _ h1] at e1
  rw [e1, ← tab_getD_act, List.getD_eq_getElem _ _ h2]

theorem imgW_eq {E : List Γ} {U : List (List ℕ)} (hU : U = E.map (tab n)) :
    ∀ w : List ℕ, (∀ l ∈ w, l < E.length) → ∀ p < n, imgW U w p = act n (evalL E w) p
  | [], _, p, hp => by simp [imgW, evalL, act_one hp]
  | l :: w, hw, p, hp => by
    have hl : l < E.length := hw l List.mem_cons_self
    have ih := imgW_eq hU w (fun x hx => hw x (List.mem_cons_of_mem _ hx)) p hp
    have e1 : imgW U (l :: w) p = (U.getD l []).getD (imgW U w p) 0 := rfl
    have e2 : evalL E (l :: w) = E.getD l 1 * evalL E w := by simp [evalL]
    have e3 : U.getD l [] = tab n (E.getD l 1) := by
      rw [hU, List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl]
      simp
    rw [e1, e2, ih, e3, tab_getD_act, act_mul _ _ hp]

theorem tabW_eq {E : List Γ} {U : List (List ℕ)} (hU : U = E.map (tab n)) (w : List ℕ)
    (hw : ∀ l ∈ w, l < E.length) : tabW U n w = tab n (evalL E w) := by
  refine tab_ext (by simp [tabW]) fun p hp => ?_
  rw [← imgW_eq hU w hw p hp]
  simp [tabW, List.getD_eq_getElem?_getD, hp]

theorem tab_one_eq : tab n (1 : Γ) = List.range n :=
  (tab_ext (n := n) (by simp) fun p hp => by
    rw [act_one hp, List.getD_eq_getElem _ _ (by simpa using hp)]; simp).symm

theorem eq_of_tab [FaithfulSMul Γ (Fin n)] {x y : Γ} (h : tab n x = tab n y) : x = y := by
  apply eq_of_smul_eq_smul (α := Fin n)
  intro i
  apply Fin.ext
  rw [← act_eq, ← act_eq, ← tab_getD_act, ← tab_getD_act, h]

theorem inv_of_invOK {g : Γ} {y : List ℕ} (h : invOK n (tab n g) y = true) : y = tab n g⁻¹ := by
  simp only [invOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨hlen, hlt⟩, hinv⟩ := h
  refine tab_ext hlen fun p hp => ?_
  have hq : y.getD p 0 < n := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hlt _ (List.getElem_mem _)
  have e := hinv p hp
  rw [tab_getD_act] at e
  calc y.getD p 0 = act n (g⁻¹ * g) (y.getD p 0) := by rw [inv_mul_cancel, act_one hq]
    _ = act n g⁻¹ (act n g (y.getD p 0)) := act_mul _ _ hq
    _ = act n g⁻¹ p := by rw [e]

end Tables

end CFSG.KC.ConjCount
