module

public import Certificates.Data.AE7OddGen
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Brg

public section

namespace CFSG.KC.AE7OddGenK

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  Certificates.AE117 Certificates.AE7OddGen

@[expose] def FlagP (L : List (Wr 7)) (g z : Wr 7) : Prop :=
  (∀ b ∈ L, b * g = g * b ∨ b * z = z * b) ∧
    (∀ b ∈ L, wsum b = 0 ∧ Equiv.Perm.sign b.perm = 1 ∧ b ^ 15 = 1) ∧
    (∀ j k : Fin 7, j ≠ k → ∃ w ∈ W₁, evalG L w = ofVec (indL [j, k])) ∧
    (∀ a b c : Fin 7, a ≠ b → b ≠ c → a ≠ c →
      ∃ w ∈ W₂, (evalG L w).perm = Equiv.swap a b * Equiv.swap b c)

@[expose] def flagB (L : List (Wr 7)) (g z : Wr 7) : Bool :=
  commOK L g z && aeOK L && pairsOK L && cyclesOK L

theorem eqWr_iff {x y : Wr 7} : eqWr x y = true ↔ x = y := by
  unfold eqWr
  rw [List.all_eq_true]
  constructor
  · intro h
    refine Wr.ext (funext fun i => ?_) (Equiv.ext fun i => ?_)
    · have := h i (List.mem_finRange i)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    · have := h i (List.mem_finRange i)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
  · rintro rfl i _
    simp

theorem keyV_inj {x y : Wr 7} (h : keyV x = keyV y) : x.vec = y.vec :=
  funext fun i => List.map_inj_left.mp h i (List.mem_finRange i)

theorem keyP_inj {σ τ : Equiv.Perm (Fin 7)} (h : keyP σ = keyP τ) : σ = τ :=
  Equiv.ext fun i => List.map_inj_left.mp h i (List.mem_finRange i)

theorem flagP_of_flagB {L : List (Wr 7)} {g z : Wr 7} (h : flagB L g z = true) : FlagP L g z := by
  simp only [flagB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    unfold commOK at h1
    rw [List.all_eq_true] at h1
    simpa only [Bool.or_eq_true, eqWr_iff] using h1 b hb
  · intro b hb
    unfold aeOK at h2
    rw [List.all_eq_true] at h2
    simpa only [Bool.and_eq_true, decide_eq_true_eq, eqWr_iff, and_assoc] using h2 b hb
  · intro j k hjk
    unfold pairsOK at h3
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h3
    rcases h3 j (List.mem_finRange j) k (List.mem_finRange k) with h | h
    · exact absurd h hjk
    · rw [List.contains_iff_mem, List.mem_map] at h
      obtain ⟨w, hw, hwe⟩ := h
      simp only [Prod.mk.injEq] at hwe
      exact ⟨w, hw, Wr.ext (keyV_inj hwe.2) (keyP_inj hwe.1)⟩
  · intro a b c hab hbc hac
    unfold cyclesOK at h4
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h4
    rcases h4 a (List.mem_finRange a) b (List.mem_finRange b) c (List.mem_finRange c) with
      (((h | h) | h) | h)
    · exact absurd h hab
    · exact absurd h hbc
    · exact absurd h hac
    · rw [List.contains_iff_mem, List.mem_map] at h
      obtain ⟨w, hw, hwe⟩ := h
      exact ⟨w, hw, keyP_inj hwe⟩

theorem flagB_of_flagP {L : List (Wr 7)} {g z : Wr 7} (h : FlagP L g z) : flagB L g z = true := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [flagB, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · unfold commOK
    rw [List.all_eq_true]
    intro b hb
    simpa only [Bool.or_eq_true, eqWr_iff] using h1 b hb
  · unfold aeOK
    rw [List.all_eq_true]
    intro b hb
    simpa only [Bool.and_eq_true, decide_eq_true_eq, eqWr_iff, and_assoc] using h2 b hb
  · unfold pairsOK
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    intro j _ k _
    by_cases hjk : j = k
    · exact Or.inl hjk
    · right
      obtain ⟨w, hw, hwe⟩ := h3 j k hjk
      rw [List.contains_iff_mem, List.mem_map]
      exact ⟨w, hw, by rw [hwe]; rfl⟩
  · unfold cyclesOK
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    intro a _ b _ c _
    by_cases hab : a = b
    · exact Or.inl (Or.inl (Or.inl hab))
    by_cases hbc : b = c
    · exact Or.inl (Or.inl (Or.inr hbc))
    by_cases hac : a = c
    · exact Or.inl (Or.inr hac)
    right
    obtain ⟨w, hw, hwe⟩ := h4 a b c hab hbc hac
    rw [List.contains_iff_mem, List.mem_map]
    exact ⟨w, hw, by rw [hwe]⟩

@[expose] def cj (τ : Equiv.Perm (Fin 7)) : Wr 7 →* Wr 7 := (MulAut.conj (ofPerm τ)).toMonoidHom

theorem cj_mk (τ : Equiv.Perm (Fin 7)) (v : Fin 7 → ZMod 2) (σ : Equiv.Perm (Fin 7)) :
    cj τ ⟨v, σ⟩ = ⟨fun i => v (τ.symm i), τ * σ * τ⁻¹⟩ := by
  apply Wr.ext
  · funext i
    change (0 + v (τ.symm i)) + 0 = v (τ.symm i)
    simp
  · rfl

theorem cj_perm (τ : Equiv.Perm (Fin 7)) (x : Wr 7) : (cj τ x).perm = τ * x.perm * τ⁻¹ := rfl

theorem cj_vec (τ : Equiv.Perm (Fin 7)) (x : Wr 7) (i : Fin 7) : (cj τ x).vec i = x.vec (τ.symm i) := by
  rw [cj_mk τ x.vec x.perm]

theorem indL_map (τ : Equiv.Perm (Fin 7)) (l : List (Fin 7)) :
    (fun i => indL l (τ.symm i)) = indL (l.map τ) := by
  funext i
  have h : i ∈ l.map τ ↔ τ.symm i ∈ l := by
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hi
      exact ⟨_, hi, by simp⟩
  simp only [indL, h]

theorem conj_swap3 (τ : Equiv.Perm (Fin 7)) (a b c : Fin 7) :
    τ * (Equiv.swap a b * Equiv.swap b c) * τ⁻¹ = Equiv.swap (τ a) (τ b) * Equiv.swap (τ b) (τ c) := by
  rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]
  group

theorem conj_formPerm3 (τ : Equiv.Perm (Fin 7)) (a b c : Fin 7) :
    τ * List.formPerm [a, b, c] * τ⁻¹ = List.formPerm [τ a, τ b, τ c] := by
  simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
  exact conj_swap3 τ a b c

theorem cj_zero (τ σ : Equiv.Perm (Fin 7)) :
    cj τ ⟨0, σ⟩ = ⟨0, τ * σ * τ⁻¹⟩ := by
  rw [cj_mk]
  rfl

theorem cj_indL (τ σ : Equiv.Perm (Fin 7)) (l : List (Fin 7)) :
    cj τ ⟨indL l, σ⟩ = ⟨indL (l.map τ), τ * σ * τ⁻¹⟩ := by
  rw [cj_mk, indL_map]

theorem cj_ofVec (τ : Equiv.Perm (Fin 7)) (l : List (Fin 7)) :
    cj τ (ofVec (indL l)) = ofVec (indL (l.map τ)) := by
  unfold ofVec
  rw [cj_indL, mul_one, mul_inv_cancel]

theorem Lrel_perm (τ : Equiv.Perm (Fin 7)) : Lrel ⇑τ = (Lrel id).map (cj τ) := by
  simp only [Lrel, List.map_cons, List.map_nil, cj_zero, cj_indL, conj_formPerm3, id]

theorem wsum_cj (τ : Equiv.Perm (Fin 7)) (x : Wr 7) : wsum (cj τ x) = wsum x := by
  unfold wsum
  simp only [cj_vec]
  exact Equiv.sum_comp τ.symm x.vec

theorem sign_conj (τ σ : Equiv.Perm (Fin 7)) :
    Equiv.Perm.sign (τ * σ * τ⁻¹) = Equiv.Perm.sign σ := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

theorem flagP_map (τ : Equiv.Perm (Fin 7)) {L : List (Wr 7)} {g z : Wr 7} (h : FlagP L g z) :
    FlagP (L.map (cj τ)) (cj τ g) (cj τ z) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hb'
    rcases h1 b hb with h | h
    · left
      rw [← map_mul, ← map_mul, h]
    · right
      rw [← map_mul, ← map_mul, h]
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hb'
    obtain ⟨hs, hsg, h15⟩ := h2 b hb
    refine ⟨by rw [wsum_cj, hs], by rw [cj_perm, sign_conj, hsg], by rw [← map_pow, h15, map_one]⟩
  · intro j k hjk
    obtain ⟨w, hw, hwe⟩ := h3 (τ.symm j) (τ.symm k) (fun h => hjk (τ.symm.injective h))
    refine ⟨w, hw, ?_⟩
    rw [← TL4.Mdl117.evalG_map, hwe, cj_ofVec]
    simp
  · intro a b c hab hbc hac
    obtain ⟨w, hw, hwe⟩ := h4 (τ.symm a) (τ.symm b) (τ.symm c)
      (fun h => hab (τ.symm.injective h)) (fun h => hbc (τ.symm.injective h))
      (fun h => hac (τ.symm.injective h))
    refine ⟨w, hw, ?_⟩
    rw [← TL4.Mdl117.evalG_map, cj_perm, hwe, conj_swap3]
    simp

theorem getD_inj {l : List (Fin 7)} (hl : l.length = 7) (hnd : l.Nodup) :
    Function.Injective fun i : Fin 7 => l.getD i.val i := by
  intro i j h
  have hi : i.val < l.length := by
    rw [hl]
    exact i.isLt
  have hj : j.val < l.length := by
    rw [hl]
    exact j.isLt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some] at h
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h)

theorem flag_perm {α : Finset (Fin 7)} (hα : α.card = 4) {p q : Fin 7} (hp : p ∉ α) (hq : q ∉ α)
    (hpq : p ≠ q) :
    ∃ τ : Equiv.Perm (Fin 7), ⇑τ = flagFun α p q ∧ τ 4 = p ∧ τ 5 = q ∧
      indL [τ 0, τ 1, τ 2, τ 3] = indF α := by
  set R := (List.finRange 7).filter fun i => decide (i ∉ α ∧ i ≠ p ∧ i ≠ q) with hR
  have hlen : (α.sort (· ≤ ·)).length = 4 := by rw [Finset.length_sort, hα]
  have hsα : ∀ a, a ∈ α.sort (· ≤ ·) ↔ a ∈ α := fun a => Finset.mem_sort _
  have hmR : ∀ a, a ∈ R ↔ a ∉ α ∧ a ≠ p ∧ a ≠ q := by
    intro a
    simp [hR]
  have hnd : (flagList α p q).Nodup := by
    unfold flagList
    rw [← hR, List.nodup_append, List.nodup_append]
    refine ⟨⟨Finset.sort_nodup _ _, by simp [hpq], ?_⟩, (List.nodup_finRange 7).filter _, ?_⟩
    · intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rw [hsα] at ha
      rcases hb with rfl | rfl
      · exact fun h => hp (h ▸ ha)
      · exact fun h => hq (h ▸ ha)
    · intro a ha b hb
      rw [hmR] at hb
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hsα] at ha
      rintro rfl
      rcases ha with ha | rfl | rfl
      · exact hb.1 ha
      · exact hb.2.1 rfl
      · exact hb.2.2 rfl
  have hmem : ∀ i, i ∈ flagList α p q := by
    intro i
    unfold flagList
    rw [← hR]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hsα, hmR]
    tauto
  have hl7 : (flagList α p q).length = 7 := by
    rw [← List.toFinset_card_of_nodup hnd,
      Finset.eq_univ_of_forall fun i => List.mem_toFinset.2 (hmem i)]
    simp
  have hinj := getD_inj hl7 hnd
  let τ : Equiv.Perm (Fin 7) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
  have hτ : ⇑τ = flagFun α p q := rfl
  generalize hS : α.sort (· ≤ ·) = S at hlen hsα
  obtain ⟨a0, a1, a2, a3, rfl⟩ : ∃ a0 a1 a2 a3 : Fin 7, S = [a0, a1, a2, a3] := by
    match S, hlen with
    | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩
  have hfl : flagList α p q = [a0, a1, a2, a3, p, q] ++ R := by
    unfold flagList
    rw [hS, ← hR]
    rfl
  have hval : ∀ i : Fin 7, τ i = (flagList α p q).getD i.val i := fun _ => rfl
  refine ⟨τ, hτ, ?_, ?_, ?_⟩
  · rw [hval, hfl]
    rfl
  · rw [hval, hfl]
    rfl
  · have h0 : [τ 0, τ 1, τ 2, τ 3] = [a0, a1, a2, a3] := by
      simp only [hval, hfl]
      rfl
    rw [h0]
    funext i
    simp only [indL, indF, hsα]

theorem oddGenProp_of_base
    (hb : flagB (Lrel id) (ofVec (indL [4, 5])) (ofVec (indL [0, 1, 2, 3])) = true) :
    oddGenProp := by
  intro α hα p q hp hq hpq
  obtain ⟨τ, hτ, h4, h5, hz⟩ := flag_perm (Finset.mem_powersetCard.1 hα).2 hp hq hpq
  have hP := flagP_map τ (flagP_of_flagB hb)
  rw [cj_ofVec, cj_ofVec] at hP
  simp only [List.map_cons, List.map_nil, h4, h5] at hP
  rw [hz, ← Lrel_perm, hτ] at hP
  exact flagB_of_flagP hP

end CFSG.KC.AE7OddGenK

end
