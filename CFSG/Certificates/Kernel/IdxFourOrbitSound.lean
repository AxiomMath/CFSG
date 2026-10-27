
module

public import Certificates.Data.Kernel.IdxFourOrbitK
public import CFSG.Certificates.Kernel.IdxFourChainSound

public section

namespace CFSG.KC.IF4O

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU

theorem allLt_iff (n : Nat) (w : List Nat) : allLt n w = true ↔ ∀ e ∈ w, e < n := by
  induction w with
  | nil => simp [allLt]
  | cons a w ih =>
    change (Nat.blt a n && allLt n w) = true ↔ _
    rw [Bool.and_eq_true, Nat.blt_eq, ih, List.forall_mem_cons]

theorem fld_lt (P c : Nat) : fld P c < 4096 :=
  Nat.lt_of_le_of_lt (Nat.and_le_right) (by norm_num)

section
variable {SP VT PS n : Nat} {L : List Nat} {P : Nat → Bool}

theorem entOK_spec {j : Nat} {e : List Nat} (h : entOK SP VT PS n L P j e = true) :
    fld PS (fld VT j) = j ∧ fld VT j ∉ L ∧
      ((e.getD 1 0 < n ∧ e.getD 0 0 < j ∧
          ap12 (look SP (e.getD 1 0)) (fld VT (e.getD 0 0)) = fld VT j) ∨
        ((∀ x ∈ e.drop 2, x < n) ∧
          (P (fld VT j) = true ∨ P (fld VT j ^^^ apW SP (e.drop 2) (fld VT j)) = true))) := by
  unfold entOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true', nthD_eq, dropN_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun hm => by simp [(memN_iff _ _).2 hm] at h2, ?_⟩
  cases hb : Nat.blt (e.getD 1 0) n
  · rw [hb] at h3
    simp only [cond_false, Bool.and_eq_true, allLt_iff, Bool.or_eq_true] at h3
    exact Or.inr ⟨h3.1, h3.2⟩
  · rw [hb] at h3
    simp only [cond_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h3
    exact Or.inl ⟨by simpa using hb, h3.1, h3.2⟩

theorem entsOK_spec : ∀ {es : List (List Nat)} {j0 : Nat}, entsOK SP VT PS n L P es j0 = true →
    ∀ k < es.length, entOK SP VT PS n L P (j0 + k) (es.getD k []) = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | e :: es, j0, h, k, hk => by
    change (entOK SP VT PS n L P j0 e && entsOK SP VT PS n L P es (Nat.succ j0)) = true at h
    rw [Bool.and_eq_true] at h
    cases k with
    | zero => exact h.1
    | succ k =>
      have := entsOK_spec h.2 k (by simpa using hk)
      rwa [Nat.succ_add, ← Nat.add_succ] at this

theorem entOK_of_blk {E : List (List Nat)} {K : Nat} (hK : E.length ≤ 128 * K)
    (h : ∀ c < K, blkOK SP VT PS n L P E c = true) :
    ∀ j < E.length, entOK SP VT PS n L P j (E.getD j []) = true := by
  intro j hj
  have hc : j / 128 < K := by omega
  have hb := h (j / 128) hc
  unfold blkOK at hb
  rw [takeN_eq, dropN_eq] at hb
  have hk : j % 128 < (List.take 128 (List.drop (Nat.mul 128 (j / 128)) E)).length := by
    simp only [List.length_take, List.length_drop, Nat.mul_eq]
    omega
  have := entsOK_spec hb (j % 128) hk
  have hj' : Nat.mul 128 (j / 128) + j % 128 = j := by
    rw [Nat.mul_eq]
    exact Nat.div_add_mod j 128
  rw [hj'] at this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop] at this
  rw [if_pos (Nat.mod_lt j (by norm_num)), hj'] at this
  simpa only [List.getD_eq_getElem?_getD] using this

variable {U : Submodule (ZMod 2) V12}

theorem apW_lt {c : Nat} (hc : c < 4096) : ∀ w : List Nat, apW SP w c < 4096
  | [] => hc
  | _ :: _ => ap12_lt _ _

theorem apW_mem (hU : ∀ g < n, ∀ x, vecOf x ∈ U → vecOf (ap12 (look SP g) x) ∈ U) {c : Nat}
    (hc : vecOf c ∈ U) : ∀ w : List Nat, (∀ e ∈ w, e < n) → vecOf (apW SP w c) ∈ U
  | [], _ => hc
  | e :: w, hw => hU e (hw e List.mem_cons_self) _
      (apW_mem hU hc w fun x hx => hw x (List.mem_cons_of_mem e hx))

theorem exists_P_of_mem {E : List (List Nat)}
    (hE : ∀ j < E.length, entOK SP VT PS n L P j (E.getD j []) = true)
    (hU : ∀ g < n, ∀ x, vecOf x ∈ U → vecOf (ap12 (look SP g) x) ∈ U)
    (hU' : ∀ g < n, ∀ x, vecOf (ap12 (look SP g) x) ∈ U → vecOf x ∈ U) :
    ∀ j < E.length, vecOf (fld VT j) ∈ U → ∃ w < 4096, P w = true ∧ vecOf w ∈ U := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hjU
    obtain ⟨-, -, hr⟩ := entOK_spec (hE j hj)
    rcases hr with ⟨hg, hp, heq⟩ | ⟨hw, hP | hP⟩
    · refine ih _ hp (by omega) (hU' _ hg _ ?_)
      rwa [heq]
    · exact ⟨_, fld_lt _ _, hP, hjU⟩
    · refine ⟨_, Nat.xor_lt_two_pow (n := 12) (fld_lt _ _) (apW_lt (fld_lt _ _) _), hP, ?_⟩
      rw [vecOf_xor]
      exact U.add_mem hjU (apW_mem hU hjU _ hw)

theorem exists_index {N : Nat} (hE : ∀ j < N, fld PS (fld VT j) = j ∧ fld VT j ∉ L)
    (hL : L.Nodup) (hL4 : ∀ x ∈ L, x < 4096) (hN : N + L.length = 4096) :
    ∀ v < 4096, v ∉ L → ∃ j < N, fld VT j = v := by
  classical
  let S := (Finset.range N).image (fld VT)
  let T := Finset.range 4096 \ L.toFinset
  have hinj : Set.InjOn (fld VT) (Finset.range N : Set Nat) := by
    intro a ha b hb hab
    have ha' := (hE a (Finset.mem_range.1 ha)).1
    have hb' := (hE b (Finset.mem_range.1 hb)).1
    rw [← ha', ← hb', hab]
  have hS : S.card = N := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : S ⊆ T := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_sdiff.2 ⟨Finset.mem_range.2 (fld_lt _ _),
      fun h => (hE j (Finset.mem_range.1 hj)).2 (List.mem_toFinset.1 h)⟩
  have hT : T.card = N := by
    have hLs : L.toFinset ⊆ Finset.range 4096 := fun x hx =>
      Finset.mem_range.2 (hL4 x (List.mem_toFinset.1 hx))
    rw [Finset.card_sdiff_of_subset hLs, Finset.card_range, List.toFinset_card_of_nodup hL]
    omega
  have heq : S = T := Finset.eq_of_subset_of_card_le hsub (by rw [hS, hT])
  intro v hv hvL
  have : v ∈ S := heq ▸ Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hv, by simpa using hvL⟩
  obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 this
  exact ⟨j, Finset.mem_range.1 hj, hjv⟩

theorem exists_P_of_blk {E : List (List Nat)} {K N : Nat}
    (h : ∀ c < K, blkOK SP VT PS n L P E c = true) (hcnt : cntOK E N = true) (hK : N ≤ 128 * K)
    (hL : L.Nodup) (hL4 : ∀ x ∈ L, x < 4096) (hN : N + L.length = 4096)
    (hU : ∀ g < n, ∀ x, vecOf x ∈ U → vecOf (ap12 (look SP g) x) ∈ U)
    (hU' : ∀ g < n, ∀ x, vecOf (ap12 (look SP g) x) ∈ U → vecOf x ∈ U)
    {v : Nat} (hv : v < 4096) (hvL : v ∉ L) (hvU : vecOf v ∈ U) :
    ∃ w < 4096, P w = true ∧ vecOf w ∈ U := by
  have hlen : E.length = N := by
    unfold cntOK at hcnt
    rwa [Nat.beq_eq, lenN_eq] at hcnt
  subst hlen
  have hE := entOK_of_blk hK h
  obtain ⟨j, hj, rfl⟩ := exists_index (fun j hj => ⟨(entOK_spec (hE j hj)).1,
    (entOK_spec (hE j hj)).2.1⟩) hL hL4 hN v hv hvL
  exact exists_P_of_mem hE hU hU' j hj hvU

end

end CFSG.KC.IF4O

end
