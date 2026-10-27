module

public import CFSG.ClassicalInvolution.Q3.Q3VChainNodes

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Chain

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs

local notation "F3" => GaloisField 3 1

variable {m : ℕ} {G : Type} [Group G]

section Positions

variable [NeZero m]

@[expose] def posB (c : Fin (m + 1)) : Fin m :=
  ⟨c.val - 1, by have := c.isLt; have := NeZero.pos m; omega⟩

@[expose] def posA (c : Fin (m + 1)) : Fin m :=
  if c.val = 0 then ⟨m - 1, by have := NeZero.pos m; omega⟩ else posB c

@[expose] def plane0 : Fin m := ⟨0, NeZero.pos m⟩

@[expose] def planeL : Fin m := ⟨m - 1, by have := NeZero.pos m; omega⟩

theorem posB_val (c : Fin (m + 1)) : (posB c).val = c.val - 1 := rfl

theorem posA_val_zero {c : Fin (m + 1)} (h : c.val = 0) : (posA c).val = m - 1 := by
  unfold posA
  rw [ite_eq_left h]

theorem posA_val {c : Fin (m + 1)} (h : c.val ≠ 0) : (posA c).val = c.val - 1 := by
  unfold posA
  rw [ite_eq_right h, posB_val]

theorem plane0_val : (plane0 : Fin m).val = 0 := rfl

theorem planeL_val : (planeL : Fin m).val = m - 1 := rfl

end Positions

theorem val_succAbove_of_lt {n : ℕ} {p : Fin (n + 1)} {i : Fin n} (h : i.val < p.val) :
    (p.succAbove i).val = i.val := by
  rw [Fin.succAbove_of_castSucc_lt p i (by rw [Fin.lt_def]; simpa using h), Fin.val_castSucc]

theorem val_succAbove_of_le {n : ℕ} {p : Fin (n + 1)} {i : Fin n} (h : p.val ≤ i.val) :
    (p.succAbove i).val = i.val + 1 := by
  rw [Fin.succAbove_of_le_castSucc p i (by rw [Fin.le_def]; simpa using h), Fin.val_succ]

theorem succAbove_zero_posB [NeZero m] {c : Fin (m + 1)} (hc : c ≠ 0) :
    (0 : Fin (m + 1)).succAbove (posB c) = c := by
  have h0 := val_ne_zero_of_ne_zero hc
  apply Fin.ext
  rw [val_succAbove_of_le (by rw [Fin.val_zero]; omega), posB_val]
  omega

theorem succAbove_val_one_posB [NeZero m] {l : Fin (m + 1)} (hl : l.val = 1) {c : Fin (m + 1)}
    (hc : c ≠ l) : l.succAbove (posB c) = c := by
  have hc1 : c.val ≠ 1 := fun h => hc (Fin.ext (by rw [hl]; exact h))
  apply Fin.ext
  by_cases h : c.val = 0
  · rw [val_succAbove_of_lt (by rw [posB_val, hl]; omega), posB_val]
    omega
  · rw [val_succAbove_of_le (by rw [posB_val, hl]; omega), posB_val]
    omega

theorem exists_nodeData [NeZero m] (hm : 4 ≤ m) {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (hnonab : ∀ M ∈ Ω, ¬ Commutes M M) {K : Fin (m + 1) → Subgroup G}
    (hK : IsMemberFrame Ω K) {Θ : Fin (m + 1) → (StatedSp m F3 →* G)}
    (hΘ : ∀ l, IsLabLift m Ω K l (Θ l)) :
    ∃ (A : StatedSp m F3 →* G) (pA pB : Fin (m + 1) → Fin m), NodeData Ω K A (Θ 0) pA pB := by
  obtain ⟨l1, hl1⟩ : ∃ l1 : Fin (m + 1), l1.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hl1ne : l1 ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_zero] at this
    omega
  have hl1last : l1 ≠ Fin.last m := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_last] at this
    omega
  have hlast0 : Fin.last m ≠ 0 := fun e => by
    have := congrArg Fin.val e
    rw [Fin.val_last, Fin.val_zero] at this
    omega
  have labB : ∀ c : Fin (m + 1), c ≠ 0 →
      (planeGroup (stdPlane F3 m (posB c))).map (Θ 0) = K c := by
    intro c hc
    have h := (hΘ 0).lab (posB c)
    rwa [succAbove_zero_posB hc] at h
  have labC : ∀ c : Fin (m + 1), c ≠ l1 →
      (planeGroup (stdPlane F3 m (posB c))).map (Θ l1) = K c := by
    intro c hc
    have h := (hΘ l1).lab (posB c)
    rwa [succAbove_val_one_posB hl1 hc] at h
  have injB : ∀ c d : Fin (m + 1), c ≠ 0 → d ≠ 0 → posB c = posB d → c = d := by
    intro c d hc hd e
    have h := congrArg Fin.val e
    rw [posB_val, posB_val] at h
    have h1 := val_ne_zero_of_ne_zero hc
    have h2 := val_ne_zero_of_ne_zero hd
    exact Fin.ext (by omega)
  have injC : ∀ c d : Fin (m + 1), c ≠ l1 → d ≠ l1 → posB c = posB d → c = d := by
    intro c d hc hd e
    have h := congrArg Fin.val e
    rw [posB_val, posB_val] at h
    have h1 : c.val ≠ 1 := fun h' => hc (Fin.ext (by rw [hl1]; exact h'))
    have h2 : d.val ≠ 1 := fun h' => hd (Fin.ext (by rw [hl1]; exact h'))
    exact Fin.ext (by omega)
  have hL : ∀ c : Fin (m + 1), c ≠ l1 →
      (longBlock F3 m (posB c)).range.map (Θ l1) = K c := by
    intro c hc
    have h := labC c hc
    rwa [planeGroup_stdPlane_eq_range] at h
  have hK0 : K 0 = (longBlock F3 m (plane0 : Fin m)).range.map (Θ l1) := by
    have h := hL 0 (Ne.symm hl1ne)
    have e : posB (0 : Fin (m + 1)) = (plane0 : Fin m) := Fin.ext (by
      simp [posB_val, plane0_val])
    rw [e] at h
    exact h.symm
  have hKl : K (Fin.last m) = (longBlock F3 m (planeL : Fin m)).range.map (Θ l1) := by
    have h := hL (Fin.last m) (Ne.symm hl1last)
    have e : posB (Fin.last m) = (planeL : Fin m) := Fin.ext (by
      rw [posB_val, planeL_val, Fin.val_last])
    rw [e] at h
    exact h.symm
  have c0 : (K 0).map (MulAut.conj ((Θ l1) (swapElt F3 (plane0 : Fin m) planeL))).toMonoidHom =
      K (Fin.last m) := by
    rw [hK0, hKl]
    exact map_map_conj_swapElt_left (Θ l1) _ _
  have cl : (K (Fin.last m)).map
      (MulAut.conj ((Θ l1) (swapElt F3 (plane0 : Fin m) planeL))).toMonoidHom = K 0 := by
    rw [hKl, hK0]
    exact map_map_conj_swapElt_right (Θ l1) _ _
  have cfix : ∀ c : Fin (m + 1), c ≠ 0 → c ≠ Fin.last m →
      (K c).map (MulAut.conj ((Θ l1) (swapElt F3 (plane0 : Fin m) planeL))).toMonoidHom = K c := by
    intro c hc0 hcl
    by_cases hc1 : c = l1
    · have hcomm : ∀ y ∈ K c, Commute ((Θ l1) (swapElt F3 (plane0 : Fin m) planeL)) y := by
        rw [hc1]
        exact fun y hy => (hΘ l1).loc.comm ((Θ l1) (swapElt F3 (plane0 : Fin m) planeL))
          ⟨swapElt F3 (plane0 : Fin m) planeL, rfl⟩ y hy
      exact map_conj_eq_of_forall_commute _ hcomm
    · have hc0v := val_ne_zero_of_ne_zero hc0
      have hclv := val_lt_of_ne_last hcl
      have hc1v : c.val ≠ 1 := fun h => hc1 (Fin.ext (by rw [hl1]; exact h))
      rw [← hL c hc1]
      refine map_conj_eq_of_forall_commute _ (commute_map_swapElt_longBlock (Θ l1) ?_ ?_)
      · exact fun e => by
          have h := congrArg Fin.val e
          rw [posB_val, plane0_val] at h
          omega
      · exact fun e => by
          have h := congrArg Fin.val e
          rw [posB_val, planeL_val] at h
          omega
  refine ⟨(MulAut.conj ((Θ l1) (swapElt F3 (plane0 : Fin m) planeL))).toMonoidHom.comp (Θ 0),
    posA, posB, ?_⟩
  refine
    { hm := hm
      nonab := hnonab
      frame := hK
      locA := ?_
      locB := (hΘ 0).loc
      labA := ?_
      labB := labB
      valB := fun c => posB_val c
      valA0 := fun c h => posA_val_zero h
      valA := fun c h => posA_val h
      coh := ?_
      third := fun l => ⟨Θ l, hΘ l⟩ }
  ·
    have h := Frame.IsLocLift.conj hΩ (hΘ 0).loc ((Θ l1) (swapElt F3 (plane0 : Fin m) planeL))
    have e : conjSub ((Θ l1) (swapElt F3 (plane0 : Fin m) planeL)) (K 0) = K (Fin.last m) := c0
    rw [e] at h
    exact h
  ·
    intro c hc
    rw [← Subgroup.map_map]
    by_cases hc0 : c = 0
    · have h0 : c.val = 0 := by rw [hc0, Fin.val_zero]
      have e : posA c = posB (Fin.last m) := Fin.ext (by
        rw [posA_val_zero h0, posB_val, Fin.val_last])
      rw [e, labB (Fin.last m) hlast0, cl, hc0]
    · have e : posA c = posB c := Fin.ext (by
        rw [posA_val (val_ne_zero_of_ne_zero hc0), posB_val])
      rw [e, labB c hc0]
      exact cfix c hc0 hc
  ·
    intro i hi x hx
    have hn := nxt_val i
    have hi0 : i ≠ 0 := fun e => by
      have h := congrArg Fin.val e
      rw [Fin.val_zero] at h
      omega
    have hn0 : nxt i ≠ 0 := fun e => by
      have h := congrArg Fin.val e
      rw [Fin.val_zero] at h
      omega
    have hi1 : i ≠ l1 := fun e => by
      have h := congrArg Fin.val e
      rw [hl1] at h
      omega
    have hn1 : nxt i ≠ l1 := fun e => by
      have h := congrArg Fin.val e
      rw [hl1] at h
      omega
    have hine : i ≠ nxt i := ne_nxt (by omega)
    have hpab : posB i ≠ posB (nxt i) := fun e => hine (injB i _ hi0 hn0 e)
    have hxr : x ∈ (pairEmbed F3 hpab).range := shortSub_le_range_pairEmbed hpab hx
    have hBx : (Θ 0) x ∈ layerSub Ω K i (nxt i) := by
      rw [Frame.layerSub_eq (by omega) hnonab hK (hΘ 0).loc posB labB injB hi0 hn0 hine hpab]
      exact ⟨x, hxr, rfl⟩
    rw [Frame.layerSub_eq (by omega) hnonab hK (hΘ l1).loc posB labC injC hi1 hn1 hine hpab]
      at hBx
    obtain ⟨y, hy, hyx⟩ := hBx
    have hcomm : Commute ((Θ l1) (swapElt F3 (plane0 : Fin m) planeL)) ((Θ l1) y) := by
      refine commute_map_swapElt_pairEmbed_range (Θ l1) hpab ?_ ?_ ?_ ?_ ((Θ l1) y) ⟨y, hy, rfl⟩
      · exact fun e => by
          have h := congrArg Fin.val e
          rw [posB_val, plane0_val] at h
          omega
      · exact fun e => by
          have h := congrArg Fin.val e
          rw [posB_val, planeL_val] at h
          omega
      · exact fun e => by
          have h := congrArg Fin.val e
          rw [posB_val, plane0_val] at h
          omega
      · exact fun e => by
          have h := congrArg Fin.val e
          rw [posB_val, planeL_val] at h
          omega
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hyx, hcomm.eq, mul_inv_cancel_right]

end CFSG.ClassicalInvolution.Q3.Q3V.Chain
