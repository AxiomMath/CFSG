module

public import CFSG.ClassicalInvolution.Q3.Q3VChain3Nodes
public import CFSG.ClassicalInvolution.Q3.Q3VChainMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Chain3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3V.Chain

local notation "F3" => GaloisField 3 1

variable {m : ℕ} {G : Type} [Group G]

theorem conjInvariant_conjClass3 (K₀ : Subgroup G) : ConjInvariant (conjClass3 K₀) := by
  rintro n _ ⟨g, rfl⟩
  exact ⟨n * g, conjSub_mul n g K₀⟩

theorem nonab_conjClass3 {K₀ : Subgroup G} (hK₀ : ¬ Commutes K₀ K₀) :
    ∀ M ∈ conjClass3 K₀, ¬ Commutes M M := by
  rintro _ ⟨g, rfl⟩ h
  exact hK₀ ((commutes_conjSub_iff g).1 h)

theorem posB_zero [NeZero m] : posB (0 : Fin (m + 1)) = (plane0 : Fin m) :=
  Fin.ext (by simp [posB_val, plane0_val])

theorem posB_last [NeZero m] : posB (Fin.last m) = (planeL : Fin m) :=
  Fin.ext (by rw [posB_val, planeL_val, Fin.val_last])

theorem exists_nodeDataW [NeZero m] (hm : 3 ≤ m) {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (hnonab : ∀ M ∈ Ω, ¬ Commutes M M) {K : Fin (m + 1) → Subgroup G}
    (hK : IsMemberFrame Ω K) {Θ : Fin (m + 1) → (StatedSp m F3 →* G)}
    (hΘ : ∀ l, IsLabLift m Ω K l (Θ l))
    (hdisj : ∀ i j : Fin (m + 1), i.val + 1 < j.val → j.val < m →
      Commutes (layerSub Ω K i (nxt i)) (layerSub Ω K j (nxt j)))
    (hjunc : ∀ i : Fin (m + 1), i.val + 2 = m →
      Commutes (layerSub Ω K 0 (Fin.last m)) (layerSub Ω K i (nxt i))) :
    ∃ (A : StatedSp m F3 →* G) (pA pB : Fin (m + 1) → Fin m), NodeDataW Ω K A (Θ 0) pA pB := by
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
    rw [posB_zero] at h
    exact h.symm
  have hKl : K (Fin.last m) = (longBlock F3 m (planeL : Fin m)).range.map (Θ l1) := by
    have h := hL (Fin.last m) (Ne.symm hl1last)
    rw [posB_last] at h
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
  have hpab0L : posB (0 : Fin (m + 1)) ≠ posB (Fin.last m) := by
    rw [posB_zero, posB_last]
    intro e
    have h := congrArg Fin.val e
    rw [plane0_val, planeL_val] at h
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
      disj := hdisj }
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
    have hine : i ≠ nxt i := ne_nxt (by omega)
    have hpab : posB i ≠ posB (nxt i) := fun e => hine (injB i _ hi0 hn0 e)
    have hxr : x ∈ (pairEmbed F3 hpab).range := shortSub_le_range_pairEmbed hpab hx
    have hBx : (Θ 0) x ∈ layerSub Ω K i (nxt i) := by
      rw [Frame.layerSub_eq hm hnonab hK (hΘ 0).loc posB labB injB hi0 hn0 hine hpab]
      exact ⟨x, hxr, rfl⟩
    have hsw : (Θ l1) (swapElt F3 (plane0 : Fin m) planeL) ∈ layerSub Ω K 0 (Fin.last m) := by
      rw [Frame.layerSub_eq hm hnonab hK (hΘ l1).loc posB labC injC (Ne.symm hl1ne)
        (Ne.symm hl1last) (Ne.symm hlast0) hpab0L]
      refine ⟨swapElt F3 (plane0 : Fin m) planeL, ?_, rfl⟩
      rw [range_pairEmbed hpab0L, posB_zero, posB_last]
      exact swapElt_mem_suppGroup _ _
    have hcomm := hjunc i hi _ hsw _ hBx
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hcomm, mul_inv_cancel_right]

theorem exists_nodeDataW_four {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (hnonab : ∀ M ∈ Ω, ¬ Commutes M M) {K : Fin 4 → Subgroup G} (hK : IsMemberFrame Ω K)
    {Θ : Fin 4 → (StatedSp 3 F3 →* G)} (hΘ : ∀ l, IsLabLift 3 Ω K l (Θ l))
    (R1 : Commutes (layerSub Ω K 0 1) (layerSub Ω K 2 3))
    (R1' : Commutes (layerSub Ω K 0 3) (layerSub Ω K 1 2)) :
    ∃ (A : StatedSp 3 F3 →* G) (pA pB : Fin 4 → Fin 3), NodeDataW Ω K A (Θ 0) pA pB := by
  refine exists_nodeDataW (m := 3) le_rfl hΩ hnonab hK hΘ ?_ ?_
  · intro i j hij hj
    have hi : i = 0 := Fin.ext (show i.val = 0 by omega)
    have hj2 : j = 2 := Fin.ext (show j.val = 2 by omega)
    subst hi hj2
    exact R1
  · intro i hi
    have hi1 : i = 1 := Fin.ext (show i.val = 1 by omega)
    subst hi1
    exact R1'

end CFSG.ClassicalInvolution.Q3.Q3V.Chain3
