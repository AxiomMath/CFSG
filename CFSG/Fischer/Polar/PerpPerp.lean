
module

public import CFSG.Fischer.Polar.PerpPerpBase

public import CFSG.Fischer.Polar.Lines
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

local notation "PT" => perpTab ()
local notation "PL" => perpLists (perpTab ())

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  perpLists lineTab


theorem perpPerp_zero
    {q : Fin 693} (hq : ¬ perp 0 q) :
    {w | perp w 0 ∧ perp w q}.ncard = 45 ∧
      (∀ a b : Fin 693, (perp a 0 ∧ perp a q) → (perp b 0 ∧ perp b q) → a ≠ b → perp a b →
        ∃ w, (perp w 0 ∧ perp w q) ∧ ¬ (perp w a ↔ perp w b)) ∧
      (∀ q' : Fin 693, ¬ perp 0 q' → (∀ w, perp w 0 ∧ perp w q ↔ perp w 0 ∧ perp w q') →
        q' = q ∨ q' = tvP 0 q) ∧
      ∃ a b c : Fin 693, (perp a 0 ∧ perp a q) ∧ (perp b 0 ∧ perp b q) ∧ (perp c 0 ∧ perp c q) ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ perp a b ∧ c ∈ lineThru a b := by
  have h0 := polarLinesFacts.perpPerp
  unfold perpPerpOK at h0
  have h := (allIn_eq_true.1 h0) q.val (Nat.zero_le _) q.2
  have hq' : (PT[0]!)[q.val]! = false := by
    rw [Bool.eq_false_iff]
    exact fun h' => hq ((perpTab_spec 0 q).1 h')
  rw [hq', Bool.false_or] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hsize, hcol⟩, htw⟩, hdet⟩ := h
  set N := (PL[0]!).filter (fun w => (PT[w]!)[q.val]!) with hNdef
  have hmemN : ∀ w, w ∈ N ↔ ∃ h : w < 693, perp ⟨w, h⟩ 0 ∧ perp ⟨w, h⟩ q :=
    fun w => mem_perpPerpList
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hset : {w : Fin 693 | perp w 0 ∧ perp w q} = {w : Fin 693 | w.val ∈ N.toList} := by
      ext w
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Array.mem_toList_iff, hmemN]
      exact ⟨fun h => ⟨w.2, h⟩, fun ⟨_, h⟩ => h⟩
    have hnd : N.toList.Nodup := by
      rw [hNdef, Array.toList_filter]
      exact (nodup_perpLists 0).filter _
    rw [hset, ncard_setOf_mem_list hnd (fun i hi => ((hmemN i).1
      (Array.mem_toList_iff.1 hi)).1), Array.length_toList, hsize]
  · intro a b ha hb hab hp
    have h1 := (Array.all_eq_true'.1 htw) a.val ((hmemN _).2 ⟨a.2, ha⟩)
    have h2 := (Array.all_eq_true'.1 h1) b.val ((hmemN _).2 ⟨b.2, hb⟩)
    have hab' : (a.val == b.val) = false := by
      rw [beq_eq_false_iff_ne]; exact fun h' => hab (Fin.ext h')
    rw [hab', (perpTab_spec a b).2 hp, Bool.false_or, Bool.not_true, Bool.false_or,
      Array.any_eq_true'] at h2
    obtain ⟨w, hw, hne⟩ := h2
    obtain ⟨hwlt, hw0, hwq⟩ := (hmemN _).1 hw
    refine ⟨⟨w, hwlt⟩, ⟨hw0, hwq⟩, fun hiff => ?_⟩
    rw [bne_iff_ne, ne_eq, Bool.eq_iff_iff, perpTab_spec ⟨w, hwlt⟩ a,
      perpTab_spec ⟨w, hwlt⟩ b] at hne
    exact hne hiff
  · intro q' hq0 hN
    have h3 := (allIn_eq_true.1 hdet) q'.val (Nat.zero_le _) q'.2
    have hq0' : (PT[0]!)[q'.val]! = false := by
      rw [Bool.eq_false_iff]
      exact fun h' => hq0 ((perpTab_spec 0 q').1 h')
    have hall : ((PL[0]!).all fun w => (PT[w]!)[q.val]! == (PT[w]!)[q'.val]!) = true := by
      rw [Array.all_eq_true']
      intro w hw
      obtain ⟨hwlt, hw0⟩ := mem_perpLists_zero.1 hw
      rw [beq_iff_eq, Bool.eq_iff_iff, perpTab_spec ⟨w, hwlt⟩ q, perpTab_spec ⟨w, hwlt⟩ q']
      have := hN ⟨w, hwlt⟩
      exact ⟨fun h => (this.1 ⟨perp_comm.1 hw0, h⟩).2, fun h => (this.2 ⟨perp_comm.1 hw0, h⟩).2⟩
    have hr : ap tvTabs[0]! q.val = (tvP 0 q).val := by
      have := rep_tvP 0 q.val q.2
      rw [idx_of_lt _ q.2] at this
      exact this
    rw [hq0', hall, Bool.false_or, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
      beq_iff_eq, hr] at h3
    rcases h3 with h3 | h3
    · exact Or.inl (Fin.ext h3)
    · exact Or.inr (Fin.ext h3)
  · rw [Array.any_eq_true'] at hcol
    obtain ⟨a, ha, hcol⟩ := hcol
    rw [Array.any_eq_true'] at hcol
    obtain ⟨b, hb, hcol⟩ := hcol
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Array.any_eq_true'] at hcol
    obtain ⟨⟨hab, hpab⟩, c, hcL, hcab⟩ := hcol
    obtain ⟨⟨hca, hcb⟩, hcN⟩ := hcab
    obtain ⟨halt, ha0, haq⟩ := (hmemN a).1 ha
    obtain ⟨hblt, hb0, hbq⟩ := (hmemN b).1 hb
    obtain ⟨hclt, hc0, hcq⟩ := (hmemN c).1 (Array.contains_iff_mem.1 hcN)
    have hab' : (⟨a, halt⟩ : Fin 693) ≠ ⟨b, hblt⟩ := fun h => hab (congrArg Fin.val h)
    have hp' : perp ⟨a, halt⟩ ⟨b, hblt⟩ := (perpTab_spec ⟨a, halt⟩ ⟨b, hblt⟩).1 hpab
    refine ⟨⟨a, halt⟩, ⟨b, hblt⟩, ⟨c, hclt⟩, ⟨ha0, haq⟩, ⟨hb0, hbq⟩, ⟨hc0, hcq⟩, hab',
      fun h => hca (congrArg Fin.val h).symm, fun h => hcb (congrArg Fin.val h).symm, hp', ?_⟩
    rw [mem_lineThru_iff hab' hp', ← lineTab_get hp']
    exact hcL

theorem eq_of_perp_perp
    {p q q' : Fin 693} (h : ¬ perp p q) (h' : ¬ perp p q')
    (hN : ∀ w, perp w p ∧ perp w q ↔ perp w p ∧ perp w q') : q' = q ∨ q' = tvP p q := by
  obtain ⟨g, hg, rfl⟩ := exists_smul_zero p
  have ha := isPolarAut_of_mem hg
  have hq : ¬ perp 0 (g⁻¹ q) := fun h'' =>
    h (by rw [← perm_apply_inv_self g q, ha.map_perp]; exact h'')
  have hq' : ¬ perp 0 (g⁻¹ q') := fun h'' =>
    h' (by rw [← perm_apply_inv_self g q', ha.map_perp]; exact h'')
  have hN' : ∀ w, perp w 0 ∧ perp w (g⁻¹ q) ↔ perp w 0 ∧ perp w (g⁻¹ q') := by
    intro w
    have := hN (g w)
    rw [← perm_apply_inv_self g q, ← perm_apply_inv_self g q'] at this
    simpa only [ha.map_perp] using this
  rcases (perpPerp_zero hq).2.2.1 (g⁻¹ q') hq' hN' with h1 | h1
  · left
    rw [← perm_apply_inv_self g q', h1, perm_apply_inv_self]
  · right
    rw [← perm_apply_inv_self g q', h1, ha.map_tvP, perm_apply_inv_self]

theorem ncard_perp_perp
    {p q : Fin 693} (h : ¬ perp p q) :
    {w | perp w p ∧ perp w q}.ncard = 45 := by
  obtain ⟨g, hg, rfl⟩ := exists_smul_zero p
  have ha := isPolarAut_of_mem hg
  have hq : ¬ perp 0 (g⁻¹ q) := fun h' =>
    h (by rw [← perm_apply_inv_self g q, ha.map_perp]; exact h')
  have := (perpPerp_zero hq).1
  rw [← perm_apply_inv_self g q, perpPerp_image ha, Set.ncard_image_of_injective _ g.injective]
  exact this

theorem twinFree_perp_perp
    {p q : Fin 693} (h : ¬ perp p q) {x y : Fin 693}
    (hx : perp x p ∧ perp x q) (hy : perp y p ∧ perp y q) (hxy : x ≠ y) (hp : perp x y) :
    ∃ w, (perp w p ∧ perp w q) ∧ ¬ (perp w x ↔ perp w y) := by
  obtain ⟨g, hg, rfl⟩ := exists_smul_zero p
  have ha := isPolarAut_of_mem hg
  have hi := ha.inv
  have hq : ¬ perp 0 (g⁻¹ q) := fun h' =>
    h (by rw [← perm_apply_inv_self g q, ha.map_perp]; exact h')
  have tr : ∀ a, perp a (g 0) ∧ perp a q → perp (g⁻¹ a) 0 ∧ perp (g⁻¹ a) (g⁻¹ q) := by
    intro a ⟨h1, h2⟩
    refine ⟨?_, (hi.map_perp a q).2 h2⟩
    have := (hi.map_perp a (g 0)).2 h1
    rwa [perm_inv_apply_self] at this
  obtain ⟨w, ⟨hw0, hwq⟩, hne⟩ := (perpPerp_zero hq).2.1 (g⁻¹ x) (g⁻¹ y) (tr x hx) (tr y hy)
    (g⁻¹.injective.ne hxy) ((hi.map_perp x y).2 hp)
  refine ⟨g w, ⟨?_, ?_⟩, fun hiff => hne ?_⟩
  · rw [← ha.map_perp] at hw0; exact hw0
  · rw [← perm_apply_inv_self g q, ha.map_perp]; exact hwq
  · rw [← perm_apply_inv_self g x, ← perm_apply_inv_self g y, ha.map_perp, ha.map_perp] at hiff
    exact hiff

theorem IsClosedHyperoval.not_linear
    {O : Set (Fin 693)} (hO : IsClosedHyperoval O) {p : Fin 693}
    (hp : p ∈ O) {q : Fin 693} (hpq : ¬ perp p q) :
    ¬ ∀ w, perp w p → w ≠ p → (w ∈ O ↔ perp w q) := by
  intro H
  obtain ⟨g, hg, rfl⟩ := exists_smul_zero p
  have ha := isPolarAut_of_mem hg
  have hq : ¬ perp 0 (g⁻¹ q) := fun h' =>
    hpq (by rw [← perm_apply_inv_self g q, ha.map_perp]; exact h')
  obtain ⟨a, b, c, ha', hb', hc', hab, hac, hbc, hpab, hcL⟩ := (perpPerp_zero hq).2.2.2
  have mem : ∀ x : Fin 693, perp x 0 ∧ perp x (g⁻¹ q) → g x ∈ O := by
    intro x ⟨hx0, hxq⟩
    have h1 : perp (g x) (g 0) := (ha.map_perp x 0).2 hx0
    have h2 : perp (g x) q := by rw [← perm_apply_inv_self g q, ha.map_perp]; exact hxq
    refine (H (g x) h1 fun h => hpq ?_).2 h2
    rw [← h]
    exact h2
  have hL := (isLine_lineThru hab hpab).image ha
  rw [image_lineThru ha hab hpab] at hL
  have hcL' : g c ∈ lineThru (g a) (g b) := by
    rw [← image_lineThru ha hab hpab]
    exact ⟨c, hcL, rfl⟩
  exact g.injective.ne hbc (hO.eq_of_mem hL ⟨left_mem_lineThru _ _, mem a ha'⟩
    ⟨right_mem_lineThru _ _, mem b hb'⟩ ⟨hcL', mem c hc'⟩ (g.injective.ne hab)
    (g.injective.ne hac))

end CFSG.Fischer
