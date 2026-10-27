module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverSylow

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.Sporadic.Mathieu

namespace LiftClasses

def letterCode (k : ℕ) : List ℕ :=
  if k = 0 then [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]
  else if k = 1 then [7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]
  else [8, 3, 1, 2, 10, 6, 9, 0, 7, 5, 11, 4]

def letterPerm (k : ℕ) : Equiv.Perm (Fin 12) :=
  if k = 0 then m12gA else if k = 1 then m12gB else m12gB⁻¹

def wordCode (w : List ℕ) : List ℕ :=
  w.foldr (fun k c => SylowTable.comp (letterCode k) c) (List.range 12)

def wordPerm (w : List ℕ) : Equiv.Perm (Fin 12) := (w.map letterPerm).prod

theorem isCode_letterCode (k : ℕ) : SylowTable.IsCode (letterCode k) (letterPerm k) := by
  unfold letterCode letterPerm
  split_ifs
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩

theorem isCode_wordCode : ∀ w : List ℕ, SylowTable.IsCode (wordCode w) (wordPerm w)
  | [] => SylowTable.isCode_one
  | k :: w => by
    change SylowTable.IsCode (SylowTable.comp (letterCode k) (wordCode w))
      (letterPerm k * wordPerm w)
    exact (isCode_letterCode k).mul (isCode_wordCode w)

theorem wordPerm_mem (w : List ℕ) : wordPerm w ∈ NativeSporadic.M12 := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
  unfold letterPerm
  split_ifs
  · exact m12a.2
  · exact m12b.2
  · exact inv_mem m12b.2

def codeR : List ℕ := [0, 1, 10, 5, 8, 3, 11, 7, 4, 9, 2, 6]

def codeZ : List ℕ := [9, 7, 3, 2, 11, 10, 8, 1, 6, 0, 5, 4]

theorem isCode_permR : SylowTable.IsCode codeR permR := ⟨rfl, by decide +kernel⟩

theorem isCode_permZ : SylowTable.IsCode codeZ permZ := ⟨rfl, by decide +kernel⟩

def conjData : List (ℕ × List ℕ × Bool) :=
  [(1, [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0], false), (2, [2, 0, 1, 0, 1, 0, 2, 0, 2], false),
   (3, [1, 0, 2, 0, 1, 0, 2, 0, 2, 0], true), (10, [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2], false),
   (12, [0, 1, 0, 1, 0, 2], true), (14, [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1], false),
   (17, [1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0], true), (19, [2, 0, 1, 0, 1], false),
   (21, [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0], false), (22, [1, 0, 1, 0], true),
   (29, [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0], false),
   (34, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2], false),
   (36, [1, 0, 1, 0, 2, 0, 1, 0, 1], true), (42, [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1], true),
   (44, [0, 1, 0, 2, 0, 2, 0, 1, 0], true), (45, [0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2], true),
   (46, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], true), (47, [1, 0, 2, 0, 2, 0], true),
   (50, [1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0], true),
   (51, [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0], false),
   (52, [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0], true),
   (53, [1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0], true), (54, [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1], true),
   (58, [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1], false), (59, [1, 0, 1, 0], false),
   (60, [1, 0, 1, 0, 2, 0, 2, 0, 1], true), (63, [1, 0, 1, 0, 2, 0, 1, 0, 2], false)]

def classCheck : Bool :=
  (List.range 64).all fun x =>
    SylowTable.code x == List.range 12 ||
      SylowTable.comp (SylowTable.code x) (SylowTable.code x) != List.range 12 ||
      conjData.any fun d => d.1 == x &&
        SylowTable.comp (wordCode d.2.1) (SylowTable.code x) ==
          SylowTable.comp (bif d.2.2 then codeR else codeZ) (wordCode d.2.1)

theorem classCheck_eq : classCheck = true := by decide +kernel

theorem exists_conj_of_mem_S {s : Equiv.Perm (Fin 12)} (hs : s ∈ S) (h2 : s * s = 1)
    (h1 : s ≠ 1) : ∃ c ∈ NativeSporadic.M12, c * s * c⁻¹ = permR ∨ c * s * c⁻¹ = permZ := by
  obtain ⟨x, hx, rfl⟩ := SylowTable.exists_elt hs
  have hc := SylowTable.isCode_elt x hx
  have h := List.all_eq_true.1 classCheck_eq x (List.mem_range.2 hx)
  have hne : (SylowTable.code x == List.range 12) = false := by
    rw [beq_eq_false_iff_ne]
    intro he
    exact h1 (hc.perm_eq (he ▸ SylowTable.isCode_one))
  have hsq : (SylowTable.comp (SylowTable.code x) (SylowTable.code x) != List.range 12) =
      false := by
    rw [bne_eq_false_iff_eq]
    exact (hc.mul hc).code_eq (h2 ▸ SylowTable.isCode_one)
  rw [hne, hsq, Bool.false_or, Bool.false_or, List.any_eq_true] at h
  obtain ⟨⟨x', w, b⟩, -, hd⟩ := h
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hd
  have e1 := (isCode_wordCode w).mul hc
  rw [hd.2] at e1
  refine ⟨wordPerm w, wordPerm_mem w, ?_⟩
  cases b
  · exact Or.inr (by rw [e1.perm_eq (isCode_permZ.mul (isCode_wordCode w)), mul_inv_cancel_right])
  · exact Or.inl (by rw [e1.perm_eq (isCode_permR.mul (isCode_wordCode w)), mul_inv_cancel_right])

end LiftClasses

theorem exists_conj_mem_S (q : NativeSporadic.M12) (hq : orderOf q = 2) :
    ∃ g : NativeSporadic.M12, ((g⁻¹ * q * g : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈ S := by
  have hp : IsPGroup 2 (Subgroup.zpowers q) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hq, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq NativeSporadic.M12 sylow P
  have hqP : q ∈ (P : Subgroup NativeSporadic.M12) := hP (Subgroup.mem_zpowers q)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hqP
  obtain ⟨s, hs, rfl⟩ := hqP
  refine ⟨g, ?_⟩
  rw [coe_sylow, Subgroup.mem_subgroupOf] at hs
  rw [MulAut.smul_def, MulAut.conj_apply]
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hs

theorem m12_involution_conj_elemR_or_elemZ (q : NativeSporadic.M12) (hq : orderOf q = 2) :
    (∃ g : NativeSporadic.M12, g * elemR * g⁻¹ = q) ∨
      ∃ g : NativeSporadic.M12, g * elemZ * g⁻¹ = q := by
  obtain ⟨g, hg⟩ := exists_conj_mem_S q hq
  set s : NativeSporadic.M12 := g⁻¹ * q * g with hs
  have hq2 : q * q = 1 := by rw [← pow_two, ← hq, pow_orderOf_eq_one]
  have hs2 : s * s = 1 := by
    rw [hs]
    calc g⁻¹ * q * g * (g⁻¹ * q * g) = g⁻¹ * (q * q) * g := by group
      _ = 1 := by rw [hq2, mul_one, inv_mul_cancel]
  have hs1 : s ≠ 1 := by
    intro h1
    have hq1 : q = 1 := by
      calc q = g * s * g⁻¹ := by rw [hs]; group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    rw [hq1, orderOf_one] at hq
    exact absurd hq (by norm_num)
  have hs2' : (s : Equiv.Perm (Fin 12)) * s = 1 := by
    rw [← Subgroup.coe_mul, hs2, Subgroup.coe_one]
  have hs1' : (s : Equiv.Perm (Fin 12)) ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨c, hc, hcs⟩ := LiftClasses.exists_conj_of_mem_S hg hs2' hs1'
  set c' : NativeSporadic.M12 := ⟨c, hc⟩
  have hq' : q = g * s * g⁻¹ := by rw [hs]; group
  rcases hcs with hcs | hcs
  · refine Or.inl ⟨g * c'⁻¹, ?_⟩
    have he : elemR = c' * s * c'⁻¹ := Subtype.ext hcs.symm
    rw [he, hq']
    group
  · refine Or.inr ⟨g * c'⁻¹, ?_⟩
    have he : elemZ = c' * s * c'⁻¹ := Subtype.ext hcs.symm
    rw [he, hq']
    group

@[expose] def fixedCount (q : NativeSporadic.M12) : ℕ :=
  (Finset.univ.filter fun i : Fin 12 => (q : Equiv.Perm (Fin 12)) i = i).card

theorem fixedCount_conj (g q : NativeSporadic.M12) : fixedCount (g * q * g⁻¹) = fixedCount q := by
  unfold fixedCount
  refine Finset.card_equiv (g : Equiv.Perm (Fin 12)).symm fun i => ?_
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
    Equiv.Perm.coe_inv]
  rw [Equiv.eq_symm_apply]

theorem fixedCount_elemR : fixedCount elemR = 4 := by
  change (Finset.univ.filter fun i : Fin 12 => permR i = i).card = 4
  decide +kernel

theorem fixedCount_elemZ : fixedCount elemZ = 0 := by
  change (Finset.univ.filter fun i : Fin 12 => permZ i = i).card = 0
  decide +kernel

theorem fixedCount_of_orderOf_eq_two (q : NativeSporadic.M12) (hq : orderOf q = 2) :
    fixedCount q = 4 ∨ fixedCount q = 0 := by
  rcases m12_involution_conj_elemR_or_elemZ q hq with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact Or.inl (by rw [fixedCount_conj, fixedCount_elemR])
  · exact Or.inr (by rw [fixedCount_conj, fixedCount_elemZ])

theorem conj_elemR_of_fixedCount_four (q : NativeSporadic.M12) (hq : orderOf q = 2)
    (h4 : fixedCount q = 4) : ∃ g : NativeSporadic.M12, g * elemR * g⁻¹ = q := by
  rcases m12_involution_conj_elemR_or_elemZ q hq with h | ⟨g, rfl⟩
  · exact h
  · rw [fixedCount_conj, fixedCount_elemZ] at h4
    exact absurd h4 (by norm_num)

theorem conj_elemZ_of_fixedCount_zero (q : NativeSporadic.M12) (hq : orderOf q = 2)
    (h0 : fixedCount q = 0) : ∃ g : NativeSporadic.M12, g * elemZ * g⁻¹ = q := by
  rcases m12_involution_conj_elemR_or_elemZ q hq with ⟨g, rfl⟩ | h
  · rw [fixedCount_conj, fixedCount_elemR] at h0
    exact absurd h0 (by norm_num)
  · exact h

end CFSG.ComponentClassification.M12Cover
