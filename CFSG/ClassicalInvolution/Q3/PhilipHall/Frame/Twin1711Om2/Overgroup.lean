module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.ClassPkg

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK eA keyF)

open CFSG.ClassicalInvolution.Generic
open scoped Pointwise

set_option linter.unusedSectionVars false


private theorem og2_mem_zip_map {α β : Type*} (l : List α) (f : α → β) {a : α} (ha : a ∈ l) :
    (a, f a) ∈ l.zip (l.map f) := by
  induction l with
  | nil => exact absurd ha (by simp)
  | cons b l ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih ha)

private theorem og2_getElem_mem (c : ArrCert) {i : ℕ} (hi : i < c.pts.size) :
    c.pts[i]! ∈ c.pts.toList := by
  rw [getElem!_pos c.pts i hi]
  exact Array.mem_toList_iff.2 (Array.getElem_mem hi)

private theorem og2_listed_mem {c : ArrCert} {F : Array ℕ} (hF : F ∈ c.pts.toList) :
    decFY F ∈ (fun i => decFY c.pts[i]!) '' {i | i < c.pts.size} := by
  obtain ⟨j, hj, hjF⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hF)
  exact ⟨j, hj, congrArg decFY ((getElem!_pos c.pts j hj).trans hjF)⟩

private theorem og2_wordYOK_T0 : wordYOK wT0 = true := by decide

private theorem og2_fuse0_len : wFuse0.length = 3 := rfl

private theorem og2_genY_size : (genY (reflTab ())).size = 8 := by
  simp [genY]

private theorem og2_decF_F0 :
    decFY (fCodeY (wY (lettersY (reflTab ())) wT0)) = negSetY t0Y :=
  decFY_fCodeY (rep_wordE og2_wordYOK_T0)

private theorem og2_orbit_parts :
    validFY (fCodeY (wY (lettersY (reflTab ())) wT0)) = true ∧
      orbSizeY (genY (reflTab ())) (fCodeY (wY (lettersY (reflTab ())) wT0)) 6300 = true := by
  have h := om2A_parts.2.2.2.2.1
  simp only [orbitCheckY, Bool.and_eq_true] at h
  exact h

private theorem og2_sub_parts :
    (∀ w ∈ wSub, arrCertOK (fun k X => actFY (wT.map (wY (lettersY (reflTab ())))).toArray[k]! X)
        (wT.map (wY (lettersY (reflTab ())))).toArray.size validFY keyF
        (actFY (wY (lettersY (reflTab ())) w) (fCodeY (wY (lettersY (reflTab ())) wT0)))
        (orbFY (wT.map (wY (lettersY (reflTab ())))).toArray
          (actFY (wY (lettersY (reflTab ())) w) (fCodeY (wY (lettersY (reflTab ())) wT0))) 6301)
        = true) ∧
    (∀ F ∈ (orbFY (genY (reflTab ())) (fCodeY (wY (lettersY (reflTab ())) wT0)) 6301).pts.toList,
        F = fCodeY (wY (lettersY (reflTab ())) wT0) ∨
        (∃ w ∈ wFuse0, F = actFY (wY (lettersY (reflTab ())) w)
          (fCodeY (wY (lettersY (reflTab ())) wT0))) ∨
        ∃ w ∈ wSub, F ∈ (orbFY (wT.map (wY (lettersY (reflTab ())))).toArray
          (actFY (wY (lettersY (reflTab ())) w) (fCodeY (wY (lettersY (reflTab ())) wT0)))
          6301).pts.toList) ∧
    (∀ w ∈ wSub, orbSizeY ((wT.map (wY (lettersY (reflTab ())))).toArray.push
        (wY (lettersY (reflTab ())) w)) (fCodeY (wY (lettersY (reflTab ())) wT0)) 6300 = true) := by
  have h := om2A_parts.2.2.2.2.2.1
  simp only [subCheckY, subCertsY, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun w hw => ?_, fun F hF => ?_, fun w hw => ?_⟩
  · have hmem := og2_mem_zip_map wSub
      (fun w => orbFY (wT.map (wY (lettersY (reflTab ())))).toArray
        (actFY (wY (lettersY (reflTab ())) w) (fCodeY (wY (lettersY (reflTab ())) wT0))) 6301) hw
    have key := List.all_eq_true.1 h1 _ hmem
    exact key
  · have h := List.all_eq_true.1 h2 F hF
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with (h | ⟨w, hw, hFw⟩) | ⟨c, hc, hFc⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨w, hw, hFw⟩)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
      refine Or.inr (Or.inr ⟨w, hw, ?_⟩)
      simp only [inCertY, List.any_eq_true, beq_iff_eq] at hFc
      obtain ⟨F', hF', rfl⟩ := hFc
      exact hF'
  · exact List.all_eq_true.1 h3 w hw

private theorem og2_conj_of_mem_T0 {y : HY} (hy : y ∈ T0Y) : y * t0Y * y⁻¹ = t0Y := by
  rw [Subgroup.mem_centralizer_singleton_iff.1 hy, mul_inv_cancel_right]

private noncomputable def og2_S : Subgroup HY where
  carrier := {x | x * t0Y * x⁻¹ = t0Y ∨ ∃ k < 3, x * t0Y * x⁻¹ = t0Y * cK k}
  one_mem' := Or.inl (by simp)
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have e : x * y * t0Y * (x * y)⁻¹ = x * (y * t0Y * y⁻¹) * x⁻¹ := by group
    rw [e]
    rcases hy with hy | ⟨b, hb, hy⟩
    · rw [hy]
      exact hx
    · rw [hy]
      have hc : x * cK b * x⁻¹ = cK b := by rw [cK_comm b x, mul_inv_cancel_right]
      have e2 : x * (t0Y * cK b) * x⁻¹ = (x * t0Y * x⁻¹) * cK b :=
        calc x * (t0Y * cK b) * x⁻¹ = (x * t0Y * x⁻¹) * (x * cK b * x⁻¹) := by group
          _ = (x * t0Y * x⁻¹) * cK b := by rw [hc]
      rw [e2]
      rcases hx with hx | ⟨a, ha, hx⟩
      · rw [hx]
        exact Or.inr ⟨b, hb, rfl⟩
      · rw [hx]
        by_cases hab : a = b
        · subst hab
          rw [mul_assoc, cK_mul_self, mul_one]
          exact Or.inl rfl
        · obtain ⟨c, hc', hcc⟩ := mul_cK_mem ha hb hab
          rw [mul_assoc, hcc]
          exact Or.inr ⟨c, hc', rfl⟩
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [inv_inv]
    rcases hx with hx | ⟨a, ha, hx⟩
    · left
      calc x⁻¹ * t0Y * x = x⁻¹ * (x * t0Y * x⁻¹) * x := by rw [hx]
        _ = t0Y := by group
    · right
      refine ⟨a, ha, ?_⟩
      have hcx : x⁻¹ * cK a * x = cK a := by rw [cK_comm a x⁻¹, inv_mul_cancel_right]
      have h1 : (x⁻¹ * t0Y * x) * cK a = t0Y :=
        calc (x⁻¹ * t0Y * x) * cK a = (x⁻¹ * t0Y * x) * (x⁻¹ * cK a * x) := by rw [hcx]
          _ = x⁻¹ * (t0Y * cK a) * x := by group
          _ = x⁻¹ * (x * t0Y * x⁻¹) * x := by rw [hx]
          _ = t0Y := by group
      calc x⁻¹ * t0Y * x = (x⁻¹ * t0Y * x * cK a) * cK a := by
            rw [mul_assoc (x⁻¹ * t0Y * x) (cK a) (cK a), cK_mul_self, mul_one]
        _ = t0Y * cK a := by rw [h1]

private theorem og2_cover (x : HY) :
    x ∈ og2_S ∨ ∃ g ∈ wordE '' {w | w ∈ wSub}, ∃ h ∈ MulAction.stabilizer HY (negSetY t0Y),
      x • negSetY t0Y = (h * g) • negSetY t0Y := by
  obtain ⟨hclosure, hTstab, -, -, -, -, -, horb, -⟩ := classPkg0Y
  obtain ⟨hF0v, hO⟩ := og2_orbit_parts
  obtain ⟨hA, hB, -⟩ := og2_sub_parts
  have hcl : Subgroup.closure (genE '' {k | k < (genY (reflTab ())).size}) = closureG := by
    unfold closureG
    rw [og2_genY_size]
  have hOm := (orbSizeY_spec (gens := genE) (gs := genY (reflTab ()))
    (fun k hk => rep_genY hk) hO).1
  rw [hcl, og2_decF_F0] at hOm
  have hxO : x • negSetY t0Y ∈ MulAction.orbit closureG (negSetY t0Y) := by
    rw [horb]
    exact MulAction.mem_orbit _ x
  rw [hOm] at hxO
  obtain ⟨i, hi, hix⟩ := hxO
  change decFY _ = x • negSetY t0Y at hix
  rcases hB _ (og2_getElem_mem _ hi) with hF | ⟨w, hw, hF⟩ | ⟨w, hw, hFw⟩
  ·
    left
    have hxT : x ∈ T0Y := by
      rw [hTstab, MulAction.mem_stabilizer_iff, ← hix, hF, og2_decF_F0]
    exact Or.inl (og2_conj_of_mem_T0 hxT)
  ·
    left
    have hwok : wordYOK w = true := (wordsCheckY_spec (wFuse0_sub w hw)).1
    have hdF : decFY (actFY (wY (lettersY (reflTab ())) w) (fCodeY (wY (lettersY (reflTab ())) wT0)))
        = wordE w • negSetY t0Y :=
      (decFY_actFY (rep_wordE hwok) hF0v).trans
        (congrArg (fun S : Finset (Fin 480) => phi (wordE w) • S) og2_decF_F0)
    have hxw : x • negSetY t0Y = wordE w • negSetY t0Y :=
      hix.symm.trans ((congrArg decFY hF).trans hdF)
    obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
    have hgetD : wFuse0.getD k [] = w := by
      rw [List.getD_eq_getElem _ _ hk, hkw]
    have hk3 : k < 3 := lt_of_lt_of_eq hk og2_fuse0_len
    have hfuse : wordE w = fuse0 k := congrArg wordE hgetD.symm
    rw [hfuse] at hxw
    have hs : (fuse0 k)⁻¹ * x ∈ T0Y := by
      rw [hTstab, MulAction.mem_stabilizer_iff, mul_smul, hxw, inv_smul_smul]
    have e : x * t0Y * x⁻¹ = fuse0 k * t0Y * (fuse0 k)⁻¹ := by
      calc x * t0Y * x⁻¹ = fuse0 k * (((fuse0 k)⁻¹ * x) * t0Y * ((fuse0 k)⁻¹ * x)⁻¹) * (fuse0 k)⁻¹ := by
            group
        _ = fuse0 k * t0Y * (fuse0 k)⁻¹ := by rw [og2_conj_of_mem_T0 hs]
    exact Or.inr ⟨k, hk3, e.trans (fuse0_conj hk3)⟩
  ·
    right
    have hwok : wordYOK w = true := (wordsCheckY_spec (wSub_sub w hw)).1
    have hS := (arrCertFY_spec (gs := (wT.map (wY (lettersY (reflTab ())))).toArray)
      (gens := gensOfY wT) (fun k hk => rep_gensOfY (wordYOK_of_sub wT_sub) hk) (hA w hw)).1
    rw [closure_gensOfY, hclosure] at hS
    have hmemO := og2_listed_mem hFw
    rw [← hS] at hmemO
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.1 hmemO
    have hdF : decFY (actFY (wY (lettersY (reflTab ())) w) (fCodeY (wY (lettersY (reflTab ())) wT0)))
        = wordE w • negSetY t0Y :=
      (decFY_actFY (rep_wordE hwok) hF0v).trans
        (congrArg (fun S : Finset (Fin 480) => phi (wordE w) • S) og2_decF_F0)
    refine ⟨wordE w, ⟨w, hw, rfl⟩, (h : HY), ?_, ?_⟩
    · rw [← hTstab]
      exact h.2
    · exact hix.symm.trans (hh.symm.trans
        ((congrArg (fun S : Finset (Fin 480) => (h : HY) • S) hdF).trans
          (mul_smul (h : HY) (wordE w) (negSetY t0Y)).symm))

private noncomputable def og2_gens (w : List ℕ) (k : ℕ) : HY :=
  if k < (wT.map (wY (lettersY (reflTab ())))).toArray.size then gensOfY wT k else wordE w

private theorem og2_rep_gens {w : List ℕ} (hw : wordYOK w = true) :
    ∀ k < ((wT.map (wY (lettersY (reflTab ())))).toArray.push
        (wY (lettersY (reflTab ())) w)).size,
      Rep 480 ((wT.map (wY (lettersY (reflTab ())))).toArray.push
        (wY (lettersY (reflTab ())) w))[k]! (phi (og2_gens w k)) := by
  intro k hk
  have h1 := Array.size_push (xs := (wT.map (wY (lettersY (reflTab ())))).toArray)
    (wY (lettersY (reflTab ())) w)
  by_cases hlt : k < (wT.map (wY (lettersY (reflTab ())))).toArray.size
  · have e : ((wT.map (wY (lettersY (reflTab ())))).toArray.push
        (wY (lettersY (reflTab ())) w))[k]! =
        (wT.map (wY (lettersY (reflTab ())))).toArray[k]! := by
      rw [getElem!_pos ((wT.map (wY (lettersY (reflTab ())))).toArray.push
          (wY (lettersY (reflTab ())) w)) k hk,
        getElem!_pos ((wT.map (wY (lettersY (reflTab ())))).toArray) k hlt,
        Array.getElem_push_lt hlt]
    rw [e, og2_gens, if_pos hlt]
    exact rep_gensOfY (wordYOK_of_sub wT_sub) hlt
  · have hk' : k = (wT.map (wY (lettersY (reflTab ())))).toArray.size := by omega
    subst hk'
    have e : ((wT.map (wY (lettersY (reflTab ())))).toArray.push
        (wY (lettersY (reflTab ())) w))[(wT.map (wY (lettersY (reflTab ())))).toArray.size]! =
        wY (lettersY (reflTab ())) w := by
      rw [getElem!_pos ((wT.map (wY (lettersY (reflTab ())))).toArray.push
          (wY (lettersY (reflTab ())) w)) _ hk, Array.getElem_push_eq]
    rw [e, og2_gens, if_neg hlt]
    exact rep_wordE hw

private theorem og2_gen {w : List ℕ} (hw : w ∈ wSub) {M : Subgroup HY}
    (hstab : MulAction.stabilizer HY (negSetY t0Y) ≤ M) (hg : wordE w ∈ M) : M = ⊤ := by
  obtain ⟨hclosure, hTstab, -, -, -, -, -, -, hncard⟩ := classPkg0Y
  have hwok : wordYOK w = true := (wordsCheckY_spec (wSub_sub w hw)).1
  have hC := og2_sub_parts.2.2 w hw
  have hTM : closureY wT ≤ M := by
    rw [hclosure, hTstab]
    exact hstab
  have hKM : Subgroup.closure (og2_gens w '' {k | k <
      ((wT.map (wY (lettersY (reflTab ())))).toArray.push (wY (lettersY (reflTab ())) w)).size}) ≤
        M := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    by_cases hlt : k < (wT.map (wY (lettersY (reflTab ())))).toArray.size
    · rw [og2_gens, if_pos hlt]
      exact hTM (by rw [← closure_gensOfY]; exact Subgroup.subset_closure ⟨k, hlt, rfl⟩)
    · rw [og2_gens, if_neg hlt]
      exact hg
  have hO := orbSizeY_spec (gens := og2_gens w) (og2_rep_gens hwok) hC
  rw [og2_decF_F0] at hO
  have horbK := OmGen.orbit_eq_of_ncard_le (negSetY t0Y) _ (le_of_eq (hncard.trans hO.2.1.symm))
  exact OmGen.eq_top_of_orbit_eq (negSetY t0Y) hKM hstab horbK

theorem overgroupY {M : Subgroup HY} (hM : T0Y ≤ M) (hMt : M ≠ ⊤) :
    ∀ m ∈ M, m * t0Y * m⁻¹ = t0Y ∨ ∃ k < 3, m * t0Y * m⁻¹ = t0Y * cK k := by
  obtain ⟨-, hTstab, -, -, -, -, -, -, -⟩ := classPkg0Y
  have hstab : MulAction.stabilizer HY (negSetY t0Y) ≤ M := by
    rw [← hTstab]
    exact hM
  have key : M ≤ og2_S :=
    OmGen.le_of_cover (negSetY t0Y) og2_S (wordE '' {w | w ∈ wSub}) og2_cover
      (by
        rintro _ ⟨w, hw, rfl⟩ M' hM' hg'
        exact og2_gen hw hM' hg')
      hstab hMt
  exact fun m hm => key hm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
