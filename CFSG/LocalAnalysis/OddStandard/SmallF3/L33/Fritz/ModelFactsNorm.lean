module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsChecks
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsPass
public import CFSG.GH74.KGroups.L33

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier

private def normT1 : List (Equiv.Perm (Fin 26)) :=
  [1, modelZ, modelY, modelZ * modelY, modelK, modelZ * modelK, modelY * modelK,
    modelZ * modelY * modelK]

private def normT2 : List (Equiv.Perm (Fin 26)) :=
  [1, modelZ, modelX ^ 2 * modelY, modelZ * (modelX ^ 2 * modelY), modelK, modelZ * modelK,
    (modelX ^ 2 * modelY) * modelK, modelZ * (modelX ^ 2 * modelY) * modelK]

private def inT1 (x : Equiv.Perm (Fin 26)) : Bool :=
  normT1.any (fun e => decide (x = e))

private def inT2 (x : Equiv.Perm (Fin 26)) : Bool :=
  normT2.any (fun e => decide (x = e))

private lemma inT1_iff (x : Equiv.Perm (Fin 26)) : inT1 x = true ↔ x ∈ normT1 := by
  simp only [inT1, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨e, he, h⟩ => by rw [h]; exact he, fun hx => ⟨x, hx, rfl⟩⟩

private lemma inT2_iff (x : Equiv.Perm (Fin 26)) : inT2 x = true ↔ x ∈ normT2 := by
  simp only [inT2, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨e, he, h⟩ => by rw [h]; exact he, fun hx => ⟨x, hx, rfl⟩⟩

private theorem normT1_mul_closed :
    normT1.all (fun x => normT1.all (fun y => inT1 (x * y))) = true := by
  decide +kernel

private theorem normT1_inv_closed : normT1.all (fun x => inT1 x⁻¹) = true := by
  decide +kernel

private theorem normT1_gens :
    inT1 1 = true ∧ inT1 modelZ = true ∧ inT1 modelY = true ∧ inT1 modelK = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem normT2_mul_closed :
    normT2.all (fun x => normT2.all (fun y => inT2 (x * y))) = true := by
  decide +kernel

private theorem normT2_inv_closed : normT2.all (fun x => inT2 x⁻¹) = true := by
  decide +kernel

private theorem normT2_gens :
    inT2 1 = true ∧ inT2 modelZ = true ∧ inT2 (modelX ^ 2 * modelY) = true ∧
      inT2 modelK = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private lemma mem_normT1 {g : Equiv.Perm (Fin 26)}
    (h : g ∈ Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26)))) :
    g ∈ normT1 := by
  refine Subgroup.closure_induction (p := fun x _ => x ∈ normT1) ?_ ?_ ?_ ?_ h
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact (inT1_iff modelZ).mp normT1_gens.2.1
    · exact (inT1_iff modelY).mp normT1_gens.2.2.1
    · exact (inT1_iff modelK).mp normT1_gens.2.2.2
  · exact (inT1_iff 1).mp normT1_gens.1
  · intro x y hx hy ihx ihy
    have h1 : normT1.all (fun y => inT1 (x * y)) = true :=
      (List.all_eq_true.mp normT1_mul_closed) x ihx
    exact (inT1_iff (x * y)).mp ((List.all_eq_true.mp h1) y ihy)
  · intro x hx ih
    exact (inT1_iff x⁻¹).mp ((List.all_eq_true.mp normT1_inv_closed) x ih)

private lemma mem_normT2 {g : Equiv.Perm (Fin 26)}
    (h : g ∈ Subgroup.closure
      ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26)))) :
    g ∈ normT2 := by
  refine Subgroup.closure_induction (p := fun x _ => x ∈ normT2) ?_ ?_ ?_ ?_ h
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact (inT2_iff modelZ).mp normT2_gens.2.1
    · exact (inT2_iff (modelX ^ 2 * modelY)).mp normT2_gens.2.2.1
    · exact (inT2_iff modelK).mp normT2_gens.2.2.2
  · exact (inT2_iff 1).mp normT2_gens.1
  · intro x y hx hy ihx ihy
    have h1 : normT2.all (fun y => inT2 (x * y)) = true :=
      (List.all_eq_true.mp normT2_mul_closed) x ihx
    exact (inT2_iff (x * y)).mp ((List.all_eq_true.mp h1) y ihy)
  · intro x hx ih
    exact (inT2_iff x⁻¹).mp ((List.all_eq_true.mp normT2_inv_closed) x ih)

private lemma e1Img_eq_normT1 : e1Img = normT1.map img := by
  simp only [e1Img, normT1, zTab_eq, yTab_eq, kTab_eq, zkTab_eq, tab_eq]

private lemma e2Img_eq_normT2 : e2Img = normT2.map img := by
  simp only [e2Img, normT2, zTab_eq, wTab_eq, kTab_eq, zkTab_eq, tab_eq]

private lemma e1Img_contains {g : Equiv.Perm (Fin 26)} (h : g ∈ normT1) :
    e1Img.contains (img g) = true := by
  rw [e1Img_eq_normT1]
  exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨g, h, rfl⟩)

private lemma e2Img_contains {g : Equiv.Perm (Fin 26)} (h : g ∈ normT2) :
    e2Img.contains (img g) = true := by
  rw [e2Img_eq_normT2]
  exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨g, h, rfl⟩)

private lemma e1_all_check (n : Equiv.Perm (Fin 26))
    (hz : n * modelZ * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))))
    (hy : n * modelY * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))))
    (hk : n * modelK * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26)))) :
    ([zTab, yTab, kTab].all fun e => e1Img.contains (conjImg n e)) = true := by
  refine List.all_eq_true.mpr ?_
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · have h : conjImg n zTab = img (n * modelZ * n⁻¹) := by
      rw [zTab_eq]
      exact (conjImg_eq_img_iff n modelZ (n * modelZ * n⁻¹)).mpr rfl
    rw [h]
    exact e1Img_contains (mem_normT1 hz)
  · have h : conjImg n yTab = img (n * modelY * n⁻¹) := by
      rw [yTab_eq]
      exact (conjImg_eq_img_iff n modelY (n * modelY * n⁻¹)).mpr rfl
    rw [h]
    exact e1Img_contains (mem_normT1 hy)
  · have h : conjImg n kTab = img (n * modelK * n⁻¹) := by
      rw [kTab_eq]
      exact (conjImg_eq_img_iff n modelK (n * modelK * n⁻¹)).mpr rfl
    rw [h]
    exact e1Img_contains (mem_normT1 hk)

private lemma e2_all_check (n : Equiv.Perm (Fin 26))
    (hz : n * modelZ * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))))
    (hw : n * (modelX ^ 2 * modelY) * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))))
    (hk : n * modelK * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26)))) :
    ([zTab, wTab, kTab].all fun e => e2Img.contains (conjImg n e)) = true := by
  refine List.all_eq_true.mpr ?_
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · have h : conjImg n zTab = img (n * modelZ * n⁻¹) := by
      rw [zTab_eq]
      exact (conjImg_eq_img_iff n modelZ (n * modelZ * n⁻¹)).mpr rfl
    rw [h]
    exact e2Img_contains (mem_normT2 hz)
  · have h : conjImg n wTab = img (n * (modelX ^ 2 * modelY) * n⁻¹) := by
      rw [wTab_eq]
      exact (conjImg_eq_img_iff n (modelX ^ 2 * modelY)
        (n * (modelX ^ 2 * modelY) * n⁻¹)).mpr rfl
    rw [h]
    exact e2Img_contains (mem_normT2 hw)
  · have h : conjImg n kTab = img (n * modelK * n⁻¹) := by
      rw [kTab_eq]
      exact (conjImg_eq_img_iff n modelK (n * modelK * n⁻¹)).mpr rfl
    rw [h]
    exact e2Img_contains (mem_normT2 hk)

theorem model_norm_one
    {n : Equiv.Perm (Fin 26)}
    (hn : n ∈ QA.originalSubgroup)
    (hz : n * modelZ * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))))
    (hy : n * modelY * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))))
    (hk : n * modelK * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26)))) :
    n * modelK * n⁻¹ = modelK := by
  have hn' : norm1B n = true := forall_of_all QA QA_ok all_norm1_total n hn
  have hall := e1_all_check n hz hy hk
  unfold norm1B at hn'
  rw [hall, Bool.not_true, Bool.false_or] at hn'
  have hk' : conjImg n kTab = img kTab := by simpa using hn'
  have h := (conjImg_eq_img_iff n kTab kTab).mp hk'
  simpa [kTab_eq] using h

theorem model_norm_two
    {n : Equiv.Perm (Fin 26)}
    (hn : n ∈ QA.originalSubgroup)
    (hz : n * modelZ * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))))
    (hw : n * (modelX ^ 2 * modelY) * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))))
    (hk : n * modelK * n⁻¹ ∈
      Subgroup.closure ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26)))) :
    n * (modelZ * modelK) * n⁻¹ = modelZ * modelK := by
  have hn' : norm2B n = true := forall_of_all QA QA_ok all_norm2_total n hn
  have hall := e2_all_check n hz hw hk
  unfold norm2B at hn'
  rw [hall, Bool.not_true, Bool.false_or] at hn'
  have hzk' : conjImg n zkTab = img zkTab := by simpa using hn'
  have h := (conjImg_eq_img_iff n zkTab zkTab).mp hzk'
  simpa [zkTab_eq] using h

end CFSG.OddStandard.SmallF3.L33
