module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalPerm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A9Local

open Equiv CFSG.Open

open scoped Pointwise

namespace NrmMax

theorem zmod_three_cases (z w u : ZMod 3) (h : z ≠ w) : u = z ∨ u = w ∨ u = w + (w - z) := by
  revert z w u
  decide

theorem zmod_three_cases_sub (i j l : ZMod 3) (h : i ≠ j) :
    l = i ∨ l = j ∨ l = j + (j - i) := by
  revert i j l
  decide

theorem zmod_three_cases_nat (m : ZMod 3) : m = 0 ∨ m = 1 ∨ m = 2 := by
  revert m
  decide

theorem zmod_three_cases_one (v u : ZMod 3) : u = v ∨ u = v + 1 ∨ u = v + 1 + 1 := by
  revert u v
  decide

theorem zmod_three_inj_translate (γ : ZMod 3 → ZMod 3) (hγ : Function.Injective γ)
    (c y : ZMod 3) : γ (y + c) = γ y + (γ c - γ 0) := by
  revert c y
  revert γ
  decide +kernel

theorem affPerm_zero_mem {Y' : Subgroup (Perm Pt)} (hτ : blockShift ∈ Y') (m : ZMod 3) :
    affPerm m 0 ∈ Y' := by
  rcases zmod_three_cases_nat m with rfl | rfl | rfl
  · rw [affPerm_one]
    exact one_mem _
  · exact hτ
  · have : affPerm 2 0 = blockShift * blockShift := by
      ext p
      · simp [blockShift]
        ring
      · simp [blockShift]
    rw [this]
    exact mul_mem hτ hτ

theorem isPretransitive_of_le {Y' : Subgroup (Perm Pt)} (hB : baseGroup ≤ Y')
    (hτ : blockShift ∈ Y') : MulAction.IsPretransitive Y' Pt := by
  refine ⟨fun x y => ?_⟩
  refine ⟨⟨shiftPerm (fun k => if k = y.1 then y.2 - x.2 else 0) * affPerm (y.1 - x.1) 0,
    mul_mem (hB (shiftPerm_mem_baseGroup _)) (affPerm_zero_mem hτ _)⟩, ?_⟩
  obtain ⟨i, z⟩ := x
  obtain ⟨j, w⟩ := y
  change shiftPerm (fun k => if k = j then w - z else 0) (affPerm (j - i) 0 (i, z)) = (j, w)
  simp

theorem apply_mem_of_isBlock {Y' : Subgroup (Perm Pt)} {C : Set Pt}
    (hC : MulAction.IsBlock Y' C) {g : Perm Pt} (hg : g ∈ Y') {a : Pt} (ha : a ∈ C)
    (hga : g a ∈ C) {y : Pt} (hy : y ∈ C) : g y ∈ C := by
  have h := hC.smul_eq_of_mem (g := (⟨g, hg⟩ : Y')) ha hga
  have h' : (⟨g, hg⟩ : Y') • y ∈ (⟨g, hg⟩ : Y') • C := Set.smul_mem_smul_set hy
  rw [h] at h'
  exact h'

theorem block_subset_of_fst_ne {Y' : Subgroup (Perm Pt)} (hB : baseGroup ≤ Y') {C : Set Pt}
    (hC : MulAction.IsBlock Y' C) {x y : Pt} (hx : x ∈ C) (hy : y ∈ C) (hxy : x.1 ≠ y.1)
    (u : ZMod 3) : (y.1, u) ∈ C := by
  have hg : shiftPerm (fun k => if k = y.1 then 1 else 0) ∈ Y' :=
    hB (shiftPerm_mem_baseGroup _)
  have hgx : shiftPerm (fun k => if k = y.1 then 1 else 0) x = x := by
    simp [hxy]
  have h1 : shiftPerm (fun k => if k = y.1 then 1 else 0) y ∈ C :=
    apply_mem_of_isBlock hC hg hx (by rw [hgx]; exact hx) hy
  have h2 : shiftPerm (fun k => if k = y.1 then 1 else 0)
      (shiftPerm (fun k => if k = y.1 then 1 else 0) y) ∈ C :=
    apply_mem_of_isBlock hC hg hx (by rw [hgx]; exact hx) h1
  simp only [shiftPerm_apply, ite_true] at h1 h2
  rcases zmod_three_cases_one y.2 u with rfl | rfl | rfl
  · exact hy
  · exact h1
  · simpa [add_assoc] using h2

theorem eq_univ_of_fst_ne {Y' : Subgroup (Perm Pt)} (hB : baseGroup ≤ Y')
    (hτ : blockShift ∈ Y') {C : Set Pt} (hC : MulAction.IsBlock Y' C) {x y : Pt} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : x.1 ≠ y.1) : C = Set.univ := by
  have hy' := block_subset_of_fst_ne hB hC hx hy hxy
  have hx' := block_subset_of_fst_ne hB hC hy hx hxy.symm
  have hg : affPerm (y.1 - x.1) 0 ∈ Y' := affPerm_zero_mem hτ _
  have hga : affPerm (y.1 - x.1) 0 (x.1, 0) ∈ C := by
    simpa using hy' 0
  have h3 : ∀ u, (y.1 + (y.1 - x.1), u) ∈ C := fun u => by
    simpa using apply_mem_of_isBlock hC hg (hx' 0) hga (hy' u)
  refine Set.eq_univ_of_forall fun ⟨l, u⟩ => ?_
  rcases zmod_three_cases_sub x.1 y.1 l hxy with rfl | rfl | rfl
  · exact hx' u
  · exact hy' u
  · exact h3 u

theorem block_subset_of_ne {Y' : Subgroup (Perm Pt)} (hB : baseGroup ≤ Y') {C : Set Pt}
    (hC : MulAction.IsBlock Y' C) {x y : Pt} (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y)
    (hfst : x.1 = y.1) (u : ZMod 3) : (x.1, u) ∈ C := by
  obtain ⟨i, z⟩ := x
  obtain ⟨j, w⟩ := y
  simp only at hfst
  subst hfst
  have hzw : z ≠ w := fun h => hne (by rw [h])
  have hg : shiftPerm (fun k => if k = i then w - z else 0) ∈ Y' :=
    hB (shiftPerm_mem_baseGroup _)
  have h1 : shiftPerm (fun k => if k = i then w - z else 0) (i, z) = (i, w) := by simp
  have h2 : shiftPerm (fun k => if k = i then w - z else 0) (i, w) ∈ C :=
    apply_mem_of_isBlock hC hg hx (by rw [h1]; exact hy) hy
  simp only [shiftPerm_apply, ite_true] at h2
  rcases zmod_three_cases z w u hzw with rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact h2

theorem exists_eq_fiber_of_isBlock {Y' : Subgroup (Perm Pt)} (hB : baseGroup ≤ Y')
    (hτ : blockShift ∈ Y') {C : Set Pt} (hC : MulAction.IsBlock Y' C)
    (hnt : ¬ MulAction.IsTrivialBlock C) : ∃ i, C = {p : Pt | p.1 = i} := by
  rw [MulAction.IsTrivialBlock, not_or] at hnt
  obtain ⟨hns, hnu⟩ := hnt
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.1 hns
  have hfst : ∀ p ∈ C, ∀ q ∈ C, p.1 = q.1 := fun p hp q hq => by
    by_contra h
    exact hnu (eq_univ_of_fst_ne hB hτ hC hp hq h)
  refine ⟨x.1, Set.ext fun p => ⟨fun hp => hfst p hp x hx, fun hp => ?_⟩⟩
  have h := block_subset_of_ne hB hC hx hy hxy (hfst x hx y hy) p.2
  have hp' : p.1 = x.1 := hp
  have hpx : p = (x.1, p.2) := Prod.ext hp' rfl
  rw [hpx]
  exact h

theorem conj_shiftPerm_apply {g : Perm Pt}
    (hg : ∀ p q : Pt, p.1 = q.1 → (g p).1 = (g q).1)
    (hg' : ∀ p q : Pt, p.1 = q.1 → (g⁻¹ p).1 = (g⁻¹ q).1) (f : ZMod 3 → ZMod 3)
    (j w : ZMod 3) :
    (g * shiftPerm f * g⁻¹) (j, w) = (j, w + ((g * shiftPerm f * g⁻¹) (j, 0)).2) := by
  have e1 : g (g⁻¹ (j, w)) = (j, w) := by simp
  have e2 : g (g⁻¹ (j, 0)) = (j, 0) := by simp
  have e3 : (g⁻¹ (j, w)).1 = (g⁻¹ (j, 0)).1 := hg' _ _ rfl
  simp only [Perm.mul_apply]
  generalize g⁻¹ (j, w) = a at *
  generalize g⁻¹ (j, 0) = b at *
  obtain ⟨i, y⟩ := a
  obtain ⟨i', y'⟩ := b
  simp only at e3
  subst e3
  have hγ : ∀ z, g (i, z) = (j, (g (i, z)).2) := fun z => by
    ext
    · simpa [e1] using hg (i, z) (i, y) rfl
    · rfl
  have hinj : Function.Injective fun z => (g (i, z)).2 := by
    intro z z' h
    have := g.injective (a₁ := (i, z)) (a₂ := (i, z'))
      (by rw [hγ z, hγ z']; simp only at h; rw [h])
    simpa using this
  have key := zmod_three_inj_translate _ hinj
  have h1 : (g (i, y)).2 = w := by rw [e1]
  have h2 : (g (i, y')).2 = 0 := by rw [e2]
  simp only [shiftPerm_apply]
  rw [hγ (y + f i), hγ (y' + f i)]
  simp only [key, h1, h2]
  simp

theorem exists_conj_shiftPerm {g : Perm Pt}
    (hg : ∀ p q : Pt, p.1 = q.1 → (g p).1 = (g q).1)
    (hg' : ∀ p q : Pt, p.1 = q.1 → (g⁻¹ p).1 = (g⁻¹ q).1) (f : ZMod 3 → ZMod 3) :
    ∃ f', g * shiftPerm f * g⁻¹ = shiftPerm f' :=
  ⟨fun j => ((g * shiftPerm f * g⁻¹) (j, 0)).2,
    Equiv.ext fun ⟨j, w⟩ => conj_shiftPerm_apply hg hg' f j w⟩

theorem mem_nrm_of_fibers {g : Perm Pt}
    (hg : ∀ p q : Pt, p.1 = q.1 → (g p).1 = (g q).1)
    (hg' : ∀ p q : Pt, p.1 = q.1 → (g⁻¹ p).1 = (g⁻¹ q).1) : g ∈ nrm := by
  refine mem_nrm_of_conj (exists_conj_shiftPerm hg hg') fun f => ?_
  simpa using exists_conj_shiftPerm (g := g⁻¹) hg' (by simpa using hg) f

theorem le_nrm_of_not_isPreprimitive {Y' : Subgroup (Perm Pt)} (hB : baseGroup ≤ Y')
    (hτ : blockShift ∈ Y') (hnp : ¬ MulAction.IsPreprimitive Y' Pt) : Y' ≤ nrm := by
  have := isPretransitive_of_le hB hτ
  obtain ⟨C, hC, hnt⟩ : ∃ C : Set Pt, MulAction.IsBlock Y' C ∧ ¬ MulAction.IsTrivialBlock C := by
    by_contra hcon
    refine hnp (MulAction.IsPreprimitive.of_isTrivialBlock_base (0, 0) fun {C} _ hC => ?_)
    by_contra hC'
    exact hcon ⟨C, hC, hC'⟩
  obtain ⟨i₀, rfl⟩ := exists_eq_fiber_of_isBlock hB hτ hC hnt
  have hfib : ∀ i, MulAction.IsBlock Y' {p : Pt | p.1 = i} := fun i => by
    have h := hC.translate (⟨affPerm (i - i₀) 0, affPerm_zero_mem hτ _⟩ : Y')
    convert h using 1
    ext ⟨j, z⟩
    simp [Set.mem_smul_set, eq_comm]
  have hfib_nt : ∀ i, ¬ MulAction.IsTrivialBlock {p : Pt | p.1 = i} := fun i => by
    rw [MulAction.IsTrivialBlock, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := h (show ((i, 0) : Pt) ∈ {p : Pt | p.1 = i} from rfl)
        (show ((i, 1) : Pt) ∈ {p : Pt | p.1 = i} from rfl)
      simp at this
    · have := h.symm ▸ (Set.mem_univ ((i + 1, 0) : Pt))
      simp at this
  have hmap : ∀ g ∈ Y', ∀ p q : Pt, p.1 = q.1 → (g p).1 = (g q).1 := by
    intro g hg p q hpq
    have h := (hfib p.1).translate (⟨g, hg⟩ : Y')
    have hnt' : ¬ MulAction.IsTrivialBlock ((⟨g, hg⟩ : Y') • {r : Pt | r.1 = p.1}) :=
      fun h' => hfib_nt p.1 ((MulAction.IsTrivialBlock.smul_iff _).1 h')
    obtain ⟨j, hj⟩ := exists_eq_fiber_of_isBlock hB hτ h hnt'
    have hp : g p ∈ (⟨g, hg⟩ : Y') • {r : Pt | r.1 = p.1} := Set.smul_mem_smul_set rfl
    have hq : g q ∈ (⟨g, hg⟩ : Y') • {r : Pt | r.1 = p.1} := Set.smul_mem_smul_set hpq.symm
    rw [hj] at hp hq
    exact hp.trans hq.symm
  intro g hg
  exact mem_nrm_of_fibers (hmap g hg) (hmap g⁻¹ (inv_mem hg))

@[expose] def negAll : Perm Pt where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem negAll_apply (p : Pt) : negAll p = (p.1, -p.2) := rfl

theorem negAll_inv : negAll⁻¹ = negAll := by
  ext p <;> simp [Perm.inv_def, negAll]

theorem negAll_conj_shiftPerm (f : ZMod 3 → ZMod 3) :
    negAll * shiftPerm f * negAll⁻¹ = shiftPerm (fun i => - f i) := by
  rw [negAll_inv]
  ext p
  · simp
  · simp [add_comm]

theorem negAll_mem_nrm : negAll ∈ nrm :=
  mem_nrm_of_conj (fun f => ⟨_, negAll_conj_shiftPerm f⟩)
    (fun f => ⟨_, by rw [negAll_inv]; exact negAll_conj_shiftPerm f⟩)

theorem sign_negAll : Perm.sign negAll = -1 := by
  decide +kernel

theorem isThreeCycle_shiftPerm_single :
    (shiftPerm (fun k => if k = 0 then 1 else 0)).IsThreeCycle := by
  have h : shiftPerm (fun k => if k = 0 then 1 else 0) =
      swap ((0 : ZMod 3), (0 : ZMod 3)) (0, 2) * swap (0, 0) (0, 1) := by
    rw [Equiv.ext_iff]
    decide +kernel
  rw [h]
  exact Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem eq_of_isPreprimitive {Y Y' : Subgroup (Perm Pt)} (hA : alternatingGroup Pt ≤ Y)
    (h1 : Y ⊓ nrm ≤ Y') (h2 : Y' ≤ Y) (hB : baseGroup ≤ Y')
    (hprim : MulAction.IsPreprimitive Y' Pt) : Y' = Y := by
  have hAY' : alternatingGroup Pt ≤ Y' :=
    Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
      isThreeCycle_shiftPerm_single (hB (shiftPerm_mem_baseGroup _))
  refine le_antisymm h2 fun y hy => ?_
  rcases Int.units_eq_one_or (Perm.sign y) with hs | hs
  · exact hAY' (Perm.mem_alternatingGroup.2 hs)
  · have hneg : negAll * y⁻¹ ∈ alternatingGroup Pt := by
      rw [Perm.mem_alternatingGroup, map_mul, map_inv, hs, sign_negAll]
      decide
    have hnY : negAll ∈ Y := by
      simpa using mul_mem (hA hneg) hy
    have hnY' : negAll ∈ Y' := h1 ⟨hnY, negAll_mem_nrm⟩
    have hneg' : y * negAll⁻¹ ∈ alternatingGroup Pt := by
      rw [Perm.mem_alternatingGroup, map_mul, map_inv, hs, sign_negAll]
      decide
    simpa using mul_mem (hAY' hneg') hnY'

end NrmMax

theorem le_nrm_or_eq {Y Y' : Subgroup (Perm Pt)} (hA : alternatingGroup Pt ≤ Y)
    (h1 : Y ⊓ nrm ≤ Y') (h2 : Y' ≤ Y) : Y' ≤ nrm ∨ Y' = Y := by
  have hB : baseGroup ≤ Y' := fun g hg =>
    h1 ⟨hA (baseGroup_le_alternatingGroup hg), baseGroup_le_nrm hg⟩
  have hτ : blockShift ∈ Y' := h1 ⟨hA blockShift_mem_alternatingGroup, blockShift_mem_nrm⟩
  by_cases hprim : MulAction.IsPreprimitive Y' Pt
  · exact Or.inr (NrmMax.eq_of_isPreprimitive hA h1 h2 hB hprim)
  · exact Or.inl (NrmMax.le_nrm_of_not_isPreprimitive hB hτ hprim)

end CFSG.AGLEmbedding.A9Local
