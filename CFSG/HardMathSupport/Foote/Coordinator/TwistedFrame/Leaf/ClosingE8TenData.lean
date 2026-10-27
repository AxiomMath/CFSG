module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.LAData
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenDataK

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

@[expose] def simpIdx : List (Fin Tag.E8.rank) := [0, 1, 2, 3, 5, 6]

@[expose] def simp6 : List (Fin Tag.E8.rank → ℤ) := simpIdx.map fun j => Pi.single j 1

@[expose] def gens12 : List (Fin Tag.E8.rank → ℤ) := simp6 ++ simp6.map fun γ => -γ

@[expose] def typ (γ ν : Fin Tag.E8.rank → ℤ) : ℤ :=
  (if ν - γ ∈ rootFinset Tag.E8 then 1 else 0) - (if ν + γ ∈ rootFinset Tag.E8 then 1 else 0)

@[expose] def typVec (ν : Fin Tag.E8.rank → ℤ) : List ℤ := simp6.map fun γ => typ γ ν

@[expose] def cls (ν : Fin Tag.E8.rank → ℤ) : ℤ := ν 4 % 5

@[expose] def descendStep (ν : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  match simp6.find? (fun γ => decide (ν - γ ∈ mRoots)) with
  | some γ => ν - γ
  | none => ν

@[expose] def lowOf (ν : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ := descendStep^[10] ν

@[expose] def lowRep (k : ℤ) : Fin Tag.E8.rank → ℤ :=
  if k = 1 then ![0, 0, 0, 0, 1, 1, 1, 1]
  else if k = 2 then ![0, 1, 1, 2, 2, 1, 1, 1]
  else if k = 3 then ![1, 1, 2, 3, 3, 2, 1, 1]
  else ![1, 2, 2, 4, 4, 3, 2, 1]

theorem gens12_data : ∀ γ ∈ gens12, γ ∈ rootFinset Tag.E8 ∧ γ 7 = 0 ∧ γ 4 = 0 := by
  simp only [e8tK_mem_iff]
  decide +kernel

theorem simp6_sub : ∀ γ ∈ simp6, γ ∈ gens12 ∧ -γ ∈ gens12 := by decide +kernel

theorem typVec_nodup : (deg1Roots.val.map typVec).Nodup := by
  have h7 : ∀ l ∈ e8tK_deg1L, ∀ γ ∈ simp6, (e8tK_vec l - γ) 7 = 1 ∧ (e8tK_vec l + γ) 7 = 1 := by
    have hb : (e8tK_deg1L.all fun l => simp6.all fun γ =>
        (e8tK_vec l - γ) 7 == 1 && (e8tK_vec l + γ) 7 == 1) = true := by
      decide +kernel
    intro l hl γ hγ
    have h := List.all_eq_true.1 (List.all_eq_true.1 hb l hl) γ hγ
    simpa only [Bool.and_eq_true, beq_iff_eq] using h
  have hG : ∀ l ∈ e8tK_deg1L, typVec (e8tK_vec l) = simp6.map fun γ =>
      (bif e8tK_deg1L.contains (List.ofFn (e8tK_vec l - γ)) then 1 else 0) -
        (bif e8tK_deg1L.contains (List.ofFn (e8tK_vec l + γ)) then 1 else 0) := by
    intro l hl
    rw [typVec]
    refine List.map_congr_left fun γ hγ => ?_
    simp only [typ, e8tK_mem_deg1 (h7 l hl γ hγ).1, e8tK_mem_deg1 (h7 l hl γ hγ).2,
      ← List.contains_iff_mem, cond_eq_if]
  have hc : (e8tK_deg1L.map (fun l => simp6.map fun γ =>
      (bif e8tK_deg1L.contains (List.ofFn (e8tK_vec l - γ)) then (1 : ℤ) else 0) -
        (bif e8tK_deg1L.contains (List.ofFn (e8tK_vec l + γ)) then 1 else 0)) == e8tK_tvL) =
      true := by
    decide +kernel
  have hn : (e8tK_deg1L.map fun l => typVec (e8tK_vec l)).Nodup := by
    rw [List.map_congr_left hG, beq_iff_eq.1 hc]
    exact e8tK_tvL_nodup
  rw [Multiset.nodup_map_iff_inj_on deg1Roots.nodup]
  intro x hx y hy hxy
  rw [Finset.mem_val] at hx hy
  have hx' := e8tK_deg1_iff.1 hx
  have hy' := e8tK_deg1_iff.1 hy
  have hxy' : typVec (e8tK_vec (List.ofFn x)) = typVec (e8tK_vec (List.ofFn y)) := by
    rw [e8tK_vec_ofFn, e8tK_vec_ofFn]
    exact hxy
  exact List.ofFn_injective (List.inj_on_of_nodup_map hn hx' hy' hxy')

theorem typ_excl : ∀ ν ∈ deg1Roots, ∀ γ ∈ simp6,
    ¬(ν - γ ∈ rootFinset Tag.E8 ∧ ν + γ ∈ rootFinset Tag.E8) := by
  have hb : (e8tK_deg1L.all fun l => simp6.all fun γ =>
      (e8tK_vec l - γ) 7 == 1 && (e8tK_vec l + γ) 7 == 1 &&
        !(e8tK_deg1L.contains (List.ofFn (e8tK_vec l - γ)) &&
          e8tK_deg1L.contains (List.ofFn (e8tK_vec l + γ)))) = true := by
    decide +kernel
  intro ν hν γ hγ
  have hl := e8tK_deg1_iff.1 hν
  have h := List.all_eq_true.1 (List.all_eq_true.1 hb _ hl) γ hγ
  rw [e8tK_vec_ofFn, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [e8tK_mem_deg1 h1, e8tK_mem_deg1 h2]
  rintro ⟨m1, m2⟩
  rw [List.contains_iff_mem.2 m1, List.contains_iff_mem.2 m2] at h3
  exact absurd h3 (by decide)

theorem gens12_lx : ∀ γ ∈ gens12, γ ∈ lxRoots := by
  simp only [e8tK_lx_iff]
  decide +kernel

theorem mRoots_cls : ∀ μ ∈ mRoots, cls μ = 1 ∨ cls μ = 2 ∨ cls μ = 3 ∨ cls μ = 4 := by
  exact e8tK_forall_of e8tK_m_iff.1 (Q := fun μ => cls μ = 1 ∨ cls μ = 2 ∨ cls μ = 3 ∨ cls μ = 4)
    (by decide +kernel)

theorem descendStep_spec : ∀ ν ∈ mRoots, descendStep ν = ν ∨
    ∃ γ ∈ simp6, ν - γ ∈ mRoots ∧ descendStep ν = ν - γ := by
  have hd : descendStep = fun ν =>
      (simp6.find? fun γ => decide (List.ofFn (ν - γ) ∈ e8tK_mL)).elim ν fun γ => ν - γ := by
    funext ν
    have hf : (fun γ : Fin Tag.E8.rank → ℤ => decide (ν - γ ∈ mRoots)) =
        fun γ : Fin Tag.E8.rank → ℤ => decide (List.ofFn (ν - γ) ∈ e8tK_mL) :=
      funext fun γ => decide_eq_decide.2 e8tK_m_iff
    unfold descendStep
    rw [hf]
    cases simp6.find? fun γ => decide (List.ofFn (ν - γ) ∈ e8tK_mL) <;> rfl
  intro ν _
  rw [hd]
  beta_reduce
  cases h : simp6.find? fun γ => decide (List.ofFn (ν - γ) ∈ e8tK_mL) with
  | none => exact Or.inl rfl
  | some γ =>
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    exact Or.inr ⟨γ, List.mem_of_find?_eq_some h, e8tK_m_iff.2 hp, rfl⟩

theorem lowOf_eq : ∀ ν ∈ mRoots, lowOf ν = lowRep (cls ν) := by
  have hd : descendStep = fun ν =>
      (simp6.find? fun γ => decide (List.ofFn (ν - γ) ∈ e8tK_mL)).elim ν fun γ => ν - γ := by
    funext ν
    have hf : (fun γ : Fin Tag.E8.rank → ℤ => decide (ν - γ ∈ mRoots)) =
        fun γ : Fin Tag.E8.rank → ℤ => decide (List.ofFn (ν - γ) ∈ e8tK_mL) :=
      funext fun γ => decide_eq_decide.2 e8tK_m_iff
    unfold descendStep
    rw [hf]
    cases simp6.find? fun γ => decide (List.ofFn (ν - γ) ∈ e8tK_mL) <;> rfl
  have hs : (e8tK_mL.all fun l => e8tK_mL.contains (e8tK_nx l) &&
      List.ofFn ((simp6.find? fun γ => decide (List.ofFn (e8tK_vec l - γ) ∈ e8tK_mL)).elim
        (e8tK_vec l) fun γ => e8tK_vec l - γ) == e8tK_nx l) = true := by
    decide +kernel
  have hr : (e8tK_mL.all fun l =>
      List.ofFn (lowRep (cls (e8tK_vec l))) == e8tK_nx^[10] l) = true := by
    decide +kernel
  have hstep : ∀ l ∈ e8tK_mL,
      e8tK_nx l ∈ e8tK_mL ∧ descendStep (e8tK_vec l) = e8tK_vec (e8tK_nx l) := by
    intro l hl
    have h1 := List.all_eq_true.1 hs l hl
    rw [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h1
    refine ⟨h1.1, ?_⟩
    rw [hd, ← h1.2, e8tK_vec_ofFn]
  refine e8tK_forall_of e8tK_m_iff.1 (Q := fun ν => lowOf ν = lowRep (cls ν)) ?_
  intro l hl
  beta_reduce
  have h2 := List.all_eq_true.1 hr l hl
  rw [beq_iff_eq] at h2
  rw [lowOf, e8tK_iter hstep 10 l hl, ← h2, e8tK_vec_ofFn]

theorem no_string : ∀ μ ∈ deg1Roots, ∀ γ ∈ lxRoots,
    μ + γ ∈ rootFinset Tag.E8 → μ + γ + γ ∉ rootFinset Tag.E8 := by
  have hb : (e8tK_deg1L.all fun l => e8tK_lxL.all fun n =>
      !(e8tK_deg1L.contains (List.ofFn (e8tK_vec l + e8tK_vec n)) &&
        e8tK_deg1L.contains (List.ofFn (e8tK_vec l + e8tK_vec n + e8tK_vec n)))) = true := by
    decide +kernel
  have h : ∀ l ∈ e8tK_deg1L, ∀ n ∈ e8tK_lxL, List.ofFn (e8tK_vec l + e8tK_vec n) ∈ e8tK_deg1L →
      List.ofFn (e8tK_vec l + e8tK_vec n + e8tK_vec n) ∉ e8tK_deg1L := by
    intro l hl n hn m1 m2
    have h3 := List.all_eq_true.1 (List.all_eq_true.1 hb l hl) n hn
    rw [List.contains_iff_mem.2 m1, List.contains_iff_mem.2 m2] at h3
    exact absurd h3 (by decide)
  intro μ hμ γ hγ h1
  have hμ7 : μ 7 = 1 := (Finset.mem_filter.1 hμ).2
  have hγ7 : γ 7 = 0 := (Finset.mem_filter.1 hγ).2.1
  have e1 : (μ + γ) 7 = 1 := by rw [Pi.add_apply, hμ7, hγ7, add_zero]
  have e2 : (μ + γ + γ) 7 = 1 := by rw [Pi.add_apply, e1, hγ7, add_zero]
  have h2 := h _ (e8tK_deg1_iff.1 hμ) _ (e8tK_lx_iff.1 hγ)
  rw [e8tK_vec_ofFn, e8tK_vec_ofFn] at h2
  rw [e8tK_mem_deg1 e1] at h1
  rw [e8tK_mem_deg1 e2]
  exact h2 h1

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
