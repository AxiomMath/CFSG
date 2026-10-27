module

public import CFSG.LieType.Ree.LargeReeEightCollection

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree.ReeTag

section Exclusion

variable {K : Type} [Field K]

abbrev rootProd
    (l : List ((Fin F4.tag.rank → ℤ) × K)) : ModGL F4.tag K :=
  (l.map fun p => pinnedX F4.tag K p.1 p.2).prod

@[expose] def rootParam (l : List ((Fin F4.tag.rank → ℤ) × K)) (α : Fin F4.tag.rank → ℤ) : K :=
  (l.lookup α).getD 0

theorem rootParam_cons_self (p : (Fin F4.tag.rank → ℤ) × K)
    (l : List ((Fin F4.tag.rank → ℤ) × K)) : rootParam (p :: l) p.1 = p.2 := by
  obtain ⟨α, c⟩ := p
  simp [rootParam, List.lookup]

theorem rootParam_cons_of_ne {p : (Fin F4.tag.rank → ℤ) × K}
    {l : List ((Fin F4.tag.rank → ℤ) × K)} {α : Fin F4.tag.rank → ℤ} (h : α ≠ p.1) :
    rootParam (p :: l) α = rootParam l α := by
  obtain ⟨β, c⟩ := p
  have : (α == β) = false := by simpa using h
  simp [rootParam, List.lookup, this]

theorem rootParam_of_not_mem {l : List ((Fin F4.tag.rank → ℤ) × K)} {α : Fin F4.tag.rank → ℤ}
    (h : α ∉ l.map Prod.fst) : rootParam l α = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [rootParam_cons_of_ne h.1, ih h.2]

theorem rootParam_of_mem {l : List ((Fin F4.tag.rank → ℤ) × K)} (hnd : (l.map Prod.fst).Nodup)
    {p : (Fin F4.tag.rank → ℤ) × K} (hp : p ∈ l) : rootParam l p.1 = p.2 := by
  induction l with
  | nil => exact absurd hp List.not_mem_nil
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hp with rfl | hp
    · exact rootParam_cons_self _ _
    · have hne : p.1 ≠ q.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hp)
      rw [rootParam_cons_of_ne hne, ih hnd.2 hp]

theorem rootProd_eq_map_rootParam
    {l : List ((Fin F4.tag.rank → ℤ) × K)}
    (hnd : (l.map Prod.fst).Nodup) :
    rootProd l = ((l.map Prod.fst).map fun α => pinnedX F4.tag K α (rootParam l α)).prod := by
  rw [List.map_map]
  exact congrArg List.prod (List.map_congr_left fun p hp => by
    simp only [Function.comp_apply, rootParam_of_mem hnd hp])

theorem prod_map_pinnedX_zero
    (L : List (Fin F4.tag.rank → ℤ)) {c : (Fin F4.tag.rank → ℤ) → K}
    (hc : ∀ α ∈ L, c α = 0) : (L.map fun α => pinnedX F4.tag K α (c α)).prod = 1 := by
  induction L with
  | nil => rfl
  | cons α L ih =>
    rw [List.map_cons, List.prod_cons, hc α List.mem_cons_self, pinnedX_zero,
      ih fun β hβ => hc β (List.mem_cons_of_mem _ hβ), one_mul]

theorem rootProd_filter_mul
    {l : List ((Fin F4.tag.rank → ℤ) × K)}
    (hcomm : l.Pairwise fun p q => Commute (pinnedX F4.tag K p.1 p.2) (pinnedX F4.tag K q.1 q.2))
    (P : (Fin F4.tag.rank → ℤ) × K → Bool) :
    rootProd l = rootProd (l.filter P) * rootProd (l.filter fun p => !P p) := by
  have hperm := (List.filter_append_perm P l).map fun p => pinnedX F4.tag K p.1 p.2
  have hc : (l.map fun p => pinnedX F4.tag K p.1 p.2).Pairwise Commute := by
    rw [List.pairwise_map]
    exact hcomm
  rw [rootProd, hperm.symm.prod_eq' hc, List.map_append, List.prod_append]

theorem eq_zero_of_rootProd_mem_posUnipotent
    {l : List ((Fin F4.tag.rank → ℤ) × K)}
    (hnd : (l.map Prod.fst).Nodup) (hroot : ∀ p ∈ l, IsRoot F4.tag p.1)
    (hcomm : l.Pairwise fun p q => Commute (pinnedX F4.tag K p.1 p.2) (pinnedX F4.tag K q.1 q.2))
    (hU : rootProd l ∈ posUnipotent F4.tag K) :
    ∀ p ∈ l, height p.1 < 0 → p.2 = 0 := by
  classical
  set P : (Fin F4.tag.rank → ℤ) × K → Bool := fun p => decide (0 < height p.1) with hP
  set lp := l.filter P with hlp
  set ln := l.filter fun p => !P p with hln
  have hsplit := rootProd_filter_mul hcomm P
  have hpU : rootProd lp ∈ posUnipotent F4.tag K := by
    refine (posUnipotent F4.tag K).list_prod_mem fun g hg => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    obtain ⟨hpl, hpP⟩ := List.mem_filter.1 hp
    exact pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ 0 < height α})
      ⟨hroot p hpl, by simpa [hP] using hpP⟩ _
  have hnV : rootProd ln ∈ negUnipotent F4.tag K := by
    refine (negUnipotent F4.tag K).list_prod_mem fun g hg => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    obtain ⟨hpl, hpP⟩ := List.mem_filter.1 hp
    have h0 : ¬ 0 < height p.1 := by simpa [hP] using hpP
    exact pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ height α < 0})
      ⟨hroot p hpl, by have := (hroot p hpl).height_ne_zero; omega⟩ _
  have hnU : rootProd ln ∈ posUnipotent F4.tag K := by
    have e : rootProd ln = (rootProd lp)⁻¹ * rootProd l := by
      rw [hsplit, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem hpU) hU
  have h1 : rootProd ln = 1 := by
    have := Subgroup.mem_inf.2 ⟨hnU, hnV⟩
    rwa [CFSG.Blueprint.Chevalley.posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at this
  have hndn : (ln.map Prod.fst).Nodup := (hnd.sublist (List.filter_sublist.map _))
  have hinj := pinnedX_list_prod_injective_neg (R := K) (ln.map Prod.fst) hndn
    (fun α hα => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hα
      obtain ⟨hpl, hpP⟩ := List.mem_filter.1 hp
      have h0 : ¬ 0 < height p.1 := by simpa [hP] using hpP
      exact ⟨hroot p hpl, by have := (hroot p hpl).height_ne_zero; omega⟩)
    (rootParam ln) 0 (by
      rw [← rootProd_eq_map_rootParam hndn, h1]
      exact (prod_map_pinnedX_zero _ fun _ _ => rfl).symm)
  intro p hp hneg
  have hpn : p ∈ ln := List.mem_filter.2 ⟨hp, by simp [hP]; omega⟩
  rw [← rootParam_of_mem hndn hpn]
  exact hinj p.1 (List.mem_map_of_mem hpn)

theorem eq_zero_of_rootProd_eq
    {l l' : List ((Fin F4.tag.rank → ℤ) × K)}
    (hnd : (l.map Prod.fst).Nodup) (hnd' : (l'.map Prod.fst).Nodup)
    (hroot : ∀ p ∈ l, IsRoot F4.tag p.1) (hpos' : ∀ p ∈ l', IsRoot F4.tag p.1 ∧ 0 < height p.1)
    (hcomm : l.Pairwise fun p q => Commute (pinnedX F4.tag K p.1 p.2) (pinnedX F4.tag K q.1 q.2))
    (hcomm' : l'.Pairwise fun p q =>
      Commute (pinnedX F4.tag K p.1 p.2) (pinnedX F4.tag K q.1 q.2))
    (h : rootProd l = rootProd l') : ∀ p ∈ l, p.1 ∉ l'.map Prod.fst → p.2 = 0 := by
  classical
  have hU' : rootProd l' ∈ posUnipotent F4.tag K := by
    refine (posUnipotent F4.tag K).list_prod_mem fun g hg => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ 0 < height α}) (hpos' p hp) _
  have hneg := eq_zero_of_rootProd_mem_posUnipotent hnd hroot hcomm (h ▸ hU')
  set P : (Fin F4.tag.rank → ℤ) × K → Bool := fun p => decide (0 < height p.1) with hP
  set lp := l.filter P with hlp
  have hln1 : rootProd (l.filter fun p => !P p) = 1 := by
    refine (List.prod_eq_one fun g hg => ?_)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    obtain ⟨hpl, hpP⟩ := List.mem_filter.1 hp
    have h0 : ¬ 0 < height p.1 := by simpa [hP] using hpP
    rw [hneg p hpl (by have := (hroot p hpl).height_ne_zero; omega), pinnedX_zero]
  have hlp' : rootProd lp = rootProd l' := by
    rw [← h, rootProd_filter_mul hcomm P, hln1, mul_one]
  have hndp : (lp.map Prod.fst).Nodup := hnd.sublist (List.filter_sublist.map _)
  set L1 := lp.map Prod.fst with hL1
  set L2 := (l'.map Prod.fst).filter fun α => α ∉ L1 with hL2
  have hndL : (L1 ++ L2).Nodup := by
    refine List.nodup_append.2 ⟨hndp, (hnd'.sublist List.filter_sublist), fun α hα β hβ => ?_⟩
    rintro rfl
    exact of_decide_eq_true (List.mem_filter.1 hβ).2 hα
  have hposL : ∀ α ∈ L1 ++ L2, IsRoot F4.tag α ∧ 0 < height α := by
    intro α hα
    rcases List.mem_append.1 hα with hα | hα
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hα
      obtain ⟨hpl, hpP⟩ := List.mem_filter.1 hp
      exact ⟨hroot p hpl, by simpa [hP] using hpP⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hα).1
      exact hpos' p hp
  have e1 : ((L1 ++ L2).map fun α => pinnedX F4.tag K α (rootParam lp α)).prod = rootProd lp := by
    rw [List.map_append, List.prod_append, ← rootProd_eq_map_rootParam hndp,
      prod_map_pinnedX_zero L2 fun α hα => rootParam_of_not_mem
        (of_decide_eq_true (List.mem_filter.1 hα).2), mul_one]
  have e2 : ((L1 ++ L2).map fun α => pinnedX F4.tag K α (rootParam l' α)).prod = rootProd l' := by
    set L' := (L1 ++ L2).filter fun α => α ∈ l'.map Prod.fst with hL'
    have hfilt : ((L1 ++ L2).map fun α => pinnedX F4.tag K α (rootParam l' α)).prod =
        (L'.map fun α => pinnedX F4.tag K α (rootParam l' α)).prod :=
      LargeReeCover.list_prod_map_filter _ _ _ fun α _ hα => by
        rw [rootParam_of_not_mem (by simpa using hα), pinnedX_zero]
    have hperm : L'.Perm (l'.map Prod.fst) := by
      refine (List.perm_ext_iff_of_nodup (hndL.filter _) hnd').2 fun α => ?_
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro hα
        refine ⟨?_, hα⟩
        by_cases h1 : α ∈ L1
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_filter.2 ⟨hα, by simpa using h1⟩)
    have hc' : (L'.map fun α => pinnedX F4.tag K α (rootParam l' α)).Pairwise Commute := by
      rw [List.pairwise_map]
      refine (hndL.filter _).pairwise_of_forall_ne fun α hα β hβ hne => ?_
      obtain ⟨pa, hpa, rfl⟩ := List.mem_map.1 (of_decide_eq_true (List.mem_filter.1 hα).2)
      obtain ⟨pb, hpb, rfl⟩ := List.mem_map.1 (of_decide_eq_true (List.mem_filter.1 hβ).2)
      rw [rootParam_of_mem hnd' hpa, rootParam_of_mem hnd' hpb]
      have : Std.Symm fun p q : (Fin F4.tag.rank → ℤ) × K =>
          Commute (pinnedX F4.tag K p.1 p.2) (pinnedX F4.tag K q.1 q.2) :=
        ⟨fun _ _ h => h.symm⟩
      exact hcomm'.forall hpa hpb fun h => hne (h ▸ rfl)
    rw [hfilt, (hperm.map _).prod_eq' hc', ← rootProd_eq_map_rootParam hnd']
  have hinj := pinnedX_list_prod_injective (R := K) (L1 ++ L2) hndL hposL (rootParam lp)
    (rootParam l') (by rw [e1, e2, hlp'])
  intro p hp hnot
  by_cases hpos : 0 < height p.1
  · have hpp : p ∈ lp := List.mem_filter.2 ⟨hp, by simpa [hP] using hpos⟩
    rw [← rootParam_of_mem hndp hpp, hinj p.1 (List.mem_append_left _ (List.mem_map_of_mem hpp)),
      rootParam_of_not_mem hnot]
  · exact hneg p hp (by have := (hroot p hp).height_ne_zero; omega)

end Exclusion

end CFSG.LieType.Ree.LargeReeInvolution
