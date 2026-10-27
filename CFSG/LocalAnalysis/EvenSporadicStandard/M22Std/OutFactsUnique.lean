module

public import Certificates.Certificate24802
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsS0b

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.Blueprint.NativeSporadic

theorem tinv_tabP (σ : Equiv.Perm (Fin 22)) : tinv (tabP σ) = tabP σ⁻¹ := by
  have hnd : (tabP σ).Nodup := by
    rw [tabP, List.nodup_ofFn]
    intro i j h
    exact σ.injective (Fin.ext h)
  refine List.ext_getElem (by simp [tinv, length_tabP]) fun i h1 h2 => ?_
  have hi : i < 22 := by simpa [tinv] using h1
  have hlen : (tabP σ).length = 22 := length_tabP σ
  have hj : (σ⁻¹ ⟨i, hi⟩ : Fin 22).val < (tabP σ).length := by rw [hlen]; exact (σ⁻¹ _).2
  have hval : (tabP σ)[(σ⁻¹ ⟨i, hi⟩ : Fin 22).val]'hj = i := by
    have := getD_tabP σ (σ⁻¹ ⟨i, hi⟩)
    rw [List.getD_eq_getElem _ _ hj] at this
    rw [this]
    simp
  have hget : (tabP σ⁻¹)[i]'h2 = (σ⁻¹ ⟨i, hi⟩ : Fin 22).val := by
    have := getD_tabP σ⁻¹ ⟨i, hi⟩
    rwa [List.getD_eq_getElem _ _ h2] at this
  rw [hget]
  simp only [tinv, List.getElem_map, List.getElem_range]
  have := hnd.idxOf_getElem _ hj
  rw [hval] at this
  exact this


theorem autTab_conj_class (α β : MulAut (Carrier .M22)) :
    tmul (tmul (autTab α) (autTab β)) (tinv (autTab α)) = autTab (α * β * α⁻¹) := by
  rw [autTab_mul, autTab_mul, autTab_inv, autTab, tinv_tabP]

theorem mem_classTabs_iff (β : MulAut (Carrier .M22)) (l : Tab) :
    l ∈ classTabs s0Tabs (autTab β) ↔ ∃ α ∈ s0, autTab (α * β * α⁻¹) = l := by
  rw [classTabs, List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨α, hα, rfl⟩ := isTabsOf_s0.exists_mem a ha
    exact ⟨α, hα, (autTab_conj_class α β).symm⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨autTab α, (mem_s0_iff α).1 hα, autTab_conj_class α β⟩

theorem length_classTabs (β : MulAut (Carrier .M22)) :
    (classTabs s0Tabs (autTab β)).length = (autConjClass s0 β).ncard := by
  have hset : autConjClass s0 β = {γ | autTab γ ∈ classTabs s0Tabs (autTab β)} := by
    ext γ
    simp only [autConjClass, Set.mem_ofPred_eq, mem_classTabs_iff]
    constructor
    · rintro ⟨α, hα, rfl⟩
      exact ⟨α, hα, rfl⟩
    · rintro ⟨α, hα, h⟩
      exact ⟨α, hα, (autTab_injective h).symm⟩
  rw [hset]
  refine (ncard_preimage_mem_tabs autTab autTab_injective (classTabs s0Tabs (autTab β))
    (by unfold classTabs; exact List.nodup_dedup _) fun l hl => ?_).symm
  obtain ⟨α, -, hα⟩ := (mem_classTabs_iff β l).1 hl
  exact ⟨_, hα⟩

theorem conj_injective_m22 :
    Function.Injective (MulAut.conj : Carrier .M22 → MulAut (Carrier .M22)) :=
  fun y z h => tab_injective (by rw [← autTab_conj, ← autTab_conj, h])

theorem card_innerImage {F : Subgroup (Carrier .M22)} (hF : Nat.card F = 16) :
    Nat.card (innerImage (Carrier .M22) F) = 16 := by
  rw [innerImage, Subgroup.card_map_of_injective conj_injective_m22, hF]

theorem closure_class_eq {G : Type*} [Group G] [Finite G] (E : Subgroup G) (hE : Nat.card E = 16)
    (C : Set G) (hCE : C ⊆ E) (hC1 : (1 : G) ∉ C) (hC8 : C.ncard = 8) :
    Subgroup.closure C = E := by
  have hle : Subgroup.closure C ≤ E := (Subgroup.closure_le E).2 hCE
  have hsub : insert (1 : G) C ⊆ (Subgroup.closure C : Set G) := by
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hx
  have h9 : 9 ≤ Nat.card (Subgroup.closure C) := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : Nat.card (Subgroup.closure C) = (Subgroup.closure C : Set G).ncard :=
      Nat.card_coe_set_eq _
    rw [Set.ncard_insert_of_notMem hC1 (Set.toFinite _), hC8] at h1
    omega
  have hdvd : Nat.card (Subgroup.closure C) ∣ 16 := hE ▸ Subgroup.card_dvd_of_le hle
  have hle16 : Nat.card (Subgroup.closure C) ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  have h16 : Nat.card (Subgroup.closure C) = 16 := by
    generalize Nat.card (Subgroup.closure C) = n at h9 hdvd hle16
    interval_cases n <;> omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h16, hE])

theorem uniqOK_spec : uniqOK s0Tabs f1Tabs = true :=
  Certificates.certificate24802

theorem s0_unique {F : Subgroup (Carrier .M22)}
    (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1) (hFcard : Nat.card F = 16) :
    ∀ E : Subgroup (MulAut (Carrier .M22)), E ≤ s0 → (∀ α ∈ s0, ∀ β ∈ E, α * β * α⁻¹ ∈ E) →
      (∀ α ∈ E, ∀ β ∈ E, α * β = β * α) → (∀ α ∈ E, α * α = 1) → Nat.card E = 16 →
      (∀ γ ∈ s0, (∀ β ∈ E, γ * β = β * γ) → γ ∈ E) →
      (∃ β ∈ E, β ≠ 1 ∧ (autConjClass s0 β).ncard = 8) → E = innerImage (Carrier .M22) F := by
  intro E hES hEn hEc hEsq hEcard hEself ⟨a0, ha0E, ha01, ha08⟩
  have hCE : autConjClass s0 a0 ⊆ E := by
    rintro _ ⟨α, hα, rfl⟩
    exact hEn α hα a0 ha0E
  have hC1 : (1 : MulAut (Carrier .M22)) ∉ autConjClass s0 a0 := by
    rintro ⟨α, hα, h⟩
    apply ha01
    calc a0 = α⁻¹ * (α * a0 * α⁻¹) * α := by group
      _ = 1 := by rw [← h]; group
  have hD := closure_class_eq E hEcard _ hCE hC1 ha08
  have haT : autTab a0 ∈ s0Tabs := (mem_s0_iff a0).1 (hES ha0E)
  have hinv : isInv (autTab a0) = true := by
    simp only [isInv, decide_eq_true_eq]
    refine ⟨fun h => ha01 (autTab_injective (h.trans autTab_one.symm)), ?_⟩
    rw [← autTab_mul, hEsq a0 ha0E, autTab_one]
  have hcls : ((classTabs s0Tabs (autTab a0)).length == 8) = true := by
    rw [length_classTabs, ha08]
    rfl
  have hmem : autTab a0 ∈ cls8Invs s0Tabs := by
    unfold cls8Invs
    rw [List.mem_filter, List.mem_filter]
    exact ⟨⟨haT, hinv⟩, hcls⟩
  have hchk := uniqOK_spec
  unfold uniqOK at hchk
  rw [List.all_eq_true] at hchk
  have h1 := hchk _ hmem
  have hCl : ∀ x ∈ classTabs s0Tabs (autTab a0), ∃ c ∈ autConjClass s0 a0, autTab c = x := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := (mem_classTabs_iff a0 x).1 hx
    exact ⟨α * a0 * α⁻¹, ⟨α, hα, rfl⟩, rfl⟩
  have hCl' : ∀ c ∈ autConjClass s0 a0, autTab c ∈ classTabs s0Tabs (autTab a0) := by
    rintro _ ⟨α, hα, rfl⟩
    exact (mem_classTabs_iff a0 _).2 ⟨α, hα, rfl⟩
  have hA : (classTabs s0Tabs (autTab a0)).all
      (fun x => (classTabs s0Tabs (autTab a0)).all fun y => comm x y) = true := by
    simp only [List.all_eq_true]
    intro x hx y hy
    obtain ⟨c, hc, rfl⟩ := hCl x hx
    obtain ⟨d, hd, rfl⟩ := hCl y hy
    simp only [TabCheck.comm, decide_eq_true_eq]
    rw [← autTab_mul, ← autTab_mul, hEc c (hCE hc) d (hCE hd)]
  have hcnt : ((s0Tabs.filter fun l => (classTabs s0Tabs (autTab a0)).all
      fun x => comm l x).length == 16) = true := by
    have hset : (E : Set (MulAut (Carrier .M22))) = {γ | autTab γ ∈ s0Tabs.filter fun l =>
        (classTabs s0Tabs (autTab a0)).all fun x => comm l x} := by
      ext γ
      simp only [SetLike.mem_coe, Set.mem_ofPred_eq, List.mem_filter, List.all_eq_true]
      constructor
      · intro hγ
        refine ⟨(mem_s0_iff γ).1 (hES hγ), fun x hx => ?_⟩
        obtain ⟨c, hc, rfl⟩ := hCl x hx
        simp only [TabCheck.comm, decide_eq_true_eq]
        rw [← autTab_mul, ← autTab_mul, hEc γ hγ c (hCE hc)]
      · rintro ⟨hγs, hγ⟩
        have hγS : γ ∈ s0 := (mem_s0_iff γ).2 hγs
        apply hEself γ hγS
        have hle : E ≤ Subgroup.centralizer {γ} := by
          rw [← hD]
          refine (Subgroup.closure_le _).2 fun c hc => ?_
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          have := hγ _ (hCl' c hc)
          simp only [TabCheck.comm, decide_eq_true_eq] at this
          apply autTab_injective
          rw [autTab_mul, autTab_mul]
          exact this.symm
        intro β hβ
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hβ)).symm
    have hL := ncard_preimage_mem_tabs autTab autTab_injective
      (s0Tabs.filter fun l => (classTabs s0Tabs (autTab a0)).all fun x => comm l x)
      ((s0Check_spec).1.2.1.filter _) fun l hl =>
        (isTabsOf_s0.exists_mem l (List.mem_filter.1 hl).1).imp fun x hx => hx.2
    rw [← hset, ← Nat.card_coe_set_eq (E : Set (MulAut (Carrier .M22)))] at hL
    rw [beq_iff_eq, ← hL]
    exact hEcard
  simp only [hA, hcnt, Bool.not_true, Bool.false_or] at h1
  have hCI : autConjClass s0 a0 ⊆ innerImage (Carrier .M22) F := by
    intro c hc
    have hx := List.all_eq_true.1 h1 _ (hCl' c hc)
    have hf1 : autTab c ∈ f1Tabs := of_decide_eq_true hx
    rcases List.mem_cons.1 hf1 with h | h
    · have : c = 1 := autTab_injective (h.trans autTab_one.symm)
      rw [this]
      exact Subgroup.one_mem _
    · rw [← tab_invs16] at h
      obtain ⟨y, hy, hyc⟩ := List.mem_map.1 h
      have : c = MulAut.conj y := autTab_injective (by rw [autTab_conj, hyc])
      rw [this]
      exact ⟨y, (hF y).2 (Or.inr hy), rfl⟩
  have hEle : E ≤ innerImage (Carrier .M22) F := hD ▸ (Subgroup.closure_le _).2 hCI
  exact Subgroup.eq_of_le_of_card_ge hEle (by rw [card_innerImage hFcard, hEcard])

end CFSG.EvenSporadicStandard.M22Std
