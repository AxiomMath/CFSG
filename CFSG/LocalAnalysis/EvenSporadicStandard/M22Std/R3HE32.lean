module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32Level
public import Certificates.Certificate25930

public section

namespace CFSG.EvenSporadicStandard.M22Std.E32Check

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck


theorem checkProp : CheckProp := of_decide_eq_true Certificates.certificate25930

theorem stepOK : ∀ k < 5, StepOK s0Tabs k := checkProp.1

theorem elemLevel_four_length : (elemLevel s0Tabs 4).length = 1 := checkProp.2.1

theorem elemLevel_five : elemLevel s0Tabs 5 = [] := elemLevel_eq_nil le_rfl

theorem jTabs_length : jTabs.length = 32 := checkProp.2.2.1

theorem jTabs_nodup : jTabs.Nodup := checkProp.2.2.2.1

theorem jTabs_sorted : jTabs.Pairwise (fun a b => tabLE a b = true) := checkProp.2.2.2.2.1

theorem idTab_mem_jTabs : idTab ∈ jTabs := checkProp.2.2.2.2.2.1

theorem tTab_mem_jTabs : FusionCheck.tTab ∈ jTabs := checkProp.2.2.2.2.2.2.1

theorem jTabs_prop : ∀ a ∈ jTabs, a ∈ s0Tabs ∧ tmul a a = idTab ∧
    ∀ b ∈ jTabs, tmul a b ∈ jTabs ∧ comm a b = true := checkProp.2.2.2.2.2.2.2.1

theorem eq_jTabs_of_mem {L : List Tab} (hL : L ∈ elemLevel s0Tabs 4) : L = jTabs := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 elemLevel_four_length
  rw [ha, List.mem_singleton] at hL
  rw [jTabs_eq, ha, hL]
  rfl

theorem exists_jTabs_not_f1 : ∃ l ∈ s0Inner, l ∈ jTabs ∧ l ∉ f1Tabs :=
  checkProp.2.2.2.2.2.2.2.2.1

theorem level3_prop : ∀ L ∈ elemLevel s0Tabs 3, L.Nodup ∧
    (normB L = true → 4 < (L.filter fun l => decide (l ∈ jTabs)).length ∨ ∀ l ∈ L, l ∈ f1Tabs) :=
  checkProp.2.2.2.2.2.2.2.2.2

end CFSG.EvenSporadicStandard.M22Std.E32Check


namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.E32Check CFSG.Blueprint.NativeSporadic


theorem sq_of_autTab_mem_jTabs {a : MulAut (Carrier .M22)} (ha : autTab a ∈ jTabs) :
    a * a = 1 :=
  autTab_injective (by rw [autTab_mul, autTab_one]; exact (jTabs_prop _ ha).2.1)

noncomputable def jSub : Subgroup (MulAut (Carrier .M22)) where
  carrier := {a | autTab a ∈ jTabs}
  mul_mem' := fun {a b} ha hb => by
    show autTab (a * b) ∈ jTabs
    rw [autTab_mul]
    exact ((jTabs_prop _ ha).2.2 _ hb).1
  one_mem' := by
    show autTab 1 ∈ jTabs
    rw [autTab_one]
    exact idTab_mem_jTabs
  inv_mem' := fun {a} ha => by
    show autTab a⁻¹ ∈ jTabs
    rw [inv_eq_of_mul_eq_one_right (sq_of_autTab_mem_jTabs ha)]
    exact ha

theorem mem_jSub {a : MulAut (Carrier .M22)} : a ∈ jSub ↔ autTab a ∈ jTabs := Iff.rfl

theorem jSub_comm : ∀ a ∈ jSub, ∀ b ∈ jSub, a * b = b * a := by
  intro a ha b hb
  apply autTab_injective
  rw [autTab_mul, autTab_mul]
  have := ((jTabs_prop _ ha).2.2 _ hb).2
  simpa only [TabCheck.comm, decide_eq_true_eq] using this

theorem jSub_sq : ∀ a ∈ jSub, a * a = 1 := fun _ ha => sq_of_autTab_mem_jTabs ha

theorem jSub_exists_b {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    ∃ b : Carrier .M22, b * b = 1 ∧ b ∉ F1 ∧ MulAut.conj b ∈ jSub := by
  obtain ⟨l, hlS, hlJ, hlF⟩ := exists_jTabs_not_f1
  have hl : l ∈ (spanE sylowGens).map tab := by
    rw [tab_spanE, tab_sylowGens]
    exact hlS
  obtain ⟨z, -, hz⟩ := List.mem_map.1 hl
  refine ⟨z, ?_, ?_, ?_⟩
  · apply tab_injective
    rw [tab_mul, hz, tab_one]
    exact (jTabs_prop l hlJ).2.1
  · intro hzF
    apply hlF
    rcases (hmem1 z).1 hzF with rfl | hzI
    · rw [← hz, tab_one]
      exact List.mem_cons_self ..
    · rw [← hz]
      refine List.mem_cons_of_mem _ ?_
      rw [← tab_invs16]
      exact List.mem_map_of_mem hzI
  · rw [mem_jSub, autTab_conj, hz]
    exact hlJ


theorem jSub_le : jSub ≤ s0 := fun _ ha => (mem_s0_iff _).2 (jTabs_prop _ ha).1

theorem card_jSub : Nat.card jSub = 32 := by
  have h1 := ncard_preimage_mem_tabs autTab autTab_injective jTabs jTabs_nodup fun l hl =>
    (isTabsOf_s0.exists_mem l (jTabs_prop l hl).1).imp fun x hx => hx.2
  rw [jTabs_length] at h1
  rw [← h1]
  exact Nat.card_coe_set_eq {a : MulAut (Carrier .M22) | autTab a ∈ jTabs}

noncomputable abbrev tAut : MulAut (Carrier .M22) := MulAut.conj tEl

theorem autTab_tAut : autTab tAut = FusionCheck.tTab := autTab_conj_tEl

theorem tAut_sq : tAut * tAut = 1 := by
  rw [tAut, ← map_mul, tEl_involution.1, map_one]

theorem tAut_mem : tAut ∈ s0 := by
  rw [mem_s0_iff, autTab_tAut]
  exact (jTabs_prop _ tTab_mem_jTabs).1

theorem tAut_comm {α : MulAut (Carrier .M22)} (hα : α ∈ s0) : α * tAut = tAut * α :=
  (s0_center tAut tAut_mem).2 (Or.inr rfl) α hα

noncomputable def withT (E : Subgroup (MulAut (Carrier .M22))) : Subgroup (MulAut (Carrier .M22)) :=
  Subgroup.closure ((E : Set (MulAut (Carrier .M22))) ∪ {tAut})

theorem le_withT (E : Subgroup (MulAut (Carrier .M22))) : E ≤ withT E :=
  fun _ hx => Subgroup.subset_closure (Set.mem_union_left _ hx)

theorem tAut_mem_withT (E : Subgroup (MulAut (Carrier .M22))) : tAut ∈ withT E :=
  Subgroup.subset_closure (Set.mem_union_right _ rfl)

theorem withT_le {E : Subgroup (MulAut (Carrier .M22))} (hE : E ≤ s0) : withT E ≤ s0 := by
  rw [withT, Subgroup.closure_le]
  rintro x (hx | hx)
  · exact hE hx
  · rw [Set.mem_singleton_iff.1 hx]
    exact tAut_mem

theorem withT_comm {E : Subgroup (MulAut (Carrier .M22))} (hE : E ≤ s0)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α) :
    ∀ α ∈ withT E, ∀ β ∈ withT E, α * β = β * α := by
  have hk : ∀ x ∈ ((E : Set (MulAut (Carrier .M22))) ∪ {tAut}),
      ∀ y ∈ ((E : Set (MulAut (Carrier .M22))) ∪ {tAut}), x * y = y * x := by
    rintro x (hx | hx) y (hy | hy)
    · exact hc x hx y hy
    · rw [Set.mem_singleton_iff.1 hy]
      exact tAut_comm (hE hx)
    · rw [Set.mem_singleton_iff.1 hx]
      exact (tAut_comm (hE hy)).symm
    · rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]
  have h1 : withT E ≤ Subgroup.centralizer ((E : Set (MulAut (Carrier .M22))) ∪ {tAut}) := by
    rw [withT, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun y hy => hk y hy x hx
  intro α hα β hβ
  have h2 : withT E ≤ Subgroup.centralizer {α} := by
    rw [withT, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ((Subgroup.mem_centralizer_iff.1 (h1 hα)) x hx).symm
  exact Subgroup.mem_centralizer_iff.1 (h2 hβ) α rfl

theorem withT_sq {E : Subgroup (MulAut (Carrier .M22))} (hE : E ≤ s0)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α) (hsq : ∀ α ∈ E, α * α = 1) :
    ∀ α ∈ withT E, α * α = 1 := by
  have hcomm := withT_comm hE hc
  intro α hα
  replace hα : α ∈ Subgroup.closure ((E : Set (MulAut (Carrier .M22))) ∪ {tAut}) := hα
  induction hα using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hsq x hx
    · rw [Set.mem_singleton_iff.1 hx]
      exact tAut_sq
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    rw [mul_assoc, ← mul_assoc y x y, ← hcomm x hx y hy, mul_assoc x y y, ← mul_assoc, ihx, ihy,
      one_mul]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem jSub_unique_t (E : Subgroup (MulAut (Carrier .M22))) (hE : E ≤ s0)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α) (hsq : ∀ α ∈ E, α * α = 1) (ht : tAut ∈ E)
    (h32 : 32 ≤ Nat.card E) : E = jSub := by
  have hdvd : Nat.card E ∣ 256 := by
    have := Subgroup.card_dvd_of_le hE
    rwa [card_s0] at this
  have hcard : Nat.card E = 32 := by
    by_contra hne
    have h64 : 2 ^ 6 ≤ Nat.card E := by
      by_contra hlt
      rw [not_le] at hlt
      generalize Nat.card E = n at h32 hdvd hne hlt
      interval_cases n <;> omega
    obtain ⟨L, hL, -⟩ := elemLevel_cover stepOK hE hc hsq ht autTab_tAut 5 h64
    rw [elemLevel_five] at hL
    exact List.not_mem_nil hL
  obtain ⟨L, hL, hLE⟩ := elemLevel_cover stepOK hE hc hsq ht autTab_tAut 4 (by rw [hcard]; norm_num)
  obtain rfl := eq_jTabs_of_mem hL
  ext a
  rw [mem_iff_autTab_mem jTabs_nodup (by rw [jTabs_length, hcard]) hLE a]
  exact mem_jSub.symm

theorem jSub_unique (E : Subgroup (MulAut (Carrier .M22))) (hE : E ≤ s0)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α) (hsq : ∀ α ∈ E, α * α = 1)
    (h32 : 32 ≤ Nat.card E) : E = jSub := by
  have hT := jSub_unique_t (withT E) (withT_le hE) (withT_comm hE hc) (withT_sq hE hc hsq)
    (tAut_mem_withT E) (h32.trans (Subgroup.card_le_of_le (le_withT E)))
  have hle : E ≤ jSub := by
    rw [← hT]
    exact le_withT E
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_jSub]; exact h32)

theorem jSub_normal_E16 {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) (hF16 : Nat.card F1 = 16)
    (V : Subgroup (MulAut (Carrier .M22))) (hVS : V ≤ s0)
    (hVn : ∀ α ∈ s0, ∀ β ∈ V, α * β * α⁻¹ ∈ V)
    (hVc : ∀ α ∈ V, ∀ β ∈ V, α * β = β * α) (hVsq : ∀ α ∈ V, α * α = 1)
    (hV16 : Nat.card V = 16) (hVJ : Nat.card ↥(V ⊓ jSub) ≤ 4) :
    V = innerImage (Carrier .M22) F1 := by
  by_cases ht : tAut ∈ V
  swap
  · exfalso
    have hW := withT_le hVS
    have hdvd : Nat.card (withT V) ∣ 256 := by
      have := Subgroup.card_dvd_of_le hW
      rwa [card_s0] at this
    have h16 : 16 ≤ Nat.card (withT V) := by
      rw [← hV16]
      exact Subgroup.card_le_of_le (le_withT V)
    have hne : Nat.card (withT V) ≠ 16 := by
      intro h
      have hEq : V = withT V := Subgroup.eq_of_le_of_card_ge (le_withT V)
        (le_of_eq (by rw [h, hV16]))
      apply ht
      rw [hEq]
      exact tAut_mem_withT V
    have h32 : 32 ≤ Nat.card (withT V) := by
      by_contra hlt
      rw [not_le] at hlt
      generalize Nat.card (withT V) = n at hdvd h16 hne hlt
      interval_cases n <;> omega
    have hJ := jSub_unique (withT V) hW (withT_comm hVS hVc) (withT_sq hVS hVc hVsq) h32
    have hVJ' : V ⊓ jSub = V := inf_eq_left.2 (by rw [← hJ]; exact le_withT V)
    rw [hVJ', hV16] at hVJ
    omega
  obtain ⟨L, hL, hLV⟩ :=
    elemLevel_cover stepOK hVS hVc hVsq ht autTab_tAut 3 (by rw [hV16]; norm_num)
  obtain ⟨hnd, hnorm⟩ := level3_prop L hL
  have hlen : L.length = Nat.card V := by
    rw [length_of_mem_elemLevel stepOK 3 L hL, hV16]
    norm_num
  have hmem := mem_iff_autTab_mem hnd hlen hLV
  have hnB : normB L = true := by
    unfold normB
    simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
    intro g hg l hl
    have hg' : g ∈ s0Gens'.map autTab := by
      rw [map_autTab_s0Gens']
      exact hg
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg'
    have hγS : γ ∈ s0 := Subgroup.subset_closure hγ
    obtain ⟨β, hβ, rfl⟩ := hLV l hl
    refine ⟨autTab (γ * β * γ⁻¹), (hmem _).1 (hVn γ hγS β hβ), ?_⟩
    rw [← autTab_mul, ← autTab_mul]
    congr 1
    group
  have hL4 : (L.filter fun l => decide (l ∈ jTabs)).length ≤ 4 := by
    have hset : ((V ⊓ jSub : Subgroup (MulAut (Carrier .M22))) :
        Set (MulAut (Carrier .M22))) = {a | autTab a ∈ L.filter fun l => decide (l ∈ jTabs)} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_ofPred_eq, List.mem_filter,
        decide_eq_true_eq, hmem a, mem_jSub]
    have h1 := ncard_preimage_mem_tabs autTab autTab_injective
      (L.filter fun l => decide (l ∈ jTabs)) (hnd.filter _) fun l hl => by
        obtain ⟨e, he, rfl⟩ := hLV l (List.mem_filter.1 hl).1
        exact ⟨e, rfl⟩
    rw [← hset] at h1
    have h2 := Nat.card_coe_set_eq ((V ⊓ jSub : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22)))
    calc (L.filter fun l => decide (l ∈ jTabs)).length
        = Nat.card ↑((V ⊓ jSub : Subgroup (MulAut (Carrier .M22))) :
          Set (MulAut (Carrier .M22))) := (h2.trans h1).symm
      _ ≤ 4 := hVJ
  have hF : ∀ l ∈ L, l ∈ f1Tabs := by
    rcases hnorm hnB with h | h
    · omega
    · exact h
  have hle : V ≤ innerImage (Carrier .M22) F1 := by
    intro v hv
    rcases List.mem_cons.1 (hF _ ((hmem v).1 hv)) with h | h
    · have : v = 1 := autTab_injective (h.trans autTab_one.symm)
      rw [this]
      exact Subgroup.one_mem _
    · rw [← tab_invs16] at h
      obtain ⟨y, hy, hyc⟩ := List.mem_map.1 h
      have : v = MulAut.conj y := autTab_injective (by rw [autTab_conj, hyc])
      rw [this]
      exact ⟨y, (hmem1 y).2 (Or.inr hy), rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_innerImage hF16, hV16])

theorem e32Facts_pinned {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) (hF16 : Nat.card F1 = 16) :
    ∃ J : Subgroup (MulAut (Carrier .M22)), E32Facts (Carrier .M22) s0 F1 J :=
  ⟨jSub,
    { le := jSub_le
      comm := jSub_comm
      sq := jSub_sq
      card := card_jSub
      unique := fun E hE hc hsq h32 => jSub_unique E hE hc hsq h32
      exists_b := jSub_exists_b hmem1
      normal_E16 := fun V hVS hVn hVc hVsq hV16 hVJ =>
        jSub_normal_E16 hmem1 hF16 V hVS hVn hVc hVsq hV16 hVJ }⟩

end CFSG.EvenSporadicStandard.M22Std
