module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32Level
public import Certificates.Certificate25930

public section

namespace CFSG.EvenSporadicStandard.M22Std.E32Check

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck


theorem checkProp : CheckProp := of_decide_eq_true Certificates.certificate25930

theorem elemLevel_five_length : (elemLevel s0Tabs 5).length = 1 := checkProp.1

theorem elemLevel_six : elemLevel s0Tabs 6 = [] := checkProp.2.1

theorem jTabs_length : jTabs.length = 32 := checkProp.2.2.1

theorem jTabs_nodup : jTabs.Nodup := checkProp.2.2.2.1

theorem idTab_mem_jTabs : idTab ∈ jTabs := checkProp.2.2.2.2.1

theorem jTabs_prop : ∀ a ∈ jTabs, a ∈ s0Tabs ∧ tmul a a = idTab ∧
    ∀ b ∈ jTabs, tmul a b ∈ jTabs ∧ comm a b = true := checkProp.2.2.2.2.2.1

theorem eq_jTabs_of_mem {L : List Tab} (hL : L ∈ elemLevel s0Tabs 5) : L = jTabs := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 elemLevel_five_length
  rw [ha, List.mem_singleton] at hL
  rw [jTabs_eq, ha, hL]
  rfl

theorem exists_jTabs_not_f1 : ∃ l ∈ s0Inner, l ∈ jTabs ∧ l ∉ f1Tabs :=
  checkProp.2.2.2.2.2.2.1

theorem level4_prop : ∀ L ∈ elemLevel s0Tabs 4, L.Nodup ∧
    (normB L = true → 4 < (L.filter fun l => decide (l ∈ jTabs)).length ∨ ∀ l ∈ L, l ∈ f1Tabs) :=
  checkProp.2.2.2.2.2.2.2

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

theorem jSub_unique (E : Subgroup (MulAut (Carrier .M22))) (hE : E ≤ s0)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α) (hsq : ∀ α ∈ E, α * α = 1)
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
    obtain ⟨L, hL, -⟩ := elemLevel_cover hE hc hsq 6 h64
    rw [elemLevel_six] at hL
    exact List.not_mem_nil hL
  obtain ⟨L, hL, hLE⟩ := elemLevel_cover hE hc hsq 5 (by rw [hcard]; norm_num)
  obtain rfl := eq_jTabs_of_mem hL
  ext a
  rw [mem_iff_autTab_mem jTabs_nodup (by rw [jTabs_length, hcard]) hLE a]
  exact mem_jSub.symm

theorem jSub_normal_E16 {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) (hF16 : Nat.card F1 = 16)
    (V : Subgroup (MulAut (Carrier .M22))) (hVS : V ≤ s0)
    (hVn : ∀ α ∈ s0, ∀ β ∈ V, α * β * α⁻¹ ∈ V)
    (hVc : ∀ α ∈ V, ∀ β ∈ V, α * β = β * α) (hVsq : ∀ α ∈ V, α * α = 1)
    (hV16 : Nat.card V = 16) (hVJ : Nat.card ↥(V ⊓ jSub) ≤ 4) :
    V = innerImage (Carrier .M22) F1 := by
  obtain ⟨L, hL, hLV⟩ := elemLevel_cover hVS hVc hVsq 4 (by rw [hV16]; norm_num)
  obtain ⟨hnd, hnorm⟩ := level4_prop L hL
  have hlen : L.length = Nat.card V := by
    rw [length_of_mem_elemLevel s0Tabs 4 L hL, hV16]
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
