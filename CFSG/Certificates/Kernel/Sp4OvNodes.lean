module

public import CFSG.Certificates.Kernel.Sp4OvSound
public import CFSG.Quasithin.H13.L32NSp4Over

public section

namespace CFSG.KD.Sp4Ov

open CFSG.Quasithin.H13 Sp4Cert KGCert CFSG.ComponentClassification.PresentationLocal

theorem toNode_facts {spM : ℕ} {L : List NodeR} (he : elemsOK spM = true)
    (hL : ovK spM L = true) {s : Node} (hs : s ∈ L.map toNode) :
    s.mask = maskOf s.els ∧ (∀ x ∈ s.els, ValidC4 x) ∧ (∀ g ∈ s.gens, ValidC4 g) ∧
      (∀ g ∈ s.gens, memM s.mask g = true) ∧
      (∀ P : List ℕ → Prop, P oneC4 → (∀ a, P a → ∀ g ∈ s.gens, P (mulC a g)) →
        ∀ x ∈ s.els, P x) ∧
      (∀ r ∈ s.reps, ValidC4 r) ∧ (∀ r ∈ s.reps, memM s.mask r = false) ∧
      (∀ x ∈ spElsC, memM s.mask x = true ∨ ∃ r ∈ s.reps, ∃ ri, ValidC4 ri ∧
        mulC ri r = oneC4 ∧ ∃ a ∈ s.els, memM s.mask (mulC (mulC ri a) x) = true) ∧
      ∀ r ∈ s.reps, ∃ t ∈ L.map toNode, subM s.mask t.mask = true ∧ memM t.mask r = true ∧
        ∀ P : List ℕ → Prop, P oneC4 → (∀ a, P a → ∀ l, (l ∈ s.els ∨ l = r) → P (mulC a l)) →
          ∀ g ∈ t.gens, P g := by
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  obtain ⟨h1, -, -, h4, h5, h6, h7, h8⟩ := nodeK_sound he hL hs'
  refine ⟨h1, fun x hx => ?_, fun x hx => ?_, h4, h5, fun x hx => ?_, h6, h7, fun r hr => ?_⟩
  rotate_left 3
  all_goals
    try
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
      exact validC4_dec _
  obtain ⟨t, ht, h⟩ := h8 r hr
  exact ⟨toNode t, List.mem_map_of_mem ht, h⟩

theorem exists_node_eq_ofK {spM : ℕ} {L : List NodeR} (he : elemsOK spM = true)
    (hL : ovK spM L = true) {gens₀ : List (List ℕ)}
    (hg₀ : (L.map toNode).any (fun s => s.gens == gens₀) = true)
    {Δ : Subgroup (GL (Fin 4) (ZMod 2))} (hΔ : Δ ≤ sympFour) (hP : ∀ x ∈ gens₀, InD Δ x) :
    ∃ s ∈ L.map toNode, (∀ x ∈ s.els, InD Δ x) ∧ ∀ g ∈ Δ, colsOf4 (g : Mat4) ∈ s.els := by
  classical
  have hok := fun s (hs : s ∈ L.map toNode) => toNode_facts he hL hs
  set S := (L.map toNode).filter fun s => decide (∀ x ∈ s.els, InD Δ x) with hSdef
  have hmemS : ∀ s, s ∈ S ↔ s ∈ L.map toNode ∧ ∀ x ∈ s.els, InD Δ x := by
    intro s
    simp only [hSdef, List.mem_filter, decide_eq_true_eq]
  obtain ⟨s₀, hs₀L, hs₀g⟩ := List.any_eq_true.mp hg₀
  have hs₀g' : s₀.gens = gens₀ := by simpa using hs₀g
  have hs₀S : s₀ ∈ S := by
    refine (hmemS s₀).mpr ⟨hs₀L, ?_⟩
    obtain ⟨-, -, -, -, hgen, -⟩ := hok s₀ hs₀L
    exact hgen (InD Δ) (inD_oneC4 Δ) fun a ha g hg => inD_mulC ha (hP g (hs₀g' ▸ hg))
  obtain ⟨s, hsS, hmax⟩ : ∃ s ∈ S, ∀ t ∈ S, nodeCard t ≤ nodeCard s := by
    obtain ⟨s, hs, hmax⟩ := S.toFinset.exists_max_image nodeCard
      ⟨s₀, List.mem_toFinset.mpr hs₀S⟩
    exact ⟨s, List.mem_toFinset.mp hs, fun t ht => hmax t (List.mem_toFinset.mpr ht)⟩
  obtain ⟨hsL, hsD⟩ := (hmemS s).mp hsS
  obtain ⟨hm, hv, -, -, -, hrv, hrs, hcov, hrt⟩ := hok s hsL
  refine ⟨s, hsL, hsD, fun g hg => ?_⟩
  by_contra hgs
  set x := colsOf4 (g : Mat4) with hxdef
  have hxv : ValidC4 x := validC4_colsOf4 _
  have hxsp : x ∈ spElsC := colsOf4_mem_spElsC (hΔ hg)
  rcases hcov x hxsp with hxm | ⟨r, hr, ri, hriv, hrr, a, ha, hab⟩
  · rw [hm] at hxm
    exact hgs (mem_of_memM_maskOf hv hxv hxm)
  have hbv : ValidC4 (mulC (mulC ri a) x) := validC4_mulC (validC4_mulC hriv (hv a ha)) hxv
  rw [hm] at hab
  have hb := mem_of_memM_maskOf hv hbv hab
  have hrD : InD Δ r := inD_of_mul_eq hriv (hsD a ha) hxv (hsD _ hb) rfl (hrv r hr) hrr
    (inD_colsOf4 hg)
  obtain ⟨t, htL, hst, hrt', htgen⟩ := hrt r hr
  obtain ⟨htm, -, -, -, htcl, -⟩ := hok t htL
  have htg : ∀ y ∈ t.gens, InD Δ y := htgen (InD Δ) (inD_oneC4 Δ) fun a ha l hl => by
    rcases hl with hl | rfl
    · exact inD_mulC ha (hsD l hl)
    · exact inD_mulC ha hrD
  have htD : ∀ y ∈ t.els, InD Δ y :=
    htcl (InD Δ) (inD_oneC4 Δ) fun a ha g hg => inD_mulC ha (htg g hg)
  have htS : t ∈ S := (hmemS t).mpr ⟨htL, htD⟩
  have hsub : (s.els.map codeC).toFinset ⊂ (t.els.map codeC).toFinset := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨codeC r, ?_, ?_⟩
      · rw [htm] at hrt'
        obtain ⟨y, hy, hyr⟩ := memM_maskOf.mp hrt'
        simp only [List.mem_toFinset, List.mem_map]
        exact ⟨y, hy, hyr⟩
      · intro hc
        simp only [List.mem_toFinset, List.mem_map] at hc
        obtain ⟨y, hy, hyr⟩ := hc
        have := hrs r hr
        rw [hm, memM_maskOf.mpr ⟨y, hy, hyr⟩] at this
        exact Bool.noConfusion this
    · intro c hc
      simp only [List.mem_toFinset, List.mem_map] at hc ⊢
      obtain ⟨y, hy, rfl⟩ := hc
      have hym : memM s.mask y = true := by rw [hm]; exact memM_maskOf_of_mem hy
      have := subM_iff.mp hst _ hym
      rw [htm] at this
      exact memM_maskOf.mp this
  have := hmax t htS
  have hlt := Finset.card_lt_card hsub
  simp only [nodeCard] at this
  omega

end CFSG.KD.Sp4Ov

end
