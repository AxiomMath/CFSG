module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23FusionData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KDichotomy
public import Certificates.Certificate24471

public section

namespace CFSG.EvenSporadicStandard.M23Std

open CFSG.EvenSporadicStandard.Wong77 CFSG.EvenSporadicStandard.Wong77.M23Sylow
  CFSG.EvenSporadicStandard.M23Std.FusionCheck CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Fixed

theorem fixedCheck_spec :
    (stabTabs.length = 2 ∧ ∀ g ∈ stabTabs, normOK (elemTabs 1) g = true ∧
      M23Sylow.comm g tTab = true) ∧
    (∀ x ∈ elemTabs 1, (∀ g ∈ stabTabs, tmul g x = tmul x g ∨
      tmul g x = tmul (tmul x tTab) g) → x = tTab) ∧
    (f2Tab ≠ tTab ∧ ∀ y ∈ elemTabs 1, y ≠ tTab → ∃ i ∈ List.range 14,
      normOK (elemTabs 1) (qTab i) = true ∧ M23Sylow.comm (qTab i) tTab = true ∧
        tmul (qTab i) f2Tab = tmul y (qTab i)) := by
  have h := Certificates.certificate24471
  simp only [fixedCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

@[expose] def qEl (i : Nat) : Carrier .M23 := wordElt [genA, genB, genBi] (qWords.getD i [])

theorem tab_qEl (i : Nat) : tab (qEl i) = qTab i := by
  rw [qEl, tab_wordElt, tab_letters]
  rfl

@[expose] def f2El : Carrier .M23 := (invs16 1).getD 0 1

theorem tab_f2El : tab f2El = f2Tab := by
  rw [f2El, tab_getD, tab_invs16]
  rfl

theorem exists_elt_of_mem_stabTabs {g : Tab} (hg : g ∈ stabTabs) :
    ∃ s : Carrier .M23, tab s = g := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact ⟨wordElt [genA, genB, genBi] w, by rw [tab_wordElt, tab_letters]⟩

theorem fixedData_pinned
    {F1 : Subgroup (Carrier .M23)} (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    FixedData (⊤ : Subgroup (Carrier .M23)) F1 := by
  obtain ⟨hstab, hFP, -⟩ := fixedCheck_spec
  refine ⟨fun f hf hf1 x hx H => ?_⟩
  have hfm : f ∈ invs16 1 := ((hmem1 f).1 hf).resolve_left hf1
  obtain ⟨b, hbn, hbt⟩ := exists_conj_tEl hmem1 f hfm
  have hbmem : b ∈ Subgroup.normalizer (F1 : Set (Carrier .M23)) :=
    Subgroup.mem_normalizer_iff.2 hbn
  have hbinv := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbmem)
  have hx'F : b⁻¹ * x * b⁻¹⁻¹ ∈ F1 := (hbinv x).1 hx
  rw [inv_inv] at hx'F
  by_cases hx'1 : b⁻¹ * x * b = 1
  · left
    have : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
    rw [this, hx'1]
    group
  · right
    obtain ⟨x', hx'⟩ : ∃ x', x' = b⁻¹ * x * b := ⟨_, rfl⟩
    have hx'F' : x' ∈ F1 := hx' ▸ hx'F
    have hx'1' : x' ≠ 1 := hx' ▸ hx'1
    have hx'm : x' ∈ invs16 1 := ((hmem1 _).1 hx'F').resolve_left hx'1'
    have hxt : tab x' ∈ elemTabs 1 := by
      rw [← tab_invs16]
      exact List.mem_map_of_mem hx'm
    have hx't : x' = tEl := by
      apply tab_injective
      rw [tab_tEl]
      refine hFP _ hxt (fun g hg => ?_)
      obtain ⟨s, hs⟩ := exists_elt_of_mem_stabTabs hg
      obtain ⟨hsn, hsc⟩ := hstab.2 g hg
      have hsmem : s ∈ Subgroup.normalizer (F1 : Set (Carrier .M23)) :=
        Subgroup.mem_normalizer_iff.2 (normalizes_of_normOK hmem1 (by rw [hs]; exact hsn))
      have hst : s * tEl = tEl * s :=
        tab_injective (by rw [tab_mul, tab_mul, tab_tEl, hs]; exact of_decide_eq_true hsc)
      have hn' : b * s * b⁻¹ ∈ Subgroup.normalizer (F1 : Set (Carrier .M23)) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hbmem hsmem) (Subgroup.inv_mem _ hbmem)
      have hb'f : (b * s * b⁻¹) * f * (b * s * b⁻¹)⁻¹ = f := by
        rw [← hbt]
        calc b * s * b⁻¹ * (b * tEl * b⁻¹) * (b * s * b⁻¹)⁻¹ = b * (s * tEl * s⁻¹) * b⁻¹ := by
              group
          _ = b * tEl * b⁻¹ := by rw [hst]; group
      have hH := H (b * s * b⁻¹) (Subgroup.mem_top _) (Subgroup.mem_normalizer_iff.1 hn') hb'f
      have hconj : b * s * b⁻¹ * x * (b * s * b⁻¹)⁻¹ = b * (s * x' * s⁻¹) * b⁻¹ := by
        rw [hx']
        group
      have hbx : x = b * x' * b⁻¹ := by
        rw [hx']
        group
      have hbf : x * f = b * (x' * tEl) * b⁻¹ := by
        rw [hx', ← hbt]
        group
      rcases hH with h1 | h1
      · left
        rw [hconj] at h1
        have h3 : b * (s * x' * s⁻¹) * b⁻¹ = b * x' * b⁻¹ := by rw [h1]; exact hbx
        have h2 : s * x' * s⁻¹ = x' := mul_left_cancel (mul_right_cancel h3)
        have h4 : s * x' = x' * s := mul_inv_eq_iff_eq_mul.1 h2
        have := congrArg tab h4
        rw [tab_mul, tab_mul, hs] at this
        exact this
      · right
        rw [hconj, hbf] at h1
        have h2 : s * x' * s⁻¹ = x' * tEl := mul_left_cancel (mul_right_cancel h1)
        have h4 : s * x' = x' * tEl * s := mul_inv_eq_iff_eq_mul.1 h2
        have := congrArg tab h4
        rw [tab_mul, tab_mul, tab_mul, hs, tab_tEl] at this
        exact this
    have hxe : x = b * x' * b⁻¹ := by
      rw [hx']
      group
    rw [hxe, hx't, hbt]

end Fixed

section Trans2

theorem exists_normalizer_to_pair
    {F1 : Subgroup (Carrier .M23)} (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    {f f' : Carrier .M23} (hf : f ∈ F1) (hf1 : f ≠ 1) (hf' : f' ∈ F1) (hf'1 : f' ≠ 1)
    (hff : f ≠ f') :
    ∃ u : Carrier .M23, (∀ x, x ∈ F1 ↔ u * x * u⁻¹ ∈ F1) ∧ u * f * u⁻¹ = tEl ∧
      u * f' * u⁻¹ = f2El := by
  obtain ⟨-, -, -, hq⟩ := fixedCheck_spec
  have hfm : f ∈ invs16 1 := ((hmem1 f).1 hf).resolve_left hf1
  obtain ⟨p, hpn, hpt⟩ := exists_conj_tEl hmem1 f hfm
  have hpmem : p ∈ Subgroup.normalizer (F1 : Set (Carrier .M23)) :=
    Subgroup.mem_normalizer_iff.2 hpn
  have hpt' : p⁻¹ * f * p = tEl := by rw [← hpt]; group
  have hf''F : p⁻¹ * f' * p ∈ F1 := by
    have := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hpmem) f'
    rw [inv_inv] at this
    exact this.1 hf'
  have hf''1 : p⁻¹ * f' * p ≠ 1 := by
    intro h
    apply hf'1
    have : f' = p * (p⁻¹ * f' * p) * p⁻¹ := by group
    rw [this, h]
    group
  have hf''t : p⁻¹ * f' * p ≠ tEl := by
    intro h
    apply hff
    have h1 : f' = p * tEl * p⁻¹ := by rw [← h]; group
    rw [h1, hpt]
  have hf''m : p⁻¹ * f' * p ∈ invs16 1 := ((hmem1 _).1 hf''F).resolve_left hf''1
  have hf''tab : tab (p⁻¹ * f' * p) ∈ elemTabs 1 := by
    rw [← tab_invs16]
    exact List.mem_map_of_mem hf''m
  have hf''tne : tab (p⁻¹ * f' * p) ≠ tTab := fun h => hf''t (tab_injective (by rw [h, tab_tEl]))
  obtain ⟨i, -, hqn, hqc, hqf⟩ := hq _ hf''tab hf''tne
  have hqmem : qEl i ∈ Subgroup.normalizer (F1 : Set (Carrier .M23)) :=
    Subgroup.mem_normalizer_iff.2 (normalizes_of_normOK hmem1 (by rw [tab_qEl]; exact hqn))
  have hqt : qEl i * tEl = tEl * qEl i :=
    tab_injective (by rw [tab_mul, tab_mul, tab_qEl, tab_tEl]; exact of_decide_eq_true hqc)
  have hqf2 : qEl i * f2El = (p⁻¹ * f' * p) * qEl i :=
    tab_injective (by rw [tab_mul, tab_mul, tab_qEl, tab_f2El]; exact hqf)
  refine ⟨(qEl i)⁻¹ * p⁻¹, ?_, ?_, ?_⟩
  · exact Subgroup.mem_normalizer_iff.1
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hqmem) (Subgroup.inv_mem _ hpmem))
  · calc (qEl i)⁻¹ * p⁻¹ * f * ((qEl i)⁻¹ * p⁻¹)⁻¹ = (qEl i)⁻¹ * (p⁻¹ * f * p) * qEl i := by group
      _ = (qEl i)⁻¹ * (tEl * qEl i) := by rw [hpt', mul_assoc]
      _ = (qEl i)⁻¹ * (qEl i * tEl) := by rw [hqt]
      _ = tEl := by group
  · calc (qEl i)⁻¹ * p⁻¹ * f' * ((qEl i)⁻¹ * p⁻¹)⁻¹ = (qEl i)⁻¹ * ((p⁻¹ * f' * p) * qEl i) := by
          group
      _ = (qEl i)⁻¹ * (qEl i * f2El) := by rw [← hqf2]
      _ = f2El := by group

theorem trans2Data_pinned
    {F1 : Subgroup (Carrier .M23)} (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    Trans2Data (⊤ : Subgroup (Carrier .M23)) F1 := by
  refine ⟨fun f hf hf1 f' hf' hf'1 hff g hg hg1 g' hg' hg'1 hgg => ?_⟩
  obtain ⟨u, hun, huf, huf'⟩ := exists_normalizer_to_pair hmem1 hf hf1 hf' hf'1 hff
  obtain ⟨v, hvn, hvg, hvg'⟩ := exists_normalizer_to_pair hmem1 hg hg1 hg' hg'1 hgg
  have hu : u ∈ Subgroup.normalizer (F1 : Set (Carrier .M23)) :=
    Subgroup.mem_normalizer_iff.2 hun
  have hv : v ∈ Subgroup.normalizer (F1 : Set (Carrier .M23)) :=
    Subgroup.mem_normalizer_iff.2 hvn
  refine ⟨v⁻¹ * u, Subgroup.mem_top _,
    Subgroup.mem_normalizer_iff.1 (Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hu), ?_, ?_⟩
  · calc v⁻¹ * u * f * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * f * u⁻¹) * v := by group
      _ = v⁻¹ * tEl * v := by rw [huf]
      _ = g := by rw [← hvg]; group
  · calc v⁻¹ * u * f' * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * f' * u⁻¹) * v := by group
      _ = v⁻¹ * f2El * v := by rw [huf']
      _ = g' := by rw [← hvg']; group

end Trans2

end CFSG.EvenSporadicStandard.M23Std
