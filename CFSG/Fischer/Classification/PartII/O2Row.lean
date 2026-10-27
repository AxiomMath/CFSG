module

public import CFSG.Fischer.Classification.PartII.O2Module

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace O2Mod

variable {H : Type} [Group H] {E μ : Set H}

theorem eq_or_eq_or_eq_of_ncard_eq_three {α : Type*} {S : Set α} (hS : S.ncard = 3)
    {a b c x : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hx : x ∈ S) : x = a ∨ x = b ∨ x = c := by
  have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hsub : ({a, b, c} : Set α) ⊆ S := by
    intro y hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Set α).ncard = 3 := Set.ncard_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  have heq : ({a, b, c} : Set α) = S := Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
  rw [← heq] at hx
  simpa using hx

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E)
include hμ hP

theorem mate_mate_eq_of_isTwin {f g k : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hfg : f * g ≠ g * f) (hk : IsTwin E (f * g * f) k) :
    mate E μ (mate E μ f g) k = mate E μ f k := by
  have h := hμ.mate_mate_mate_of_isTwin hP hf hfμ hg hfg hk
  have hf'E := hμ.mate_mem hP hf hfμ hg hfg
  have hf'μ := hμ.mate_notMem hP hf hfμ hg hfg
  have hgk : g * k ≠ k * g := by
    have h := Pair.mul_mul_not_commute_right hP hf hg hfg
    exact not_commute_of_isTwin' hk hg fun e => h e.symm
  have hf'k : mate E μ f g * k ≠ k * mate E μ f g :=
    not_commute_of_isTwin (hμ.isTwin_mate hP hf hfμ hg hfg) hk.2.1 hgk
  have hfk : f * k ≠ k * f := by
    have h := Pair.mul_mul_not_commute_left hP hf hfg
    exact not_commute_of_isTwin' hk hf fun e => h e.symm
  have hf''E := hμ.mate_mem hP hf'E hf'μ hk.2.1 hf'k
  have hkf'' := hμ.isTwin_mate hP hf'E hf'μ hk.2.1 hf'k
  have hf''f : mate E μ (mate E μ f g) k * f ≠ f * mate E μ (mate E μ f g) k := fun e =>
    not_commute_of_isTwin' hkf'' hf hfk e.symm
  have h2 := hμ.mate_mate hP hf''E (hμ.mate_notMem hP hf'E hf'μ hk.2.1 hf'k) hf hf''f
  rw [h] at h2
  exact h2.symm.trans (hμ.mate_congr hP hf hfμ hk.2.1 hfk hkf'')

theorem mate_mate_eq_of_commute {f g k : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hk : k ∈ E) (hfg : f * g ≠ g * f) (hgk : g * k ≠ k * g) (hfk : f * k ≠ k * f)
    (hc : k * (f * g * f) = f * g * f * k) :
    mate E μ (mate E μ f g) k = mate E μ f k := by
  have h := hμ.mate_mate_mate_of_commute hP hf hfμ hg hk hfg hgk hfk hc
  have hf'E := hμ.mate_mem hP hf hfμ hg hfg
  have hf'μ := hμ.mate_notMem hP hf hfμ hg hfg
  have hf'k : mate E μ f g * k ≠ k * mate E μ f g :=
    not_commute_of_isTwin (hμ.isTwin_mate hP hf hfμ hg hfg) hk hgk
  have hf''E := hμ.mate_mem hP hf'E hf'μ hk hf'k
  have hkf'' := hμ.isTwin_mate hP hf'E hf'μ hk hf'k
  have hf''f : mate E μ (mate E μ f g) k * f ≠ f * mate E μ (mate E μ f g) k := fun e =>
    not_commute_of_isTwin' hkf'' hf hfk e.symm
  have h2 := hμ.mate_mate hP hf''E (hμ.mate_notMem hP hf'E hf'μ hk hf'k) hf hf''f
  rw [h] at h2
  exact h2.symm.trans (hμ.mate_congr hP hf hfμ hk hfk hkf'')

theorem mate_mate_ne_of_affine {f g k : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hk : k ∈ E) (hfg : f * g ≠ g * f) (hgk : g * k ≠ k * g) (hfk : f * k ≠ k * f)
    (hc : k * (f * g * f) ≠ f * g * f * k) :
    mate E μ (mate E μ f g) k ≠ mate E μ f k := by
  intro heq
  apply hμ.mate_mate_mate_ne_of_affine hP hf hfμ hg hk hfg hgk hfk hc
  rw [heq]
  exact hμ.mate_mate hP hf hfμ hk hfk

theorem bform_conj {s f g : H} (hs : s ∈ μ) :
    bform μ (s * f * s) (s * g * s) = bform μ f g := by
  have hsE := hμ.subset hs
  have hcomm : s * f * s * (s * g * s) = s * g * s * (s * f * s) ↔ f * g = g * f := by
    have := conj_commute_iff s f g
    rwa [Pair.inv_eq hP hsE] at this
  have hmem : s * f * s * (s * g * s) * (s * f * s) ∈ μ ↔ f * g * f ∈ μ := by
    have e : s * f * s * (s * g * s) * (s * f * s) = s * (f * g * f) * s := by
      calc s * f * s * (s * g * s) * (s * f * s) = s * f * (s * s) * g * (s * s) * f * s := by
            group
        _ = s * (f * g * f) * s := by rw [Pair.mul_self hP hsE]; group
    rw [e]
    refine ⟨fun h => ?_, fun h => hμ.mul_mul_mem _ hs _ h⟩
    rw [← Pair.mul_mul_mul_mul hP hsE (f * g * f)]
    exact hμ.mul_mul_mem _ hs _ h
  by_cases h : f * g = g * f
  · rw [bform_of_commute h, bform_of_commute (hcomm.2 h)]
  · by_cases h' : f * g * f ∈ μ
    · rw [bform_of_mem h', bform_of_mem (hmem.2 h')]
    · rw [bform_of_not_mem h h', bform_of_not_mem (fun e => h (hcomm.1 e)) (fun e => h' (hmem.1 e))]

theorem bform_eq_zero_iff_mate {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hgμ : g ∉ μ) (hfg : f * g ≠ g * f) : bform μ f g = 0 ↔ mate E μ f g = g := by
  constructor
  · intro h
    have hm : f * g * f ∈ μ := by
      by_contra hm
      rw [bform_of_not_mem hfg hm] at h
      exact one_ne_zero h
    exact hμ.mate_eq hP hf hfμ hg hfg (self_mem_twinClass hg) hgμ hm
  · intro h
    apply bform_of_mem
    rw [← h]
    exact hμ.mul_mate_mul_mem hP hf hfμ hg hfg

theorem mate_injOn {a b g : H} (ha : a ∈ E) (haμ : a ∉ μ) (hb : IsTwin E a b) (hbμ : b ∉ μ)
    (hg : g ∈ E) (hag : a * g ≠ g * a) (h : mate E μ a g = mate E μ b g) : a = b := by
  have hbg : b * g ≠ g * b := not_commute_of_isTwin hb hg hag
  have h1 := hμ.mate_mate hP ha haμ hg hag
  have h2 := hμ.mate_mate hP hb.2.1 hbμ hg hbg
  have hmE := hμ.mate_mem hP ha haμ hg hag
  have hmμ := hμ.mate_notMem hP ha haμ hg hag
  have hma : mate E μ a g * a ≠ a * mate E μ a g := fun e =>
    hμ.mate_not_commute hP ha haμ hg hag e.symm
  rw [← h1, ← h2, ← h, hμ.mate_congr hP hmE hmμ ha hma hb]

theorem mate_mate_conj_iff {s f g : H} (hs : s ∈ μ) (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hgμ : g ∉ μ) (hsg : s * g ≠ g * s) (hfG : f * (s * g * s) ≠ s * g * s * f) :
    mate E μ (mate E μ f (s * g * s)) g = g ↔ mate E μ f (s * g * s) = s * g * s := by
  have hsE := hμ.subset hs
  have hGE : s * g * s ∈ E := Pair.mul_mul_mem hP hsE hg
  have hAE := hμ.mate_mem hP hf hfμ hGE hfG
  have hAμ := hμ.mate_notMem hP hf hfμ hGE hfG
  have hGA := hμ.isTwin_mate hP hf hfμ hGE hfG
  have hgG : g * (s * g * s) ≠ s * g * s * g := fun e =>
    Pair.mul_mul_not_commute_right hP hsE hg hsg e.symm
  have hAg : mate E μ f (s * g * s) * g ≠ g * mate E μ f (s * g * s) :=
    not_commute_of_isTwin hGA hg fun e => hgG e.symm
  have hmc : mate E μ g (s * g * s) = s * g * s := hμ.mate_conj hP hs hg hgμ hsg
  constructor
  · intro h
    have h1 := hμ.mate_mate hP hAE hAμ hg hAg
    rw [h] at h1
    rw [← h1, hμ.mate_congr hP hg hgμ hGE hgG hGA, hmc]
  · intro h
    have h1 := hμ.mate_mate hP hg hgμ hGE hgG
    rw [hmc, ← h] at h1
    exact h1

theorem ncard_twinClass_diff (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4) {g : H} (hg : g ∈ E) :
    (twinClass E g \ μ).ncard = 3 := by
  have := Pair.finite hP
  have e : twinClass E g \ μ = twinClass E g \ {sec E μ g} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxμ⟩
      exact ⟨hx, fun h => hxμ (h ▸ hμ.sec_mem hg)⟩
    · rintro ⟨hx, hxs⟩
      exact ⟨hx, fun hxμ => hxs (hμ.eq_sec hxμ hx)⟩
  rw [e, Set.ncard_sdiff_singleton_of_mem (show sec E μ g ∈ twinClass E g from hμ.isTwin_sec hg),
    h4 g hg]

theorem bform_row (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4) {s f g : H} (hs : s ∈ μ)
    (hf : f ∈ E) (hfμ : f ∉ μ) (hsf : s * f ≠ f * s) (hg : g ∈ E) (hgμ : g ∉ μ) :
    bform μ (s * f * s) g = bform μ f g + bform μ (mate E μ f s) g := by
  have hsE := hμ.subset hs
  have hfs : f * s ≠ s * f := fun e => hsf e.symm
  have hmE := hμ.mate_mem hP hf hfμ hsE hfs
  have hmμ := hμ.mate_notMem hP hf hfμ hsE hfs
  have hsm := hμ.isTwin_mate hP hf hfμ hsE hfs
  have hL : bform μ (s * f * s) g = bform μ f (s * g * s) := by
    have := hμ.bform_conj hP (f := f) (g := s * g * s) hs
    rwa [Pair.mul_mul_mul_mul hP hsE] at this
  rw [hL]
  by_cases hsg : s * g = g * s
  ·
    rw [(Pair.mul_mul_eq_self_iff hP hsE g).2 hsg]
    have hmg : mate E μ f s * g = g * mate E μ f s := ((hsm.2.2.2 g hg).1 hsg.symm).symm
    rw [bform_of_commute hmg, add_zero]
  have hGE : s * g * s ∈ E := Pair.mul_mul_mem hP hsE hg
  have hGμ : s * g * s ∉ μ := hμ.conj_notMem hP hs hgμ
  have hFE : s * f * s ∈ E := Pair.mul_mul_mem hP hsE hf
  have hFμ : s * f * s ∉ μ := hμ.conj_notMem hP hs hfμ
  have hgsg : g * (s * g * s) * g = s := by
    rw [Pair.mul_mul_eq hP hsE hg hsg, Pair.mul_mul_mul_mul hP hg]
  have hmg : mate E μ f s * g ≠ g * mate E μ f s := not_commute_of_isTwin hsm hg hsg
  have hsG : s * (s * g * s) ≠ s * g * s * s := fun e =>
    Pair.mul_mul_not_commute_left hP hsE hsg e.symm
  have hgG : g * (s * g * s) ≠ s * g * s * g := fun e =>
    Pair.mul_mul_not_commute_right hP hsE hg hsg e.symm
  have hfF : f * (s * f * s) ≠ s * f * s * f := fun e =>
    Pair.mul_mul_not_commute_right hP hsE hf hsf e.symm
  have hfsf : f * s * f = s * f * s := Pair.mul_mul_eq hP hf hsE hfs
  have hcomm_iff : ∀ a b : H, s * a * s * (s * b * s) = s * b * s * (s * a * s) ↔ a * b = b * a :=
    fun a b => by have := conj_commute_iff s a b; rwa [Pair.inv_eq hP hsE] at this
  have hz : ∀ x y : ZMod 2, (x = 0 ↔ y = 0) → x = y := fun x y h => by
    rcases Symplectic.zmod_two_cases x with hx | hx <;>
      rcases Symplectic.zmod_two_cases y with hy | hy <;> simp_all
  have hmm : mate E μ (mate E μ f s) f = f := hμ.mate_mate hP hf hfμ hsE hfs
  by_cases h1 : IsTwin E f g
  ·
    have hFG : IsTwin E (s * f * s) (s * g * s) := by
      have := isTwin_conj hP s h1; rwa [Pair.inv_eq hP hsE] at this
    have hfG : f * (s * g * s) ≠ s * g * s * f := not_commute_of_isTwin' hFG hf hfF
    rw [bform_of_commute h1.2.2.1, zero_add]
    refine hz _ _ ?_
    rw [hμ.bform_eq_zero_iff_mate hP hf hfμ hGE hGμ hfG,
      hμ.bform_eq_zero_iff_mate hP hmE hmμ hg hgμ hmg,
      hμ.mate_congr hP hf hfμ hFE hfF hFG, hμ.mate_conj hP hs hf hfμ hsf,
      hμ.mate_congr hP hmE hmμ hf (fun e => hμ.mate_not_commute hP hf hfμ hsE hfs e.symm) h1, hmm]
    constructor
    · intro h
      rw [← Pair.mul_mul_mul_mul hP hsE f, h, Pair.mul_mul_mul_mul hP hsE g]
    · intro h; rw [h]
  by_cases h2 : IsTwin E (s * f * s) g
  ·
    have hfG : f * (s * g * s) = s * g * s * f := by
      have := isTwin_conj hP s h2
      rw [Pair.inv_eq hP hsE, Pair.mul_mul_mul_mul hP hsE] at this
      exact this.2.2.1
    have hfg : f * g ≠ g * f := not_commute_of_isTwin' h2 hf hfF
    rw [bform_of_commute hfG]
    have hsF : s * (s * f * s) ≠ s * f * s * s := fun e =>
      Pair.mul_mul_not_commute_left hP hsE hsf e.symm
    have hmF : mate E μ f s * (s * f * s) ≠ s * f * s * mate E μ f s :=
      not_commute_of_isTwin hsm hFE hsF
    have hcol : IsTwin E (f * s * f) (s * f * s) := by rw [hfsf]; exact isTwin_refl hFE
    have : bform μ f g = bform μ (mate E μ f s) g := by
      refine hz _ _ ?_
      rw [hμ.bform_eq_zero_iff_mate hP hf hfμ hg hgμ hfg,
        hμ.bform_eq_zero_iff_mate hP hmE hmμ hg hgμ hmg,
        hμ.mate_congr hP hf hfμ hFE hfF h2, hμ.mate_congr hP hmE hmμ hFE hmF h2,
        hμ.mate_mate_eq_of_isTwin hP hf hfμ hsE hfs hcol, hμ.mate_conj hP hs hf hfμ hsf]
    rw [this, Symplectic.zmod_two_add_self]
  have hnot : ¬ (f * g = g * f ∧ f * (s * g * s) = s * g * s * f) := by
    rintro ⟨ha, hb⟩
    have hc : Commute f (g * (s * g * s) * g) :=
      ((Commute.mul_right (show Commute f g from ha) (show Commute f (s * g * s) from hb)).mul_right
        (show Commute f g from ha))
    rw [hgsg] at hc
    exact hsf hc.eq.symm
  have hmG : mate E μ f s * (s * g * s) ≠ s * g * s * mate E μ f s :=
    not_commute_of_isTwin hsm hGE hsG
  have hcolm : IsTwin E (mate E μ f s * (s * g * s) * mate E μ f s) g := by
    have := Pair.isTwin_mul_mul hP hsm hGE hsG
    rw [Pair.mul_mul_mul_mul hP hsE g] at this
    exact isTwin_symm this
  have hmcol : mate E μ (mate E μ (mate E μ f s) (s * g * s)) g = mate E μ (mate E μ f s) g :=
    hμ.mate_mate_eq_of_isTwin hP hmE hmμ hGE hmG hcolm
  have hgF : g * (s * f * s) = s * f * s * g ↔ f * (s * g * s) = s * g * s * f := by
    have := hcomm_iff (s * g * s) f
    rw [Pair.mul_mul_mul_mul hP hsE g] at this
    rw [this]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  by_cases hfg : f * g = g * f
  ·
    have hfG : f * (s * g * s) ≠ s * g * s * f := fun e => hnot ⟨hfg, e⟩
    rw [bform_of_commute hfg, zero_add]
    have hda : mate E μ (mate E μ f s) (s * g * s) = mate E μ f (s * g * s) :=
      hμ.mate_mate_eq_of_commute hP hf hfμ hsE hGE hfs hsG hfG (by
        rw [hfsf]; exact (hcomm_iff g f).2 hfg.symm)
    refine hz _ _ ?_
    rw [hμ.bform_eq_zero_iff_mate hP hf hfμ hGE hGμ hfG,
      hμ.bform_eq_zero_iff_mate hP hmE hmμ hg hgμ hmg, ← hmcol, hda,
      hμ.mate_mate_conj_iff hP hs hf hfμ hg hgμ hsg hfG]
  by_cases hfG : f * (s * g * s) = s * g * s * f
  ·
    rw [bform_of_commute hfG]
    have hdb : mate E μ (mate E μ f s) g = mate E μ f g :=
      hμ.mate_mate_eq_of_commute hP hf hfμ hsE hg hfs hsg hfg (by rw [hfsf]; exact hgF.2 hfG)
    have : bform μ f g = bform μ (mate E μ f s) g := by
      refine hz _ _ ?_
      rw [hμ.bform_eq_zero_iff_mate hP hf hfμ hg hgμ hfg,
        hμ.bform_eq_zero_iff_mate hP hmE hmμ hg hgμ hmg, hdb]
    rw [this, Symplectic.zmod_two_add_self]
  have hGg : s * g * s * g ≠ g * (s * g * s) := fun e => hgG e.symm
  have hAE := hμ.mate_mem hP hf hfμ hg hfg
  set A := mate E μ f g with hA
  set B := mate E μ (mate E μ f (s * g * s)) g with hB
  set C := mate E μ (mate E μ f s) g with hC
  have hAGE := hμ.mate_mem hP hf hfμ hGE hfG
  have hAGμ := hμ.mate_notMem hP hf hfμ hGE hfG
  have hGAG := hμ.isTwin_mate hP hf hfμ hGE hfG
  have hAGg : mate E μ f (s * g * s) * g ≠ g * mate E μ f (s * g * s) :=
    not_commute_of_isTwin hGAG hg hGg
  have hAS : A ∈ twinClass E g \ μ :=
    ⟨hμ.isTwin_mate hP hf hfμ hg hfg, hμ.mate_notMem hP hf hfμ hg hfg⟩
  have hBS : B ∈ twinClass E g \ μ :=
    ⟨hμ.isTwin_mate hP hAGE hAGμ hg hAGg, hμ.mate_notMem hP hAGE hAGμ hg hAGg⟩
  have hCS : C ∈ twinClass E g \ μ :=
    ⟨hμ.isTwin_mate hP hmE hmμ hg hmg, hμ.mate_notMem hP hmE hmμ hg hmg⟩
  have hAC : A ≠ C := fun e => hμ.mate_mate_ne_of_affine hP hf hfμ hsE hg hfs hsg hfg
    (by rw [hfsf]; exact fun h => hfG (hgF.1 h)) e.symm
  have hBC : B ≠ C := by
    intro e
    rw [← hmcol] at e
    have hAG := isTwin_trans (isTwin_symm hGAG) (hμ.isTwin_mate hP hmE hmμ hGE hmG)
    have := hμ.mate_injOn hP hAGE hAGμ hAG (hμ.mate_notMem hP hmE hmμ hGE hmG) hg hAGg e
    exact hμ.mate_mate_ne_of_affine hP hf hfμ hsE hGE hfs hsG hfG
      (by rw [hfsf]; exact fun h => hfg ((hcomm_iff g f).1 h).symm) this.symm
  have hAB : A ≠ B := by
    intro e
    refine hμ.mate_mate_ne_of_affine hP hf hfμ hGE hg hfG hGg hfg ?_ e.symm
    intro h
    rw [Pair.mul_mul_eq hP hf hGE hfG] at h
    have h' := (conj_commute_iff (s * g * s) g (s * g * s * f * (s * g * s))).2 h
    rw [Pair.inv_eq hP hGE, Pair.mul_mul_mul_mul hP hGE, Pair.mul_mul_eq hP hGE hg hGg,
      hgsg] at h'
    exact hsf h'
  have hA0 : bform μ f g = 0 ↔ A = g := hμ.bform_eq_zero_iff_mate hP hf hfμ hg hgμ hfg
  have hB0 : bform μ f (s * g * s) = 0 ↔ B = g := by
    rw [hμ.bform_eq_zero_iff_mate hP hf hfμ hGE hGμ hfG, hB,
      hμ.mate_mate_conj_iff hP hs hf hfμ hg hgμ hsg hfG]
  have hC0 : bform μ (mate E μ f s) g = 0 ↔ C = g :=
    hμ.bform_eq_zero_iff_mate hP hmE hmμ hg hgμ hmg
  have h1 := fun {x : ZMod 2} (h : x ≠ 0) => Symplectic.zmod_two_eq_one_of_ne_zero h
  rcases eq_or_eq_or_eq_of_ncard_eq_three (hμ.ncard_twinClass_diff hP h4 hg) hAS hBS hCS hAB hAC
    hBC ⟨self_mem_twinClass hg, hgμ⟩ with hx | hx | hx
  · rw [h1 (fun h => hAB (hx ▸ (hB0.1 h).symm)), hA0.2 hx.symm,
      h1 (fun h => hAC (hx ▸ (hC0.1 h).symm)), zero_add]
  · rw [hB0.2 hx.symm, h1 (fun h => hAB (hx ▸ hA0.1 h)), h1 (fun h => hBC (hx ▸ (hC0.1 h).symm))]
    rfl
  · rw [h1 (fun h => hBC (hx ▸ hB0.1 h)), h1 (fun h => hAC (hx ▸ hA0.1 h)), hC0.2 hx.symm,
      add_zero]

theorem vec_conj (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4) {s : H} (hs : s ∈ μ) (f : XT E μ)
    (hsf : s * f ≠ f * s) :
    vec (⟨s * f * s, Pair.mul_mul_mem hP (hμ.subset hs) f.2.1, hμ.conj_notMem hP hs f.2.2⟩ :
        XT E μ) =
      vec f + vec (⟨mate E μ f s, hμ.mate_mem hP f.2.1 f.2.2 (hμ.subset hs) fun e => hsf e.symm,
        hμ.mate_notMem hP f.2.1 f.2.2 (hμ.subset hs) fun e => hsf e.symm⟩ : XT E μ) := by
  refine eq_of_secForm_vec hP fun g => ?_
  rw [map_add, LinearMap.add_apply, secForm_vec, secForm_vec, secForm_vec]
  exact hμ.bform_row hP h4 hs f.2.1 f.2.2 hsf g.2.1 g.2.2

theorem vec_add_add (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4) {a b c : XT E μ}
    (hb : IsTwin E a b) (hc : IsTwin E a c) (hab : (a : H) ≠ b) (hac : (a : H) ≠ c)
    (hbc : (b : H) ≠ c) : vec a + vec b + vec c = 0 := by
  refine eq_of_secForm_vec hP fun g => ?_
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, secForm_vec, secForm_vec,
    secForm_vec, map_zero, LinearMap.zero_apply]
  have haE := a.2.1
  by_cases hga : (g : H) * a = a * g
  · have hgb : (g : H) * b = b * g := (hb.2.2.2 g g.2.1).1 hga
    have hgc : (g : H) * c = c * g := (hc.2.2.2 g g.2.1).1 hga
    rw [bform_of_commute hga.symm, bform_of_commute hgb.symm, bform_of_commute hgc.symm]
    rfl
  have hgb : (g : H) * b ≠ b * g := fun e => hga ((hb.2.2.2 g g.2.1).2 e)
  have hgc : (g : H) * c ≠ c * g := fun e => hga ((hc.2.2.2 g g.2.1).2 e)
  have hgE := g.2.1
  have hgμ := g.2.2
  set M := mate E μ g a
  have hM : M ∈ twinClass E a \ μ :=
    ⟨hμ.isTwin_mate hP hgE hgμ haE hga, hμ.mate_notMem hP hgE hgμ haE hga⟩
  have key : ∀ x : XT E μ, IsTwin E a x → (g : H) * x ≠ x * g →
      (bform μ (x : H) g = 0 ↔ (x : H) = M) := by
    intro x hx hgx
    rw [bform_comm hP x.2.1 hgE, hμ.bform_eq_zero_iff_mate hP hgE hgμ x.2.1 x.2.2 hgx,
      hμ.mate_congr hP hgE hgμ haE hga hx]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have h1 := fun {x : ZMod 2} (h : x ≠ 0) => Symplectic.zmod_two_eq_one_of_ne_zero h
  rcases eq_or_eq_or_eq_of_ncard_eq_three (hμ.ncard_twinClass_diff hP h4 haE)
    ⟨self_mem_twinClass haE, a.2.2⟩ ⟨hb, b.2.2⟩ ⟨hc, c.2.2⟩ hab hac hbc hM with h | h | h
  · rw [(key a (isTwin_refl haE) hga).2 h.symm,
      h1 (fun e => hab ((((key b hb hgb).1 e).trans h).symm)),
      h1 (fun e => hac ((((key c hc hgc).1 e).trans h).symm))]
    rfl
  · rw [h1 (fun e => hab (((key a (isTwin_refl haE) hga).1 e).trans h)),
      (key b hb hgb).2 h.symm, h1 (fun e => hbc ((((key c hc hgc).1 e).trans h).symm))]
    rfl
  · rw [h1 (fun e => hac (((key a (isTwin_refl haE) hga).1 e).trans h)),
      h1 (fun e => hbc (((key b hb hgb).1 e).trans h)), (key c hc hgc).2 h.symm]
    rfl

end IsTwinSection

end O2Mod

end CFSG.Fischer.Classification
