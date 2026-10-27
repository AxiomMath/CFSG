module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Clauses


variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem inner_innDiag_any {X L : Subgroup G} {g : G} (hL : GLAPComponent p X L)
    (hchev : IsChevSimple 2 (PSimple p L)) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hin : InducesInnerMod p L g) : InnDiagOn p (Subgroup.zpowers g) L := by
  refine ⟨Subgroup.zpowers_le.2 hg, ?_⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_any hL
  have h0 := CFSG.StandardType.ChevTwo.ys08_holds (PQuot p L) hq hchev
  have h1 := canon_marking_and_labelAll_simple (P' := RawInnBody 3)
    (fun lab hlab => canonRawInn' Nat.prime_three (by norm_num) hlab) h0
  refine Canonical.largeEvenMarking_mono ?_ h1
  rintro lab R _ I F θ ⟨-, -, -, hinn, -⟩ a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hak : g ^ k ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ hg k
  have hmem : indAut p L (g ^ k) hak ∈ inner (PSimple p L) := by
    have e : indAut p L (g ^ k) hak = (indAut p L g hg) ^ k := by
      unfold indAut
      rw [← map_zpow]
      congr 1
      exact Subtype.ext (by simp [zpow_neg, inv_zpow])
    rw [e]
    exact Subgroup.zpow_mem _ ((indAut_mem_inner_iff_any hq hg).2 hin) k
  obtain ⟨s, hs⟩ := hmem
  refine ⟨MulAut.congr θ (indAut p L (g ^ k) hak), ?_, (induces_indRel_iff hak θ).2 rfl⟩
  rw [← hs, congr_conj]
  exact hinn _

theorem field_nonInnDiag_any {X L : Subgroup G} {g : G} (hL : GLAPComponent p X L)
    (hF : FieldOn p g L) : NonInnDiag p g L := by
  have hp1 : p ≠ 1 := by
    rintro rfl
    exact not_glaPComponent_one hL
  refine ⟨hF.1, fun hD => ?_⟩
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p L)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p L g) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh g (Subgroup.mem_zpowers g)) hD.2
  have h1 := marking_transport (indRel p L g) hdiag hF.2
  have h2 := canon_marking_and_labelAll_simple (P' := RawInnBody p)
    (fun lab hlab => canonRawInnAny hp1 hlab) h1
  obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨⟨hlt, f, hf, u, hu, hord, hind⟩, φ, hφ, hind'⟩,
    hmul, hinv, hinn, hfI⟩ := Canonical.largeEvenMarking_exists h2
  have e1 := (induces_indRel_iff hF.1 θ).1 hind
  have e2 := (induces_indRel_iff hF.1 θ).1 hind'
  have e3 : φ = u * f * u⁻¹ := e2.trans e1.symm
  have hfI' : f ∈ I := by
    have : f = u⁻¹ * φ * u := by rw [e3]; group
    rw [this]
    exact hmul (u⁻¹ * φ) (hmul u⁻¹ (hinv u hu) φ hφ) u hu
  exact hfI f hf hord hfI'

theorem td4_nonInnDiag_any {X L : Subgroup G} {g : G}
    (hL : GLAPComponent p X L) (hTD4 : IsTD4 p L) (hNI : NonInner p g L) : NonInnDiag p g L := by
  refine ⟨hNI.1, fun hD => hNI.2 ?_⟩
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p L)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p L g) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh g (Subgroup.mem_zpowers g)) hD.2
  have h1 := canon_marking_and_labelAll_simple (P' := TD4Inn)
    (fun lab hlab => canonTD4Inn hlab) hdiag
  obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨φ, hφ, hind⟩, hTD⟩ :=
    Canonical.largeEvenMarking_exists h1
  have hI : I ⊆ LargeEvenInnSet R := hTD (PSimple p L) hTD4 ⟨θ⟩
  have e := (induces_indRel_iff hNI.1 θ).1 hind
  have hmem : φ ∈ (MulAut.conj : R →* MulAut R).range := by
    obtain ⟨r, hr⟩ := hI hφ
    exact ⟨r, hr⟩
  rw [← indAut_mem_inner_iff_any (isQuasisimple_pQuot_any hL) hNI.1]
  rw [e] at hmem
  exact (ggCongr_mem_range_conj_iff θ _).1 hmem

theorem autCalcAt_all (G : Type) [Group G] [Finite G] (p : ℕ) : AutCalcAt G p where
  field_nonInnDiag := fun X L g hL _ hF => field_nonInnDiag_any hL hF
  td4_nonInnDiag := fun X L g hL hTD4 hNI => td4_nonInnDiag_any hL hTD4 hNI
  inner_innDiag := fun X L g hL hchev hg hin => inner_innDiag_any hL hchev hg hin
  innDiag_unif := fun X L A _ _ hA h => innDiag_unif_holds hA h
  td4_not_field := fun X L g _ _ hTD4 => td4_not_field_holds hTD4

end Clauses

end MI

end CFSG.LocalAnalysis.GLTheoremA
