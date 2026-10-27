module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Lin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Spin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Exc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
public import CFSG.Assembly.InCatalogConverse

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314

namespace Bridge2314

theorem coe_mem_normalizer_map {A : Type} [Group A] {L : Subgroup A} {R : Subgroup L} {g : L}
    (hg : g ∈ Subgroup.normalizer (R : Set L)) :
    (g : A) ∈ Subgroup.normalizer ((R.map L.subtype : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  change ∀ y : L, y ∈ R ↔ g * y * g⁻¹ ∈ R at hg
  change ∀ h : A, h ∈ R.map L.subtype ↔ (g : A) * h * (g : A)⁻¹ ∈ R.map L.subtype
  have hinj : Function.Injective L.subtype := Subtype.val_injective
  have hle : R.map L.subtype ≤ L := Subgroup.map_subtype_le R
  intro h
  by_cases hh : h ∈ L
  · obtain ⟨y, rfl⟩ : ∃ y : L, (y : A) = h := ⟨⟨h, hh⟩, rfl⟩
    have e1 : (y : A) ∈ R.map L.subtype ↔ y ∈ R := by
      have := Subgroup.mem_map_iff_mem (f := L.subtype) hinj (K := R) (x := y)
      simpa using this
    have e2 : (g : A) * (y : A) * (g : A)⁻¹ ∈ R.map L.subtype ↔ g * y * g⁻¹ ∈ R := by
      have hc : (g : A) * (y : A) * (g : A)⁻¹ = ((g * y * g⁻¹ : L) : A) := by simp
      rw [hc]
      have := Subgroup.mem_map_iff_mem (f := L.subtype) hinj (K := R) (x := g * y * g⁻¹)
      simpa using this
    rw [e1, e2]
    exact hg y
  · have hh' : (g : A) * h * (g : A)⁻¹ ∉ L := by
      intro hc
      apply hh
      have hid : h = (g : A)⁻¹ * ((g : A) * h * (g : A)⁻¹) * (g : A) := by group
      rw [hid]
      exact L.mul_mem (L.mul_mem (L.inv_mem g.2) hc) g.2
    exact ⟨fun hx => absurd (hle hx) hh, fun hx => absurd (hle hx) hh'⟩

theorem normalizer_le_subgroupOf {A : Type} [Group A] [Finite A] {L F J : Subgroup A} {f : ℕ}
    (hf : f.Prime) {Q : Subgroup L} (hQ : Q.map L.subtype = F)
    (hJ : ∀ S₀ : Subgroup A, S₀ ≤ F → 2 ≤ CFSG.Open.pRank f S₀ →
      Subgroup.normalizer (S₀ : Set A) ⊓ L ≤ J)
    {R : Subgroup L} (hRQ : R ≤ Q) (hR : 2 ≤ CFSG.Open.pRank f R) :
    Subgroup.normalizer (R : Set L) ≤ J.subgroupOf L := by
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  have hS : R.map L.subtype ≤ F := (Subgroup.map_mono hRQ).trans hQ.le
  have hrank : 2 ≤ CFSG.Open.pRank f (R.map L.subtype) :=
    hR.trans (CFSG.SectionRank.pRank_le_map hf.one_lt L.subtype L.subtype_injective R)
  exact hJ _ hS hrank ⟨coe_mem_normalizer_map hg, g.2⟩

theorem le_of_glbCore_two_eq_top {A : Type} [Group A] [Finite A] {L F J : Subgroup A} {f : ℕ}
    (hf : f.Prime) {Q : Sylow f L} (hQ : (Q : Subgroup L).map L.subtype = F)
    (hJ : ∀ S₀ : Subgroup A, S₀ ≤ F → 2 ≤ CFSG.Open.pRank f S₀ →
      Subgroup.normalizer (S₀ : Set A) ⊓ L ≤ J)
    (htop : CFSG.Open.GLBCore f 2 (Q : Subgroup L) = ⊤) : L ≤ J := by
  have hle : CFSG.Open.GLBCore f 2 (Q : Subgroup L) ≤ J.subgroupOf L := by
    unfold CFSG.Open.GLBCore
    apply sSup_le
    rintro N ⟨R, hRQ, hR, rfl⟩
    exact normalizer_le_subgroupOf hf hQ hJ hRQ hR
  rw [htop] at hle
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top ⟨x, hx⟩))

end Bridge2314

namespace Fact2314

section Certified


theorem charPGen2 : CharPGen2 :=
  charPGen2_of_charPGen2At
    (charPGen2At_or charPGen2At_sl (charPGen2At_or charPGen2At_sp (charPGen2At_or charPGen2At_su
      (charPGen2At_or charPGen2At_bOdd (charPGen2At_or charPGen2At_d
        (charPGen2At_or charPGen2At_twistedD charPGen2At_exceptional))))))
    fun _ _ _ hp2 hchar hrank => CFSG.AGLEmbedding.exists_family_of_odd hp2 hchar hrank

end Certified

end Fact2314

section Certified


theorem kFact2314_holds : KFact2314 := by
  intro A _ _ L F f hf hf2 hL hF J hJ
  obtain ⟨Q, hQ⟩ := hF
  obtain ⟨i, hi, ⟨e⟩⟩ := hL
  rcases i with ⟨p, hp⟩ | ⟨m, hm⟩ | d | s
  · exact False.elim hi
  · exact False.elim hi
  · obtain ⟨dd, hv⟩ := d
    obtain ⟨hchar, hdih, hree⟩ := hi
    have hs : IsSimpleGroup L :=
      e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple ⟨dd, hv⟩).2
    have hrank : ¬ CFSG.AGLEmbedding.IsRankOneLieIndex dd := by
      rintro (⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨m, rfl⟩)
      · apply hdih
        simp only [TauCeti.LieTypeIndex.characteristic_A] at hchar
        simp only [IsDihedralTypeIndex]
        rw [hchar]
        exact hf2
      · apply hdih
        simp only [TauCeti.LieTypeIndex.characteristic_twistedA] at hchar
        simp only [IsDihedralTypeIndex]
        rw [hchar]
        exact hf2
      · exact hree trivial
    exact Bridge2314.le_of_glbCore_two_eq_top hf hQ hJ
      (Fact2314.charPGen2 L hs ⟨dd, hv⟩ ⟨e⟩ f hf hf2 hchar.symm hrank Q)
  · exact False.elim hi

end Certified

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
