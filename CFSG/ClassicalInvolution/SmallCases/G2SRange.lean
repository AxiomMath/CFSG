module

public import CFSG.ClassicalInvolution.SmallCases.G2SBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem mem_nbhd_of_compMembers (C : Ctx p f Ω L w)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) (i₁ : Fin D.card)
    (htag : D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4) {N : Subgroup G}
    (hN : N ∈ compMembers Ω w D i₁) : N ∈ nbhd Ω L := by
  have hN' : N ∈ insert L (nbhd Ω L) := C.omega_eq ▸ hN.1
  rcases hN' with rfl | hN'
  · exfalso
    obtain ⟨i₀, hi₀t, -, hi₀⟩ := locImg_eq_range_of_involution C.mfz D C.mem_centralizingMembers
      C.cls
    have hle0 : locImg Ω w N ≤ (D.hom i₀).range := hi₀ ▸ le_rfl
    have := eq_of_locImg_le_range C.inClass C.exact D hN.1 hle0 hN.2
    subst this
    rcases htag with h | h <;> rw [h] at hi₀t <;> exact absurd hi₀t (by decide)
  · exact hN'

theorem range_eq (C : Ctx p f Ω L w)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) (i₁ : Fin D.card) (hcard : D.card = 2)
    (htag : D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) :
    (D.hom i₁).range = ⨆ N ∈ nbhd Ω L, locImg Ω w N := by
  apply le_antisymm
  · set S₀ : Subgroup (locQuot Ω w) := ⨆ N ∈ nbhd Ω L, locImg Ω w N with hS₀
    have hsimple := Asc77.T3Typed.isSimpleGroup_model_of_g2d4 C.odd (D.admissible i₁) htag
    obtain ⟨R₀, hR₀, hmem⟩ := D.meets i₁
    obtain ⟨M₀, hM₀, hM₀R⟩ := mem_locFamily_iff.mp hmem
    have hbot : R₀ ≠ ⊥ := by
      intro h
      apply locImg_ne_bot C.inClass C.exact hM₀
      rw [hM₀R, h, Subgroup.map_bot]
    have hΦ : ConjInvariant (locFamily Ω w) :=
      conjInvariant_oddQuotientFamily
        (inClass_local C.inClass {w} ⟨L, C.mem_centralizingMembers⟩).conjInvariant
    have htop : Subgroup.normalClosure (SetLike.coe R₀) = ⊤ := by
      have := hsimple
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure (SetLike.coe R₀)) with h | h
      · exfalso
        apply hbot
        rw [eq_bot_iff]
        intro x hx
        have hx' : x ∈ Subgroup.normalClosure (SetLike.coe R₀) := Subgroup.subset_normalClosure hx
        rw [h] at hx'
        exact hx'
      · exact h
    rintro _ ⟨g, rfl⟩
    have hg : g ∈ Subgroup.normalClosure (SetLike.coe R₀) := htop ▸ Subgroup.mem_top g
    have hsub : Group.conjugatesOfSet (SetLike.coe R₀) ⊆ (SetLike.coe (S₀.comap (D.hom i₁))) := by
      intro c hc
      obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.mp hc
      obtain ⟨x, hx⟩ := isConj_iff.mp hbc
      have hΦ' : (conjSub x R₀).map (D.hom i₁) ∈ locFamily Ω w := by
        rw [← conjSub_map]
        exact hΦ _ _ hmem
      obtain ⟨N', hN', hN'R⟩ := mem_locFamily_iff.mp hΦ'
      have hle : locImg Ω w N' ≤ (D.hom i₁).range := hN'R ▸ Subgroup.map_le_range _ _
      have hnb : N' ∈ nbhd Ω L := C.mem_nbhd_of_compMembers D i₁ htag ⟨hN', hle⟩
      have hcmem : c ∈ conjSub x R₀ := by
        rw [mem_conjSub_iff, ← hx]
        simpa [mul_assoc] using hb
      have hcm : D.hom i₁ c ∈ locImg Ω w N' := by
        rw [hN'R]
        exact Subgroup.mem_map_of_mem _ hcmem
      exact le_iSup₂ (f := fun N (_ : N ∈ nbhd Ω L) => locImg Ω w N) N' hnb hcm
    exact (Subgroup.closure_le (S₀.comap (D.hom i₁))).mpr hsub hg
  · exact iSup₂_le fun N hN => (C.nbhd_mem_compMembers D i₁ hcard htag hrest hN).2

end Ctx

end CFSG.ClassicalInvolution.NDB.G2S
