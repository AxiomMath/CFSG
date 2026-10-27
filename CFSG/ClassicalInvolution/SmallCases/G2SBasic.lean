module

public import CFSG.ClassicalInvolution.SmallCases.G2SCtx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem mem_centralizingMembers (C : Ctx p f Ω L w) : L ∈ centralizingMembers Ω {w} :=
  ⟨C.mem, le_centralizer_of_isClassicalMember C.cls⟩

theorem omega_eq (C : Ctx p f Ω L w) : centralizingMembers Ω {w} = insert L (nbhd Ω L) := by
  obtain ⟨D, i₁, -, -, -⟩ := C.exists_data
  ext N
  constructor
  · intro hN
    by_cases hNL : N = L
    · exact Or.inl hNL
    · right
      rcases commutes_or_eq_of_involution C.mfz C.inClass C.exact C.p1 D
        C.mem_centralizingMembers hN C.cls with h | h
      · exact ⟨hN.1, hNL, h⟩
      · exact absurd h hNL
  · rintro (rfl | hN)
    · exact C.mem_centralizingMembers
    · exact mem_centralizingMembers_of_commutes hN.1 C.cls.mem hN.2.2.symm

theorem nbhd_mem_centralizingMembers (C : Ctx p f Ω L w) {N : Subgroup G} (hN : N ∈ nbhd Ω L) :
    N ∈ centralizingMembers Ω {w} := by
  rw [C.omega_eq]
  exact Or.inr hN

theorem nbhd_mem_compMembers (C : Ctx p f Ω L w)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) (i₁ : Fin D.card) (hcard : D.card = 2)
    (htag : D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) {N : Subgroup G} (hN : N ∈ nbhd Ω L) :
    N ∈ compMembers Ω w D i₁ := by
  have hNw := C.nbhd_mem_centralizingMembers hN
  refine ⟨hNw, ?_⟩
  obtain ⟨j, hj⟩ := Gaps.exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hNw, rfl⟩)
  by_cases hji : j = i₁
  · subst hji
    exact hj
  · exfalso
    obtain ⟨i₀, hi₀t, hi₀r, hi₀⟩ := locImg_eq_range_of_involution C.mfz D
      C.mem_centralizingMembers C.cls
    have hi₀ne : i₀ ≠ i₁ := by
      rintro rfl
      rcases htag with h | h <;> rw [h] at hi₀t <;> exact absurd hi₀t (by decide)
    have hj₀ : j = i₀ := by
      refine Fin.ext ?_
      have h1 := j.isLt
      have h2 := i₀.isLt
      have h3 := i₁.isLt
      have h4 := Fin.val_ne_of_ne hji
      have h5 := Fin.val_ne_of_ne hi₀ne
      omega
    subst hj₀
    have hNimg := Exotic.locImg_eq_range_of_le_a1 C.inClass C.exact D hNw (hrest j hji) hj
    exact hN.2.1 (locImg_injOn C.inClass C.p1 hNw C.mem_centralizingMembers
      (hNimg.trans hi₀.symm))

theorem nbhd_noncommuting (C : Ctx p f Ω L w) {N N' : Subgroup G} (hN : N ∈ nbhd Ω L)
    (hN' : N' ∈ nbhd Ω L) (hne : N ≠ N') : ¬ Commutes N N' := by
  intro hcomm
  obtain ⟨D, i₁, hcard, htag, hrest⟩ := C.exists_data
  obtain ⟨w₀, hw₀⟩ := C.inClass.classical N hN.1
  obtain ⟨w₁, hw₁⟩ := C.inClass.classical N' hN'.1
  have h := eq_involution_of_commuting_pair C.shared C.odd C.inClass C.p1 D htag
    (C.nbhd_mem_compMembers D i₁ hcard htag hrest hN)
    (C.nbhd_mem_compMembers D i₁ hcard htag hrest hN') hw₀ hw₁ hcomm
  subst h
  exact hne (C.uniq N hN.1 N' hN'.1 w₀ hw₀ hw₁)

end Ctx

end CFSG.ClassicalInvolution.NDB.G2S
