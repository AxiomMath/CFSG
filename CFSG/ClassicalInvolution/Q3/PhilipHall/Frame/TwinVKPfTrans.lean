module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVKPfSet
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace TwinConnT

variable {G : Type} [Group G] [Finite G]

theorem conjSub_le_of_mem_normalizer {X' L : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (X' : Set G)) (h : L ≤ X') : conjSub c L ≤ X' := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 := h hx
  have h2 := (Subgroup.mem_normalizer_iff.mp hc _).mp h1
  simpa [mul_assoc] using h2

theorem conj_mem_twinSet_of_fix {K₀ : Subgroup G} {t : G} (hΩ : HypOmegaGen (CoreAssembly.conjClass K₀))
    (hz : IsUniqueInvolution K₀ t) {J : Subgroup G}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass K₀) K₀) {c : G} (hct : c * t * c⁻¹ = t) :
    conjSub c J ∈ twinSet (CoreAssembly.conjClass K₀) K₀ := by
  refine ⟨hΩ.conjInvariant c J hJ.1, t, hz, ?_⟩
  have := (TwinSecXg.isUniqueInvolution_of_mem_twinSet hz hJ).conj c
  rwa [hct] at this

theorem classical_lifts_set {K₀ : Subgroup G} {Λ : Subgroup G → Subgroup G} {π : Set (Subgroup G)}
    {g t : G} (hs : TwinGraphStd K₀) (hz : IsUniqueInvolution K₀ t)
    (hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K₀) (hH1 : NoCentralInv π)
    (hg : conjSub g K₀ ∈ π) (hK₀8 : Nat.card K₀ = 8)
    (hmodel : Model1520 (piGen π) (g * t * g⁻¹))
    (hΛ : ∀ J ∈ twinSet (CoreAssembly.conjClass K₀) K₀,
      Λ J ≤ conjSub g (piGen π) ∧ J ≤ Λ J ∧
        TwinSecXg.IsClassicalMember3On (conjSub g (piGen π)) (Λ J) t)
    (hcomm : ∀ J ∈ twinSet (CoreAssembly.conjClass K₀) K₀,
      ∀ J' ∈ twinSet (CoreAssembly.conjClass K₀) K₀, J ≠ J' →
        ∀ x ∈ Λ J, ∀ y ∈ Λ J', x * y = y * x)
    (hOL : ∀ J ∈ twinSet (CoreAssembly.conjClass K₀) K₀, classicalInvolutionOddCore ↥(Λ J) = ⊥)
    (hOC : classicalInvolutionOddCore
      ↥(conjSub g (piGen π) ⊓ Subgroup.centralizer ({t} : Set G)) = ⊥) :
    ∀ J ∈ twinSet (CoreAssembly.conjClass K₀) K₀, IsClassicalMember3 (Λ J) t := by
  classical
  set V := twinSet (CoreAssembly.conjClass K₀) K₀ with hVdef
  have hos := hs.orbitStd
  have hK₀Ω : K₀ ∈ CoreAssembly.conjClass K₀ := CoreAssembly.mem_conjClass_self _
  have hCX : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (piGen π : Set G) :=
    hos.centralizer_le_normalizer_piGen hK₀Ω hπ hH1 hz
  have htX : g * t * g⁻¹ ∈ piGen π := le_piGen hg (hz.conj g).mem
  have hside : ∀ J, ∃ A : Subgroup G, J ∈ V →
      Lift217Side (piGen π) J (Λ J) A t := by
    intro J
    by_cases hJ : J ∈ V
    · obtain ⟨hLX, hJL, hL⟩ := hΛ J hJ
      have hzJ : IsUniqueInvolution J t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hz hJ
      have hJ8 : Nat.card J = 8 := by
        rw [TwinSecXg.card_eq_of_mem_conjClass hK₀Ω hJ.1, hK₀8]
      have hcent : J ≤ Subgroup.centralizer (piGen π : Set G) :=
        hos.beta_le_centralizer (hos.twinSet_subset_beta hπ hH1 hJ)
      obtain ⟨A, hA⟩ := TwinSecXg.lift217Side_of_exact hzJ hcent hJL hJ8 (hOL J hJ)
        (TwinSecXg.IsClassicalMember3On.quotient hLX hL)
      exact ⟨A, fun _ => hA⟩
    · exact ⟨⊥, fun h => absurd h hJ⟩
  choose A hA using hside
  have hdata : LiftSetData (piGen π) t V Λ A := by
    refine ⟨hA, ?_, ?_, hcomm, ?_⟩
    · intro J hJ
      rw [TwinSecXg.card_eq_of_mem_conjClass hK₀Ω hJ.1, hK₀8]
    · intro J hJ
      exact card_eq_24_of_exact (hOL J hJ) (hA J hJ).quotient
    · intro J hJ
      exact ((hA J hJ).le_centralizer).trans hCX
  refine transport217Set hdata hmodel hCX htX ?_
  set N : Subgroup G := ⨆ J ∈ V, Λ J with hN
  set C : Subgroup G := Subgroup.centralizer ({g * t * g⁻¹, t} : Set G) with hC
  refine mem_normalizer_of_conjSub_le (fun c hc => C.inv_mem hc) ?_
  intro c hc
  have hcw : g * t * g⁻¹ * c = c * (g * t * g⁻¹) := Subgroup.mem_centralizer_iff.mp hc _ (by simp)
  have hct : t * c = c * t := Subgroup.mem_centralizer_iff.mp hc t (by simp)
  have hcN : c ∈ Subgroup.normalizer (conjSub g (piGen π) : Set G) :=
    (hos.conj_piGen_le_centralizer hK₀Ω hπ hH1 hz g).2
      (Subgroup.mem_centralizer_singleton_iff.mpr hcw.symm)
  have hct' : c * t * c⁻¹ = t := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hct.symm
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_le fun J => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hJ => ?_
  obtain ⟨hLX, hJL, hL⟩ := hΛ J hJ
  have hJc := conj_mem_twinSet_of_fix hs.hyp hz hJ hct'
  obtain ⟨hLcX, hJcL, hLc⟩ := hΛ _ hJc
  have hconj := isClassicalMember3On_conj hcN hct' hL
  have heq : conjSub c (Λ J) = Λ (conjSub c J) :=
    liftUnique_on hs.hyp hJc.1 (TwinSecXg.isUniqueInvolution_of_mem_twinSet hz hJc)
      (Subgroup.map_mono hJL) hJcL (conjSub_le_of_mem_normalizer hcN hLX) hLcX hconj hLc hOC
  show Subgroup.map (MulAut.conj c).toMonoidHom (Λ J) ≤ N
  have heq' : Subgroup.map (MulAut.conj c).toMonoidHom (Λ J) = Λ (conjSub c J) := heq
  rw [heq']
  exact le_iSup₂_of_le (conjSub c J) hJc le_rfl

end TwinConnT

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
