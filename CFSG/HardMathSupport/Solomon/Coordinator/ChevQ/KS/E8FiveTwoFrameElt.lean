module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveTwistedFrame
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Malle.SeitzCube.D4PlaneGen
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Malle.SeitzCube
  CFSG.LieType.SeitzGeneration.ExcHigh

set_option linter.unusedSectionVars false

section FrameElt


theorem closingFrame_twisted {K : Type} [Field K] [Finite K] (hK : 5 ∣ Nat.card K + 1)
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) (ζ : D.Lˣ) (hζ : orderOf ζ = 5)
    (z : adjointGroup TwClass.e8Ten.tag K)
    (hzbc : baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.e8Ten.tag K) =
      D.g * rootDiagUnit TwClass.e8Ten.tag (Pi.mulSingle (⟨4, by decide⟩ :
        Fin TwClass.e8Ten.tag.rank) ζ) * D.g⁻¹) :
    ClosingFrameAt z (frameIn (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D)) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set i₁ : Fin TwClass.e8Ten.tag.rank := ⟨4, by decide⟩ with hi₁
  set a : Fin TwClass.e8Ten.tag.rank → D.Lˣ := Pi.mulSingle i₁ ζ with ha
  have hchar : ∀ α : Fin TwClass.e8Ten.tag.rank → ℤ, rootChar a α = ζ ^ (α i₁) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single i₁]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hS : ∀ S : Set (Fin TwClass.e8Ten.tag.rank → ℤ), (∀ α ∈ S, 5 ∣ α i₁) →
      (∀ α ∈ S, IsRoot TwClass.e8Ten.tag α) → ∀ α ∈ S, IsRoot TwClass.e8Ten.tag α ∧
        rootChar a α = 1 := by
    intro S h5S hrS α hα
    refine ⟨hrS α hα, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hζ]
    exact_mod_cast h5S α hα
  have hS₁ : ∀ α ∈ TwClass.e8Ten.S₁, IsRoot TwClass.e8Ten.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ e8ListB} := by rw [← QuasiE8Ten.S₁_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.E8 4 5 := by
      rw [e8_coset_eq]
      exact Or.inr hα'
    exact hmem.2
  have hS₂ : ∀ α ∈ TwClass.e8Ten.S₂, IsRoot TwClass.e8Ten.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ e8ListA} := by rw [← QuasiE8Ten.S₂_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.E8 4 5 := by
      rw [e8_coset_eq]
      exact Or.inl hα'
    exact hmem.2
  have hcomm : ∀ S : Set (Fin TwClass.e8Ten.tag.rank → ℤ),
      (∀ α ∈ S, IsRoot TwClass.e8Ten.tag α ∧ rootChar a α = 1) →
      D.frame S ≤ Subgroup.centralizer
        ({(z : ModGL TwClass.e8Ten.tag K)} : Set (ModGL TwClass.e8Ten.tag K)) := by
    intro S hS' x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxc := rootSpan_le_centralizer_rootDiagUnit (K := D.L) a hS' hx.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxc
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_mul, map_mul, hzbc]
    calc baseChangeGL (algebraMap K D.L) x * (D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹)
        = D.g * ((D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g⁻¹⁻¹) *
            rootDiagUnit TwClass.e8Ten.tag a) * D.g⁻¹ := by group
      _ = D.g * (rootDiagUnit TwClass.e8Ten.tag a * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x *
            D.g⁻¹⁻¹)) * D.g⁻¹ := by rw [hxc]
      _ = (D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x := by
          group
  have hKq : TwClass.e8Ten.minQ ≤ Nat.card K := by
    show 2 ≤ Nat.card K
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hle : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ adjointGroup TwClass.e8Ten.tag K :=
    sup_le inf_le_left inf_le_left
  have hq3 := twQuasi_of_ne_e6Six TwClass.e8Ten (by decide) K hKq D
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hy' : (y : ModGL TwClass.e8Ten.tag K) ∈
        TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D := hy
    have hsup : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤
        Subgroup.centralizer
          ({(z : ModGL TwClass.e8Ten.tag K)} : Set (ModGL TwClass.e8Ten.tag K)) :=
      sup_le (hcomm _ hS₁) (hcomm _ hS₂)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hsup hy')
  · refine nonsolvable_frameIn hle ?_
    intro hs
    haveI := hs
    haveI h2 : Group.IsSolvable ↥(TwClass.e8Ten.X₂ D) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective
        (le_sup_right : TwClass.e8Ten.X₂ D ≤ TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D))
    obtain ⟨hperf, -, a₀, b₀, hab⟩ := hq3.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
    haveI : Nontrivial ↥(TwClass.e8Ten.X₂ D) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
    exact (IsSolvable.commutator_lt_top_of_nontrivial
      (↥(TwClass.e8Ten.X₂ D))).ne hperf.commutator_eq_top
  · have h3 : 3 ≤ Nat.card K := by
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      omega
    exact closing_of_twFrameClosing hle (E8TenAux.twClosing_e8Ten_three K D h3)
  · exact normalizerSolvable_of_twFrame hle (twNormalizer_e8Ten K hKq D)

end FrameElt

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
