module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOnePerfectMat
public import CFSG.Sporadic.Co1Block.TwoACent
public import CFSG.Sporadic.Co1Block.TwoCCent
public import Certificates.Certificate24510
public import Certificates.Certificate24512

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.EvenSporadicStandard.TwoCo1.HypOne

theorem aG_mem_commutator :
    aG ∈ ⁅(GA ⊓ Subgroup.centralizer ({aG} : Set GL24) : Subgroup GL24),
      (GA ⊓ Subgroup.centralizer ({aG} : Set GL24) : Subgroup GL24)⁆ := by
  have hrepB := rep_brayElts (bidx := twoABray) rep_iotaA (centCheck_parts twoA_cent_check).1
  have hBGK : ∀ g ∈ brayEltsG aG twoAD1 twoABray, g ∈ GA ⊓ Subgroup.centralizer {aG} :=
    fun g hg => twoAE_le (Subgroup.subset_closure hg)
  obtain ⟨P, hPK, hP, hQ⟩ := exists_perfect_of_check hrepB hBGK Certificates.certificate24510
  have hQP : twoAQ ≤ P := by
    show Subgroup.closure (twoAQg '' {l | l < twoAQRows.length}) ≤ P
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < twoAQRows.length := hl
    refine hQ _ ?_ _ (qRep_twoA l hl')
    rw [List.getD_eq_getElem _ _ hl']
    exact List.getElem_mem hl'
  exact Subgroup.commutator_mono hPK hPK (hP (hQP aG_mem_twoAQ))

theorem cG_mem_commutator :
    cG ∈ ⁅(GA ⊓ Subgroup.centralizer ({cG} : Set GL24) : Subgroup GL24),
      (GA ⊓ Subgroup.centralizer ({cG} : Set GL24) : Subgroup GL24)⁆ := by
  have hrepB := rep_brayElts (bidx := twoCBray) rep_iotaC (centCheck_parts twoC_cent_check).1
  have hBGK : ∀ g ∈ brayEltsG cG twoCD1 twoCBray, g ∈ GA ⊓ Subgroup.centralizer {cG} :=
    fun g hg => twoCE_le (Subgroup.subset_closure hg)
  obtain ⟨P, hPK, hP, hQ⟩ := exists_perfect_of_check hrepB hBGK Certificates.certificate24512
  have hQP : twoCQ ≤ P := by
    rw [twoCQ_eq, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < twoCQRows.length := by rw [twoCQRows_length]; exact hl
    refine hQ _ ?_ _ (qRep_twoC l hl')
    rw [List.getD_eq_getElem _ _ hl']
    exact List.getElem_mem hl'
  have hcG : cG ∈ twoCQ := by
    refine twoC_selfCentralizing cG ⟨iotaC_mem_GA, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
      fun q hq => ?_
    exact (Subgroup.mem_centralizer_singleton_iff.1 (twoCQ_le hq).2).symm
  exact Subgroup.commutator_mono hPK hPK (hP (hQP hcG))

theorem mem_commutator_centralizer_GA (t : GA)
    (h : (t : GL24) ∈ ⁅(GA ⊓ Subgroup.centralizer ({(t : GL24)} : Set GL24) : Subgroup GL24),
      (GA ⊓ Subgroup.centralizer ({(t : GL24)} : Set GL24) : Subgroup GL24)⁆) :
    t ∈ ⁅Subgroup.centralizer ({t} : Set GA), Subgroup.centralizer ({t} : Set GA)⁆ := by
  rw [← map_centralizer_GA, ← Subgroup.map_commutator] at h
  exact (Subgroup.mem_map_iff_mem GA.subtype_injective).1 h

theorem mem_commutator_centralizer_of_isConj {Y : Type*} [Group Y] {w r : Y} (h : IsConj w r)
    (hr : r ∈ ⁅Subgroup.centralizer ({r} : Set Y), Subgroup.centralizer ({r} : Set Y)⁆) :
    w ∈ ⁅Subgroup.centralizer ({w} : Set Y), Subgroup.centralizer ({w} : Set Y)⁆ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hw : w = c⁻¹ * r * c := by rw [← hc]; group
  set f : Y →* Y := (MulAut.conj c⁻¹).toMonoidHom with hf
  have hfr : f r = w := by
    show c⁻¹ * r * c⁻¹⁻¹ = w
    rw [hw]
    group
  have hmap : (Subgroup.centralizer ({r} : Set Y)).map f ≤ Subgroup.centralizer ({w} : Set Y) := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have hy' : y * r = r * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    show c⁻¹ * y * c⁻¹⁻¹ * w = w * (c⁻¹ * y * c⁻¹⁻¹)
    calc c⁻¹ * y * c⁻¹⁻¹ * w = c⁻¹ * (y * r) * c := by rw [hw]; group
      _ = c⁻¹ * (r * y) * c := by rw [hy']
      _ = w * (c⁻¹ * y * c⁻¹⁻¹) := by rw [hw]; group
  have h2 := Subgroup.mem_map_of_mem f hr
  rw [hfr, Subgroup.map_commutator] at h2
  exact Subgroup.commutator_mono hmap hmap h2

theorem perfectInvolutions_GA
    (h2B : a₁ ∈ ⁅Subgroup.centralizer ({a₁} : Set GA), Subgroup.centralizer ({a₁} : Set GA)⁆) :
    PerfectInvolutions GA := by
  intro w hw
  rcases involution_classes.1 w hw with h | h | h
  · exact mem_commutator_centralizer_of_isConj h
      (mem_commutator_centralizer_GA aC aG_mem_commutator)
  · exact mem_commutator_centralizer_of_isConj h
      (mem_commutator_centralizer_GA cC cG_mem_commutator)
  · exact mem_commutator_centralizer_of_isConj h h2B

theorem PerfectInvolutions.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : PerfectInvolutions X) : PerfectInvolutions Y := by
  intro w hw
  have hw' : orderOf (e.symm w) = 2 := by
    have := orderOf_injective e.symm.toMonoidHom e.symm.injective w
    exact this.trans hw
  have h1 := h (e.symm w) hw'
  have hmap : (Subgroup.centralizer ({e.symm w} : Set X)).map e.toMonoidHom ≤
      Subgroup.centralizer ({w} : Set Y) := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have hy' : y * e.symm w = e.symm w * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    have := congrArg e.toMonoidHom hy'
    simpa using this
  have h2 := Subgroup.mem_map_of_mem e.toMonoidHom h1
  rw [Subgroup.map_commutator] at h2
  have := Subgroup.commutator_mono hmap hmap h2
  simpa using this

theorem perfectInvolutions_native
    (h2B : a₁ ∈ ⁅Subgroup.centralizer ({a₁} : Set GA), Subgroup.centralizer ({a₁} : Set GA)⁆) :
    PerfectInvolutions CFSG.Blueprint.NativeSporadic.Co1 :=
  @PerfectInvolutions.of_mulEquiv GA CFSG.Blueprint.NativeSporadic.Co1 _ Units.instGroup
    co1MatEquiv.symm (perfectInvolutions_GA h2B)

end CFSG.EvenSporadicStandard.Solomon78
