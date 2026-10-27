module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOtherTypeDet
import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Label
import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
import CFSG.LocalAnalysis.StandardType.MarkingSmall
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LargeExtraspecial.DW2AOut
import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import CFSG.LargeExtraspecial.DW2AOutInput

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA.MI CFSG.ComponentClassification.OuterAutomorphisms

theorem t2021Layer_dvd_card_of_conj {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) {r : R}
    (hrp : MulAut.conj r ^ p = 1) (hr1 : MulAut.conj r ≠ 1) : p ∣ Nat.card R := by
  have hZ : Subgroup.center R = ⊥ :=
    (hs.eq_bot_or_eq_top_of_normal (Subgroup.center R)).resolve_right fun h => by
      obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hc : r ^ p ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : r ^ p * g * (r ^ p)⁻¹ = g := by
      have := DFunLike.congr_fun hrp g
      rwa [← map_pow, MulAut.conj_apply, MulAut.one_apply] at this
    calc g * r ^ p = r ^ p * g * (r ^ p)⁻¹ * r ^ p := by rw [h1]
      _ = r ^ p * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  have hr : r ≠ 1 := by
    rintro rfl
    exact hr1 (map_one _)
  haveI := Fact.mk hp
  rw [← orderOf_eq_prime hc hr]
  exact orderOf_dvd_natCard r

section Small

theorem t2021Layer_isPGroup_outer {lab : LargeEvenLabel} (h : lab.tag = .B2der ∨ DerivedLab lab)
    {R : Type} [Group R] [Finite R] (hM : MarkedModel lab R) : IsPGroup 2 (Outer R) := by
  obtain ⟨t, l, n⟩ := lab
  unfold DerivedLab at h
  rcases h with h | h | h <;> dsimp only at h <;> subst h
  · obtain ⟨e⟩ := nonempty_alternatingGroup_of_markedModel_b2der rfl hM
    exact CFSG.LargeExtraspecial.DW.isPGroup_outer_alt6 e
  · exact CFSG.LargeExtraspecial.DW.isPGroup_outer_psu hM
  · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    rcases hM with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier R _ _ hR).1
    · exact absurd ht (by decide)

end Small

section Sq

theorem t2021Layer_dvd_card_of_dvd_sq {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hc : markChar lab = 2) (hB2 : lab.tag ≠ .twB2) (hq : p ∣ (2 ^ lab.n) ^ 2 - 1) :
    CAll lab (LargeEvenSimpleGuard fun R _ _ _ => p ∣ Nat.card R) :=
  canonAll_simple_of_markedModel hlab fun R _ _ _ _ _ hM => by
    have hL := NbrInnerMore.lieModel_of_markedModel_two hc hM
    refine hq.trans (dvd_trans ?_ (F4Nonsplit.sq_sub_one_dvd_card_of_lieModel hL.admissible hL
      (F4Nonsplit.markTag_ne_twistedB2 hB2)))
    rcases F4Nonsplit.markDeg_eq_or hc with h | h
    · rw [h]
    · have e : (2 : ℕ) ^ (2 * lab.n) = (2 ^ lab.n) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [h, e]
      have := Nat.sub_dvd_pow_sub_pow ((2 ^ lab.n) ^ 2) 1 2
      rwa [one_pow] at this

end Sq

section Inner

theorem t2021Layer_outdiagPrime {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hB2der : lab.tag ≠ .B2der) (hnd : ¬ DerivedLab lab)
    (hq : lab.tag ≠ .twB2 → ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) :
    CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) := by
  have hm : lab.tag ≠ .twB2 → ¬ p ∣ 2 ^ lab.n - 1 := fun ht h =>
    hq ht (h.trans (Nat.sub_one_dvd_pow_sub_one _ 2))
  have hpl : lab.tag ≠ .twB2 → ¬ p ∣ 2 ^ lab.n + 1 := fun ht h => hq ht (h.trans ⟨2 ^ lab.n - 1, by
    have h2 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
    zify [h2, Nat.one_le_pow 2 (2 ^ lab.n) h2]
    ring⟩)
  have guard : ∀ {P : LargeEvenRawCont}, CFSG.StandardType.LargeEvenLabelAll lab P →
      CFSG.StandardType.LargeEvenLabelAll lab (LargeEvenSimpleGuard P) :=
    fun h => h.mono fun _ _ _ _ hP _ _ => hP
  have inn : CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) →
      CFSG.StandardType.LargeEvenLabelAll lab
        (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) :=
    NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
  have hsi : GGInnerDiagInnLabel lab → CFSG.StandardType.LargeEvenLabelAll lab
      (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) :=
    fun h => inn (largeEvenLabelAll_subset_inn hlab h)
  obtain ⟨t, l, n⟩ := lab
  cases t with
  | A => exact guard (NbrInnerMore.largeEvenLabelAll_outdiagPrime_linear hp hlab rfl (hm nofun))
  | twA => exact guard (NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlab rfl (hpl nofun))
  | B => exact hsi (Or.inl (Or.inl rfl))
  | C => exact hsi (Or.inl (Or.inr (Or.inl rfl)))
  | D =>
    by_cases h3 : l = 3
    · exact hsi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨rfl, h3⟩)))))))))
    · exact hsi (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, h3⟩))))
  | twD =>
    by_cases h2 : l = 2
    · exact hsi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr ⟨rfl, h2⟩)))))))))
    · by_cases h3 : l = 3
      · exact guard (NbrInnerMore.largeEvenLabelAll_outdiagPrime_twD3 hp hlab rfl h3 (hpl nofun))
      · exact hsi (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h2, h3⟩)))))
  | G2 => exact hsi (Or.inr (Or.inl rfl))
  | F4 => exact hsi (Or.inr (Or.inr (Or.inl rfl)))
  | E7 => exact hsi (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | E8 => exact hsi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | E6 => exact NbrInnerMore.largeEvenLabelAll_outdiagPrime_E6 hp rfl (hm nofun)
  | twE6 =>
    refine NbrInnerMore.largeEvenLabelAll_outdiagPrime_twE6 hp ?_ hlab rfl
    rintro rfl
    refine hq nofun ?_
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ 2) n
  | triD4 => exact inn (TableBExcSmallRest.largeEvenLabelAll_subset_inn_triD4 hlab rfl)
  | twB2 => exact hsi (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  | twF4 => exact inn (largeEvenLabelAll_subset_inn_twF4 hlab rfl)
  | B2der => exact absurd rfl hB2der
  | G2der => exact absurd (Or.inl rfl) hnd
  | twF4der => exact absurd (Or.inr rfl) hnd

end Inner

section Main

theorem t2021Layer_labelAll {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) :
    CAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      Finite R → ∀ φ ∈ I, φ ^ p = 1 → φ ≠ 1 → p ∣ Nat.card R) := by
  by_cases hsmall : lab.tag = .B2der ∨ DerivedLab lab
  · refine canonAll_simple_of_markedModel hlab fun R _ I F hs hna hM hfin φ _ hφp hφ1 => ?_
    obtain ⟨r, rfl⟩ := RawAut.mem_inner_of_isPGroup_outer (t2021Layer_isPGroup_outer hsmall hM)
      (hp.odd_of_ne_two hp2) hφp
    exact t2021Layer_dvd_card_of_conj hs hna hp hφp hφ1
  have hB2der : lab.tag ≠ .B2der := fun h => hsmall (Or.inl h)
  have hnd : ¬ DerivedLab lab := fun h => hsmall (Or.inr h)
  by_cases hq : lab.tag ≠ .twB2 ∧ p ∣ (2 ^ lab.n) ^ 2 - 1
  · refine (t2021Layer_dvd_card_of_dvd_sq hlab
      (markChar_eq_two_of_ne hB2der fun h => hnd (Or.inl h)) hq.1 hq.2).mono ?_
    exact fun R _ I F h hs hna _ _ _ _ _ => h hs hna
  · refine ((canonAll_iff_legacyAll hlab hnd _).2
      (t2021Layer_outdiagPrime hp hlab hB2der hnd fun ht h => hq ⟨ht, h⟩)).mono ?_
    intro R _ I F h hs hna _ φ hφ hφp hφ1
    obtain ⟨r, rfl⟩ := h hs hna φ hφ hφp
    exact t2021Layer_dvd_card_of_conj hs hna hp hφp hφ1

theorem t2021Layer_dvd_card {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut (Q ⧸ Subgroup.center Q)} (hβp : β ^ p = 1) (hβ1 : β ≠ 1)
    (hb : GLAMarking Q fun _ _ _ I _ θ => MulAut.congr θ β ∈ I) :
    p ∣ Nat.card (Q ⧸ Subgroup.center Q) := by
  obtain ⟨-, lab, hlab, hraw⟩ := hb
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, hβI⟩, hP⟩ :=
    Canonical.largeEvenRawDatum_exists (t2021Layer_labelAll hp hp2 hlab _ hraw)
  have hfin : Finite R := Finite.of_equiv _ θ.toEquiv
  rw [Nat.card_congr θ.toEquiv]
  refine hP hs hna hfin _ hβI (by rw [← map_pow, hβp, map_one]) fun h => hβ1 ?_
  exact (MulAut.congr θ).injective (h.trans (map_one _).symm)

end Main

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
