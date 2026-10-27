module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOmega

import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmGaps
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmMinus6
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinOmega
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGUComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGUIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8A
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmBasic
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8b
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnD4b
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab5
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
import CFSG.Quasithin.Background.ONanE68LieSwap
import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import Certificates.Data.U62Rank.Check
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTitsPair
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenUnitary
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3Final
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFinal
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeProp121
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Final
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Id
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineMain
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdTabCover
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdTabEmbed
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.B1More13
import CFSG.Quasithin.Background.C129NativeMain
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.E4Solv
import CFSG.Quasithin.Background.F9Sixteen
import CFSG.Quasithin.Background.ONanE68Alt
import CFSG.Quasithin.Background.ONanE68Cases
import CFSG.Quasithin.Background.ONanE68Elim
import CFSG.Quasithin.Background.ONanE68L42
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.S153H32
import CFSG.Quasithin.EmptyFaithful.S153Nine
import CFSG.Quasithin.H13.A5S1514
import CFSG.Quasithin.H13.GoldschmidtC137H6Alg
import CFSG.Quasithin.H13.KGFact68L2p
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.HSubT
open CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon
open CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8
open CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.OrthogonalInvolutions CFSG.LinearGroups
open Polynomial

private theorem centralizer_eq_sup_comap {Ω : Subgroup SpGL} (hΩ : Ω ≤ StatedSp 4 (ZMod 2))
    {t : StatedSp 4 (ZMod 2)} {s : ↥Ω} (hst : t = Subgroup.inclusion hΩ s)
    {A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))}
    (hcent : Subgroup.centralizer ({t} : Set (StatedSp 4 (ZMod 2))) = A₀ ⊔ A₁)
    (hcomm : ∀ a ∈ A₀, ∀ b ∈ A₁, a * b = b * a)
    (hA₁ : A₁ ≤ OmInSp Ω) :
    Subgroup.centralizer ({s} : Set ↥Ω) =
      A₀.comap (Subgroup.inclusion hΩ) ⊔ A₁.comap (Subgroup.inclusion hΩ) := by
  let incl : ↥Ω →* ↥(StatedSp 4 (ZMod 2)) := Subgroup.inclusion hΩ
  have hincl : Function.Injective incl := Subgroup.inclusion_injective hΩ
  have hrange : incl.range = OmInSp Ω := by
    ext x
    rw [MonoidHom.mem_range, mem_OmInSp]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨(x : SpGL), hx⟩, rfl⟩
  apply le_antisymm
  · intro x hx
    have hx' : incl s * incl x = incl x * incl s := by
      have h := (Subgroup.mem_centralizer_iff.mp hx) s (Set.mem_singleton s)
      rw [← map_mul, ← map_mul, h]
    have hxC : incl x ∈ A₀ ⊔ A₁ := by
      rw [← hcent]
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      rw [hh, hst]
      exact hx'
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hcomm hxC
    have hbO : b ∈ OmInSp Ω := hA₁ hb
    have haO : a ∈ OmInSp Ω := by
      have hae : a = incl x * b⁻¹ := by rw [hab, mul_inv_cancel_right]
      rw [hae]
      exact (OmInSp Ω).mul_mem (mem_OmInSp.mpr x.2) ((OmInSp Ω).inv_mem hbO)
    have ha' : (⟨(a : SpGL), mem_OmInSp.mp haO⟩ : ↥Ω) ∈ A₀.comap incl := ha
    have hb' : (⟨(b : SpGL), mem_OmInSp.mp hbO⟩ : ↥Ω) ∈ A₁.comap incl := hb
    have hxe : x = (⟨(a : SpGL), mem_OmInSp.mp haO⟩ : ↥Ω) *
        ⟨(b : SpGL), mem_OmInSp.mp hbO⟩ := by
      apply hincl
      rw [map_mul]
      exact hab
    rw [hxe]
    exact Subgroup.mul_mem_sup ha' hb'
  · refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      apply hincl
      rw [map_mul, map_mul]
      have hcen : incl a ∈ A₀ ⊔ A₁ := Subgroup.mem_sup_left (show incl a ∈ A₀ from ha)
      rw [← hcent] at hcen
      have := (Subgroup.mem_centralizer_iff.mp hcen) t (Set.mem_singleton t)
      rw [hst] at this
      exact this
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      apply hincl
      rw [map_mul, map_mul]
      have hcen : incl b ∈ A₀ ⊔ A₁ := Subgroup.mem_sup_right (show incl b ∈ A₁ from hb)
      rw [← hcent] at hcen
      have := (Subgroup.mem_centralizer_iff.mp hcen) t (Set.mem_singleton t)
      rw [hst] at this
      exact this

theorem centSplitOn_Om8 : CentSplitOn ↥CFSG.AGLEmbedding.Om8 := by
  classical
  intro s hs
  have hs3 : s ^ 3 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  let incl : ↥CFSG.AGLEmbedding.Om8 →* ↥(StatedSp 4 (ZMod 2)) :=
    Subgroup.inclusion om8_le_sp8
  have hincl : Function.Injective incl := Subgroup.inclusion_injective om8_le_sp8
  let t : StatedSp 4 (ZMod 2) := incl s
  have ht3 : t ^ 3 = 1 := by
    dsimp only [t]
    rw [← map_pow, hs3, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    exact hs1 (hincl (by simpa [t] using h))
  obtain ⟨s₀, hC⟩ := exists_class_spSupported ht3 ht1
  generalize hA₀def : spSupported t {(Polynomial.X - 1 : Polynomial (ZMod 2))} = A₀ at hC
  generalize hA₁def : spSupported t {q2} = A₁ at hC
  generalize hmdef : primaryMultiplicity (spEnd t) q2 = m at hC
  have hmem : t ∈ OmInSp CFSG.AGLEmbedding.Om8 := by
    rw [mem_OmInSp]
    exact s.2
  have hA₁ : A₁ ≤ OmInSp CFSG.AGLEmbedding.Om8 := by
    rw [← hA₁def]
    exact omegaUnitaryInOm8_holds t ht3 ht1 hmem
  have hrange : incl.range = OmInSp CFSG.AGLEmbedding.Om8 := by
    ext x
    rw [MonoidHom.mem_range, mem_OmInSp]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨(x : SpGL), hx⟩, rfl⟩
  have hcent : Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8) =
      A₀.comap incl ⊔ A₁.comap incl :=
    centralizer_eq_sup_comap om8_le_sp8 rfl hC.centralizer_eq hC.commute hA₁
  have hA₁range : A₁ ≤ incl.range := by
    rw [hrange]
    exact hA₁
  have hcomm' : ∀ a ∈ A₀.comap incl, ∀ b ∈ A₁.comap incl, a * b = b * a := by
    intro a ha b hb
    apply hincl
    rw [map_mul, map_mul]
    exact hC.commute (incl a) ha (incl b) hb
  have hA₀map : (A₀.comap incl).map incl = A₀ ⊓ OmInSp CFSG.AGLEmbedding.Om8 := by
    rw [Subgroup.map_comap_eq, hrange, inf_comm]
  let eA₀ : ↥(A₀.comap incl) ≃* ↥(A₀ ⊓ OmInSp CFSG.AGLEmbedding.Om8) :=
    (Subgroup.equivMapOfInjective (A₀.comap incl) incl hincl).trans
      (MulEquiv.subgroupCongr hA₀map)
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by
    have h1 := hC.one_le
    have h4 := hC.sum_eq
    omega
  rcases hm with hm1 | hm2 | hm3 | hm4
  ·
    right
    have hs0 : s₀ = 3 := by
      have h4 := hC.sum_eq
      omega
    obtain ⟨E, hEf, hE, W, hWa, hWm, hWf, Hf, hsymm, hsep, hfr, ⟨eA1⟩⟩ := hC.unitary
    letI : Field E := hEf
    letI : AddCommGroup W := hWa
    letI : Module E W := hWm
    letI : FiniteDimensional E W := hWf
    have hcardA1 : Nat.card ↥A₁ = 3 := by
      have h := (unitary_full_group_order (B := Hf) hE hsymm hsep (n := m) hfr (by omega)).1
      rw [hm1] at h
      have hnum : (((2 : ℕ) ^ 1 : ℕ) : ℤ) ^ (1 * (1 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 1, (((((2 : ℕ) ^ 1 : ℕ)) : ℤ) ^ i - (-1) ^ i) = 3 := by decide
      rw [hnum] at h
      have h3 : Nat.card ↥(sesqUnitaryGroup Hf) = 3 := by exact_mod_cast h
      rw [Nat.card_congr eA1.toEquiv]
      exact h3
    have htA₁ : t ∈ A₁ := by
      rw [← hA₁def, mem_spSupported_q2_iff ht3]
      refine ⟨rfl, fun v hv => ?_⟩
      rw [fixV_eq_ker, LinearMap.mem_ker] at hv
      simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hv
    have hA1eq : A₁ = Subgroup.zpowers t := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hle : Subgroup.zpowers t ≤ A₁ := Subgroup.zpowers_le.mpr htA₁
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [Nat.card_zpowers, hcardA1, orderOf_eq_prime ht3 ht1]
    have h6 : Module.finrank (ZMod 2) ↥(fixV t) = 6 := by
      have h := finrank_fixV ht3 ht1
      rw [hmdef] at h
      omega
    have h36 : {v | fixQ t v = 1}.ncard = 36 :=
      ncard_fixQ_of_mult_one ht3 ht1 hmem (by rw [hmdef]; exact hm1)
    have hZomega : Subgroup.center ↥(omegaGroup (fixQ t) (fixQ_nondegenerate ht3 ht1)) = ⊥ :=
      (omegaGroup_minus_six_facts (fixQ t) (fixQ_nondegenerate ht3 ht1) h6 h36).2.1
    have hcatOmega : catalogIs ↥(omegaGroup (fixQ t) (fixQ_nondegenerate ht3 ht1)) isU4two :=
      (omegaGroup_minus_six_facts (fixQ t) (fixQ_nondegenerate ht3 ht1) h6 h36).2.2
    obtain ⟨eOmega⟩ := nonempty_spSupported_inf_om8_equiv ht3 ht1
    have hA₀eq : A₀ ⊓ OmInSp CFSG.AGLEmbedding.Om8 =
        spSupported t {(Polynomial.X - 1 : Polynomial (ZMod 2))} ⊓
          OmInSp CFSG.AGLEmbedding.Om8 := by
      rw [hA₀def]
    let eOmega' : ↥(A₀ ⊓ OmInSp CFSG.AGLEmbedding.Om8) ≃*
        ↥(omegaGroup (fixQ t) (fixQ_nondegenerate ht3 ht1)) :=
      (MulEquiv.subgroupCongr hA₀eq).trans eOmega
    refine ⟨A₀.comap incl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcent]
      exact le_sup_left
    · intro g hg
      rw [hcent] at hg
      obtain ⟨a, ha, b, hb, hgab⟩ := exists_mul_of_mem_sup_of_commute hcomm' hg
      have hbA₁ : incl b ∈ A₁ := hb
      have hbzp : incl b ∈ Subgroup.zpowers t := by rwa [← hA1eq]
      rw [mem_zpowers_iff_mem_range_orderOf] at hbzp
      obtain ⟨n, -, hn⟩ := Finset.mem_image.mp hbzp
      have hbn : b = s ^ n := by
        apply hincl
        rw [map_pow, ← hn]
      have hsn : s ^ n ∈ A₁.comap incl := by
        rw [← hbn]
        exact hb
      refine ⟨n, a, ha, ?_⟩
      rw [hgab, hbn, hcomm' a ha (s ^ n) hsn]
    · intro hsK
      have htA₀ : t ∈ A₀ := hsK
      have hdisj : t ∈ A₀ ⊓ A₁ := ⟨htA₀, htA₁⟩
      rw [hC.disjoint] at hdisj
      exact ht1 (Subgroup.mem_bot.mp hdisj)
    · exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv (eA₀.trans eOmega') hZomega
    · rw [Nat.card_congr (eA₀.trans eOmega').toEquiv]
      exact card_of_catalogIs_u4two hcatOmega
  ·
    left
    intro K hK hperf h5
    have hsolvC : Group.IsSolvable ↥(Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8)) := by
      rw [hcent]
      have hsolvA₀' : Group.IsSolvable ↥(A₀.comap incl) := by
        have hsolv : Group.IsSolvable ↥(A₀ ⊓ OmInSp CFSG.AGLEmbedding.Om8) := by
          rw [← hA₀def]
          exact omegaOrthRank2Solvable_holds t ht3 ht1 hmem (by rw [hmdef]; exact hm2)
        haveI : Group.IsSolvable ↥(A₀ ⊓ OmInSp CFSG.AGLEmbedding.Om8) := hsolv
        exact Group.isSolvable_of_isSolvable_injective (f := eA₀.toMonoidHom) eA₀.injective
      have hsolvA₁' : Group.IsSolvable ↥(A₁.comap incl) := by
        obtain ⟨E, hEf, hE, W, hWa, hWm, hWf, Hf, hsymm, hsep, hfr, ⟨eA1⟩⟩ := hC.unitary
        letI : Field E := hEf
        letI : AddCommGroup W := hWa
        letI : Module E W := hWm
        letI : FiniteDimensional E W := hWf
        obtain ⟨eA1'⟩ := comap_equiv_of_injective_le_range incl hincl A₁ hA₁range
        obtain ⟨eGU⟩ := resGU_mulEquiv hE Hf hsymm hsep
        rw [hfr] at eGU
        haveI : Group.IsSolvable ↥(heldGU m E (resTau hE) (resTau_invol hE)) :=
          resGU_solvable hE m (by omega)
        have hsolvSesq : Group.IsSolvable ↥(sesqUnitaryGroup Hf) :=
          Group.isSolvable_of_isSolvable_injective (f := eGU.toMonoidHom) eGU.injective
        have hsolvA₁ : Group.IsSolvable ↥A₁ :=
          Group.isSolvable_of_isSolvable_injective (f := eA1.toMonoidHom) eA1.injective
        haveI : Group.IsSolvable ↥A₁ := hsolvA₁
        exact Group.isSolvable_of_isSolvable_injective (f := eA1'.toMonoidHom) eA1'.injective
      haveI := hsolvA₀'
      haveI := hsolvA₁'
      exact CFSG.Quasithin.E6.E68Proof.isSolvable_sup_of_commute hcomm'
    haveI : Group.IsSolvable ↥K := isSolvable_of_le_of_solvable hK hsolvC
    haveI : Nontrivial ↥K := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro hbot
      rw [hbot, Subgroup.card_bot] at h5
      norm_num at h5
    haveI : Group.IsPerfect ↥K := hperf
    exact (Group.IsPerfect.not_isSolvable ↥K) inferInstance
  ·
    left
    have hs0 : s₀ = 1 := by
      have h4 := hC.sum_eq
      omega
    intro K hK hperf h5
    have hsolvC : Group.IsSolvable ↥(Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8)) := by
      rw [hcent]
      have hsolvA₀' : Group.IsSolvable ↥(A₀.comap incl) := by
        have hsolvA₀ : Group.IsSolvable ↥A₀ := by
          rcases hC.fixed with ⟨h0, -⟩ | ⟨-, ⟨eSp⟩⟩
          · omega
          · rw [hs0] at eSp
            haveI : Group.IsSolvable ↥(StatedSp 1 (ZMod 2)) := sp1_solvable
            exact Group.isSolvable_of_isSolvable_injective (f := eSp.toMonoidHom) eSp.injective
        have hsolv : Group.IsSolvable ↥(A₀ ⊓ OmInSp CFSG.AGLEmbedding.Om8) :=
          isSolvable_of_le_of_solvable inf_le_left hsolvA₀
        haveI : Group.IsSolvable ↥(A₀ ⊓ OmInSp CFSG.AGLEmbedding.Om8) := hsolv
        exact Group.isSolvable_of_isSolvable_injective (f := eA₀.toMonoidHom) eA₀.injective
      have hsolvA₁' : Group.IsSolvable ↥(A₁.comap incl) := by
        obtain ⟨E, hEf, hE, W, hWa, hWm, hWf, Hf, hsymm, hsep, hfr, ⟨eA1⟩⟩ := hC.unitary
        letI : Field E := hEf
        letI : AddCommGroup W := hWa
        letI : Module E W := hWm
        letI : FiniteDimensional E W := hWf
        obtain ⟨eA1'⟩ := comap_equiv_of_injective_le_range incl hincl A₁ hA₁range
        obtain ⟨eGU⟩ := resGU_mulEquiv hE Hf hsymm hsep
        rw [hfr] at eGU
        haveI : Group.IsSolvable ↥(heldGU m E (resTau hE) (resTau_invol hE)) :=
          resGU_solvable hE m (by omega)
        have hsolvSesq : Group.IsSolvable ↥(sesqUnitaryGroup Hf) :=
          Group.isSolvable_of_isSolvable_injective (f := eGU.toMonoidHom) eGU.injective
        have hsolvA₁ : Group.IsSolvable ↥A₁ :=
          Group.isSolvable_of_isSolvable_injective (f := eA1.toMonoidHom) eA1.injective
        haveI : Group.IsSolvable ↥A₁ := hsolvA₁
        exact Group.isSolvable_of_isSolvable_injective (f := eA1'.toMonoidHom) eA1'.injective
      haveI := hsolvA₀'
      haveI := hsolvA₁'
      exact CFSG.Quasithin.E6.E68Proof.isSolvable_sup_of_commute hcomm'
    haveI : Group.IsSolvable ↥K := isSolvable_of_le_of_solvable hK hsolvC
    haveI : Nontrivial ↥K := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro hbot
      rw [hbot, Subgroup.card_bot] at h5
      norm_num at h5
    haveI : Group.IsPerfect ↥K := hperf
    exact (Group.IsPerfect.not_isSolvable ↥K) inferInstance
  ·
    right
    have hs0 : s₀ = 0 := by
      have h4 := hC.sum_eq
      omega
    have hA₀bot : A₀ = ⊥ := by
      rcases hC.fixed with ⟨-, h⟩ | ⟨h1, -⟩
      · exact h
      · omega
    have hcentA1 : Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8) = A₁.comap incl := by
      rw [hcent, hA₀bot, MonoidHom.comap_bot, MonoidHom.ker_eq_bot incl hincl, bot_sup_eq]
    obtain ⟨E, hEf, hE, W, hWa, hWm, hWf, Hf, hsymm, hsep, hfr, ⟨eA1⟩⟩ := hC.unitary
    letI : Field E := hEf
    letI : AddCommGroup W := hWa
    letI : Module E W := hWm
    letI : FiniteDimensional E W := hWf
    haveI : Fact (Nat.Prime 2) := ⟨hE.prime⟩
    haveI : CharP E 2 := hE.charP
    haveI : Finite E := hE.finite
    haveI : Fintype E := Fintype.ofFinite E
    have hE4 : Nat.card E = 4 := by
      rw [hE.card]
      norm_num
    have hEcard : Fintype.card E = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hE4
    have hfr4 : Module.finrank E W = 4 := by rw [hfr, hm4]
    obtain ⟨eA1'⟩ := comap_equiv_of_injective_le_range incl hincl A₁ hA₁range
    obtain ⟨eGU⟩ := resGU_mulEquiv hE Hf hsymm hsep
    rw [hfr4] at eGU
    let eC : ↥(A₁.comap incl) ≃* heldGU 4 E (resTau hE) (resTau_invol hE) :=
      eA1'.trans (eA1.trans eGU)
    let SU : Subgroup ↥(heldGU 4 E (resTau hE) (resTau_invol hE)) :=
      (heldSU 4 E (resTau hE) (resTau_invol hE)).subgroupOf
        (heldGU 4 E (resTau hE) (resTau_invol hE))
    let K₀' : Subgroup ↥(A₁.comap incl) := SU.comap eC.toMonoidHom
    let K₀ : Subgroup ↥CFSG.AGLEmbedding.Om8 := K₀'.map (A₁.comap incl).subtype
    have hHeldSUeq : heldSU 4 E (resTau hE) (resTau_invol hE) = StatedSU 4 2 E :=
      hct_heldSU_eq_statedSU (a := 4) (Q := 2) (resTau_apply hE)
    have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (F := E) (p := 2) (f := 1) (n := 4) (by rw [hE4]; norm_num) (by norm_num)
      (by norm_num)
    have hq2 : Subgroup.center ↥(StatedSU 4 2 E) =
        (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 2 E) := by
      have h := hq.2
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num] at h
      exact h
    have hcenterStated : Subgroup.center ↥(StatedSU 4 2 E) = ⊥ := by
      rw [hq2, scalars_subgroupOf_statedSU_four hEcard]
    have hcenterHeldSU : Subgroup.center ↥(heldSU 4 E (resTau hE) (resTau_invol hE)) = ⊥ := by
      rw [hHeldSUeq]
      exact hcenterStated
    have hcardHeldSU : Nat.card ↥(heldSU 4 E (resTau hE) (resTau_invol hE)) = 25920 := by
      rw [hHeldSUeq]
      obtain ⟨eP⟩ := statedProj_equiv_statedSU_four hEcard
      rw [Nat.card_congr eP.symm.toEquiv]
      exact natCard_statedProj_statedSU_four hE4
    have hcenterSU : Subgroup.center ↥SU = ⊥ := by
      dsimp only [SU]
      exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : heldSU 4 E (resTau hE) (resTau_invol hE) ≤
          heldGU 4 E (resTau hE) (resTau_invol hE))) hcenterHeldSU
    have hcardSU : Nat.card ↥SU = 25920 := by
      dsimp only [SU]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        heldSU 4 E (resTau hE) (resTau_invol hE) ≤
          heldGU 4 E (resTau hE) (resTau_invol hE))).toEquiv).trans hcardHeldSU
    have hSUmem : ∀ A : heldGU 4 E (resTau hE) (resTau_invol hE),
        A ∈ SU ↔ ((A : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E).det = 1 := by
      intro A
      dsimp only [SU]
      rw [Subgroup.mem_subgroupOf, heldSU, Subgroup.mem_inf,
        CFSG.Open.StatedAPI.mem_statedSL_iff]
      exact ⟨fun h => h.2, fun h => ⟨A.2, h⟩⟩
    have hsA₁' : s ∈ A₁.comap incl := by
      rw [← hcentA1]
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
    let s' : ↥(A₁.comap incl) := ⟨s, hsA₁'⟩
    let d : Eˣ := Matrix.GeneralLinearGroup.det ((eC s' : GL (Fin 4) E))
    have hcentGU : eC s' ∈ Subgroup.center ↥(heldGU 4 E (resTau hE) (resTau_invol hE)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := eC.surjective y
      have hx : (x : ↥CFSG.AGLEmbedding.Om8) ∈
          Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8) := by
        rw [hcentA1]
        exact x.2
      have hxs : s * (x : ↥CFSG.AGLEmbedding.Om8) = (x : ↥CFSG.AGLEmbedding.Om8) * s :=
        (Subgroup.mem_centralizer_iff.mp hx) s (Set.mem_singleton s)
      have hx' : x * s' = s' * x := by
        apply Subtype.ext
        exact hxs.symm
      calc eC x * eC s' = eC (x * s') := by rw [map_mul]
        _ = eC (s' * x) := by rw [hx']
        _ = eC s' * eC x := by rw [map_mul]
    have hdet_ne : d ≠ 1 := by
      intro hdet
      have hdet' : ((eC s' : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E).det = 1 := by
        dsimp only [d] at hdet
        rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
      have hmemSU : eC s' ∈ SU := (hSUmem (eC s')).2 hdet'
      have hcentSU : (⟨eC s', hmemSU⟩ : ↥SU) ∈ Subgroup.center ↥SU := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply Subtype.ext
        simpa using (Subgroup.mem_center_iff.mp hcentGU) z
      rw [hcenterSU] at hcentSU
      have h1 : (⟨eC s', hmemSU⟩ : ↥SU) = 1 := Subgroup.mem_bot.mp hcentSU
      have h1' : eC s' = 1 := by
        have := congrArg Subtype.val h1
        simpa using this
      have h2 : s' = 1 := eC.injective (by rw [h1', map_one])
      exact hs1 (congrArg Subtype.val h2)
    have hs'3 : s' ^ 3 = 1 := by
      apply Subtype.ext
      change ((s' : ↥CFSG.AGLEmbedding.Om8) ^ 3) = 1
      rw [show (s' : ↥CFSG.AGLEmbedding.Om8) = s from rfl, hs3]
    have hdet3 : d ^ 3 = 1 := by
      have hpow : eC s' ^ 3 = 1 := by rw [← map_pow, hs'3, map_one]
      dsimp only [d]
      rw [← map_pow, ← Subgroup.coe_pow, hpow, Subgroup.coe_one, map_one]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hordDet : orderOf d = 3 := orderOf_eq_prime hdet3 hdet_ne
    have hcardUnits : Nat.card Eˣ = 3 := by
      rw [Nat.card_units, hE4]
    have hgen : Subgroup.zpowers d = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [Nat.card_zpowers, hordDet, hcardUnits]
    have hpow_mem : ∀ c : Eˣ, ∃ n : ℕ, c = d ^ n := by
      intro c
      have hc : c ∈ Subgroup.zpowers d := by rw [hgen]; exact Subgroup.mem_top c
      rw [mem_zpowers_iff_mem_range_orderOf] at hc
      obtain ⟨n, -, hn⟩ := Finset.mem_image.mp hc
      exact ⟨n, hn.symm⟩
    have hSUrange : SU ≤ eC.toMonoidHom.range := by
      rw [MonoidHom.range_eq_top.mpr eC.surjective]
      exact le_top
    have hK₀leA₁' : K₀ ≤ A₁.comap incl := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact y.2
    refine ⟨K₀, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcentA1]
      exact hK₀leA₁'
    · intro g hg
      have hgA₁' : g ∈ A₁.comap incl := by
        rw [← hcentA1]
        exact hg
      let g' : ↥(A₁.comap incl) := ⟨g, hgA₁'⟩
      obtain ⟨n, hn⟩ := hpow_mem
        (Matrix.GeneralLinearGroup.det ((eC g' : heldGU 4 E (resTau hE) (resTau_invol hE)) :
          GL (Fin 4) E))
      have hkSU : eC g' * ((eC s') ^ n)⁻¹ ∈ SU := by
        refine (hSUmem _).2 ?_
        rw [← Matrix.GeneralLinearGroup.val_det_apply, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_pow, map_mul, map_inv, map_pow, hn]
        dsimp only [d]
        rw [mul_inv_cancel]
        rfl
      have hkK₀' : g' * (s' ^ n)⁻¹ ∈ K₀' := by
        change eC (g' * (s' ^ n)⁻¹) ∈ SU
        rw [map_mul, map_inv, map_pow]
        exact hkSU
      let k' : ↥(A₁.comap incl) := g' * (s' ^ n)⁻¹
      have hk' : k' ∈ K₀' := hkK₀'
      refine ⟨n, (k' : ↥CFSG.AGLEmbedding.Om8), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨k', hk', rfl⟩
      · have hg' : g' = k' * s' ^ n := by
          dsimp only [k']
          group
        have hgval : g = (k' : ↥CFSG.AGLEmbedding.Om8) * s ^ n := by
          have := congrArg Subtype.val hg'
          simpa [g', s'] using this
        have hcomm : Commute (k' : ↥CFSG.AGLEmbedding.Om8) s := by
          have hkC : (k' : ↥CFSG.AGLEmbedding.Om8) ∈
              Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8) := by
            rw [hcentA1]
            exact k'.2
          exact ((Subgroup.mem_centralizer_iff.mp hkC) s (Set.mem_singleton s)).symm
        rw [hgval, (hcomm.pow_right n).eq]
    · intro hsK
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hsK
      have hy' : y = s' := by
        apply Subtype.ext
        simpa [s'] using congrArg Subtype.val hyeq
      have hmem : eC y ∈ SU := hy
      rw [hy'] at hmem
      have h1 : ((eC s' : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E).det = 1 :=
        (hSUmem (eC s')).1 hmem
      apply hdet_ne
      apply Units.ext
      dsimp only [d]
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact h1
    · have hcenterK₀' : Subgroup.center ↥K₀' = ⊥ := by
        obtain ⟨eK⟩ := comap_equiv_of_injective_le_range eC.toMonoidHom eC.injective SU hSUrange
        exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv eK hcenterSU
      exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv
        (Subgroup.equivMapOfInjective K₀' (A₁.comap incl).subtype
          (Subgroup.subtype_injective _)).symm hcenterK₀'
    · dsimp only [K₀]
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      obtain ⟨eK⟩ := comap_equiv_of_injective_le_range eC.toMonoidHom eC.injective SU hSUrange
      rw [Nat.card_congr eK.toEquiv]
      exact hcardSU

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
