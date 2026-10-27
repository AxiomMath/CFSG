module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigCtx
public import CFSG.Walter.AStar.Subnormal
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFBuild
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.Stage2.Local.P34S5SE
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.L52Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.L52Split
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42
public import CFSG.GH74.Generic.BProg.B1.PilotS1ThreeFacts
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerOut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCUb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILi
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUk
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUl
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4ProdU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4SteinU
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigQuot
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NoPump
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7OS1U
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3g
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB10
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIRed
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Final
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalB
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82SecondCentral
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Lift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBSections
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3B
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecLinearHigh
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair
public import CFSG.LocalAnalysis.ComponentClassification.TBLitAssembly
public import CFSG.LocalAnalysis.LargeEvenClassification.Delta
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalCoreIntersection
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption
public import CFSG.LocalAnalysis.OddStandard.Solomon75Inputs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.NonSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Remaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.WalterRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.TheoremC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec

public section

namespace CFSG.ComponentClassification.GSThmB.HConfig

open CFSG Subgroup LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups

section Norm

variable {G : Type} [Group G] [Finite G] {B K : Subgroup G} (hK : IsComponent K)
  [Fintype (Orb B K)]

include hK in
theorem normMap_commute_of_isComponent (x : ↥(K ⊓ centralizer (stab B K : Set G)))
    (hx : ∀ k ∈ K, (x : G) * k = k * x) {L : Subgroup G} (hL : IsComponent L) {y : G}
    (hy : y ∈ L) : Commute y (normMap B K hK x) := by
  rw [normMap_apply]
  refine Finset.noncommProd_commute _ _ _ y fun q _ => ?_
  by_cases hq : L = cj (rep q) K
  · subst hq
    rw [mem_cj] at hy
    have h1 := hx _ hy
    rw [normPart_apply]
    change y * (rep q * x * (rep q)⁻¹) = rep q * x * (rep q)⁻¹ * y
    calc y * (rep q * x * (rep q)⁻¹) = rep q * (((rep q)⁻¹ * y * rep q) * x) * (rep q)⁻¹ := by
          group
      _ = rep q * (x * ((rep q)⁻¹ * y * rep q)) * (rep q)⁻¹ := by rw [h1]
      _ = rep q * x * (rep q)⁻¹ * y := by group
  · exact commute_of_isComponent hL (isComponent_cj hK (rep q)) hq hy (normPart_mem B K q x)

include hK in
theorem normMap_layer_le_centralizer (x : ↥(K ⊓ centralizer (stab B K : Set G)))
    (hx : ∀ k ∈ K, (x : G) * k = k * x) :
    layer G ≤ centralizer ({normMap B K hK x} : Set G) := by
  rw [layer.eq_sSup]
  refine sSup_le fun L hL y hy => ?_
  rw [mem_centralizer_singleton_iff]
  exact (normMap_commute_of_isComponent hK x hx hL hy).eq

end Norm

variable {G : Type} [Group G]

theorem core_config_norm
    [Finite G]
    {B N : Subgroup G} (hNC : N ≤ centralizer (B : Set G))
    (hN : IsPComponent 2 (N.subgroupOf (centralizer (B : Set G)))) (hNE : N ≤ layer G)
    {t : G} (htZ : t ∈ center G) (htN : t ∈ N) (ht1 : t ≠ 1) (htt : t * t = 1) {q : ℕ}
    (hq : Odd q) (h5 : 5 ≤ q) (hSL : HarrisLit.IsSLTwoOver q (↥N ⧸ pPrimeCore 2 ↥N)) :
    ∃ (K T : Subgroup G) (w : G), IsComponent K ∧
      T ≤ K ⊓ centralizer (stab B K : Set G) ∧
      IsPComponent 2 (T.subgroupOf (K ⊓ centralizer (stab B K : Set G))) ∧
      HarrisLit.IsSLTwoOver q (↥T ⧸ pPrimeCore 2 ↥T) ∧
      orderOf w = 2 ∧ w ∈ T ∧ (∀ k ∈ K, w * k = k * w) ∧
      ∀ ω ∈ K, (∀ k ∈ K, ω * k = k * ω) → ω ∈ centralizer (stab B K : Set G) → ω * ω = w →
        ∃ Ω ∈ centralizer (B : Set G), Ω * Ω = t ∧ layer G ≤ centralizer ({Ω} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, -, hNJ⟩ := exists_component_orbit hNC hN hNE
  haveI : Fintype (Orb B K) := Fintype.ofFinite _
  set C := K ⊓ centralizer (stab B K : Set G) with hCdef
  set D' := orbRest B K with hD'def
  set ψ := normMap B K hK with hψdef
  have hN2 := (CatalogueBAlternating.pComponent_two_iff _).mp hN
  have hperf : ⁅N, N⁆ = N := GH74.GLS.TwoThin.commutator_self_of_isTwoComponent hNC hN2
  have hKD' : ⁅K, D'⁆ = ⊥ := by
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    exact orbRest_le_centralizer hK
  have hcKD : ∀ {u v : G}, u ∈ K → v ∈ D' → Commute u v := fun hu hv =>
    commute_of_commutator_eq_bot hKD' hu hv
  have hfixB : ∀ {w : G}, w ∈ centralizer (B : Set G) → ∀ b ∈ B, b * w * b⁻¹ = w := by
    intro w hw b hb
    rw [mem_centralizer_iff.mp hw b hb, mul_inv_cancel_right]
  have hNV : N ≤ C ⊔ D' := by
    rw [← hperf, commutator_le]
    intro n₁ hn₁ n₂ hn₂
    have h1 : n₁ ∈ ((K ⊔ D' : Subgroup G) : Set G) := by
      rw [← orbJoin_eq_sup]
      exact hNJ hn₁
    have h2 : n₂ ∈ ((K ⊔ D' : Subgroup G) : Set G) := by
      rw [← orbJoin_eq_sup]
      exact hNJ hn₂
    rw [coe_sup_of_commutator_eq_bot hKD'] at h1 h2
    obtain ⟨k₁, hk₁, d₁, hd₁, rfl⟩ := h1
    obtain ⟨k₂, hk₂, d₂, hd₂, rfl⟩ := h2
    rw [commutatorElement_mul_mul_eq_mul (hcKD hk₁ hd₁) (hcKD hk₁ hd₂) (hcKD hk₂ hd₁)
      (hcKD hk₂ hd₂)]
    refine mul_mem (mem_sup_left (mem_inf.mpr ⟨?_, ?_⟩)) (mem_sup_right ?_)
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hk₁ hk₂) (inv_mem hk₁)) (inv_mem hk₂)
    · rw [mem_centralizer_iff]
      intro r hr
      have h3 := conj_commutator_eq_of_fixed hKD' (mem_inf.mp hr).2
        (stab_le_normalizer_orbRest hr) hk₁ hd₁ hk₂ hd₂
        (hfixB (hNC hn₁) r (mem_inf.mp hr).1) (hfixB (hNC hn₂) r (mem_inf.mp hr).1)
      exact mul_inv_eq_iff_eq_mul.mp h3
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)
  have hNW : N ≤ ψ.range := by
    set W : Subgroup G := ψ.range with hWdef
    set Z' : Subgroup G := D' ⊓ centralizer (B : Set G) with hZ'def
    have hWZ : ⁅W, Z'⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨x, rfl⟩
      rw [mem_centralizer_iff]
      intro m hm
      have h1 := orbJoin_le_centralizer_of_mem hK (mem_inf.mp hm).1 (mem_inf.mp hm).2
        (normMap_mem_orbJoin hK x)
      rw [mem_centralizer_singleton_iff] at h1
      exact h1.symm
    have hNWZ : N ≤ W ⊔ Z' := by
      intro n hn
      have h1 : n ∈ ((C ⊔ D' : Subgroup G) : Set G) := hNV hn
      have hCD' : ⁅C, D'⁆ = ⊥ := eq_bot_iff.mpr (hKD' ▸ commutator_mono inf_le_left le_rfl)
      rw [coe_sup_of_commutator_eq_bot hCD'] at h1
      obtain ⟨x, hx, d, hd, rfl⟩ := h1
      have he := inv_mul_normMap_mem hK ⟨x, hx⟩
      have hm : (ψ ⟨x, hx⟩)⁻¹ * (x * d) ∈ Z' := by
        refine mem_inf.mpr ⟨?_, mul_mem (inv_mem (normMap_mem_centralizer hK _)) (hNC hn)⟩
        have h2 : (ψ ⟨x, hx⟩)⁻¹ * (x * d) = ((x : G)⁻¹ * ψ ⟨x, hx⟩)⁻¹ * d := by group
        rw [h2]
        exact mul_mem (inv_mem he) hd
      have h3 : x * d = ψ ⟨x, hx⟩ * ((ψ ⟨x, hx⟩)⁻¹ * (x * d)) := by group
      change x * d ∈ W ⊔ Z'
      rw [h3]
      exact mul_mem (mem_sup_left ⟨⟨x, hx⟩, rfl⟩) (mem_sup_right hm)
    rw [← hperf, commutator_le]
    intro n₁ hn₁ n₂ hn₂
    have h1 : n₁ ∈ ((W ⊔ Z' : Subgroup G) : Set G) := hNWZ hn₁
    have h2 : n₂ ∈ ((W ⊔ Z' : Subgroup G) : Set G) := hNWZ hn₂
    rw [coe_sup_of_commutator_eq_bot hWZ] at h1 h2
    obtain ⟨w₁, hw₁, z₁, hz₁, rfl⟩ := h1
    obtain ⟨w₂, hw₂, z₂, hz₂, rfl⟩ := h2
    have hc : ∀ {u v : G}, u ∈ W → v ∈ Z' → Commute u v := fun hu hv =>
      commute_of_commutator_eq_bot hWZ hu hv
    rw [commutatorElement_mul_mul_eq_mul (hc hw₁ hz₁) (hc hw₁ hz₂) (hc hw₂ hz₁) (hc hw₂ hz₂)]
    have hzz : ⁅z₁, z₂⁆ = 1 := by
      have h4 := orbJoin_le_centralizer_of_mem hK (mem_inf.mp hz₁).1 (mem_inf.mp hz₁).2
        (orbRest_le_orbJoin B K (mem_inf.mp hz₂).1)
      rw [mem_centralizer_singleton_iff] at h4
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h4.symm
    rw [hzz, mul_one, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hw₁ hw₂) (inv_mem hw₁)) (inv_mem hw₂)
  have hNperf : Group.IsPerfect ↥N := Subgroup.isPerfect_iff.mpr hperf
  set P : Subgroup ↥C := N.comap ψ with hPdef
  set T₀ : Subgroup ↥C := (perfectResidual ↥P).map P.subtype with hT₀def
  have hT₀perf : Group.IsPerfect ↥T₀ :=
    SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map P
  have hT₀map : T₀.map ψ = N := by
    rw [hT₀def, SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map ψ P, hPdef,
      Subgroup.map_comap_eq, inf_eq_right.mpr hNW]
    exact GS82PumpInputs.P4.map_perfectResidual_of_isPerfect hNperf
  have hψB : ∀ x, ψ x ∈ centralizer (B : Set G) := normMap_mem_centralizer hK
  have hPsub : P.IsSubnormal := by
    obtain ⟨-, -, hsub, -, -⟩ := hN
    have h1 := hsub.comap (ψ.codRestrict (centralizer (B : Set G)) hψB)
    convert h1 using 1
    ext x
    exact Iff.rfl
  have hT₀sub : T₀.IsSubnormal :=
    SignalizerFunctorTheorem.Nonsolvable.isSubnormal_perfectResidual_map hPsub
  have hρmem : ∀ x : ↥T₀, ψ x ∈ N := fun x => hT₀map ▸ ⟨x, x.2, rfl⟩
  let ρ : ↥T₀ →* ↥N := (ψ.comp T₀.subtype).codRestrict N hρmem
  have hρ : Function.Surjective ρ := by
    rintro ⟨n, hn⟩
    rw [← hT₀map] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    exact ⟨⟨x, hx⟩, rfl⟩
  have hρker : ρ.ker ≤ center ↥T₀ := by
    intro x hx
    have h1 : ψ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 := mem_orbRest_of_normMap_eq_one hK h1
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (Subtype.ext (hcKD (mem_inf.mp (y : ↥C).2).1 h2).eq)
  obtain ⟨eT⟩ := nonempty_quot_equiv_of_central_surj hT₀perf ρ hρ hρker hq h5 hSL
  have htc : (⟨t, htN⟩ : ↥N) ∈ center ↥N :=
    mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp htZ y)
  obtain ⟨w₀, hw₀w₀, hρw₀⟩ := GS82PumpInputs.P4.exists_involution_lift ρ hρ hρker hq h5 hSL
    htc (Subtype.ext htt)
  set w : G := ((w₀ : ↥C) : G) with hwdef
  have hψw : ψ (w₀ : ↥C) = t := congrArg Subtype.val hρw₀
  have hww : w * w = 1 := congrArg (fun z : ↥T₀ => ((z : ↥C) : G)) hw₀w₀
  have hw1 : w ≠ 1 := by
    intro h
    apply ht1
    rw [← hψw]
    have h' : (w₀ : ↥C) = 1 := Subtype.ext h
    rw [h', map_one]
  have hwK : ∀ k ∈ K, w * k = k * w := by
    intro k hk
    have he := inv_mul_normMap_mem hK (w₀ : ↥C)
    rw [hψw] at he
    have hc := hcKD hk he
    have htk : Commute t k := (mem_center_iff.mp htZ k).symm
    have h1 : Commute (t * (w⁻¹ * t)⁻¹) k := htk.mul_left hc.symm.inv_left
    rw [show t * (w⁻¹ * t)⁻¹ = w by group] at h1
    exact h1.eq
  have hNq : IsQuasisimple (↥N ⧸ pPrimeCore 2 ↥N) := by
    obtain ⟨e⟩ := nonempty_quot_equiv_of_mulEquiv (subgroupOfEquivOfLe hNC)
    exact LocalCores.isQuasisimple_of_mulEquiv e
      (GH74.GLS.TwoThin.isQuasisimple_hat_of_isPComponent hN)
  have hT₀q : IsQuasisimple (↥T₀ ⧸ pPrimeCore 2 ↥T₀) :=
    LocalCores.isQuasisimple_of_mulEquiv eT.symm hNq
  have hT₀SL : HarrisLit.IsSLTwoOver q (↥T₀ ⧸ pPrimeCore 2 ↥T₀) := by
    obtain ⟨F, hF, hFt, hFq, ⟨eA⟩⟩ := hSL
    exact ⟨F, hF, hFt, hFq, ⟨eT.trans eA⟩⟩
  refine ⟨K, T₀.map C.subtype, w, hK, map_subtype_le _, ?_,
    isSLTwoOver_of_mulEquiv (T₀.equivMapOfInjective C.subtype C.subtype_injective) hT₀SL,
    orderOf_eq_prime (by rw [sq]; exact hww) hw1, ⟨(w₀ : ↥C), w₀.2, rfl⟩, hwK, ?_⟩
  · have h1 : (T₀.map C.subtype).subgroupOf C = T₀ :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective T₀
    rw [h1]
    exact (HarrisLit.isTwoComponent_iff_isPComponent T₀).mp ⟨hT₀sub, hT₀perf, hT₀q⟩
  ·
    intro ω hωK hωc hωR hωw
    set x : ↥C := ⟨ω, mem_inf.mpr ⟨hωK, hωR⟩⟩ with hxdef
    refine ⟨ψ x, hψB x, ?_, normMap_layer_le_centralizer hK x hωc⟩
    have hxx : x * x = (w₀ : ↥C) := Subtype.ext hωw
    rw [← map_mul, hxx, hψw]

variable {H : Type} [Group H] [Finite H]

theorem lift_config_norm {B : Subgroup H} (hB : IsPGroup 2 B) {Kb Tb : Subgroup (Bar H)}
    {wb : Bar H} (hKb : IsComponent Kb)
    (hTb : Tb ≤ Kb ⊓ centralizer (stab (B.map (bar H)) Kb : Set (Bar H)))
    (hTbc : IsPComponent 2 (Tb.subgroupOf (Kb ⊓ centralizer (stab (B.map (bar H)) Kb :
      Set (Bar H))))) {q : ℕ} (hSL : HarrisLit.IsSLTwoOver q (↥Tb ⧸ pPrimeCore 2 ↥Tb))
    (hwb : orderOf wb = 2) (hwbT : wb ∈ Tb) (hwbK : ∀ k ∈ Kb, wb * k = k * wb) :
    ∃ (K R T : Subgroup H) (w : H), IsPComponent 2 K ∧ IsPGroup 2 R ∧
      R ≤ normalizer (K : Set H) ∧ T ≤ K ⊓ centralizer (R : Set H) ∧
      IsPComponent 2 (T.subgroupOf (K ⊓ centralizer (R : Set H))) ∧
      HarrisLit.IsSLTwoOver q (↥T ⧸ pPrimeCore 2 ↥T) ∧ orderOf w = 2 ∧ w ∈ T ∧
      w ∈ (Open.fusionZStar ↥K).map K.subtype ∧
      K.map (bar H) = Kb ∧ R.map (bar H) = stab (B.map (bar H)) Kb ∧ bar H w = wb := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := bar H with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  set O := pPrimeCore 2 H with hO
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨hKc, hKmap, -, huniq⟩ := (CatalogueBPrimeJoin.canonical_prime_component_lift 2).1 Kb hKb
  set K := CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb with hKdef
  set M := Kb.comap φ with hMdef
  set R := B ⊓ (normalizer (Kb : Set (Bar H))).comap φ with hRdef
  have hR2 : IsPGroup 2 R := hB.to_le inf_le_left
  have hRmap : R.map φ = stab (B.map φ) Kb := by
    rw [hRdef, inf_comm, map_comap_inf, inf_comm]
  have hRK : R ≤ normalizer (K : Set H) := by
    intro r hr
    have hrK : φ r ∈ normalizer (Kb : Set (Bar H)) := (mem_inf.mp hr).2
    have h1 : IsPComponent 2 (cj r K) :=
      LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj r) hKc
    have h2 : (cj r K).map φ = Kb := by
      rw [cj, Subgroup.map_map]
      have h3 : φ.comp (MulAut.conj r).toMonoidHom = (MulAut.conj (φ r)).toMonoidHom.comp φ :=
        MonoidHom.ext fun x => by simp
      rw [h3, ← Subgroup.map_map, hKmap]
      exact cj_eq_self_iff.mpr hrK
    exact cj_eq_self_iff.mp (huniq _ h1 h2)
  have hcR : (centralizer (R : Set H)).map φ = centralizer ((R.map φ : Subgroup (Bar H)) :
      Set (Bar H)) := GrSLit.map_centralizer_eq_of_odd_ker φ hφs not_two_dvd_card_ker_bar hR2
  set C₁ := M ⊓ centralizer (R : Set H) with hC₁
  set C₂ := Kb ⊓ centralizer (stab (B.map φ) Kb : Set (Bar H)) with hC₂
  have hC : C₁.map φ = C₂ := by
    rw [hC₁, map_comap_inf, hcR, hRmap]
  have hmem : ∀ x : ↥C₁, φ x ∈ C₂ := fun x => hC ▸ ⟨x, x.2, rfl⟩
  let f : ↥C₁ →* ↥C₂ := (φ.comp C₁.subtype).codRestrict C₂ hmem
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hC] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfφ : φ.comp C₁.subtype = C₂.subtype.comp f := MonoidHom.ext fun _ => rfl
  have hTbq := (HarrisLit.isTwoComponentIn_iff hTb).mpr hTbc
  obtain ⟨-, hTbsub, hTbqs⟩ := hTbq
  set S : Subgroup ↥C₁ := (Tb.subgroupOf C₂).comap f with hSdef
  set T' : Subgroup ↥C₁ := (perfectResidual ↥S).map S.subtype with hT'def
  set T : Subgroup H := T'.map C₁.subtype with hTdef
  have hT'perf : Group.IsPerfect ↥T' :=
    SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map S
  have hT'sub : T'.IsSubnormal :=
    SignalizerFunctorTheorem.Nonsolvable.isSubnormal_perfectResidual_map (hTbsub.comap f)
  have hTbperf : Group.IsPerfect ↥(Tb.subgroupOf C₂) := by
    haveI := hTbqs.1
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTb).symm.toMonoidHom)
      (subgroupOfEquivOfLe hTb).symm.surjective
  have hT'map : T'.map f = Tb.subgroupOf C₂ := by
    rw [hT'def, SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map f S, hSdef,
      Subgroup.map_comap_eq_self_of_surjective hf]
    exact SignalizerFunctorTheorem.Nonsolvable.perfectResidual_map_eq_of_isPerfect hTbperf
  have hTmap : T.map φ = Tb := by
    rw [hTdef, Subgroup.map_map, hfφ, ← Subgroup.map_map, hT'map, subgroupOf_map_subtype,
      inf_eq_left.mpr hTb]
  have hTperf : Group.IsPerfect ↥T := by
    haveI := hT'perf
    exact Group.IsPerfect.map C₁.subtype
  have hTC₁ : T ≤ C₁ := map_subtype_le _
  have hTK : T ≤ K := le_canonicalPrimeLift_of_isPerfect Kb hTperf (hTC₁.trans inf_le_left)
  have hTKR : T ≤ K ⊓ centralizer (R : Set H) := le_inf hTK (hTC₁.trans inf_le_right)
  obtain ⟨eT⟩ := nonempty_quot_equiv_map φ odd_card_ker_bar T
  have eT' : Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* ↥Tb ⧸ pPrimeCore 2 ↥Tb) := by
    obtain ⟨e2⟩ := nonempty_quot_equiv_of_mulEquiv (MulEquiv.subgroupCongr hTmap)
    exact ⟨eT.trans e2⟩
  obtain ⟨eT2⟩ := eT'
  have hwbT' : wb ∈ T.map φ := hTmap ▸ hwbT
  obtain ⟨w₁, hw₁T, hw₁⟩ := hwbT'
  set w := w₁ ^ Nat.card O with hwdef
  have hwb2 : wb * wb = 1 := by
    have h1 := pow_orderOf_eq_one wb
    rwa [hwb, sq] at h1
  have hw₁O : w₁ * w₁ ∈ O := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    change φ (w₁ * w₁) = 1
    rw [map_mul, hw₁, hwb2]
  have hww : w * w = 1 := by
    rw [hwdef, ← pow_add, ← two_mul, pow_mul, sq]
    have h1 : (⟨w₁ * w₁, hw₁O⟩ : ↥O) ^ Nat.card ↥O = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hφw : φ w = wb := by
    rw [hwdef, map_pow, hw₁]
    obtain ⟨k, hk⟩ := hOodd
    rw [hk, pow_succ, pow_mul, sq, hwb2, one_pow, one_mul]
  have hw1 : w ≠ 1 := by
    intro h
    have h1 : wb = 1 := by rw [← hφw, h, map_one]
    rw [h1, orderOf_one] at hwb
    exact absurd hwb (by norm_num)
  have hwT : w ∈ T := pow_mem hw₁T _
  have hwK : w ∈ K := hTK hwT
  refine ⟨K, R, T, w, hKc, hR2, hRK, hTKR, ?_, ?_, orderOf_eq_prime (by rw [sq]; exact hww) hw1,
    hwT, ⟨⟨w, hwK⟩, ?_, rfl⟩, hKmap, hRmap, hφw⟩
  ·
    refine (HarrisLit.isTwoComponentIn_iff hTKR).mp ⟨hTKR, ?_, hTperf,
      LocalCores.isQuasisimple_of_mulEquiv eT2.symm hTbqs.2⟩
    have h1 : T.subgroupOf C₁ = T' := Subgroup.comap_map_eq_self_of_injective
      C₁.subtype_injective T'
    have hle : K ⊓ centralizer (R : Set H) ≤ C₁ :=
      inf_le_inf_right _ (fun x hx => by
        change φ x ∈ Kb
        rw [← hKmap]
        exact ⟨x, hx, rfl⟩)
    have h2 : T.subgroupOf (K ⊓ centralizer (R : Set H)) =
        (T.subgroupOf C₁).comap (Subgroup.inclusion hle) := by
      ext x
      exact Iff.rfl
    rw [h2, h1]
    exact hT'sub.comap _
  · obtain ⟨F, hF, hFt, hFq, ⟨eA⟩⟩ := hSL
    exact ⟨F, hF, hFt, hFq, ⟨eT2.trans eA⟩⟩
  ·
    change (⟨w, hwK⟩ : ↥K) ∈ Open.fusionZStar ↥K
    rw [OddQuot.mem_fusionZStar_iff]
    intro m
    have h1 : ⁅w, (m : H)⁆ ∈ O := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      change φ ⁅w, (m : H)⁆ = 1
      rw [map_commutatorElement, hφw, commutatorElement_eq_one_iff_mul_comm]
      have hm : φ m ∈ Kb := by
        rw [← hKmap]
        exact ⟨m, m.2, rfl⟩
      exact hwbK _ hm
    have h2 : O.subgroupOf K ≤ pPrimeCore 2 ↥K := by
      refine le_sSup ⟨inferInstance, ?_⟩
      have h3 : Nat.card ↥(O.subgroupOf K) ∣ Nat.card O := by
        rw [← Subgroup.card_map_of_injective K.subtype_injective]
        exact Subgroup.card_dvd_of_le (by
          rintro _ ⟨x, hx, rfl⟩
          exact hx)
      exact Nat.Coprime.coprime_dvd_right h3 pPrimeCore_coprime_card
    exact h2 (mem_subgroupOf.mpr h1)

theorem exists_hconfig_norm
    {B N : Subgroup H} (hB : IsPGroup 2 B) (hNC : N ≤ centralizer (B : Set H))
    (hN : IsPComponent 2 (N.subgroupOf (centralizer (B : Set H)))) {t : H}
    (htZ : t ∈ center H) (htN : t ∈ N) (ht : orderOf t = 2) {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hSL : HarrisLit.IsSLTwoOver q (↥N ⧸ pPrimeCore 2 ↥N)) :
    ∃ (K R T : Subgroup H) (w : H), IsPComponent 2 K ∧ IsPGroup 2 R ∧
      R ≤ normalizer (K : Set H) ∧ T ≤ K ⊓ centralizer (R : Set H) ∧
      IsPComponent 2 (T.subgroupOf (K ⊓ centralizer (R : Set H))) ∧
      HarrisLit.IsSLTwoOver q (↥T ⧸ pPrimeCore 2 ↥T) ∧ orderOf w = 2 ∧ w ∈ T ∧
      w ∈ (Open.fusionZStar ↥K).map K.subtype ∧
      ∀ ω ∈ K, (∀ k ∈ K, ω⁻¹ * (k⁻¹ * ω * k) ∈ GH74.GLS.pPrimeCoreOf 2 K) →
        (∀ r ∈ R, ω⁻¹ * (r * ω * r⁻¹) ∈ GH74.GLS.pPrimeCoreOf 2 K) →
        (ω * ω)⁻¹ * w ∈ GH74.GLS.pPrimeCoreOf 2 K →
        ∃ Ω : H, (∀ b ∈ B, Ω⁻¹ * (b * Ω * b⁻¹) ∈ pPrimeCore 2 H) ∧
          (Ω * Ω)⁻¹ * t ∈ pPrimeCore 2 H ∧ (∃ n : ℕ, Ω ^ 2 ^ n ∈ pPrimeCore 2 H) ∧
          ∀ y ∈ pLayer H 2, y⁻¹ * (Ω⁻¹ * y * Ω) ∈ pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hNC', hN', hNE, htZ', htN', ht1, htt, hSL'⟩ := push_config hB hNC hN htZ htN ht hSL
  obtain ⟨Kb, Tb, wb, hKb, hTb, hTbc, hSLb, hwb, hwbT, hwbK, hnorm⟩ :=
    core_config_norm hNC' hN' hNE htZ' htN' ht1 htt hq h5 hSL'
  obtain ⟨K, R, T, w, hKc, hR2, hRK, hTKR, hT, hSLT, hw, hwT, hwK, hKmap, hRmap, hφw⟩ :=
    lift_config_norm hB hKb hTb hTbc hSLb hwb hwbT hwbK
  refine ⟨K, R, T, w, hKc, hR2, hRK, hTKR, hT, hSLT, hw, hwT, hwK, ?_⟩
  intro ω hωK hωc hωR hωw
  have hO : ∀ x : H, bar H x = 1 → x ∈ pPrimeCore 2 H := fun x h =>
    (QuotientGroup.eq_one_iff x).mp h
  have hOK : ∀ x ∈ GH74.GLS.pPrimeCoreOf 2 K, bar H x = 1 := by
    obtain ⟨-, -, hKsub, -, -⟩ := hKc
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mpr (Walter.map_pPrimeCore_le_of_isSubnormal hKsub hx)
  have hωKb : bar H ω ∈ Kb := hKmap ▸ ⟨ω, hωK, rfl⟩
  have hωc' : ∀ k ∈ Kb, bar H ω * k = k * bar H ω := by
    intro k hk
    rw [← hKmap] at hk
    obtain ⟨k, hk, rfl⟩ := hk
    have h2 := hOK _ (hωc k hk)
    simp only [map_mul, map_inv] at h2
    calc bar H ω * bar H k = bar H k * (bar H ω *
          ((bar H ω)⁻¹ * ((bar H k)⁻¹ * bar H ω * bar H k))) := by group
      _ = bar H k * bar H ω := by rw [h2, mul_one]
  have hωR' : bar H ω ∈ centralizer (stab (B.map (bar H)) Kb : Set (Bar H)) := by
    rw [mem_centralizer_iff]
    intro s hs
    rw [← hRmap] at hs
    obtain ⟨r, hr, rfl⟩ := hs
    have h2 := hOK _ (hωR r hr)
    simp only [map_mul, map_inv] at h2
    calc bar H r * bar H ω = bar H ω * ((bar H ω)⁻¹ * (bar H r * bar H ω * (bar H r)⁻¹)) *
          bar H r := by group
      _ = bar H ω * bar H r := by rw [h2, mul_one]
  have hωw' : bar H ω * bar H ω = wb := by
    have h2 := hOK _ hωw
    rw [map_mul, map_inv, map_mul, hφw, inv_mul_eq_one] at h2
    exact h2
  obtain ⟨Ωb, hΩB, hΩt, hΩL⟩ := hnorm _ hωKb hωc' hωR' hωw'
  have hφs : Function.Surjective (bar H) := QuotientGroup.mk'_surjective _
  obtain ⟨Ω, rfl⟩ := hφs Ωb
  refine ⟨Ω, fun b hb => hO _ ?_, hO _ ?_, ⟨2, hO _ ?_⟩, fun y hy => hO _ ?_⟩
  · have h2 : bar H b * bar H Ω = bar H Ω * bar H b :=
      mem_centralizer_iff.mp hΩB _ ⟨b, hb, rfl⟩
    simp only [map_mul, map_inv]
    rw [h2]
    group
  · rw [map_mul, map_inv, map_mul, hΩt, inv_mul_cancel]
  · rw [map_pow, show 2 ^ 2 = 2 * 2 from rfl, pow_mul, sq (bar H Ω), hΩt, sq, htt]
  · have hy' : bar H y ∈ layer (Bar H) := by
      rw [← LBalance.Quot.map_pLayer_eq_layer_quotient]
      exact ⟨y, hy, rfl⟩
    have h2 : bar H y * bar H Ω = bar H Ω * bar H y :=
      mem_centralizer_singleton_iff.mp (hΩL hy')
    simp only [map_mul, map_inv]
    rw [mul_assoc (bar H Ω)⁻¹, h2]
    group

end CFSG.ComponentClassification.GSThmB.HConfig

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open scoped MatrixGroups

theorem pPrimeCoreOf_map_subtype {G : Type*} [Group G] (Y : Subgroup G) (K : Subgroup ↥Y) :
    GH74.GLS.pPrimeCoreOf 2 (K.map Y.subtype) = (GH74.GLS.pPrimeCoreOf 2 K).map Y.subtype := by
  let ψ : ↥K ≃* ↥(K.map Y.subtype) := Subgroup.equivMapOfInjective K Y.subtype Y.subtype_injective
  have h1 : (pPrimeCore 2 ↥K).map ψ.toMonoidHom = pPrimeCore 2 ↥(K.map Y.subtype) :=
    pPrimeCore_map_iso 2 ψ
  have h2 : (K.map Y.subtype).subtype.comp ψ.toMonoidHom = Y.subtype.comp K.subtype := by
    ext g
    rfl
  unfold GH74.GLS.pPrimeCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

namespace Eight2

theorem CtxA0.exists_gs82HConfig_norm
    {X : Type} [Group X] [Finite X] (c : CtxA0 X)
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)))
    (hq3 : ¬ (c.s.p = 3 ∧ c.s.f = 1)) :
    ∃ (r e : ℕ) (K R T : Subgroup X) (w : X), r.Prime ∧ r ≠ 2 ∧ 1 ≤ e ∧
      GS82HConfig (r ^ e) (c.s.h.a * c.b * c.Z.z) K R T w ∧
      r ^ e = c.s.p ^ c.s.f ∧
      c.s.h.a * c.b * c.Z.z ∈
        GH74.GLS.pLayerOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) ∧
      ∀ ω : X, ω ∈ K →
        (∀ k ∈ K, ω⁻¹ * (k⁻¹ * ω * k) ∈ GH74.GLS.pPrimeCoreOf 2 K) →
        (∀ r' ∈ R, ω⁻¹ * (r' * ω * r'⁻¹) ∈ GH74.GLS.pPrimeCoreOf 2 K) →
        (ω * ω)⁻¹ * w ∈ GH74.GLS.pPrimeCoreOf 2 K →
        ∃ Ω : X, Ω ∈ centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) ∧
          (∀ b ∈ c.s.h.secB0 c.s.y, Ω⁻¹ * (b * Ω * b⁻¹) ∈
            GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) ∧
          (Ω * Ω)⁻¹ * (c.s.h.a * c.b * c.Z.z) ∈
            GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) ∧
          (∃ n : ℕ, Ω ^ 2 ^ n ∈
            GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) ∧
          (∀ y ∈ GH74.GLS.pLayerOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)),
            y⁻¹ * (Ω⁻¹ * y * Ω) ∈
              GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N₁, hN₁le, hN₁c, htN₁, p', n, hp', hp'2, hn, ⟨eN⟩, hcard⟩ :=
    gs82Step6ProdInputA0Card_of_cf CatFactsL4U4.cfL4U4ProdCard X c hA hq3
  have ht : orderOf (c.s.h.a * c.b * c.Z.z) = 2 := c.orderOf_abz
  have htL : c.s.h.a * c.b * c.Z.z ∈ Seven.Lay c.s.h c.s.y := c.delta_mem_Lay
  have hLC : Seven.Lay c.s.h c.s.y ≤ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    Seven.Lay_le_centralizer_secB0 c.s.h c.s.y
  have hB₀2 : IsPGroup 2 (c.s.h.secB0 c.s.y) := c.s.h.isPGroup_secB0 c.s.y
  have hB₀Y : c.s.h.secB0 c.s.y ≤ centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hLC htL) b hb)
  have hLY : Seven.Lay c.s.h c.s.y ⊓ centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) ≤
      centralizer (c.s.h.secB0 c.s.y : Set X) ⊓ centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) :=
    inf_le_inf_right _ hLC
  have hnorm : ((Seven.Lay c.s.h c.s.y ⊓ centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)).subgroupOf
      (centralizer (c.s.h.secB0 c.s.y : Set X) ⊓
        centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))).Normal := by
    have hLn := Seven.normal_layerIn_subgroupOf (centralizer (c.s.h.secB0 c.s.y : Set X))
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨hxL, hxY⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := hLn.conj_mem ⟨x, hLC hxL⟩ (mem_subgroupOf.mpr hxL) ⟨g, (mem_inf.mp g.2).1⟩
      exact mem_subgroupOf.mp h1
    · exact mul_mem (mul_mem (mem_inf.mp g.2).2 hxY) (inv_mem (mem_inf.mp g.2).2)
  have hN₁CY : IsPComponent 2 (N₁.subgroupOf (centralizer (c.s.h.secB0 c.s.y : Set X) ⊓
      centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hN₁le hLY hnorm.isSubnormal hN₁c
  have hcentB : centralizer (((c.s.h.secB0 c.s.y).subgroupOf
      (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) : Subgroup _) : Set _) =
      (centralizer (c.s.h.secB0 c.s.y : Set X) ⊓
        centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)).subgroupOf
        (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) := by
    ext x
    rw [mem_subgroupOf, mem_centralizer_iff, mem_inf, mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨fun b hb => ?_, x.2⟩
      exact congrArg Subtype.val (h ⟨b, hB₀Y hb⟩ (mem_subgroupOf.mpr hb))
    · rintro ⟨h, -⟩ b hb
      exact Subtype.ext (h b (mem_subgroupOf.mp hb))
  have hB : IsPGroup 2 ((c.s.h.secB0 c.s.y).subgroupOf
      (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) :=
    hB₀2.of_equiv (subgroupOfEquivOfLe hB₀Y).symm
  have hNC : N₁.subgroupOf (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) ≤
      centralizer (((c.s.h.secB0 c.s.y).subgroupOf
        (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) : Subgroup _) : Set _) := by
    rw [hcentB]
    intro x hx
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hLC (mem_inf.mp (hN₁le (mem_subgroupOf.mp hx))).1,
      x.2⟩)
  have hN : IsPComponent 2
      ((N₁.subgroupOf (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))).subgroupOf
      (centralizer (((c.s.h.secB0 c.s.y).subgroupOf
        (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) : Subgroup _) : Set _))) := by
    rw [hcentB]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two).mpr hN₁CY
  have hty : c.s.h.a * c.b * c.Z.z ∈ centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) :=
    mem_centralizer_singleton_iff.mpr rfl
  have htZ : (⟨_, hty⟩ : ↥(centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) ∈ center _ :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have htN : (⟨_, hty⟩ : ↥(centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) ∈
      N₁.subgroupOf (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) := mem_subgroupOf.mpr htN₁
  have ht' : orderOf (⟨_, hty⟩ : ↥(centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ht
  have hN₁Y : N₁ ≤ centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) := hN₁le.trans inf_le_right
  have hq : Odd (p' ^ n) := (hp'.out.odd_of_ne_two hp'2).pow
  have hSL : HarrisLit.IsSLTwoOver (p' ^ n) (↥(N₁.subgroupOf
      (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) ⧸ pPrimeCore 2 ↥(N₁.subgroupOf
      (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)))) := by
    obtain ⟨e1⟩ := HConfig.nonempty_quot_equiv_of_mulEquiv (subgroupOfEquivOfLe hN₁Y)
    letI : Fintype (GaloisField p' n) := Fintype.ofFinite _
    refine ⟨GaloisField p' n, inferInstance, inferInstance, ?_, ⟨e1.trans eN⟩⟩
    rw [← Nat.card_eq_fintype_card, GaloisField.card p' n hn.ne']
  have h5 : 5 ≤ p' ^ n := by
    have h3 : 3 ≤ p' ^ n := by
      have hp3 : 3 ≤ p' := by
        have := hp'.out.two_le
        rcases Nat.lt_or_ge p' 3 with h | h
        · exact absurd (by omega : p' = 2) hp'2
        · exact h
      exact hp3.trans (Nat.le_self_pow hn.ne' p')
    rcases (show p' ^ n = 3 ∨ 5 ≤ p' ^ n by obtain ⟨k, hk⟩ := hq; omega) with h | h
    · exfalso
      have hQ : IsQuasisimple (↥N₁ ⧸ pPrimeCore 2 ↥N₁) := by
        obtain ⟨e⟩ := HConfig.nonempty_quot_equiv_of_mulEquiv (subgroupOfEquivOfLe hN₁le)
        exact LocalCores.isQuasisimple_of_mulEquiv e
          (GH74.GLS.TwoThin.isQuasisimple_hat_of_isPComponent hN₁c)
      have hS : Group.IsSolvable SL(2, GaloisField p' n) :=
        GH74.Generic.BProg.B1.PilotS1.isSolvable_sl2_three
          (by rw [GaloisField.card p' n hn.ne', h])
      exact not_isSolvable_of_isQuasisimple hQ (solvable_of_surjective
        (f := eN.symm.toMonoidHom) eN.symm.surjective)
    · exact h
  obtain ⟨K, R, T, w, hK, hR, hRK, hTKR, hT, hSLT, hw, hwT, hwK, hΩ⟩ :=
    HConfig.exists_hconfig_norm hB hNC hN htZ htN ht' hq h5 hSL
  refine ⟨p', n, _, _, _, _, hp'.out, hp'2, hn,
    gs82HConfig_of_centralizer ht hK hR hRK hTKR hT hSLT hw hwT hwK, hcard, ?_, ?_⟩
  ·
    have h1 : c.s.h.a * c.b * c.Z.z ∈ GH74.GLS.pLayerOf 2
        (centralizer (c.s.h.secB0 c.s.y : Set X) ⊓
          centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) :=
      (le_sSup (show N₁ ∈ {L | GH74.GLS.IsPCompIn 2 (centralizer (c.s.h.secB0 c.s.y : Set X) ⊓
          centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) L} from
        ⟨hN₁le.trans hLY, hN₁CY⟩)) htN₁
    rw [inf_comm] at h1
    exact GH74.GLS.Stage2.Signalizer.L52Two.I1.pLayerOf_inf_centralizer_le hB₀Y hB₀2 h1
  ·
    intro ω hω hωc hωR hωw
    obtain ⟨ω', hω', rfl⟩ := hω
    have hOmap : ∀ x : ↥(centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)),
        (x : X) ∈ GH74.GLS.pPrimeCoreOf 2 (K.map (centralizer
          ({c.s.h.a * c.b * c.Z.z} : Set X)).subtype) → x ∈ GH74.GLS.pPrimeCoreOf 2 K := by
      intro x hx
      rw [pPrimeCoreOf_map_subtype] at hx
      exact (Subgroup.mem_map_iff_mem (centralizer
        ({c.s.h.a * c.b * c.Z.z} : Set X)).subtype_injective).mp hx
    have hO : ∀ x : ↥(centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)),
        x ∈ pPrimeCore 2 ↥(centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) →
        (x : X) ∈ GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)) :=
      fun x hx => ⟨x, hx, rfl⟩
    obtain ⟨Ω, hΩB, hΩt, ⟨m, hm⟩, hΩL⟩ := hΩ ω' hω'
      (fun k hk => hOmap (ω'⁻¹ * (k⁻¹ * ω' * k)) (hωc _ ⟨k, hk, rfl⟩))
      (fun r hr => hOmap (ω'⁻¹ * (r * ω' * r⁻¹)) (hωR _ ⟨r, hr, rfl⟩))
      (hOmap ((ω' * ω')⁻¹ * w) hωw)
    refine ⟨Ω, Ω.2, fun b hb => ?_, hO _ hΩt, ⟨m, ?_⟩, fun y hy => ?_⟩
    · exact hO (Ω⁻¹ * (⟨b, hB₀Y hb⟩ * Ω * ⟨b, hB₀Y hb⟩⁻¹))
        (hΩB ⟨b, hB₀Y hb⟩ (mem_subgroupOf.mpr hb))
    · rw [← Subgroup.coe_pow]
      exact hO _ hm
    · rw [GH74.GLS.Stage2.Signalizer.L52Two.I1.pLayerOf_eq_map_pLayer] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      exact hO (y'⁻¹ * (Ω⁻¹ * y' * Ω)) (hΩL y' hy')

end Eight2

end CFSG.ComponentClassification.GSThmB
