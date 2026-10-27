module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYMinus
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Center
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassList
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder
public import CFSG.LieType.Chevalley.C2E6StandardLeviFactors
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Steinberg.Adjoint

local instance twistedE6PilotClassesNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Defs

variable (K : Type) [Field K]

@[expose] noncomputable def stdRep : Fin 2 → ModGL TwistTag.E6.tag K :=
  ![pinnedX TwistTag.E6.tag K e6HighestRoot 1, twistedE6ClassU K]

@[expose] noncomputable def repX : Fin 2 → ModGL TwistTag.E6.tag K :=
  ![pinnedX TwistTag.E6.tag K (Pi.single 3 1) 1,
    pinnedX TwistTag.E6.tag K rootE15 1 * pinnedX TwistTag.E6.tag K rootE26 1]

@[expose] noncomputable def repY : Fin 2 → ModGL TwistTag.E6.tag K :=
  ![pinnedX TwistTag.E6.tag K (Pi.single 1 1) 1,
    pinnedX TwistTag.E6.tag K (Pi.single 2 1) 1 * pinnedX TwistTag.E6.tag K (Pi.single 4 1) 1]

end Defs

@[expose] def repWordX : Fin 2 → List (Fin TwistTag.E6.foldedTag.rank) :=
  ![relWordTX, relWordUX]

@[expose] def repWordY : Fin 2 → List (Fin TwistTag.E6.foldedTag.rank) :=
  ![relWordTY, relWordUY]


section Transport

variable {K : Type} [Field K]

theorem conj_repWordX [CharP K 2] (κ : Fin 2) :
    twistedE6RelWeyl K (repWordX κ) * stdRep K κ * (twistedE6RelWeyl K (repWordX κ))⁻¹ =
      repX K κ := by
  fin_cases κ
  · exact conj_relWordTX_pinnedX_highRoot 1
  · exact conj_relWordUX_twistedE6ClassU

theorem conj_repWordY [CharP K 2] (κ : Fin 2) :
    twistedE6RelWeyl K (repWordY κ) * stdRep K κ * (twistedE6RelWeyl K (repWordY κ))⁻¹ =
      repY K κ := by
  fin_cases κ
  · exact conj_relWordTY_pinnedX_highRoot 1
  · exact conj_relWordUY_twistedE6ClassU

theorem stdRep_mem_C0 [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    stdRep K κ ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  fin_cases κ
  · exact pinnedX_mem_graphFixedRootGroup_of_fixed σ isRoot_e6HighestRoot
      permLattice_e6HighestRoot (map_one σ)
  · exact twistedE6ClassU_mem_graphFixedRootGroup hσσ

theorem repX_mem_C0 [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    repX K κ ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  rw [← conj_repWordX]
  exact mul_mem (mul_mem (twistedE6RelWeyl_mem σ _) (stdRep_mem_C0 hσσ κ))
    (inv_mem (twistedE6RelWeyl_mem σ _))

theorem repY_mem_C0 [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    repY K κ ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  rw [← conj_repWordY]
  exact mul_mem (mul_mem (twistedE6RelWeyl_mem σ _) (stdRep_mem_C0 hσσ κ))
    (inv_mem (twistedE6RelWeyl_mem σ _))

theorem repX_mem_subsystemGroup (κ : Fin 2) :
    repX K κ ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  rw [subsystemGroup_eq_rootSpan]
  have hroots : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → γ 1 = 0 →
      γ ∈ parabolicRoots TwistTag.E6.tag E6GraphLevi.setA := by
    intro γ hγ h1
    refine ⟨hγ, fun i hi => ?_⟩
    have hi1 : i = 1 := by
      by_contra h
      exact hi h
    rw [hi1]
    exact h1
  fin_cases κ
  · exact pinnedX_mem_rootSpan (hroots _ (isRoot_single _ 3) rfl) 1
  · exact mul_mem (pinnedX_mem_rootSpan (hroots _ isRoot_rootE15.1 rfl) 1)
      (pinnedX_mem_rootSpan (hroots _ isRoot_rootE15.2 rfl) 1)

theorem repY_mem_subsystemGroup (κ : Fin 2) :
    repY K κ ∈ subsystemGroup TwistTag.E6.tag K setD := by
  have hx : ∀ j : Fin TwistTag.E6.tag.rank, j ∈ setD →
      pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 ∈ subsystemGroup TwistTag.E6.tag K setD :=
    fun j hj => by
      rw [pinnedX_single]
      exact Subgroup.subset_closure ⟨j, hj, 1, Or.inl rfl⟩
  have h1 : (1 : Fin TwistTag.E6.tag.rank) ∈ setD := by
    show (1 : Fin 6) ∈ setD
    simp [setD]
  have h2 : (2 : Fin TwistTag.E6.tag.rank) ∈ setD := by
    show (2 : Fin 6) ∈ setD
    simp [setD]
  have h4 : (4 : Fin TwistTag.E6.tag.rank) ∈ setD := by
    show (4 : Fin 6) ∈ setD
    simp [setD]
  fin_cases κ
  · exact hx 1 h1
  · exact mul_mem (hx 2 h2) (hx 4 h4)

theorem repX_mem_su6Levi [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    repX K κ ∈ su6Levi σ :=
  ⟨repX_mem_subsystemGroup κ, repX_mem_C0 hσσ κ⟩

theorem repY_mem_omegaMinusLevi [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    (κ : Fin 2) : repY K κ ∈ omegaMinusLevi σ :=
  ⟨repY_mem_subsystemGroup κ, repY_mem_C0 hσσ κ⟩

theorem isConj_stdRep_repX [CharP K 2] (σ : K →+* K) (κ : Fin 2) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ, g * stdRep K κ * g⁻¹ = repX K κ :=
  ⟨_, twistedE6RelWeyl_mem σ _, conj_repWordX κ⟩

theorem isConj_stdRep_repY [CharP K 2] (σ : K →+* K) (κ : Fin 2) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ, g * stdRep K κ * g⁻¹ = repY K κ :=
  ⟨_, twistedE6RelWeyl_mem σ _, conj_repWordY κ⟩

theorem isConj_repX_repY [CharP K 2] (σ : K →+* K) (κ : Fin 2) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ, g * repX K κ * g⁻¹ = repY K κ := by
  refine ⟨twistedE6RelWeyl K (repWordY κ) * (twistedE6RelWeyl K (repWordX κ))⁻¹,
    mul_mem (twistedE6RelWeyl_mem σ _) (inv_mem (twistedE6RelWeyl_mem σ _)), ?_⟩
  rw [← conj_repWordX, ← conj_repWordY]
  group

end Transport

section Involutions

variable {K : Type} [Field K]

theorem pinnedX_highRoot_one_ne_one : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ≠ 1 := fun h =>
  one_ne_zero (pinnedX_injective (τ := TwistTag.E6.tag) (R := K) e6HighestRoot
    (h.trans (pinnedX_zero (τ := TwistTag.E6.tag) (R := K) e6HighestRoot).symm))

theorem twistedE6ClassU_ne_one : twistedE6ClassU K ≠ 1 := by
  intro hu
  obtain ⟨hU, hU', -⟩ := isRoot_twistedE6ClassRoots
  have hpos : ∀ α ∈ [twistedE6ClassRootU, twistedE6ClassRootU'],
      IsRoot TwistTag.E6.tag α ∧ 0 < height α := by
    intro α hα
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
    rcases hα with rfl | rfl
    · exact ⟨hU, by decide⟩
    · exact ⟨hU', by decide⟩
  have h := pinnedX_list_prod_injective (τ := TwistTag.E6.tag) (R := K)
    [twistedE6ClassRootU, twistedE6ClassRootU'] (by decide) hpos (fun _ => (1 : K))
    (fun _ => (0 : K)) (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        pinnedX_zero]
      exact hu) twistedE6ClassRootU (List.mem_cons_self ..)
  exact one_ne_zero h

theorem stdRep_ne_one (κ : Fin 2) : stdRep K κ ≠ 1 := by
  fin_cases κ
  · exact pinnedX_highRoot_one_ne_one
  · exact twistedE6ClassU_ne_one

theorem stdRep_sq [CharP K 2] (κ : Fin 2) : stdRep K κ ^ 2 = 1 := by
  fin_cases κ
  · exact pinnedX_one_sq_of_charTwo _
  · exact twistedE6ClassU_sq

theorem orderOf_stdRep [CharP K 2] (κ : Fin 2) : orderOf (stdRep K κ) = 2 :=
  orderOf_eq_prime (stdRep_sq κ) (stdRep_ne_one κ)

theorem orderOf_conj_eq_two {G : Type*} [Group G] {s : G} (hs : orderOf s = 2) (n : G) :
    orderOf (n * s * n⁻¹) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [conj_pow, ← hs, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  · have h1 : s = 1 := by
      calc s = n⁻¹ * (n * s * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    rw [h1, orderOf_one] at hs
    omega

theorem orderOf_repX [CharP K 2] (κ : Fin 2) : orderOf (repX K κ) = 2 := by
  rw [← conj_repWordX]
  exact orderOf_conj_eq_two (orderOf_stdRep κ) _

theorem orderOf_repY [CharP K 2] (κ : Fin 2) : orderOf (repY K κ) = 2 := by
  rw [← conj_repWordY]
  exact orderOf_conj_eq_two (orderOf_stdRep κ) _

end Involutions

section TwoCentral

variable {f : ℕ} {K : Type} [Field K]

theorem conj_repX_zero_iff_twoCentral (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : graphFixedRootGroup TwistTag.E6 K σ}
    (hx : orderOf x = 2) :
    (∃ g : graphFixedRootGroup TwistTag.E6 K σ,
        ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
          repX K 0) ↔
      ∃ S : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ),
        ∀ s ∈ (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)), s * x = x * s := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := apply_apply_eq hK hσ
  obtain ⟨w₀, hw₀⟩ :=
    Finite.exists_max fun w : WeylGroup TwistTag.E6.tag => (coxeterSystem TwistTag.E6.tag).length w
  obtain ⟨P, hP⟩ := (exceptional_fixed_Sylow_opposition TwistTag.E6 K 2 σE w₀ hw₀).1
  set t₀ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    ⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1, stdRep_mem_C0 hσσ 0⟩ with ht₀
  set n₀ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    ⟨twistedE6RelWeyl K relWordTX, twistedE6RelWeyl_mem _ _⟩ with hn₀def
  have hn₀ : ((n₀ * t₀ * n₀⁻¹ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :
      ModGL TwistTag.E6.tag K) = repX K 0 := conj_repWordX 0
  have hPt : ∀ p ∈ (P : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)),
      p * t₀ = t₀ * p := by
    intro p hp
    rw [hP, mem_subgroupOf] at hp
    exact Subtype.ext (commute_e6HighestRoot_of_mem_posUnipotent K (mem_inf.1 hp).1 1).eq
  constructor
  · rintro ⟨g, hg⟩
    have hgx : g * x * g⁻¹ = n₀ * t₀ * n₀⁻¹ := Subtype.ext (hg.trans hn₀.symm)
    set a := g⁻¹ * n₀ with ha
    have hx' : x = a * t₀ * a⁻¹ := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (n₀ * t₀ * n₀⁻¹) * g := by rw [hgx]
        _ = a * t₀ * a⁻¹ := by rw [ha]; group
    refine ⟨a • P, fun s hs => ?_⟩
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hs
    have h1 := hPt _ hs
    rw [MulAut.smul_def, MulAut.conj_inv_apply] at h1
    rw [hx']
    calc s * (a * t₀ * a⁻¹) = a * ((a⁻¹ * s * a) * t₀) * a⁻¹ := by group
      _ = a * (t₀ * (a⁻¹ * s * a)) * a⁻¹ := by rw [h1]
      _ = a * t₀ * a⁻¹ * s := by group
  · rintro ⟨S, hS⟩
    have hxS : x ∈ (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) := by
      have hxp : IsPGroup 2 (zpowers x) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
      have hnorm : zpowers x ≤
          normalizer (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) := by
        rw [zpowers_le, mem_normalizer_iff]
        intro s
        constructor
        · intro hs
          rw [← hS s hs, mul_inv_cancel_right]
          exact hs
        · intro hs
          have e := hS _ hs
          have e2 : x * s = x * (x * s * x⁻¹) := by rw [← e]; group
          have : s = x * s * x⁻¹ := mul_left_cancel e2
          rw [this]
          exact hs
      have hsup := S.is_maximal' (S.isPGroup'.to_sup_of_normal_left' hxp hnorm) le_sup_left
      rw [← hsup]
      exact mem_sup_right (mem_zpowers x)
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (graphFixedRootGroup TwistTag.E6 K σE.toRingHom) S P
    set y := a * x * a⁻¹ with hydef
    have hmemP : ∀ z, z ∈ (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) →
        a * z * a⁻¹ ∈ (P : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) := by
      intro z hz
      rw [← ha, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_inv_apply]
      have e : a⁻¹ * (a * z * a⁻¹) * a = z := by group
      rw [e]
      exact hz
    have hyP := hmemP x hxS
    have hyc : ∀ p ∈ (P : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)),
        p * y = y * p := by
      intro p hp
      have hp' : a⁻¹ * p * a ∈ (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) := by
        rw [← ha, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
          MulAut.conj_inv_apply] at hp
        exact hp
      have e := hS _ hp'
      calc p * y = a * ((a⁻¹ * p * a) * x) * a⁻¹ := by rw [hydef]; group
        _ = a * (x * (a⁻¹ * p * a)) * a⁻¹ := by rw [e]
        _ = y * p := by rw [hydef]; group
    have hyU : (y : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σE.toRingHom := by
      rw [hP, mem_subgroupOf] at hyP
      exact hyP
    have hyZ : ∀ u ∈ graphFixedPosUnipotent TwistTag.E6 K σE.toRingHom,
        (y : ModGL TwistTag.E6.tag K) * u = u * y := by
      intro u hu
      have hu' : (⟨u, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hu⟩ :
          graphFixedRootGroup TwistTag.E6 K σE.toRingHom) ∈
            (P : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) := by
        rw [hP, mem_subgroupOf]
        exact hu
      exact (congrArg Subtype.val (hyc _ hu')).symm
    obtain ⟨d₀, hd₀⟩ := exists_twistedE6_sigma_ne hf hK hσ
    have hyθ := mem_rootSubgroup_e6HighestRoot_of_mem_center hσσ hd₀ hyU hyZ
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hyθ
    have hFy : twistHom TwistTag.E6 K σE.toRingHom (y : ModGL TwistTag.E6.tag K) = y :=
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ y.2)).2
    have hσc : σE c = c := by
      rw [← hc] at hFy
      have h' := E6GraphLevi.twistHom_pinnedX_theta (E6GraphLevi.two_eq_zero_of_card_sq hf hK)
        σE.toRingHom true c
      simp only [ite_true] at h'
      rw [h'] at hFy
      exact pinnedX_injective (τ := TwistTag.E6.tag) (R := K) e6HighestRoot hFy
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [pinnedX_zero] at hc
      have hy1 : y = 1 := Subtype.ext hc.symm
      have hx1 : x = 1 := by
        calc x = a⁻¹ * y * a := by rw [hydef]; group
          _ = 1 := by rw [hy1]; group
      rw [hx1, orderOf_one] at hx
      omega
    set cu : Kˣ := Units.mk0 c hc0 with hcu
    have hcuσ : Units.map σE.toRingHom.toMonoidHom cu⁻¹ = cu⁻¹ := by
      refine Units.ext ?_
      rw [Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]
      change σE c⁻¹ = c⁻¹
      rw [map_inv₀, hσc]
    obtain ⟨b, hb2, hbσ⟩ := exists_sq_eq_of_sigma_fixed σE.toRingHom hcuσ
    have hbC : frameTorusElt TwistTag.E6.tag K e6HighestRoot b ∈
        graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
      frameTorusElt_mem_graphFixedRootGroup σE.toRingHom permLattice_e6HighestRoot hbσ
    set h : graphFixedRootGroup TwistTag.E6 K σE.toRingHom := ⟨_, hbC⟩ with hhdef
    have hconj : h * y * h⁻¹ = t₀ := by
      refine Subtype.ext ?_
      change frameTorusElt TwistTag.E6.tag K e6HighestRoot b * (y : ModGL TwistTag.E6.tag K) *
        (frameTorusElt TwistTag.E6.tag K e6HighestRoot b)⁻¹ = pinnedX TwistTag.E6.tag K e6HighestRoot 1
      rw [← hc, frameTorusElt_conj_pinnedX _ b isRoot_e6HighestRoot c,
        show iform e6HighestRoot e6HighestRoot = 2 by decide]
      congr 1
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hb2, hcu,
        Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hc0]
    have hfin : n₀ * h * a * x * (n₀ * h * a)⁻¹ = n₀ * t₀ * n₀⁻¹ := by
      calc n₀ * h * a * x * (n₀ * h * a)⁻¹ = n₀ * (h * (a * x * a⁻¹) * h⁻¹) * n₀⁻¹ := by group
        _ = n₀ * t₀ * n₀⁻¹ := by rw [← hydef, hconj]
    exact ⟨n₀ * h * a, (congrArg Subtype.val hfin).trans hn₀⟩

end TwoCentral

section ClassList

variable {f : ℕ} {K : Type} [Field K]

theorem exists_conj_repX_or_classV (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : graphFixedRootGroup TwistTag.E6 K σ}
    (hx : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ g : graphFixedRootGroup TwistTag.E6 K σ,
      ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
          repX K 0 ∨
        ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
          repX K 1 ∨
        ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
          twistedE6ClassV K := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction hf hK hσ
    (twistedE6FrameReduction hf hK hσ) hx hx1
  have hmov : ∀ κ : Fin 2, ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :
      ModGL TwistTag.E6.tag K) = stdRep K κ →
        ∃ g' : graphFixedRootGroup TwistTag.E6 K σE.toRingHom,
          ((g' * x * g'⁻¹ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :
            ModGL TwistTag.E6.tag K) = repX K κ := by
    intro κ hκ
    set n : graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
      ⟨twistedE6RelWeyl K (repWordX κ), twistedE6RelWeyl_mem _ _⟩ with hn
    refine ⟨n * g, ?_⟩
    have e : n * g * x * (n * g)⁻¹ = n * (g * x * g⁻¹) * n⁻¹ := by group
    rw [e, ← conj_repWordX κ, ← hκ]
    rfl
  rcases hg with h | h | h
  · obtain ⟨g', hg'⟩ := hmov 0 h
    exact ⟨g', Or.inl hg'⟩
  · obtain ⟨g', hg'⟩ := hmov 1 h
    exact ⟨g', Or.inr (Or.inl hg')⟩
  · exact ⟨g, Or.inr (Or.inr h)⟩

end ClassList

section Subtype

variable {f : ℕ} {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

@[expose] noncomputable def repXC (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨repX K κ, repX_mem_C0 hσσ κ⟩

@[expose] noncomputable def repYC (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨repY K κ, repY_mem_C0 hσσ κ⟩

theorem isConj_repXC_repYC (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    IsConj (repXC hσσ κ) (repYC hσσ κ) := by
  obtain ⟨g, hg, hgx⟩ := isConj_repX_repY σ κ
  exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hgx⟩

theorem isConj_repXC_zero_iff_twoCentral (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : graphFixedRootGroup TwistTag.E6 K σ}
    (hx : orderOf x = 2) :
    IsConj x (repXC (apply_apply_eq hK hσ) 0) ↔
      ∃ S : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ),
        ∀ s ∈ (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)), s * x = x * s := by
  rw [← conj_repX_zero_iff_twoCentral hf hK hσ hx, isConj_iff]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, congrArg Subtype.val hg⟩, fun ⟨g, hg⟩ => ⟨g, Subtype.ext hg⟩⟩

end Subtype

end CFSG.SeitzReduction.TwistedE6Pilot
