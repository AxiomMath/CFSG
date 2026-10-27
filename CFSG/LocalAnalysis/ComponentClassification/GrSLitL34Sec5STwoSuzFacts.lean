module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.SuzFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzLocal
public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzPerfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.OuterBConj
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

section

open CFSG Subgroup
open CFSG.Sporadic.SuzOddCore (suzM)

@[expose] def TwoSuzAutTwoRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Blueprint.NativeSporadic.IsSporadic X .Suz →
    pRank 2 (MulAut X) ≤ 6

theorem twoSuzAutTwoRank_holds :
    TwoSuzAutTwoRank := by
  intro X _ _ hX
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.Solomon78.suz_equiv_of_isSporadic hX
  have : Finite (MulAut ↥suzM) :=
    Finite.of_injective (fun f : MulAut ↥suzM => (f : ↥suzM → ↥suzM))
      fun f g h => MulEquiv.ext (congrFun h)
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) fun f g h => MulEquiv.ext (congrFun h)
  calc pRank 2 (MulAut X) ≤ pRank 2 (MulAut ↥suzM) :=
        RankThree.OddKernel.pRank_le_of_injective (by norm_num)
          (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    _ ≤ 6 := by
      rw [SectionRank.pRank_eq_open_pRank_top]
      refine SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
      obtain ⟨hc, hpow⟩ := hE
      exact CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.suzAut_rank E
        (fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩))
        (fun x hx => by rw [← pow_two]; exact hpow x hx)

theorem suzCentralTwoGroupOrderBound_holds :
    CFSG.ComponentClassification.RankTwoSporadic.Suz.SuzCentralTwoGroupOrderBound :=
  CFSG.ComponentClassification.RankTwoSporadic.Suz.suzCentralTwoGroupOrderBound_of_checks
    CFSG.ComponentClassification.RankTwoSporadic.Suz.suz_tabCheck
    CFSG.ComponentClassification.RankTwoSporadic.Suz.suz_rho0Check
    CFSG.ComponentClassification.RankTwoSporadic.Suz.suz_l0Check
    CFSG.ComponentClassification.RankTwoSporadic.Suz.suz_l1Check
    CFSG.ComponentClassification.RankTwoSporadic.Suz.suz_l2Check

end

section

open CFSG Subgroup

@[expose] def TwoSuzCentralizerFacts : Prop :=
  ∀ (Λ : Type) [Group Λ] [Finite Λ], Group.IsPerfect Λ →
    Blueprint.NativeSporadic.IsSporadic (Λ ⧸ center Λ) .Suz → Nat.card (center Λ) = 2 →
    ∀ y : Λ, y * y = 1 → y ∉ center Λ →
      Group.IsPerfect
          (centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} : Set (Λ ⧸ center Λ))) ∧
        HasSimpleQuotient3Quart
          (centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} : Set (Λ ⧸ center Λ)))

end

section

open CFSG Subgroup
open CFSG.Sporadic.SuzOddCore (suzM suzInv invE)

theorem hasSimpleQuotient3Quart_invE_one :
    HasSimpleQuotient3Quart ↥(invE 1) := by
  obtain ⟨Q₁, ρ, hQ8, hQle, -, hrange, hker, -⟩ := AS81.SuzB0.suzB0_model
  obtain ⟨hcard, -, hsimple, -⟩ :=
    AS81.SuzB0.omega_facts AS81.SuzB0.b0_parts.2.2.2.2.2.2
  let e := (QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨ρ.ker, MonoidHom.normal_ker ρ, ?_, MulEquiv.isSimpleGroup e, ?_⟩
  · have h2 : IsPGroup 2 ↥(Q₁.subgroupOf (invE 1)) := by
      refine IsPGroup.of_card (n := 7) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv]
      exact hQ8.2.1
    rw [hker]
    have := h2.isNilpotent
    infer_instance
  · rw [Nat.card_congr e.toEquiv, hcard]
    norm_num

theorem nonempty_mulEquiv_invE_one
    {G : Type*} [Group G] (e : G ≃* ↥suzM) {a : G} {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzM)
    (hac : ((e a : ↥suzM) : Equiv.Perm (Fin 1782)) = c * suzInv 1 * c⁻¹) :
    Nonempty (↥(invE 1) ≃* ↥(centralizer ({a} : Set G))) := by
  have hE : invE 1 = suzM ⊓ centralizer ({suzInv 1} : Set (Equiv.Perm (Fin 1782))) := by
    rw [Sporadic.SuzOddCore.invE_eq_centM (by norm_num), Sporadic.SuzOddCore.centM, inf_comm]
  let κ : G →* Equiv.Perm (Fin 1782) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp (suzM.subtype.comp e.toMonoidHom)
  have hκ_apply : ∀ g, κ g = c⁻¹ * (e g : Equiv.Perm (Fin 1782)) * c := fun g => by
    simp [κ]
  have hκ : Function.Injective κ := by
    intro g h hgh
    rw [hκ_apply, hκ_apply] at hgh
    exact e.injective (Subtype.ext (mul_left_cancel (mul_right_cancel hgh)))
  have hκa : κ a = suzInv 1 := by
    rw [hκ_apply, hac]
    group
  have key : (centralizer ({a} : Set G)).map κ = invE 1 := by
    rw [hE]
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      refine ⟨?_, ?_⟩
      · rw [hκ_apply]
        exact suzM.mul_mem (suzM.mul_mem (suzM.inv_mem hc) (e g).2) hc
      · rw [← hκa, ← map_mul, ← map_mul, hg]
    · rintro ⟨hxM, hxc⟩
      set g : G := e.symm ⟨c * x * c⁻¹, suzM.mul_mem (suzM.mul_mem hc hxM) (suzM.inv_mem hc)⟩
        with hg
      have hκg : κ g = x := by
        rw [hκ_apply, hg, MulEquiv.apply_symm_apply]
        group
      refine ⟨g, ?_, hκg⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hκ
      rw [map_mul, map_mul, hκg, hκa]
      exact hxc
  exact ⟨((centralizer ({a} : Set G)).equivMapOfInjective κ hκ |>.trans
    (MulEquiv.subgroupCongr key)).symm⟩

theorem twoSuzCentralizerFacts_holds :
    TwoSuzCentralizerFacts := by
  intro Λ _ _ hperf hS hcard y hyy hy
  have := hperf
  obtain ⟨e⟩ := EvenSporadicStandard.Solomon78.suz_equiv_of_isSporadic hS
  let q : Λ →* suzM := e.toMonoidHom.comp (QuotientGroup.mk' (center Λ))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerq : q.ker = center Λ := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, q]
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  have hfin : Finite (center Λ) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hne : center Λ ≠ ⊥ := fun h => by
    rw [h] at hcard
    simp at hcard
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ht2 : orderOf (a : Λ) = 2 := by
    have hd : orderOf a ∣ 2 := hcard ▸ orderOf_dvd_natCard a
    have h1 : orderOf a ≠ 1 := fun h1 => ha (orderOf_eq_one_iff.1 h1)
    rw [Subgroup.orderOf_coe]
    exact ((Nat.dvd_prime Nat.prime_two).1 hd).resolve_left h1
  have hcenter : center Λ = zpowers (a : Λ) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 a.2) ?_
    rw [Nat.card_zpowers, ht2, hcard]
  have hker : q.ker = zpowers (a : Λ) := hkerq.trans hcenter
  have hqyy : q y * q y = 1 := by rw [← map_mul, hyy, map_one]
  have hqy1 : q y ≠ 1 := fun h => hy (hkerq ▸ MonoidHom.mem_ker.2 h)
  rcases EvenSporadicStandard.TwoSuz.sq_class_dichotomy q hqyy hqy1 with ⟨h, hh⟩ | ⟨c, hc, hqc⟩
  · exfalso
    have hsq := Sporadic.Recognition.SuzMultiplier.sq_eq_of_lift_conj_d
      Certificates.certificate15030 Certificates.certificate15031
      Certificates.certificate15032 Certificates.certificate15033
      Certificates.certificate15034 Certificates.certificate15035
      q hq ht2 hker hcenter.ge hh
    rw [sq, hyy] at hsq
    rw [← hsq, orderOf_one] at ht2
    omega
  · obtain ⟨f⟩ := nonempty_mulEquiv_invE_one e (a := (QuotientGroup.mk y : Λ ⧸ center Λ)) hc hqc
    have : Group.IsPerfect ↥(invE 1) :=
      Group.isPerfect_def.mpr AS81.SuzB0.invE_one_perfect
    exact ⟨Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective,
      HasSimpleQuotient3Quart.of_mulEquiv f hasSimpleQuotient3Quart_invE_one⟩

end

end CFSG.ComponentClassification.GrSLit.L34Sec5S
