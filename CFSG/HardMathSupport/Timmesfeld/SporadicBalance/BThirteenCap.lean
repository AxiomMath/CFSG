module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteenGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Defs
public import CFSG.Monster.Existence.StdOdd.Reduce
public import CFSG.Monster.Existence.StdOdd.Cert.Cent13
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.B.TwoA.Amalgam
  CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68

theorem card_centralizer_le_of_cover13 {E T : Type*} [Group E] [Finite E] [Group T] [Finite T]
    {K Z : Subgroup E} [Z.Normal] (hK : K.index = 2) (hZ : Nat.card Z = 2)
    (e : K ⧸ Z.subgroupOf K ≃* T)
    (hT : ∀ y : T, orderOf y = 13 → Nat.card (centralizer ({y} : Set T)) ≤ 13) {y : E}
    (hy : orderOf y = 13) : Nat.card (centralizer ({y} : Set E)) ≤ 52 := by
  have hyK : y ∈ K := mem_of_odd_orderOf_of_index_eq_two hK (by rw [hy]; decide)
  let y₀ : K := ⟨y, hyK⟩
  have hy₀ : orderOf y₀ = 13 := by rw [← hy]; exact Subgroup.orderOf_mk _ _
  let π : K →* T := e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf K))
  have hπ : ∀ g : K, π g = 1 → (g : E) ∈ Z := by
    intro g hg
    have : QuotientGroup.mk' (Z.subgroupOf K) g = 1 := (MulEquiv.map_eq_one_iff e).1 hg
    exact (QuotientGroup.eq_one_iff g).1 this
  have hπy : orderOf (π y₀) = 13 := by
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    refine orderOf_eq_prime (p := 13) ?_ ?_
    · rw [← map_pow, ← hy₀, pow_orderOf_eq_one, map_one]
    · intro h1
      have hz : y ∈ Z := hπ y₀ h1
      have hz2 : y ^ 2 = 1 := by
        have := pow_card_eq_one' (x := (⟨y, hz⟩ : Z))
        rw [hZ] at this
        exact congrArg Subtype.val this
      have := orderOf_dvd_of_pow_eq_one hz2
      rw [hy] at this
      omega
  let ψ : centralizer ({y₀} : Set K) →* T := π.comp (centralizer ({y₀} : Set K)).subtype
  have hrange : ψ.range ≤ centralizer ({π y₀} : Set T) := by
    rintro _ ⟨c, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hc : (c : K) * y₀ = y₀ * c := mem_centralizer_singleton_iff.1 c.2
    show π c * π y₀ = π y₀ * π c
    rw [← map_mul, ← map_mul, hc]
  have hker : Nat.card ψ.ker ≤ 2 := by
    let j : ψ.ker → Z := fun c => ⟨((c.1 : K) : E), hπ c.1 c.2⟩
    have hj : Function.Injective j := by
      intro a b h
      have := congrArg (fun z : Z => (z : E)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    calc Nat.card ψ.ker ≤ Nat.card Z := Nat.card_le_card_of_injective j hj
      _ = 2 := hZ
  have hCK : Nat.card (centralizer ({y₀} : Set K)) ≤ 26 := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    have h2 : Nat.card ψ.range ≤ 13 :=
      (Subgroup.card_le_of_le hrange).trans (hT _ hπy)
    rw [← h1]
    calc Nat.card ψ.ker * Nat.card ψ.range ≤ 2 * 13 := Nat.mul_le_mul hker h2
      _ = 26 := by norm_num
  have hKC : Nat.card (K ⊓ centralizer ({y} : Set E) : Subgroup E) ≤ 26 := by
    let m : (K ⊓ centralizer ({y} : Set E) : Subgroup E) → centralizer ({y₀} : Set K) :=
      fun g => ⟨⟨g.1, g.2.1⟩,
        mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 g.2.2))⟩
    have hm : Function.Injective m := by
      intro a b h
      have := congrArg (fun z : centralizer ({y₀} : Set K) => ((z : K) : E)) h
      exact Subtype.ext this
    exact (Nat.card_le_card_of_injective m hm).trans hCK
  have hrel : K.relIndex (centralizer ({y} : Set E)) ∣ 2 := by
    have : K.Normal := Subgroup.normal_of_index_eq_two hK
    exact hK ▸ Subgroup.relIndex_dvd_index_of_normal K (centralizer ({y} : Set E))
  have hrel' := Subgroup.relIndex_mul_card (H := K) (K := centralizer ({y} : Set E))
  have hle : K.relIndex (centralizer ({y} : Set E)) ≤ 2 := Nat.le_of_dvd (by norm_num) hrel
  rw [← hrel']
  calc K.relIndex (centralizer ({y} : Set E)) *
        Nat.card (K ⊓ centralizer ({y} : Set E) : Subgroup E) ≤ 2 * 26 :=
      Nat.mul_le_mul hle hKC
    _ = 52 := by norm_num

theorem arith13_baby : Arith13 babyCentOrder babyOrbitSize where
  nsq := by norm_num [babyCentOrder]
  dvd0 := by norm_num [babyOrbitSize]
  dvd3 := by norm_num [babyOrbitSize]


theorem cap13_baby : Cap13 (G := B) babyCentOrder := by
  intro u x hu hx hux
  have hfin : Finite B := CFSG.Monster.B.Pinned.finite_B
  have h3 : Nat.card ↥(centralizer ({babyRep 3} : Set B)) ≠ babyCentOrder 0 := by
    have h3' : Nat.card ↥(centralizer ({babyRep 3} : Set B)) = babyCentOrder 2 :=
      natCard_centralizer_rep_three
    rw [h3']
    decide
  obtain ⟨ψ⟩ := StdOdd.nonempty_centralizer_mulEquiv_Eam_of_babyInv_zero h3
    (show BabyInv 0 u from hu)
  have hxC : x ∈ centralizer ({u} : Set B) := (mem_centralizer_singleton_iff (G := B)).2 hux.symm
  let x' : ↥(centralizer ({u} : Set B)) := ⟨x, hxC⟩
  have hx' : orderOf x' = 13 := by
    rw [← hx]
    exact Subgroup.orderOf_mk _ _
  have hfinE : Finite ↥Eam := Finite.of_equiv _ ψ.toEquiv
  have hy : orderOf (ψ x') = 13 := by
    rw [MulEquiv.orderOf_eq]
    exact hx'
  obtain ⟨hidx, -, -, -, hZ2, ⟨e⟩, -⟩ := short_F4_derived_standard_perfect_cover
  have hfinS : Finite ↥stdGroup := StdOdd.Cert.rgrp_finite
  have hp2 : ¬ 13 ^ 2 ∣ Nat.card ↥stdGroup := by
    rw [card_stdGroup]
    norm_num
  have hT : ∀ y : ↥stdGroup, orderOf y = 13 →
      Nat.card (centralizer ({y} : Set ↥stdGroup)) ≤ 13 := by
    intro y hy13
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    rw [StdOdd.Cert.card_centralizer_eq_of_sylow_prime hp2 StdOdd.Cert.orderOf_rep13 hy13,
      StdOdd.Cert.card_centralizer_rep13]
  have hE := card_centralizer_le_of_cover13 hidx hZ2 e hT hy
  exact (card_inf_centralizer_le_of_mulEquiv (G := B) hxC ψ).trans hE

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen
