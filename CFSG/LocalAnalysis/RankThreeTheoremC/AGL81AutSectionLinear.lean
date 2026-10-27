module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionDefs
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.GroupTheory.PGroup.FrattiniQuotientRankBound

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.OrderReductions.FrattiniAutomorphisms
open scoped IsMulCommutative commutatorElement

theorem hasSmallLinearModel {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {V : Type} [Group V] [Finite V]
    (hV : IsPGroup q V) (hr : CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3) :
    HasSmallLinearModel q V := by
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  rcases subsingleton_or_nontrivial V with hV1 | hV1
  ·
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, ?_, 1, fun x _ => ⟨0, ?_⟩⟩
    · exact Module.finrank_zero_of_subsingleton.trans_le (Nat.zero_le 4)
    · ext v
      exact Subsingleton.elim _ _
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hV
  haveI := hDchar
  have hDq : IsPGroup q D := hV.to_subgroup D
  obtain ⟨-, -, -, hEA, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDq
  obtain ⟨-, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hDq
  set Q := D ⧸ frattini D with hQ
  haveI : IsMulCommutative Q := hEA.toIsMulCommutative
  letI : AddCommGroup (Additive Q) := Additive.addCommGroup
  letI : Module (ZMod q) (Additive Q) := IsElementaryAbelian.isVectorSpace q
  haveI : Finite (Additive Q) := inferInstanceAs (Finite Q)
  haveI : Module.Finite (ZMod q) (Additive Q) := Module.Finite.of_finite
  let lin : MulAut Q →* Module.End (ZMod q) (Additive Q) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap q
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  let ρ : MulAut V →* (Module.End (ZMod q) (Additive Q))ˣ :=
    (lin.comp ((quotientAutomorphism (frattini D)).comp (MulAut.characteristic D))).toHomUnits
  refine ⟨Additive Q, inferInstance, inferInstance, inferInstance, ?_, ρ, ?_⟩
  ·
    have hexp : ∀ x : D, x ^ q = 1 := fun x => Subtype.ext (hDexp x x.2)
    have hcl : ⁅⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆, (⊤ : Subgroup D)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_centralizer_iff]
      intro c _
      have hab : ⁅(a : V), (b : V)⁆ ∈ D ⊓ Subgroup.centralizer (D : Set V) :=
        hDcomm (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top _))
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hab.2 c c.2
      simpa only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] using this
    have hrD : CFSG.Open.pRank q (⊤ : Subgroup D) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact (CFSG.SectionRank.pRank_mono hq1 le_top).trans hr
    have hcard : Nat.card Q ≤ q ^ 4 :=
      CFSG.GroupTheory.card_quotient_frattini_le_pow_four hDq hexp hcl hrD
    have hfin : Nat.card (Additive Q) = q ^ Module.finrank (ZMod q) (Additive Q) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
    have h4 : q ^ Module.finrank (ZMod q) (Additive Q) ≤ q ^ 4 := hfin ▸ hcard
    exact (Nat.pow_le_pow_iff_right hq1).1 h4
  ·
    intro x hx
    have h1 : quotientAutomorphism (frattini D) (MulAut.characteristic D x) = 1 := by
      ext y
      exact congrArg (fun u : (Module.End (ZMod q) (Additive Q))ˣ =>
        (u : Module.End (ZMod q) (Additive Q)) (Additive.ofMul y)) hx
    obtain ⟨k, hk⟩ := hker ⟨MulAut.characteristic D x, MonoidHom.mem_ker.mpr h1⟩
    have h2 : MulAut.characteristic D (x ^ q ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h3 : x ^ q ^ k ∈ fixingSubgroup (MulAut V) (D : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      exact congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : V)) h2
    obtain ⟨j, hj⟩ := hDfix ⟨_, h3⟩
    refine ⟨k + j, ?_⟩
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val hj

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
