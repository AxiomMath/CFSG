module

import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.MinimalNormal
import CFSG.Assembly.OrderReductions.FixedPointLifting
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Walter86

open Subgroup
open scoped commutatorElement

section ChiefFactor

variable {X : Type} [Group X] [Finite X]

theorem exists_irreducible_chiefFactor_of_commutator_ne_bot {U Y : Subgroup X} [hUn : U.Normal]
    [hYn : Y.Normal] (hUodd : Odd (Nat.card U)) (hYperf : ⁅Y, Y⁆ = Y) (hne : ⁅U, Y⁆ ≠ ⊥) :
    ∃ (p : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (_ : Finite V)
        (ρ : Representation (ZMod p) X V),
        ρ.IsIrreducible ∧ (∃ g ∈ Y, ∃ v : V, ρ g v ≠ v) ∧
        (∀ g ∈ ⁅U, Y⁆, ∀ v : V, ρ g v = v) ∧
        ∀ t : X, t ^ 2 = 1 → ∀ v : V, ρ t v = v →
          ∃ u ∈ U, t * u = u * t ∧ ∀ g : X, g * u = u * g → ρ g v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set (Subgroup X) := {R | R.Normal ∧ R ≤ U ∧ ¬ ⁅U, Y⁆ ≤ R} with hSdef
  have hbot : (⊥ : Subgroup X) ∈ S := ⟨inferInstance, bot_le, fun h => hne (le_bot_iff.mp h)⟩
  obtain ⟨R, ⟨hRn, hRU, hRc⟩, hRmax⟩ := (Set.toFinite S).exists_maximal ⟨⊥, hbot⟩
  have := hRn
  set π := QuotientGroup.mk' R with hπ
  have hCU : ⁅U, Y⁆ ≤ U := Subgroup.commutator_le_left U Y
  set W := (⁅U, Y⁆).map π with hW
  have hWn : W.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective R)
  have hWne : W ≠ ⊥ := by
    rw [Ne, hW, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hRc
  have hWmin : ∀ N : Subgroup (X ⧸ R), N.Normal → N ≤ W → N = ⊥ ∨ N = W := by
    intro N hN hNW
    by_cases hc : ⁅U, Y⁆ ≤ N.comap π
    · exact Or.inr (le_antisymm hNW (Subgroup.map_le_iff_le_comap.mpr hc))
    · left
      have hMU : N.comap π ≤ U := by
        have h1 : N.comap π ≤ W.comap π := Subgroup.comap_mono hNW
        rw [hW, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
        exact h1.trans (sup_le hCU hRU)
      have hRM : R ≤ N.comap π := by
        intro r hr
        have h1 : π r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
        rw [Subgroup.mem_comap, h1]
        exact one_mem N
      have hle := hRmax ⟨hN.comap π, hMU, hc⟩ hRM
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R q
      exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff g).mpr (hle hq))
  have hWodd : Odd (Nat.card W) :=
    hUodd.of_dvd_nat ((Subgroup.card_map_dvd ⁅U, Y⁆ π).trans (Subgroup.card_dvd_of_le hCU))
  have : Group.IsSolvable W := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hWodd
  obtain ⟨p, hp, hWcomm, hWexp⟩ :=
    CFSG.EvenSporadicStandard.HNRecog.GH73.minimal_normal_elementary_of_solvable W hWne hWmin
  have hpf : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hWne
    have hw2 : w ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hWexp _ w.2)
    have hdvd : 2 ∣ Nat.card W := orderOf_eq_prime hw2 hw1 ▸ orderOf_dvd_natCard w
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr hdvd)
  let : CommGroup W :=
    { (inferInstance : Group W) with mul_comm := fun a b => Subtype.ext (hWcomm a a.2 b b.2) }
  have hexpV : ∀ v : Additive W, p • v = 0 := by
    intro v
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hWexp _ (Additive.toMul v).2)
  let hmod : Module (ZMod p) (Additive W) := AddCommGroup.zmodModule (n := p) hexpV
  let θ : X →* MulAut W := MulAut.conjNormal.comp π
  let f : X → (Additive W →ₗ[ZMod p] Additive W) := fun g =>
    AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive (θ g).toMonoidHom)
  have hf : ∀ g v, Additive.toMul (f g v) = θ g (Additive.toMul v) := fun _ _ => rfl
  let ρ : Representation (ZMod p) X (Additive W) :=
    { toFun := f
      map_one' := LinearMap.ext fun v => Additive.toMul.injective (by
        rw [hf, map_one]; rfl)
      map_mul' := fun g h => LinearMap.ext fun v => Additive.toMul.injective (by
        rw [hf, Module.End.mul_apply, hf, hf, map_mul]; rfl) }
  have hρ : ∀ (g : X) (v : Additive W), ρ g v = Additive.ofMul (θ g (Additive.toMul v)) :=
    fun _ _ => rfl
  have hθ : ∀ (g : X) (w : W), ((θ g w : W) : X ⧸ R) = π g * w * (π g)⁻¹ := fun _ _ => rfl
  have hfix : ∀ (g : X) (v : Additive W),
      ρ g v = v ↔ π g * ((Additive.toMul v : W) : X ⧸ R) * (π g)⁻¹ =
        ((Additive.toMul v : W) : X ⧸ R) := by
    intro g v
    rw [hρ, ← hθ]
    constructor
    · intro h
      exact congrArg (fun w => ((Additive.toMul w : W) : X ⧸ R)) h
    · intro h
      exact Additive.toMul.injective (Subtype.ext h)
  have hirr : ρ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
      obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hWne
      have hmem : Additive.ofMul w ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
      rw [← h] at hmem
      have h0 : Additive.ofMul w = 0 := (Submodule.mem_bot _).mp hmem
      exact hw1 (Additive.ofMul.injective h0)
    refine { toNontrivial := hnt, eq_bot_or_eq_top := fun σ => ?_ }
    let N : Subgroup (X ⧸ R) :=
      { carrier := {q | ∃ h : q ∈ W, Additive.ofMul (⟨q, h⟩ : W) ∈ σ.toSubmodule}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨W.mul_mem ha hb, ?_⟩
          have h := σ.toSubmodule.add_mem ha' hb'
          rw [← ofMul_mul] at h
          exact h
        one_mem' := ⟨W.one_mem, σ.toSubmodule.zero_mem⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          exact ⟨W.inv_mem ha, σ.toSubmodule.neg_mem ha'⟩ }
    have hNn : N.Normal := ⟨fun q ⟨hq, hq'⟩ g' => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R g'
      exact ⟨hWn.conj_mem q hq _, σ.apply_mem_toSubmodule g hq'⟩⟩
    rcases hWmin N hNn (fun q ⟨hq, _⟩ => hq) with hN | hN
    · left
      apply Subrepresentation.toSubmodule_injective
      show σ.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro v hv
      have hvN : ((Additive.toMul v : W) : X ⧸ R) ∈ N := ⟨(Additive.toMul v).2, hv⟩
      rw [hN] at hvN
      have h1 : Additive.toMul v = 1 := Subtype.ext ((Subgroup.mem_bot).mp hvN)
      rw [Submodule.mem_bot, ← ofMul_toMul v, h1, ofMul_one]
    · right
      apply Subrepresentation.toSubmodule_injective
      show σ.toSubmodule = ⊤
      rw [eq_top_iff]
      intro v _
      have hvN : ((Additive.toMul v : W) : X ⧸ R) ∈ N := by
        rw [hN]
        exact (Additive.toMul v).2
      obtain ⟨_, h⟩ := hvN
      exact h
  have hYact : ∃ g ∈ Y, ∃ v : Additive W, ρ g v ≠ v := by
    by_contra hcon
    push Not at hcon
    have h1 : ⁅⁅U, Y⁆, Y⁆ ≤ R := by
      rw [Subgroup.commutator_le]
      intro c hc g hg
      have hcw : π c ∈ W := Subgroup.mem_map_of_mem π hc
      have h2 := (hfix g (Additive.ofMul ⟨π c, hcw⟩)).mp (hcon g hg _)
      have h3 : π c * π g = π g * π c := by
        change π g * π c * (π g)⁻¹ = π c at h2
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2.symm
      apply (QuotientGroup.eq_one_iff _).mp
      change π ⁅c, g⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h3
    have h3 : ⁅⁅U.map π, Y.map π⁆, Y.map π⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk']
      exact h1
    have h4 : ⁅⁅Y.map π, Y.map π⁆, U.map π⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate
        (by rw [Subgroup.commutator_comm (Y.map π) (U.map π)]; exact h3) h3
    have h5 : ⁅Y.map π, Y.map π⁆ = Y.map π := by rw [← Subgroup.map_commutator, hYperf]
    rw [h5, Subgroup.commutator_comm, ← Subgroup.map_commutator] at h4
    exact hWne h4
  have htriv : ∀ g ∈ ⁅U, Y⁆, ∀ v : Additive W, ρ g v = v := by
    intro g hg v
    rw [hfix]
    have hgw : π g ∈ W := Subgroup.mem_map_of_mem π hg
    rw [hWcomm (π g) hgw _ (Additive.toMul v).2, mul_inv_cancel_right]
  have hlift : ∀ t : X, t ^ 2 = 1 → ∀ v : Additive W, ρ t v = v →
      ∃ u ∈ U, t * u = u * t ∧ ∀ g : X, g * u = u * g → ρ g v = v := by
    intro t ht v hv
    have hUπ : (U.map π).Normal :=
      Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective R)
    have hWU : W ≤ U.map π := Subgroup.map_mono hCU
    let fU : ↥U →* ↥(U.map π) := π.subgroupMap U
    have hfs : Function.Surjective fU := π.subgroupMap_surjective U
    have hker : Odd (Nat.card fU.ker) :=
      hUodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card fU.ker)
    have hinv : Function.Involutive (MulAut.conjNormal t : MulAut ↥U) := by
      intro u
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
      have ht' : t * t = 1 := by rw [← pow_two, ht]
      rw [inv_eq_of_mul_eq_one_right ht']
      calc t * (t * (u : X) * t) * t = (t * t) * u * (t * t) := by simp only [mul_assoc]
        _ = u := by rw [ht', one_mul, mul_one]
    have hequiv : ∀ u : ↥U, fU (MulAut.conjNormal t u) = MulAut.conjNormal (π t) (fU u) := by
      intro u
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      change π ((MulAut.conjNormal t u : ↥U) : X) = _
      rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]
      rfl
    have hpt : ((Additive.toMul v : W) : X ⧸ R) ∈ U.map π := hWU (Additive.toMul v).2
    have hptfix : MulAut.conjNormal (π t) (⟨_, hpt⟩ : ↥(U.map π)) = ⟨_, hpt⟩ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact (hfix t v).mp hv
    obtain ⟨e, he, hefix⟩ := CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel
      (MulAut.conjNormal t) (MulAut.conjNormal (π t)) hinv fU hfs hker hequiv _ hptfix
    have he' : π (e : X) = ((Additive.toMul v : W) : X ⧸ R) := congrArg Subtype.val he
    have hefix' : t * (e : X) * t⁻¹ = e := by
      have := congrArg Subtype.val hefix
      rwa [MulAut.conjNormal_apply] at this
    refine ⟨e, e.2, ?_, fun g hg => ?_⟩
    · rw [mul_inv_eq_iff_eq_mul] at hefix'
      exact hefix'
    · rw [hfix, ← he', ← map_mul, ← map_inv, ← map_mul, hg, mul_inv_cancel_right]
  exact ⟨p, hpf, hp2, Additive W, inferInstance, hmod, inferInstance, ρ, hirr, hYact, htriv, hlift⟩

end ChiefFactor

end CFSG.ComponentClassification.Walter86
