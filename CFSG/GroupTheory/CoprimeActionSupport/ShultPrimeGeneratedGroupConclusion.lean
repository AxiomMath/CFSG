module

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ext
meta import Lean.Elab.Tactic.NormCast
public import CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeGeneratedPGroupSpecial
public import CFSG.GroupTheory.CoprimeActionSupport.PrimeCyclicNormalizerIrreducibleRestriction
public import CFSG.LargeExtraspecial.RepresentationSupport.FaithfulIrreducibleSpecialGroupExtraspecial
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialIrreducibleDegreePower
public import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
public import CFSG.LargeExtraspecial.RepresentationSupport.ShultPrimeExtraspecialFixedFree
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
import all CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow

public section


namespace CFSG.GroupTheory.CoprimeActionSupport.ShultPrimeGeneratedGroupConclusion


open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

open CFSG.LargeExtraspecial.RepresentationSupport

open scoped commutatorElement


private lemma conj_mem {H : Type*} [Group H] (D E : Subgroup H) (hDE : ⁅D, E⁆ = E)
    {d : H} (hd : d ∈ D) {x : H} (hx : x ∈ E) : d * x * d⁻¹ ∈ E := by
  have h : ⁅d, x⁆ ∈ ⁅D, E⁆ := Subgroup.commutator_mem_commutator hd hx
  rw [hDE] at h
  have : d * x * d⁻¹ = ⁅d, x⁆ * x := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact E.mul_mem h hx


private def conjAut {H : Type*} [Group H] (D E : Subgroup H) (hDE : ⁅D, E⁆ = E)
    (d : H) (hd : d ∈ D) : MulAut E where
  toFun x := ⟨d * x * d⁻¹, conj_mem D E hDE hd x.2⟩
  invFun x := ⟨d⁻¹ * x * d, by
    simpa using conj_mem D E hDE (D.inv_mem hd) x.2⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]


private lemma conjAut_apply {H : Type*} [Group H] (D E : Subgroup H) (hDE : ⁅D, E⁆ = E)
    (d : H) (hd : d ∈ D) (x : E) : ((conjAut D E hDE d hd x : E) : H) = d * x * d⁻¹ := rfl


private lemma conjAut_pow {H : Type*} [Group H] (D E : Subgroup H) (hDE : ⁅D, E⁆ = E)
    (d : H) (hd : d ∈ D) (n : ℕ) (x : E) :
    (((conjAut D E hDE d hd) ^ n) x : H) = d ^ n * x * (d ^ n)⁻¹ := by
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, conjAut_apply]
    simp [pow_succ, mul_assoc]



private lemma stable_all {F : Type*} [Field F] {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module F W] (τ : Representation F H W)
    (S : Submodule F W) (E D : Subgroup H) (hsup : E ⊔ D = ⊤)
    (hE : ∀ e ∈ E, ∀ w ∈ S, τ e w ∈ S) (hD : ∀ d ∈ D, ∀ w ∈ S, τ d w ∈ S) (h : H) :
    ∀ w ∈ S, τ h w ∈ S := by
  let T : Subgroup H :=
    { carrier := {h | ∀ w ∈ S, τ h w ∈ S}
      mul_mem' := fun {a b} ha hb w hw => by
        have := ha _ (hb w hw)
        simpa [map_mul] using this
      one_mem' := fun w hw => by simpa using hw
      inv_mem' := fun {a} ha w hw => by
        have hpos : 0 < orderOf a := orderOf_pos a
        have hpow : ∀ n : ℕ, ∀ w ∈ S, τ (a ^ n) w ∈ S := by
          intro n
          induction n with
          | zero => intro w hw; simpa using hw
          | succ k ih => intro w hw; rw [pow_succ, map_mul]; exact ih _ (ha w hw)
        have : a⁻¹ = a ^ (orderOf a - 1) := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_succ']
          rw [Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        rw [this]
        exact hpow _ w hw }
  have hle : E ⊔ D ≤ T := sup_le (fun e he w hw => hE e he w hw) (fun d hd w hw => hD d hd w hw)
  rw [hsup] at hle
  exact hle (Subgroup.mem_top h)


theorem conclusion {F : Type*} [Field F] [IsAlgClosed F]
    {H : Type} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Nontrivial W]
    (τ : Representation F H W) (hfaith : Function.Injective τ) (hirr : τ.IsIrreducible)
    {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hr2 : r ≠ 2) (hqr : q ≠ r)
    (D E : Subgroup H) (hE1 : E ≠ ⊥) (hEq : IsPGroup q E) (hD : Nat.card D = r)
    (hDE : ⁅D, E⁆ = E) (hsup : E ⊔ D = ⊤)
    (hCV : (⨅ d ∈ D, LinearMap.ker (τ d - LinearMap.id)) = (⊥ : Submodule F W))
    (hqF : (q : F) ≠ 0) (hrF : (r : F) ≠ 0) (hHF : (Nat.card H : F) ≠ 0) :
    q = 2 ∧ ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hEF : (Nat.card E : F) ≠ 0 := by
    intro h0
    apply hHF
    obtain ⟨k, hk⟩ := Subgroup.card_subgroup_dvd_card E
    rw [hk]; push_cast; rw [h0, zero_mul]
  let σ : Representation F E W := τ.comp E.subtype
  have hτf : Function.Injective σ := hfaith.comp E.subtype_injective
  obtain ⟨hspec, hcent⟩ := FixedFreePrimeGeneratedPGroupSpecial.special_and_center τ hfaith hq hr
    hqr D hD hCV E hE1 hEq hEF hrF hDE
  have hnc := FixedFreePrimeGeneratedPGroupSpecial.nonabelian τ hfaith hq hr
    hqr D hD hCV E hE1 hEq hEF hrF hDE
  haveI : IsCyclic D := isCyclic_of_prime_card hD
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
  have hgord : orderOf g = r := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hD]
  set d : H := (g : H) with hd_def
  have hdD : d ∈ D := g.2
  have hdr : d ^ r = 1 := by
    have : (g : H) ^ r = 1 := by
      rw [← Subgroup.coe_pow, ← hgord, pow_orderOf_eq_one]; rfl
    exact this
  have hdpow : ∀ x ∈ D, ∃ n : ℕ, d ^ n = x := by
    intro x hx
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).mpr (hg ⟨x, hx⟩)
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  let α : MulAut E := conjAut D E hDE d hdD
  have hα : α ^ r = 1 := by
    ext x
    rw [conjAut_pow]
    simp [hdr]
  let T : W ≃ₗ[F] W := LinearEquiv.ofLinear (τ d) (τ d⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
  have hTapply : ∀ w, T w = τ d w := fun w => rfl
  have hTpow : ∀ (n : ℕ) w, (T ^ n) w = τ (d ^ n) w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ k ih => intro w; rw [pow_succ, LinearEquiv.mul_apply, ih, hTapply, pow_succ, map_mul]; rfl
  have hT : T ^ r = 1 := by
    ext w
    rw [hTpow, hdr]; simp
  have hker : LinearMap.ker ((T : W →ₗ[F] W) - LinearMap.id) = ⊥ := by
    rw [eq_bot_iff, ← hCV]
    intro v hv
    simp only [Submodule.mem_iInf]
    intro x hx
    obtain ⟨n, rfl⟩ := hdpow x hx
    have h1 : τ d v = v := by
      have := LinearMap.mem_ker.mp hv
      simpa [sub_eq_zero, hTapply] using this
    have : ∀ n : ℕ, τ (d ^ n) v = v := by
      intro n
      induction n with
      | zero => simp
      | succ k ih => rw [pow_succ, map_mul, Module.End.mul_apply, h1, ih]
    simpa [sub_eq_zero] using this n
  have hcov : ∀ e : E, (T : W →ₗ[F] W) * σ e =
      σ (α e) * (T : W →ₗ[F] W) := by
    intro e
    show τ d * τ e = τ (α e) * τ d
    rw [← map_mul, ← map_mul]
    congr 1
    rw [conjAut_apply]
    simp [mul_assoc]
  have hjoint : ∀ S : Submodule F W, (∀ e : E, S ≤ S.comap (σ e)) →
      S ≤ S.comap (T : W →ₗ[F] W) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hST
    have hall := stable_all τ S E D hsup (fun e he w hw => hS ⟨e, he⟩ hw) (by
      intro x hx w hw
      obtain ⟨n, rfl⟩ := hdpow x hx
      rw [← hTpow]
      have : ∀ n : ℕ, ∀ w ∈ S, (T ^ n) w ∈ S := by
        intro n
        induction n with
        | zero => intro w hw; simpa using hw
        | succ k ih => intro w hw; rw [pow_succ, LinearEquiv.mul_apply]; exact ih _ (hST hw)
      exact this n w hw)
    let S' : Subrepresentation τ := ⟨S, fun g v hv => hall g v hv⟩
    rcases hirr.eq_bot_or_eq_top S' with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  have hirrE : σ.IsIrreducible :=
    PrimeCyclicNormalizerIrreducibleRestriction.restriction_irreducible σ hr hrF
      hEF T hT hker α hα hcov hjoint
  have hZC : Subgroup.center E = commutator E :=
    Subgroup.map_injective E.subtype_injective hspec.1
  have hZF : Subgroup.center E = frattini E :=
    Subgroup.map_injective E.subtype_injective hspec.2
  have hext : CFSG.IsExtraspecialPGroup q E :=
    FaithfulIrreducibleSpecialGroupExtraspecial.extraspecial hq hEq hnc hZC hZF
      σ hτf hirrE
  obtain ⟨m, hm, -, hcard⟩ := ExtraspecialIrreducibleDegreePower.exists_degree hq hext
    σ hτf hirrE
  have hfixiff : ∀ y : E, α y = y ↔ y ∈ Subgroup.center E := by
    intro y
    constructor
    · intro hy
      have h1 : d * (y : H) * d⁻¹ = y := by
        have := congrArg Subtype.val hy
        rwa [conjAut_apply] at this
      have h2 : (y : H) ∈ Subgroup.centralizer (D : Set H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        obtain ⟨n, rfl⟩ := hdpow x hx
        have hc : Commute d (y : H) := by
          exact mul_inv_eq_iff_eq_mul.mp h1
        exact (hc.pow_left n).eq
      have h3 : (y : H) ∈ E ⊓ Subgroup.centralizer (D : Set H) := ⟨y.2, h2⟩
      rw [← hcent] at h3
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp h3
      have : z = y := Subtype.ext hzy
      rw [← this]; exact hz
    · intro hy
      have h1 : (y : H) ∈ E ⊓ Subgroup.centralizer (D : Set H) := by
        rw [← hcent]; exact ⟨y, hy, rfl⟩
      have h2 := Subgroup.mem_centralizer_iff.mp h1.2 d hdD
      apply Subtype.ext
      rw [conjAut_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact h2
  have hαZ : ∀ z : Subgroup.center E, α (z : E) = z := fun z => (hfixiff z).mpr z.2
  have hrZ : ¬ r ∣ Nat.card (Subgroup.center E) := by
    rw [hext.2.2.2]
    intro h
    exact hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp h).symm
  have hfix : ∀ x : E ⧸ Subgroup.center E, quotientHom E α x = x ↔ x = 1 := fun x =>
    CoprimeAutomorphismFixedQuotientLift.center_quotient_fixed_iff α hα hrZ hfixiff x
  exact ShultPrimeExtraspecialFixedFree.conclusion hq hqF hext hm hcard hr hr2
    (Ne.symm hqr) hrF σ hτf hirrE α hα hαZ hfix T hT hker hcov


end CFSG.GroupTheory.CoprimeActionSupport.ShultPrimeGeneratedGroupConclusion
