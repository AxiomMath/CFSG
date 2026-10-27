module

public import CFSG.CGT.Timmesfeld75.JLemma
public import CFSG.CGT.Timmesfeld75.Sec4CaseIKernel
public import CFSG.CGT.Timmesfeld75.Sec4Two

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement

@[expose] def Sec4I4RootGroupInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K] (Tb : Subgroup K), Lemma26Hyp K Tb →
    ∀ (Yb : Subgroup K) (c₁ c₂ : K), Yb = Tb ⊔ conjSubgroup c₁ Tb ⊔ conjSubgroup c₂ Tb →
      ∀ f : ℕ, 2 ≤ f → (∃ ρ : ↥Yb →* PSU3Model f, Function.Surjective ρ) → Yb = ⊤

section Ker

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_normIn_of_mem_ker_jMap {T R A B : Subgroup G} (hT : IsWC T) (hTR : T ≤ R)
    {g₁ g₂ : G} (hg₁ : g₁ ∈ R) (hg₂ : g₂ ∈ R) (hA : A = conjSubgroup g₁ T)
    (hB : B = conjSubgroup g₂ T) {w : ↥R} (hw : w ∈ (jMap ↥R).ker) {c : G} (hc : c ∈ A) :
    ⁅(w : G), c⁆ ∈ normIn A B := by
  subst hA hB
  have hwA := conjSubgroup_coe_eq_of_mem_ker_jMap hTR hT hw hg₁
  have hAR : conjSubgroup g₁ T ≤ R := conjSubgroup_le_of_le_of_mem hTR hg₁
  have h1 : (w : G) * c * (w : G)⁻¹ ∈ conjSubgroup g₁ T := by
    have := conj_mem_conjSubgroup (w : G) hc
    rwa [hwA] at this
  have h2 : ⁅(w : G), c⁆ ∈ conjSubgroup g₁ T := by
    have e : ⁅(w : G), c⁆ = ((w : G) * c * (w : G)⁻¹) * c⁻¹ := by
      rw [commutatorElement_def]
    rw [e]
    exact (conjSubgroup g₁ T).mul_mem h1 ((conjSubgroup g₁ T).inv_mem hc)
  have h3 : (⁅w, ⟨c, hAR hc⟩⁆ : ↥R) ∈ CFSG.pCore 2 ↥R := mem_ker_jMap.1 hw ⟨c, hAR hc⟩
  exact mem_normIn.2 ⟨h2, coe_mem_normalizer_conjSubgroup_of_mem_pCore hT hTR hg₂ h3⟩

variable {T T₁ T₂ : Subgroup G} {a : G}

theorem mk_mem_center_of_actsTriv
    [((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)).Normal] {y : ↥(sec4Y T T₁ T₂)}
    (hy : Sec4ActsTriv T T₁ T₂ (y : G)) :
    (QuotientGroup.mk y : ↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ∈
      Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) := by
  refine Subgroup.mem_center_iff.2 fun g => ?_
  induction g using QuotientGroup.induction_on with
  | H y' =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.2 ?_
    have h1 : ⁅(y : G)⁻¹, (y' : G)⁻¹⁆ ∈ sec4N T T₁ T₂ :=
      (sec4Ker T T₁ T₂).inv_mem hy _ ((sec4Y T T₁ T₂).inv_mem y'.2)
    have e : (((y' * y)⁻¹ * (y * y') : ↥(sec4Y T T₁ T₂)) : G) = ⁅(y : G)⁻¹, (y' : G)⁻¹⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h1

theorem Sec4Hyp.exists_surjective_psu3_range
    (hAsc : AschbacherNoPolarInput)
    (h : Sec4Hyp T T₁ a T₂) (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) {K : Type} [Group K]
    (ψ : ↥(sec4Y T T₁ T₂) →* K)
    (hψ : ∀ y : ↥(sec4Y T T₁ T₂), ψ y = 1 → Sec4ActsTriv T T₁ T₂ (y : G)) :
    ∃ f : ℕ, 2 ≤ f ∧ ∃ ρ : ↥ψ.range →* PSU3Model f, Function.Surjective ρ := by
  obtain ⟨f, hf, -, hN, ⟨e⟩⟩ :=
    h.sec4_two_of_le hAsc hq le_rfl h.sec4Y_le_normalizer h.normalClosure_sec4Y
  have := hN
  let θ : ↥(sec4Y T T₁ T₂) →* PSU3Model f := e.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center (↥(sec4Y T T₁ T₂) ⧸
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))).comp
      (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))))
  have hθ : Function.Surjective θ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.rangeRestrict.ker ≤ θ.ker := by
    intro y hy
    have hψ1 : ψ y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
    refine MonoidHom.mem_ker.2 ?_
    show e (QuotientGroup.mk' _ (QuotientGroup.mk' _ y)) = 1
    rw [MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff _).2 (mk_mem_center_of_actsTriv (hψ y hψ1))
  refine ⟨f, hf, MonoidHom.liftOfSurjective ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
    ⟨θ, hker⟩, fun z => ?_⟩
  obtain ⟨y, rfl⟩ := hθ z
  exact ⟨ψ.rangeRestrict y, by simp⟩

end Ker

end CFSG.CGT.Timmesfeld75
