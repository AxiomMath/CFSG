module

public import CFSG.FeitThompson.Representations.ScalarAxisWeightsMinimumDegree
import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ScalarCoordinateSystem

open SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open NormalInduction (conjClassFun)

variable {p q : ℕ} [Fact p.Prime] {V U : Type*} [AddCommGroup V] [Module (ZMod p) V] [Group U]
  (S : ScalarCoordinateSystem p q V U) [Finite U]

theorem exists_mem_axisWeightFinset_of_apply_one_eq {a : ℕ}
    (hinf : ∀ i j : Fin q, i ≠ j → a < (S.lineCentralizer i ⊓ S.lineCentralizer j).index)
    {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hker : ¬ (S.base : Set S.grp) ⊆ charValueKernel θ) (hdeg : θ 1 = (a : ℂ)) :
    ∃ i, θ ∈ S.axisWeightFinset i := by
  classical
  have : Finite V := S.finite_of_finite_line
  obtain ⟨e, he, -, hres⟩ := exists_pos_resClassFun_eq_nsmul_sum (N := S.base) hθ
  set T := resConstituents S.base θ with hT
  have hval : ∀ x : S.base, θ (x : S.grp) = (e : ℂ) * ∑ lam ∈ T, lam x := by
    intro x
    have h := congrFun hres x
    rw [resClassFun_apply] at h
    rw [h]
    simp [Finset.sum_apply]
  have hone : ∀ lam ∈ T, lam (1 : S.base) = 1 := fun lam hl =>
    S.apply_one_eq_one_of_mem_Irr_base (resConstituents_subset_Irr (Finset.mem_coe.2 hl))
  have hdeg' : e * T.card = a := by
    have h := hval 1
    rw [Subgroup.coe_one, Finset.sum_congr rfl hone, hdeg] at h
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h.symm
  obtain ⟨lam, hlamT, x₀, hx₀⟩ : ∃ lam ∈ T, ∃ x : S.base, lam x ≠ 1 := by
    by_contra hprinc
    push Not at hprinc
    refine hker fun g hg => ?_
    have hconst : ∀ x : S.base, θ (x : S.grp) = (e : ℂ) * (T.card : ℂ) := by
      intro x
      rw [hval x, Finset.sum_congr rfl fun lam hl => hprinc lam hl x]
      simp
    rw [mem_charValueKernel]
    calc θ g = θ ((⟨g, hg⟩ : S.base) : S.grp) := rfl
      _ = (e : ℂ) * (T.card : ℂ) := hconst _
      _ = θ ((1 : S.base) : S.grp) := (hconst 1).symm
      _ = θ 1 := by rw [Subgroup.coe_one]
  have hlamIrr : lam ∈ Irr S.base := (mem_resConstituents.1 hlamT).1
  obtain ⟨χ, rfl⟩ := S.exists_baseChar_eq hlamIrr
  have hexne : ∃ y : Multiplicative V, χ y ≠ 1 := by
    refine ⟨S.baseEquiv.symm x₀, fun hcon => hx₀ ?_⟩
    have h := S.baseChar_apply χ (S.baseEquiv.symm x₀)
    rw [← S.baseEquiv_apply, MulEquiv.apply_symm_apply, hcon] at h
    simpa using h
  obtain ⟨i, v, hvline, hvne⟩ : ∃ i, ∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy⟩ := hexne
    exact hy (S.forall_apply_eq_one χ hall (Multiplicative.toAdd y))
  set I := inertiaGroup S.base (S.baseChar χ) with hI
  have hbaseI : S.base ≤ I := le_inertiaGroup S.base (Irr_subset_classFun hlamIrr)
  have hWle : ∀ k, ∀ w ∈ S.line k, χ (Multiplicative.ofAdd w) ≠ 1 →
      I.map (rightHom : S.grp →* U) ≤ S.lineCentralizer k := by
    intro k w hwline hwne
    rintro z ⟨g, hgI, rfl⟩
    have hinr : (inr (rightHom g) : S.grp) ∈ I := by
      have hg : (inl g.left : S.grp) * inr g.right = g := inl_left_mul_inr_right g
      have h1 : (inl g.left : S.grp) ∈ I := hbaseI (S.inl_mem_base _)
      have h2 : (inr g.right : S.grp) = (inl g.left)⁻¹ * g := eq_inv_mul_of_mul_eq hg
      rw [rightHom_eq_right, h2]
      exact I.mul_mem (I.inv_mem h1) hgI
    have hfix : conjClassFun S.base (inr (rightHom g)) (S.baseChar χ) = S.baseChar χ :=
      mem_inertiaGroup.1 hinr
    have hkey : χ (Multiplicative.ofAdd (S.act (rightHom g)⁻¹ w))
        = χ (Multiplicative.ofAdd w) := by
      refine Units.ext ?_
      have h := congrFun hfix (S.baseHom (Multiplicative.ofAdd w))
      rw [S.conjClassFun_inr_apply _ (rightHom g) (Multiplicative.ofAdd w),
        S.mulAutHom_apply, S.baseChar_apply, S.baseChar_apply] at h
      exact h
    have hinv : (rightHom g)⁻¹ ∈ S.lineCentralizer k :=
      S.mem_lineCentralizer_of_apply_eq χ hwline hwne hkey
    simpa using (S.lineCentralizer k).inv_mem hinv
  have hindex : (I.map (rightHom : S.grp →* U)).index = I.index := by
    refine Subgroup.index_map_eq I rightHom_surjective ?_
    rw [← range_inl_eq_ker_rightHom, ← S.base_eq_range_inl]
    exact hbaseI
  have hcard : I.index = T.card := by
    rw [Subgroup.index_eq_card, hI]
    exact natCard_quotient_inertiaGroup_eq_card hθ hlamT
  have hTpos : 0 < T.card := Finset.card_pos.2 ⟨_, hlamT⟩
  refine ⟨i, (S.mem_axisWeightFinset_iff_baseChar).2 ⟨hθ, χ, isAxisChar_of ⟨v, hvline, hvne⟩
    fun j hj w hw => ?_, hlamT⟩⟩
  by_contra hwne
  have hle : I.map (rightHom : S.grp →* U) ≤ S.lineCentralizer i ⊓ S.lineCentralizer j :=
    le_inf (hWle i v hvline hvne) (hWle j w hw hwne)
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hindex, hcard] at hdvd
  have h1 := Nat.le_of_dvd hTpos hdvd
  have h2 := hinf i j (Ne.symm hj)
  have h3 : T.card ≤ a := by
    rw [← hdeg']; exact Nat.le_mul_of_pos_left _ he
  omega

end ScalarCoordinateSystem

namespace ScalarAxis

open SemidirectProduct

universe u

variable {p q : ℕ} [Fact p.Prime] {V U B : Type u} [AddCommGroup V] [Module (ZMod p) V]
  [Group U] [Group B]

namespace AxisSystem

variable (S : AxisSystem p q V U B) [Finite U]

theorem indClassFun_pushChar_mem_Irr {θ : S.scalar.grp → ℂ} (hθ : θ ∈ S.axisIrr) :
    indClassFun S.core (S.pushChar θ) ∈ Irr S.amb := by
  obtain ⟨-, i, hi⟩ := (S.mem_axisIrr_iff).1 hθ
  exact indClassFun_mem_Irr_of_inertiaGroup_eq (S.pushChar_mem_Irr (S.axisIrr_subset_Irr hθ))
    (S.inertiaGroup_pushChar_eq_core hi)

theorem exists_axisIrr_transversal_covering :
    ∃ T : Finset (S.scalar.grp → ℂ), (∀ θ ∈ T, θ ∈ S.axisIrr) ∧
      (∀ θ ∈ T, ∀ ψ ∈ T, indClassFun S.core (S.pushChar θ)
        = indClassFun S.core (S.pushChar ψ) → θ = ψ) ∧
      (∀ θ ∈ S.axisIrr, ∃ ψ ∈ T, indClassFun S.core (S.pushChar ψ)
        = indClassFun S.core (S.pushChar θ)) ∧
      T.card * S.a ^ 2 = (p - 1) * (commutator U).index := by
  classical
  have hfin : S.axisFamily.Finite := S.axisFamily_finite
  have hcard : hfin.toFinset.card = Nat.card S.axisFamily := by
    rw [← Set.ncard_eq_toFinset_card S.axisFamily hfin]
    rfl
  have hchoice : ∀ f ∈ hfin.toFinset, ∃ θ, θ ∈ S.axisIrr ∧
      indClassFun S.core (S.pushChar θ) = f := fun f hf =>
    (S.mem_axisFamily).1 (hfin.mem_toFinset.1 hf)
  choose! g hg1 hg2 using hchoice
  refine ⟨hfin.toFinset.image g, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hθ
    exact hg1 f hf
  · intro θ hθ ψ hψ h
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hθ
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hψ
    rw [hg2 f hf, hg2 f' hf'] at h
    rw [h]
  · intro θ hθ
    have hf : indClassFun S.core (S.pushChar θ) ∈ hfin.toFinset :=
      hfin.mem_toFinset.2 (S.indClassFun_mem_axisFamily hθ)
    exact ⟨g _, Finset.mem_image_of_mem g hf, hg2 _ hf⟩
  · rw [Finset.card_image_of_injOn, hcard]
    · exact S.natCard_axisFamily_mul_sq
    · intro f hf f' hf' h
      rw [← hg2 f hf, ← hg2 f' hf', h]

theorem exists_axisIrr_transversal :
    ∃ T : Finset (S.scalar.grp → ℂ), (∀ θ ∈ T, θ ∈ S.axisIrr) ∧
      (∀ θ ∈ T, ∀ ψ ∈ T, indClassFun S.core (S.pushChar θ)
        = indClassFun S.core (S.pushChar ψ) → θ = ψ) ∧
      T.card * S.a ^ 2 = (p - 1) * (commutator U).index := by
  obtain ⟨T, h1, h2, -, h4⟩ := S.exists_axisIrr_transversal_covering
  exact ⟨T, h1, h2, h4⟩

theorem exists_apply_inl_ne_of_mem_axisIrr {θ : S.scalar.grp → ℂ} (hθ : θ ∈ S.axisIrr) :
    ∃ v : Multiplicative V, θ (inl v) ≠ θ 1 := by
  obtain ⟨y, hy, hyker⟩ := Set.not_subset.1 (S.not_subset_charValueKernel_of_mem_axisIrr hθ)
  have hy2 : y ∈ S.scalar.base := SetLike.mem_coe.1 hy
  refine ⟨S.scalar.baseEquiv.symm ⟨y, hy2⟩, fun h => hyker (mem_charValueKernel.2 ?_)⟩
  have hcoe : ((S.scalar.baseHom (S.scalar.baseEquiv.symm ⟨y, hy2⟩) : S.scalar.grp)) = y := by
    rw [← S.scalar.baseEquiv_apply, MulEquiv.apply_symm_apply]
  rw [← hcoe, S.scalar.coe_baseHom_apply, h]

section Transport

variable {M : Type u} [Group M] {Kbar : Subgroup M} (e : S.amb ≃* M)
  (hK : Subgroup.map (e : S.amb →* M) S.core = Kbar)

noncomputable def grpMulEquivOfIso : S.scalar.grp ≃* ↥Kbar :=
  S.coreMulEquiv.trans ((MulEquiv.subgroupMap e S.core).trans (MulEquiv.subgroupCongr hK))

@[simp] theorem coe_grpMulEquivOfIso_apply (x : S.scalar.grp) :
    ((S.grpMulEquivOfIso e hK x : ↥Kbar) : M) = e (inl x) := by
  change ((MulEquiv.subgroupCongr hK (MulEquiv.subgroupMap e S.core (S.coreMulEquiv x))) : M) = _
  rw [MulEquiv.subgroupCongr_apply]
  change e ((S.coreMulEquiv x : S.amb)) = _
  rw [S.coe_coreMulEquiv_apply]

theorem grpMulEquivOfIso_symm_eq {x : S.scalar.grp} {y : ↥Kbar} (h : (y : M) = e (inl x)) :
    (S.grpMulEquivOfIso e hK).symm y = x := by
  refine (MulEquiv.symm_apply_eq _).2 (Subtype.ext ?_).symm
  rw [h, S.coe_grpMulEquivOfIso_apply e hK]

omit [Finite U] in
include hK in
theorem mem_core_iff_mem_Kbar (z : S.amb) : z ∈ S.core ↔ e z ∈ Kbar := by
  refine ⟨fun hz => hK ▸ ⟨z, hz, rfl⟩, fun hz => ?_⟩
  rw [← hK] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  rwa [show z = w from e.injective hwz.symm]

noncomputable def transportChar (θ : S.scalar.grp → ℂ) : ↥Kbar → ℂ :=
  θ ∘ (S.grpMulEquivOfIso e hK).symm

theorem transportChar_apply (θ : S.scalar.grp → ℂ) {x : S.scalar.grp} {y : ↥Kbar}
    (h : (y : M) = e (inl x)) : S.transportChar e hK θ y = θ x := by
  rw [transportChar, Function.comp_apply, S.grpMulEquivOfIso_symm_eq e hK h]

omit [Finite U] in
@[simp] theorem transportChar_one (θ : S.scalar.grp → ℂ) : S.transportChar e hK θ 1 = θ 1 := by
  rw [transportChar, Function.comp_apply, map_one]

omit [Finite U] in
theorem transportChar_mem_Irr {θ : S.scalar.grp → ℂ} (hθ : θ ∈ Irr S.scalar.grp) :
    S.transportChar e hK θ ∈ Irr ↥Kbar :=
  FrobeniusInduction.mem_Irr_comp_mulEquiv hθ (S.grpMulEquivOfIso e hK).symm

omit [Finite U] in
theorem transportChar_injective : Function.Injective (S.transportChar e hK) := fun θ ψ h =>
  funext fun x => by
    have h2 := congrFun h (S.grpMulEquivOfIso e hK x)
    rwa [transportChar, transportChar, Function.comp_apply, Function.comp_apply,
      MulEquiv.symm_apply_apply] at h2

theorem indClassFun_transportChar_comp [Fintype M] (θ : S.scalar.grp → ℂ) :
    indClassFun Kbar (S.transportChar e hK θ) ∘ e = indClassFun S.core (S.pushChar θ) := by
  refine indClassFun_comp_mulEquiv e (S.mem_core_iff_mem_Kbar e hK) ?_
  intro x y hxy
  rw [S.transportChar_apply e hK θ (x := S.coreMulEquiv.symm x)
      (by rw [hxy]; congr 1; rw [← S.coe_coreMulEquiv_apply, MulEquiv.apply_symm_apply]),
    ← S.pushChar_apply θ (S.coreMulEquiv.symm x), MulEquiv.apply_symm_apply]

theorem indClassFun_transportChar_mem_Irr [Fintype M] {θ : S.scalar.grp → ℂ}
    (hθ : θ ∈ S.axisIrr) : indClassFun Kbar (S.transportChar e hK θ) ∈ Irr M := by
  have h := S.indClassFun_pushChar_mem_Irr hθ
  rw [← S.indClassFun_transportChar_comp e hK θ] at h
  have h2 := FrobeniusInduction.mem_Irr_comp_mulEquiv h e.symm
  rwa [show (indClassFun Kbar (S.transportChar e hK θ) ∘ e) ∘ e.symm
    = indClassFun Kbar (S.transportChar e hK θ) from funext fun _ => by simp] at h2

end Transport

end AxisSystem

end ScalarAxis

end CFSG.FeitThompson
