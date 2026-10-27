module

public import CFSG.LieType.AlgebraicGroups.E7AdjointTangentFixed
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient

import CFSG.LieType.AlgebraicGroups.AdTangentRootConj
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped CFSG.ConvolutionPoints


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} [Fact p.Prime] [CharP L p]

theorem e7_exists_good_root (hp2 : p ≠ 2) (a : Fin Tag.E7.rank → Lˣ)
    (hasign : ∀ i, a i = 1 ∨ a i = -1) (ha : rootDiagUnit Tag.E7 a ∈ adjointGroup Tag.E7 L)
    {n : ModGL Tag.E7 L} (hnG : n ∈ adjointGroup Tag.E7 L) (hn : n ∈ monomialSubgroup Tag.E7 L)
    (hn2 : n ^ 2 = 1) (hna : rootDiagUnit Tag.E7 a * n = n * rootDiagUnit Tag.E7 a) :
    ∃ α, IsRoot Tag.E7 α ∧ rootChar a α = 1 ∧
      ¬ (weylQuotientHom Tag.E7 L ⟨n, hn⟩ • α = α ∧
        ∀ c : L, n * pinnedX Tag.E7 L α c * n⁻¹ = pinnedX Tag.E7 L α (-c)) := by
  classical
  by_contra hcon
  have hbad : ∀ α, IsRoot Tag.E7 α → rootChar a α = 1 →
      weylQuotientHom Tag.E7 L ⟨n, hn⟩ • α = α ∧
        ∀ c : L, n * pinnedX Tag.E7 L α c * n⁻¹ = pinnedX Tag.E7 L α (-c) := by
    intro α hα hχ
    by_contra h'
    exact hcon ⟨α, hα, hχ, h'⟩
  have h2 : (2 : L) ≠ 0 := by
    refine Ring.two_ne_zero ?_
    rw [ringChar.eq L p]
    exact hp2
  let da : ModGL Tag.E7 L := rootDiagUnit Tag.E7 a
  let M := adjointPointSubgroup Tag.E7 L
  let φ := (modGLPoint Tag.E7 L).toMonoidHom
  let hdaM : φ da ∈ M :=
    Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom ha
  let hnM : φ n ∈ M :=
    Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hnG
  have ha2 : a ^ 2 = 1 := by
    funext i
    rcases hasign i with h | h <;> simp [Pi.pow_apply, h, pow_two]
  have hda2 : da ^ 2 = 1 := by
    change rootDiagUnit Tag.E7 a ^ 2 = 1
    rw [rootDiagUnit_pow, ha2, rootDiagUnit_one]
  have hcomm : Commute da n := by
    change da * n = n * da
    exact hna
  have h28 : 28 ≤ Module.finrank L (adFixedTangent (adjointPointSubgroup Tag.E7 L)
      {φ da, φ n}) := by
    have h := e7_adFixedTangent_pair_finrank_ge (L := L) (p := p) hp2 ha hnG hda2 hn2 hcomm
    simpa only [M, φ] using h
  let F : Submodule L (TangentSpace L (realizedCoord Tag.E7 L)
      (Bialgebra.counitAlgHom L (realizedCoord Tag.E7 L))) :=
    adFixedTangent M {φ da, φ n}
  have h28F : 28 ≤ Module.finrank L F := by
    change 28 ≤ Module.finrank L (adFixedTangent M {φ da, φ n})
    exact h28
  have hF_eq : F = LinearMap.ker (adTangent M hdaM - 1) ⊓
      LinearMap.ker (adTangent M hnM - 1) :=
    adFixedTangent_pair_eq M hdaM hnM
  let e := rootModuleTangentEquiv (L := L) h2
  let W : Submodule L (RootModule Tag.E7 L) := F.comap e.toLinearMap
  have hWfin : Module.finrank L W = Module.finrank L F := by
    have hWmap : W = Submodule.map e.symm.toLinearMap F :=
      Submodule.comap_equiv_eq_map_symm e F
    rw [hWmap]
    exact LinearEquiv.finrank_map_eq e.symm F
  let S : Set (Label Tag.E7) :=
    {b | ∃ α : {α : Fin Tag.E7.rank → ℤ // IsRoot Tag.E7 α},
      b = Sum.inr α ∧ rootChar a α.1 = 1}
  let p : W →ₗ[L] (Fin Tag.E7.rank → L) :=
    LinearMap.pi fun i =>
      (Finsupp.lapply (Sum.inl i) : (Label Tag.E7 →₀ L) →ₗ[L] L).comp W.subtype
  have hp_apply : ∀ (w : W) (i : Fin Tag.E7.rank), p w i = w.1 (Sum.inl i) := by
    intro w i
    rw [LinearMap.pi_apply, LinearMap.comp_apply, Finsupp.lapply_apply]
    rfl
  have hker_bot : LinearMap.ker p = ⊥ := by
    refine (Submodule.eq_bot_iff (LinearMap.ker p)).2 ?_
    intro w hw
    have hw0 : p w = 0 := LinearMap.mem_ker.1 hw
    have hw_inl : ∀ i, w.1 (Sum.inl i) = 0 := by
      intro i
      simpa [hp_apply w i] using congrFun hw0 i
    have hWmem : e w.1 ∈ F := w.2
    have hWmem' := hWmem
    rw [hF_eq] at hWmem'
    have hW1 : adTangent M hdaM (e w.1) = e w.1 := by
      have h := LinearMap.mem_ker.1 hWmem'.1
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    have hW2 : adTangent M hnM (e w.1) = e w.1 := by
      have h := LinearMap.mem_ker.1 hWmem'.2
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    have hAdda : adTangent M hdaM (e w.1) = e (rootDiag a w.1) :=
      adTangent_rootDiagUnit_rootModuleTangentEquiv h2 ha w.1
    have hw_ker : rootDiag a w.1 = w.1 := by
      refine e.injective ?_
      rw [← hAdda, hW1]
    have hsupp : (w.1.support : Set (Label Tag.E7)) ⊆ S := by
      intro b hb
      have hbne : w.1 b ≠ 0 := Finsupp.mem_support_iff.1 hb
      have hχ : rootChar a (labelWt Tag.E7 b) = 1 := by
        have hcoord := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.rootDiag_coord
          (τ := Tag.E7) (K := L) a w.1 b
        have h1 : ((rootChar a (labelWt Tag.E7 b) : Lˣ) : L) * w.1 b = w.1 b := by
          rw [← hcoord, hw_ker]
        exact Units.ext (mul_right_cancel₀ hbne (by simpa using h1))
      rcases b with i | ⟨α, hα⟩
      · exact absurd (hw_inl i) hbne
      · exact ⟨⟨α, hα⟩, rfl, by simpa [labelWt] using hχ⟩
    have hwU : w.1 ∈ Finsupp.supported L L S := (Finsupp.mem_supported L w.1).2 hsupp
    let nEnd : Module.End L (RootModule Tag.E7 L) :=
      e.symm.toLinearMap.comp ((adTangent M hnM).comp e.toLinearMap)
    have hgen : ∀ b ∈ S, nEnd (Finsupp.single b 1) = - Finsupp.single b 1 := by
      rintro b ⟨α, hb, hχ⟩
      subst hb
      have hX : adTangent M hnM (rootTangent Tag.E7 L α.1) =
          - rootTangent Tag.E7 L α.1 := by
        change adTangent (adjointPointSubgroup Tag.E7 L)
          (Subgroup.mem_map_of_mem (modGLPoint Tag.E7 L).toMonoidHom hnG)
          (rootTangent Tag.E7 L α.1) = - rootTangent Tag.E7 L α.1
        have h := adTangent_rootTangent_of_conj_pinnedX (τ := Tag.E7) (L := L) (g := n)
          hnG (α := α.1) (β := α.1) (μ := -1) (fun c => ?_)
        · simpa using h
        · simpa using (hbad α.1 α.2 hχ).2 c
      have he : e (Finsupp.single (Sum.inr α) 1) = rootTangent Tag.E7 L α.1 := by
        change rootModuleTangentEquiv h2 (Finsupp.single (Sum.inr α) 1) = _
        exact rootModuleTangentEquiv_single_inr h2 α
      change e.symm (adTangent M hnM (e (Finsupp.single (Sum.inr α) 1))) =
        - Finsupp.single (Sum.inr α) 1
      rw [he, hX, map_neg, ← he, e.symm_apply_apply]
    have hUle : Finsupp.supported L L S ≤ LinearMap.ker (nEnd + 1) := by
      rw [Finsupp.supported_eq_span_single]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      change (nEnd + 1) (Finsupp.single b 1) = 0
      rw [LinearMap.add_apply, Module.End.one_apply, hgen b hb, neg_add_cancel]
    have hnEnd_w : nEnd w.1 = - w.1 := by
      have h0 := hUle hwU
      rw [LinearMap.mem_ker] at h0
      change nEnd w.1 + w.1 = 0 at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hnEnd_w2 : nEnd w.1 = w.1 := by
      change e.symm (adTangent M hnM (e w.1)) = w.1
      rw [hW2]
      exact e.symm_apply_apply w.1
    have hneg : w.1 = - w.1 := by
      rw [← hnEnd_w, hnEnd_w2]
    have h2w : (2 : L) • w.1 = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hneg]
      exact add_neg_cancel w.1
    have hzero : w.1 = 0 := by
      rcases smul_eq_zero.1 h2w with h | h
      · exact absurd h h2
      · exact h
    exact Subtype.ext hzero
  have hp_ker0 : ∀ m, p m = 0 → m = 0 := by
    intro m hm
    exact (Submodule.eq_bot_iff (LinearMap.ker p)).1 hker_bot m (LinearMap.mem_ker.2 hm)
  have hp_inj : Function.Injective p := by
    intro a b h
    have h0 : p (a - b) = 0 := by rw [p.map_sub a b, h, sub_self]
    exact sub_eq_zero.mp (hp_ker0 (a - b) h0)
  have hcodim : Module.finrank L (Fin Tag.E7.rank → L) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rfl
  have hleW : Module.finrank L W ≤ 7 := by
    rw [← hcodim]
    exact LinearMap.finrank_le_finrank_of_injective hp_inj
  have hleF : Module.finrank L F ≤ 7 := by
    rw [← hWfin]
    exact hleW
  omega

end CFSG.LieType.AlgebraicGroups
