module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLevi
public import CFSG.LieType.Chevalley.RightBruhatMultiplication
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le_derivedSeriesOf derivedSeriesOf)
open scoped commutatorElement

theorem commutator_le_of_forall_exists_inv_mul_mem {G : Type*} [Group G] {M H : Subgroup G}
    (S : Set G) (hSn : ∀ s ∈ S, ∀ m ∈ M, s * m * s⁻¹ ∈ M ∧ s⁻¹ * m * s ∈ M)
    (hSc : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ⁅s₁, s₂⁆ ∈ M) (hH : ∀ g ∈ H, ∃ s ∈ S, s⁻¹ * g ∈ M) :
    ⁅H, H⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨s₁, hs₁, hm₁⟩ := hH g₁ hg₁
  obtain ⟨s₂, hs₂, hm₂⟩ := hH g₂ hg₂
  set m₁ := s₁⁻¹ * g₁
  set m₂ := s₂⁻¹ * g₂
  have e₁ : g₁ = s₁ * m₁ := by simp [m₁]
  have e₂ : g₂ = s₂ * m₂ := by simp [m₂]
  have hm₁' := (hSn s₂ hs₂ m₁ hm₁).2
  have hm₂' := (hSn s₁ hs₁ m₂ hm₂).2
  have hμ : s₂⁻¹ * m₁ * s₂ * m₂ * m₁⁻¹ * (s₁⁻¹ * m₂ * s₁)⁻¹ ∈ M :=
    mul_mem (mul_mem (mul_mem hm₁' hm₂) (inv_mem hm₁)) (inv_mem hm₂')
  have hμ' := (hSn s₂ hs₂ _ (hSn s₁ hs₁ _ hμ).1).1
  have e : ⁅g₁, g₂⁆ = ⁅s₁, s₂⁆ *
      (s₂ * (s₁ * (s₂⁻¹ * m₁ * s₂ * m₂ * m₁⁻¹ * (s₁⁻¹ * m₂ * s₁)⁻¹) * s₁⁻¹) * s₂⁻¹) := by
    rw [e₁, e₂, commutatorElement_def, commutatorElement_def]
    group
  rw [e]
  exact mul_mem (hSc s₁ hs₁ s₂ hs₂) hμ'

theorem perfectCore_le_commutator_of_forall_exists_inv_mul_mem {G : Type*} [Group G]
    {M H : Subgroup G} (S : Set G) (hSn : ∀ s ∈ S, ∀ m ∈ M, s * m * s⁻¹ ∈ M ∧ s⁻¹ * m * s ∈ M)
    (hSc : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ⁅s₁, s₂⁆ ∈ M) (hH : ∀ g ∈ H, ∃ s ∈ S, s⁻¹ * g ∈ M) :
    perfectCore H ≤ ⁅M, M⁆ := by
  have h1 := commutator_le_of_forall_exists_inv_mul_mem S hSn hSc hH
  refine (perfectCore_le_derivedSeriesOf H 2).trans ?_
  change ⁅derivedSeriesOf H 1, derivedSeriesOf H 1⁆ ≤ ⁅M, M⁆
  exact Subgroup.commutator_mono h1 h1

section Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem smul_mem_parabolicRoots_of_forall
    (𝒜 : Set (Fin τ.rank → Kˣ)) (J : Set (Fin τ.rank))
    (hker : ∀ α ∈ F4Pilot.toralSetKernel 𝒜, 0 < height α → ∀ i ∉ J, α i = 0)
    (hJ1 : ∀ a ∈ 𝒜, ∀ j ∈ J, a j = 1) {w : WeylGroup τ}
    (hw : ∀ a ∈ 𝒜, w ∈ rootCharStabilizer a) {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicRoots τ J) : w • α ∈ parabolicRoots τ J := by
  have hroot : IsRoot τ (w • α) := IsRoot.smul hα.1 w
  have hkerα : ∀ a ∈ 𝒜, rootChar a (w • α) = 1 := fun a ha => by
    rw [hw a ha α]
    exact Finset.prod_eq_one fun i _ => by
      by_cases hi : i ∈ J
      · rw [hJ1 a ha i hi, one_zpow]
      · rw [hα.2 i hi, zpow_zero]
  refine ⟨hroot, fun i hi => ?_⟩
  rcases IsRoot.height_pos_or_neg hroot with h | h
  · exact hker _ ⟨hroot, hkerα⟩ h i hi
  · have hneg : -(w • α) ∈ F4Pilot.toralSetKernel 𝒜 := ⟨IsRoot.neg hroot, fun a ha => by
      rw [F4Pilot.rootChar_neg_eq_inv, hkerα a ha, inv_one]⟩
    have h' := hker _ hneg (by rw [height_neg]; omega) i hi
    rw [Pi.neg_apply, neg_eq_zero] at h'
    exact h'


theorem canonicalRep_conj_mem_parabolicLevi
    {J : Set (Fin τ.rank)}
    {w : WeylGroup τ} (hw : ∀ α ∈ parabolicRoots τ J, w • α ∈ parabolicRoots τ J)
    {m : ModGL τ K} (hm : m ∈ parabolicLevi τ K J) :
    canonicalRep (coxeterSystem τ) K w * m * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      parabolicLevi τ K J := by
  have hle : (parabolicLevi τ K J).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom ≤ parabolicLevi τ K J := by
    rw [parabolicLevi, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      exact Subgroup.mem_sup_left
        ((mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w) h).1 hh)
    · change (subsystemGroup τ K J).map _ ≤ _
      rw [subsystemGroup_eq_rootSpan, (canonical_weyl_root_transport τ K).1 w _ fun α hα => hα.1]
      refine (rootSpan_mono ?_).trans ((subsystemGroup_eq_rootSpan (K := K) J).symm.le.trans
        le_sup_right)
      rintro _ ⟨α, hα, rfl⟩
      exact hw α hα
  exact hle ⟨m, hm, rfl⟩


theorem perfectCore_le_rootSpan_of_forall_conj_eq_of_comm (𝒜 : Set (Fin τ.rank → Kˣ))
    (J : Set (Fin τ.rank))
    (hker : ∀ α ∈ F4Pilot.toralSetKernel 𝒜, 0 < height α → ∀ i ∉ J, α i = 0)
    (hJ1 : ∀ a ∈ 𝒜, ∀ j ∈ J, a j = 1)
    (hW : ∀ w₁ w₂ : WeylGroup τ, (∀ a ∈ 𝒜, w₁ ∈ rootCharStabilizer a) →
      (∀ a ∈ 𝒜, w₂ ∈ rootCharStabilizer a) →
        ∀ v : Fin τ.rank → ℤ, ∀ i ∉ J, ((w₁ * w₂ * w₁⁻¹ * w₂⁻¹) • v) i = v i)
    {H : Subgroup (ModGL τ K)}
    (hH : ∀ g ∈ H, g ∈ adjointGroup τ K ∧
      ∀ a ∈ 𝒜, rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g) :
    perfectCore H ≤ rootSpan τ K (F4Pilot.signedSimpleRoots J) := by
  set W𝒜 : Set (WeylGroup τ) := {w | ∀ a ∈ 𝒜, w ∈ rootCharStabilizer a} with hW𝒜
  have hinv : ∀ w ∈ W𝒜, w⁻¹ ∈ W𝒜 := fun w hw a ha =>
    (rootCharStabilizerSubgroup a).inv_mem (hw a ha)
  have hmaps : ∀ w ∈ W𝒜, ∀ α ∈ parabolicRoots τ J, w • α ∈ parabolicRoots τ J :=
    fun w hw α hα => smul_mem_parabolicRoots_of_forall 𝒜 J hker hJ1 hw hα
  set S : Set (ModGL τ K) := {s | ∃ w ∈ W𝒜, s = canonicalRep (coxeterSystem τ) K w} with hS
  have hSn : ∀ s ∈ S, ∀ m ∈ parabolicLevi τ K J,
      s * m * s⁻¹ ∈ parabolicLevi τ K J ∧ s⁻¹ * m * s ∈ parabolicLevi τ K J := by
    rintro _ ⟨w, hw, rfl⟩ m hm
    refine ⟨canonicalRep_conj_mem_parabolicLevi (hmaps w hw) hm, ?_⟩
    obtain ⟨k, hk, hkn⟩ := canonicalRep_inv_eq (K := K) w
    have h1 := canonicalRep_conj_mem_parabolicLevi (K := K) (hmaps _ (hinv w hw)) hm
    have hkM := torusGroup_le_parabolicLevi (K := K) J hk
    have e : (canonicalRep (coxeterSystem τ) K w)⁻¹ * m * canonicalRep (coxeterSystem τ) K w =
        k * (canonicalRep (coxeterSystem τ) K w⁻¹ * m *
          (canonicalRep (coxeterSystem τ) K w⁻¹)⁻¹) * k⁻¹ := by
      calc (canonicalRep (coxeterSystem τ) K w)⁻¹ * m * canonicalRep (coxeterSystem τ) K w =
          (canonicalRep (coxeterSystem τ) K w)⁻¹ * m *
            ((canonicalRep (coxeterSystem τ) K w)⁻¹)⁻¹ := by rw [inv_inv]
        _ = _ := by rw [hkn]; group
    rw [e]
    exact mul_mem (mul_mem hkM h1) (inv_mem hkM)
  have hSc : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ⁅s₁, s₂⁆ ∈ parabolicLevi τ K J := by
    rintro _ ⟨w₁, hw₁, rfl⟩ _ ⟨w₂, hw₂, rfl⟩
    obtain ⟨k₁, hk₁, h₁⟩ := canonicalRep_mul_mem (R := K) w₁ w₂
    obtain ⟨k₂, hk₂, h₂⟩ := canonicalRep_mul_mem (R := K) w₂ w₁
    obtain ⟨k₃, hk₃, h₃⟩ := canonicalRep_mul_mem (R := K) (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) (w₂ * w₁)
    have hc : w₁ * w₂ * w₁⁻¹ * w₂⁻¹ ∈ parabolicWeylGroup τ J := by
      rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer τ J).1]
      exact hW w₁ w₂ hw₁ hw₂
    have hnc := canonicalRep_mem_parabolicLevi (K := K) hc
    rw [show w₁ * w₂ * w₁⁻¹ * w₂⁻¹ * (w₂ * w₁) = w₁ * w₂ by group] at h₃
    have e₃ : canonicalRep (coxeterSystem τ) K (w₁ * w₂) =
        k₃⁻¹ * (canonicalRep (coxeterSystem τ) K (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) *
          canonicalRep (coxeterSystem τ) K (w₂ * w₁)) := by
      rw [h₃, inv_mul_cancel_left]
    have e : ⁅canonicalRep (coxeterSystem τ) K w₁, canonicalRep (coxeterSystem τ) K w₂⁆ =
        k₁ * k₃⁻¹ * canonicalRep (coxeterSystem τ) K (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) * k₂⁻¹ := by
      have e' : ∀ a b : ModGL τ K, a * b * a⁻¹ * b⁻¹ = (a * b) * (b * a)⁻¹ := fun a b => by
        group
      rw [commutatorElement_def, e', h₁, h₂, e₃]
      group
    rw [e]
    have hT := fun {k} (hk : k ∈ torusGroup τ K) => torusGroup_le_parabolicLevi (K := K) J hk
    exact mul_mem (mul_mem (mul_mem (hT hk₁) (inv_mem (hT hk₃))) hnc) (inv_mem (hT hk₂))
  have hsub : ∀ {T : Set (Fin τ.rank → ℤ)},
      T ⊆ F4Pilot.toralSetKernel 𝒜 ∩ {α | IsRoot τ α ∧ 0 < height α} →
        rootSpan τ K T ≤ parabolicLevi τ K J := fun {T} hT =>
    (rootSpan_mono (show T ⊆ parabolicPosRoots τ J from fun α hα =>
      ⟨⟨(hT hα).1.1, hker α (hT hα).1 (hT hα).2.2⟩, (hT hα).2⟩)).trans
        (parabolicLeviUnipotent_le_parabolicLevi J)
  have hHS : ∀ g ∈ H, ∃ s ∈ S, s⁻¹ * g ∈ parabolicLevi τ K J := by
    intro g hg
    obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ :=
      F4Pilot.exists_bruhat_factors_of_forall_conj_eq 𝒜 (hH g hg).1 (hH g hg).2
    refine ⟨canonicalRep (coxeterSystem τ) K w, ⟨w, hw, rfl⟩, ?_⟩
    have hhu : h * u ∈ parabolicLevi τ K J :=
      mul_mem (torusGroup_le_parabolicLevi J hh) (hsub le_rfl hu)
    have hvM : v ∈ parabolicLevi τ K J :=
      hsub (fun α hα => ⟨hα.1, hα.2.1, hα.2.2.1⟩) hv
    have h1 := (hSn _ ⟨w, hw, rfl⟩ _ hhu).2
    have e : (canonicalRep (coxeterSystem τ) K w)⁻¹ *
        (h * u * canonicalRep (coxeterSystem τ) K w * v) =
        (canonicalRep (coxeterSystem τ) K w)⁻¹ * (h * u) *
          canonicalRep (coxeterSystem τ) K w * v := by group
    rw [e]
    exact mul_mem h1 hvM
  exact (perfectCore_le_commutator_of_forall_exists_inv_mul_mem S hSn hSc hHS).trans
    (F4Pilot.commutator_parabolicLevi_le_rootSpan J)

end Chevalley

end CFSG.SeitzReduction.TwistedE6Pilot
