module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6LocalOut
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6ThreeCentral
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Order

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LocalTwo OuterFourInAux

namespace E6LocalAux

section Fix


theorem card_fixed_dvd_ordF4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 3)) {α : MulAut (twistedE6RootGroup K σ)}
    (hα2 : α ^ 2 = 1) (hαin : ∀ c, α ≠ MulAut.conj c) {H : Subgroup (twistedE6RootGroup K σ)}
    (hH : ∀ h ∈ H, α h = h) : Nat.card H ∣ ordF4 8 := by
  classical
  have hk : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card (f := 3) (by norm_num) hk hK
  letI : Algebra (GaloisField 2 3) K := ι.toAlgebra
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ 3 := hσ
  obtain ⟨ht, η, hη, -, -, hclass, -, -⟩ :=
    E6GraphFullCoset.twisted_full (f := 3) (by norm_num) K hK σ.toRingHom hσ'
  obtain ⟨-, hcan, e₂, -⟩ := even_E6_twisted_E6_canonical_graph_fixed_subgroup 3 (by norm_num)
    (GaloisField 2 3) K hk hK σ.toRingHom hσ'
  obtain ⟨ht', -, -, -, -, e₃, -, -, hSG⟩ := even_E6_twisted_E6_second_graph_fixed_subgroup 3
    (by norm_num) (GaloisField 2 3) K hk hK σ.toRingHom hσ'
  obtain ⟨η₀, hη₀, -, hJC, hfix, -⟩ := hcan
  obtain ⟨htJ, hJC', η₁, hη₁, -, -, -, hfixξ, -, -, -, -⟩ := hSG
  have hη₀eq : η₀ = η := MulEquiv.ext fun g => Subtype.ext (by rw [hη₀, hη])
  have hη₁eq : η₁ = η := MulEquiv.ext fun g => Subtype.ext (by rw [hη₁, hη])
  subst hη₀eq
  subst hη₁eq
  set J := (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (GaloisField 2 3) (RingHom.id _)).map
    (baseChangeGL (algebraMap (GaloisField 2 3) K)) with hJdef
  have hJcard : Nat.card J = ordF4 8 := by
    rw [Nat.card_congr e₂.toEquiv,
      CFSG.LieType.SeitzGeneration.ExcHighThree.card_adjointGroup_F4_eq, hk]
    norm_num
  have hkey : ∀ H' : Subgroup (twistedE6RootGroup K σ),
      (∀ g ∈ H', ((g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈ J) →
        Nat.card H' ∣ ordF4 8 := by
    intro H' hH'
    have hle : H' ≤ J.subgroupOf (twistedE6RootGroup K σ) := fun g hg =>
      Subgroup.mem_subgroupOf.2 (hH' g hg)
    refine (Subgroup.card_dvd_of_le hle).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv, hJcard]
  have hfixmap : ∀ (φ : MulAut (twistedE6RootGroup K σ)) (β : MulAut (twistedE6RootGroup K σ)),
      φ * α * φ⁻¹ = β → ∀ g ∈ H.map φ.toMonoidHom, β g = g := by
    rintro φ β hφ _ ⟨h, hh, rfl⟩
    rw [← hφ]
    change φ (α (φ.symm (φ h))) = φ h
    rw [MulEquiv.symm_apply_apply, hH h hh]
  have hcardmap : ∀ φ : MulAut (twistedE6RootGroup K σ),
      Nat.card (H.map φ.toMonoidHom) = Nat.card H := fun φ =>
    Subgroup.card_map_of_injective φ.injective
  rcases hclass α hα2 hαin with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · rw [← hcardmap φ]
    refine hkey _ fun g hg => (hfix g).1 (hfixmap φ _ hφ g hg)
  · rw [← hcardmap φ]
    refine hkey _ fun g hg => ?_
    have := hfixmap φ _ hφ g hg
    exact ((hfixξ g).1 this).1

theorem noOuterFixes_of_threeCentral {Q : Type} [Group Q] [Finite Q]
    (hQ : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group))
    {z : Q} (hz : IsThreeCentral Q z) :
    ∀ σ : MulAut Q, σ ^ 2 = 1 → σ ∉ innerAut Q → ∃ t : Q, z * t = t * z ∧ σ t ≠ t := by
  classical
  intro σ hσ2 hσi
  by_contra hcon
  push Not at hcon
  obtain ⟨-, P, hPz⟩ := hz
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, τ, hK, hτ, ⟨e⟩⟩ := exists_twE6_model hQ
  have hPfix : ∀ t ∈ (P : Subgroup Q), σ t = t := fun t ht =>
    hcon t (Subgroup.mem_centralizer_iff.1 (hPz ht) z (Set.mem_singleton z))
  have hα2 : MulAut.congr e σ ^ 2 = 1 := by rw [← map_pow, hσ2, map_one]
  have hαin : ∀ c, MulAut.congr e σ ≠ MulAut.conj c := by
    intro c hc
    apply hσi
    refine ⟨e.symm c, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj_apply, MulEquiv.apply_symm_apply]
    exact hc.symm
  have hHfix : ∀ h ∈ (P : Subgroup Q).map e.toMonoidHom, MulAut.congr e σ h = h := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : MulAut.congr e σ (e t) = e (σ t) := by simp [MulAut.congr_apply]
    change MulAut.congr e σ (e t) = e t
    rw [h1, hPfix t ht]
  have hdvd := card_fixed_dvd_ordF4 hK τ hτ hα2 hαin hHfix
  rw [Subgroup.card_map_of_injective e.injective] at hdvd
  have h3 : 3 ^ 11 ∣ Nat.card Q := by
    rw [card_eq_ordTwistedE6 hQ]
    norm_num [ordTwistedE6]
  have h5 := (P.pow_dvd_card_of_pow_dvd_card h3).trans hdvd
  norm_num [ordF4] at h5

end Fix

end E6LocalAux

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
