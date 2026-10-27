module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitQuotientChain

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G] (φ : G ≃* G)

theorem isTwoComponentAt_map_mulEquiv {a : G} {L : Subgroup G} (h : IsTwoComponentAt a L) :
    IsTwoComponentAt (φ a) (L.map φ.toMonoidHom) := by
  obtain ⟨ha, hLa, hLpc⟩ := h
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact ha, ?_, isPComponent_map_centralizer φ hLa hLpc⟩
  rw [← map_centralizer_singleton_mulEquiv φ a]
  exact map_mono hLa

omit [Finite G] in
theorem mem_coreActionKernel_map_mulEquiv {L : Subgroup G} {b : G}
    (hb : b ∈ coreActionKernel L) : φ b ∈ coreActionKernel (L.map φ.toMonoidHom) := by
  refine ⟨mem_normalizer_iff.mpr fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨x, rfl⟩ := φ.surjective y
    rw [show φ b * φ x * (φ b)⁻¹ = φ (b * x * b⁻¹) by simp only [map_mul, map_inv]]
    rw [mem_map_equiv, mem_map_equiv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact mem_normalizer_iff.mp hb.1 x
  · obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    have h1 := hb.2 x hx
    rw [← GSLit.map_map_pPrimeCore φ L]
    refine ⟨x⁻¹ * b⁻¹ * x * b, h1, ?_⟩
    change φ (x⁻¹ * b⁻¹ * x * b) = _
    simp only [map_mul, map_inv]
    rfl

theorem map_footeFixed_mulEquiv (L : Subgroup G) (b : G) :
    (footeFixed L b).map φ.toMonoidHom = footeFixed (L.map φ.toMonoidHom) (φ b) := by
  rw [footeFixed_eq_oddResidualIn, footeFixed_eq_oddResidualIn, map_oddResidualIn_hom,
    Subgroup.map_sup, map_inf_eq _ _ _ φ.injective, map_centralizer_singleton_mulEquiv,
    map_oddCoreOfCentralizer_mulEquiv]

theorem map_twoLayerOf_mulEquiv (b : G) :
    (twoLayerOf b).map φ.toMonoidHom = twoLayerOf (φ b) := by
  have hker : ¬ 2 ∣ Nat.card φ.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr φ.injective, card_bot]
    norm_num
  have h := GSThmB.OddQuot.map_layerIn φ.toMonoidHom hker (centralizer ({b} : Set G))
  rw [map_centralizer_singleton_mulEquiv] at h
  exact h

theorem footePointedStep_map_mulEquiv {a b : G} {L K : Subgroup G}
    (h : FootePointedStep a L b K) :
    FootePointedStep (φ a) (L.map φ.toMonoidHom) (φ b) (K.map φ.toMonoidHom) := by
  obtain ⟨hL, hK, hab, hne, hbL, hcl⟩ := h
  refine ⟨isTwoComponentAt_map_mulEquiv φ hL, isTwoComponentAt_map_mulEquiv φ hK,
    by rw [← map_mul, ← map_mul, hab], fun h => hne (φ.injective h),
    mem_coreActionKernel_map_mulEquiv φ hbL, ?_⟩
  rw [← map_footeFixed_mulEquiv, ← map_twoLayerOf_mulEquiv, ← map_conjClosure, hcl,
    Subgroup.map_sup, UnbalancedLayer.map_conjugate]
  rfl

theorem footePointedReach_map_mulEquiv {a b : G} {L K : Subgroup G}
    (h : FootePointedReach a L b K) :
    FootePointedReach (φ a) (L.map φ.toMonoidHom) (φ b) (K.map φ.toMonoidHom) := by
  unfold FootePointedReach at h ⊢
  generalize hp : ((a, L) : G × Subgroup G) = p at h
  generalize hq : ((b, K) : G × Subgroup G) = q at h
  induction h generalizing b K with
  | refl =>
    rw [← hq] at hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact Relation.ReflTransGen.refl
  | @tail r q' _ hstep ih =>
    rw [← hq] at hstep
    have h1 := ih (b := r.1) (K := r.2) rfl
    exact Relation.ReflTransGen.tail h1 (footePointedStep_map_mulEquiv φ hstep)

theorem FootePointedMaximal.map_mulEquiv {z : G} {A : Subgroup G}
    (h : FootePointedMaximal z A) : FootePointedMaximal (φ z) (A.map φ.toMonoidHom) := by
  refine ⟨isTwoComponentAt_map_mulEquiv φ h.1, fun b K hK => ?_⟩
  have h1 := footePointedReach_map_mulEquiv φ.symm hK
  have hA : (A.map φ.toMonoidHom).map φ.symm.toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A using 2
    ext x
    simp
  have hz : φ.symm (φ z) = z := φ.symm_apply_apply z
  rw [hA, hz] at h1
  obtain ⟨e⟩ := h.2 _ _ h1
  obtain ⟨e₁⟩ := nonempty_quotient_fusionZStar_equiv (A.equivMapOfInjective φ.toMonoidHom
    φ.injective)
  have hK : (K.map φ.symm.toMonoidHom).map φ.toMonoidHom = K := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id K using 2
    ext x
    simp
  obtain ⟨e₂⟩ := nonempty_quotient_fusionZStar_equiv ((K.map φ.symm.toMonoidHom).equivMapOfInjective
    φ.toMonoidHom φ.injective)
  rw [hK] at e₂
  exact ⟨e₁.symm.trans (e.trans e₂)⟩

theorem FootePointedMaximal.conjugate {z : G} {A : Subgroup G} (h : FootePointedMaximal z A)
    (g : G) : FootePointedMaximal (g⁻¹ * z * g) (conjugate A g) := by
  have h1 := h.map_mulEquiv (MulAut.conj g⁻¹)
  rw [MulAut.conj_apply, inv_inv] at h1
  exact h1

theorem conjugate_mem_footeFamilyOf {L A : Subgroup G} (hA : A ∈ footeFamilyOf L) (g : G) :
    conjugate A g ∈ footeFamilyOf L := by
  obtain ⟨⟨z, hz⟩, ⟨e⟩⟩ := hA
  refine ⟨⟨g⁻¹ * z * g, hz.conjugate g⟩, ?_⟩
  obtain ⟨e₁⟩ := nonempty_quotient_fusionZStar_equiv (A.equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)
  exact ⟨e₁.symm.trans e⟩

end CFSG.ComponentClassification.FooteLit
