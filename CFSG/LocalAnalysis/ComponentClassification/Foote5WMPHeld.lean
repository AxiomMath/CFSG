module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolIdent
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMFree
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem properFixed_of_badShape {z s : G} {D X : Subgroup G} (hz : orderOf z = 2)
    (hzs : z * s = s * z) (hX : IsTwoComponentIn X (centralizer ({s} : Set G)))
    (hD : IsTwoComponentIn D (centralizer ({z} : Set G) ⊓ centralizer ({s} : Set G)))
    (hDX : D ≤ X ⊔ conjugate X z) (hXz : conjugate X z = X) (hzX : z ∉ coreActionKernel X) :
    D ≤ X ⊓ centralizer ({z} : Set G) ∧
      IsPComponent 2 (D.subgroupOf (X ⊓ centralizer ({z} : Set G))) ∧
      (pPrimeCore 2 D).index < (pPrimeCore 2 X).index := by
  have hDX' : D ≤ X := by rw [hXz, sup_idem] at hDX; exact hDX
  have hDXz : D ≤ X ⊓ centralizer ({z} : Set G) := le_inf hDX' (hD.1.trans inf_le_left)
  have hXzC : X ⊓ centralizer ({z} : Set G) ≤
      centralizer ({z} : Set G) ⊓ centralizer ({s} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hX.1)
  have hDp : IsPComponent 2 (D.subgroupOf (X ⊓ centralizer ({z} : Set G))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hDXz hXzC hD.2
  refine ⟨hDXz, hDp, ?_⟩
  have hXX : (X ⊔ conjugate X z) ⊓ centralizer ({z} : Set G) =
      X ⊓ centralizer ({z} : Set G) := by
    rw [hXz, sup_idem]
  have hTK : D ≤ (X ⊔ conjugate X z) ⊓ centralizer ({z} : Set G) := by
    rw [hXX]
    exact hDXz
  have hTpc : IsPComponent 2 (D.subgroupOf ((X ⊔ conjugate X z) ⊓ centralizer ({z} : Set G))) := by
    rw [hXX]
    exact hDp
  obtain ⟨hle, -, heq⟩ := UGSChain.orbit_fixed_component_comparison hz hzs hX.1 hX.2 hTK hTpc
  refine lt_of_le_of_ne hle fun h => hzX ?_
  have hsup : D ⊔ oddCoreIn X = X := (heq h).2 hXz.symm
  have hzN : z ∈ normalizer (X : Set G) := by
    have h1 : X.map (MulAut.conj z⁻¹).toMonoidHom = X := hXz
    have h2 := inv_mem (mem_normalizer_iff_map_conj_eq.mpr h1)
    rwa [inv_inv] at h2
  exact FooteLit.mem_coreActionKernel_of_sup hDX' hsup hzN
    (Sol78.mem_coreActionKernel_of_commute fun d hd =>
      mem_centralizer_singleton_iff.mp ((hD.1.trans inf_le_left) hd))

theorem fusionZStar_equiv_of_mirrorStep_held (hHN : GrSLit.HeldNotProperFixedInput)
    (hK : Assembly.KProper Blueprint.Catalog G) (hZ : ∀ s : G, orderOf s = 2 → s ∉ center G)
    {Y X : Subgroup G} (h : MirrorStep Y X) (hY : GrSLit.IsHeldType (Y ⧸ Open.fusionZStar Y)) :
    Nonempty (Y ⧸ Open.fusionZStar Y ≃* X ⧸ Open.fusionZStar X) := by
  obtain ⟨z, s, D, hz, hs, hzs, hYz, hYs, hX, hD, hDY, hDX⟩ := h
  by_cases hfree : conjugate X z ≠ X ∨ z ∈ coreActionKernel X
  · exact mirror_fusionZStar_equiv_of_free hz hs hzs hYz hYs hX hD hDY hDX hfree
  · exfalso
    obtain ⟨hXz, hzX⟩ := not_or.mp hfree
    have hXz' : conjugate X z = X := not_not.mp hXz
    obtain ⟨hTM, hTpc, hlt⟩ := properFixed_of_badShape hz hzs hX hD hDX hXz' hzX
    have hstop : centralizer ({s} : Set G) ≠ ⊤ := fun htop => hZ s hs
      (mem_center_iff.mpr fun g => mem_centralizer_singleton_iff.mp (by rw [htop]; exact mem_top g))
    have hcat := GrSLit.catalog_fusionZStar_of_isPComponent hK hstop hX.1 hX.2
    obtain ⟨eDY⟩ := diagonal_fusionZStar_equiv hs hzs hYz hYs hD hDY
    exact GrSLit.properFixedComponents_notHeld hHN G z s X D hz hs hzs hX.1 hX.2 hXz' hTM hTpc
      hlt hcat (hY.map fun f => eDY.trans f)

theorem gsMirrorMaximal_of_held (hS : SchreierFor Blueprint.Catalog)
    (hHN : GrSLit.HeldNotProperFixedInput) [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog G) {J : Subgroup G}
    (hHe : GrSLit.IsHeldType (J ⧸ Open.fusionZStar J)) : GSMirrorMaximal J := by
  have hP := GrSLit.properFixedComponents_notHeld hHN
  have hZ : ∀ s : G, orderOf s = 2 → s ∉ center G := fun s hs =>
    GSLit.not_mem_center_of_orderOf_eq_two hnonab hs
  intro M hR
  induction hR with
  | refl => exact ⟨MulEquiv.refl _⟩
  | tail _ hst ih =>
    obtain ⟨e⟩ := ih
    have hHeY : GrSLit.IsHeldType _ := hHe.map fun f => e.symm.trans f
    rcases hst with ⟨c, d, hW⟩ | hM | ⟨g, rfl⟩
    · have hdZ := hZ d hW.2.1
      rcases GrSLit.gsWeakCorr_type_dichotomy hS hK hW hdZ with he | ⟨hMa, hTM, hTpc, hlt, ⟨eT⟩⟩
      · obtain ⟨e'⟩ := he
        exact ⟨e.trans e'⟩
      · exfalso
        obtain ⟨hc, hd, hcd, -, -, hMd, hMp, -⟩ := hW
        have hdtop : centralizer ({d} : Set G) ≠ ⊤ := fun htop => hdZ (mem_center_iff.mpr
          fun x => mem_centralizer_singleton_iff.mp (by rw [htop]; exact mem_top x))
        have hcat := GrSLit.catalog_fusionZStar_of_isPComponent hK hdtop hMd hMp
        exact hP G c d _ _ hc hd hcd hMd hMp hMa hTM hTpc hlt hcat
          (hHeY.map fun f => eT.symm.trans f)
    · obtain ⟨e'⟩ := fusionZStar_equiv_of_mirrorStep_held hHN hK hZ hM hHeY
      exact ⟨e.trans e'⟩
    · obtain ⟨e'⟩ := GrSLit.nonempty_fusionZStar_equiv_conjugate _ g
      exact ⟨e.trans e'⟩

theorem isSolomonMaximal_of_held (hS : SchreierFor Blueprint.Catalog)
    (hHN : GrSLit.HeldNotProperFixedInput) [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ u w : GeneralizedFitting.subgroup G, u * w ≠ w * u)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJ : IsTwoComponentIn J (centralizer ({a} : Set G)))
    (hHe : GrSLit.IsHeldType (J ⧸ Open.fusionZStar J)) : IsSolomonMaximal J :=
  isSolomonMaximal_of_gsMirrorMaximal hsF hnF ha hJ (gsMirrorMaximal_of_held hS hHN hnonab hK hHe)

end CFSG.ComponentClassification.Foote5.SolMax
