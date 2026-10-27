module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.ExtraspecialHyperplaneGeometry
public import CFSG.LinearAlgebra.CoprimeActions.HyperplaneDecompositionOnCommSpace
public import CFSG.GroupTheory.CoprimeActionSupport.IndependentFamilyRemoveZero

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

namespace ExtraspecialModuleDecomposition

open Subgroup ExtraspecialHyperplaneGeometry

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem fixedSpace_inf_commSpace_eq_bot [Finite G] (ρ : Representation (ZMod 2) G V)
    (Z : Subgroup G) (hodd : Odd (Nat.card Z)) :
    commSpace ρ Z ⊓ fixedSpace ρ Z = ⊥ := by
  classical
  haveI : Fintype Z := Fintype.ofFinite _
  have hc : ((Fintype.card Z : ℕ) : ZMod 2) = 1 := by
    rw [Fintype.card_eq_nat_card]; exact ZMod.natCast_eq_one_iff_odd.2 hodd
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  have h1 := normOp_of_mem_fixedSpace ρ Z hv.2
  have h2 := normOp_commSpace ρ Z hv.1
  rw [hc, one_smul, h2] at h1
  exact (Submodule.mem_bot _).2 h1.symm

theorem iSupIndep_and_iSup_eq [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (ρ : Representation (ZMod 2) G V)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    iSupIndep (fun Y : conjClass H X => commSpace ρ (centerIn H) ⊓ fixedSpace ρ (Y : Subgroup G)) ∧
      (⨆ Y : conjClass H X, commSpace ρ (centerIn H) ⊓ fixedSpace ρ (Y : Subgroup G)) =
        commSpace ρ (centerIn H) := by
  classical
  haveI := Fact.mk hp
  have hZcard : Nat.card (centerIn H) = p := by
    unfold centerIn
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hH.2.2.2
  have hodd : Odd (Nat.card (centerIn H)) := by
    rw [hZcard]; exact hp.odd_of_ne_two hp2
  have hc : ∀ k ∈ X ⊔ centerIn H, ∀ z ∈ centerIn H, k * z = z * k := by
    intro k hk z hz
    have hz' : z ∈ H ∧ ∀ h ∈ H, h * z = z * h := by
      obtain ⟨c, hc, rfl⟩ := hz
      refine ⟨c.2, fun h hh => ?_⟩
      have := Subgroup.mem_center_iff.mp hc ⟨h, hh⟩
      simpa using congrArg Subtype.val this
    have hkH : k ∈ H := (sup_le hXH (by rintro w ⟨c, -, rfl⟩; exact c.2)) hk
    exact hz'.2 k hkH
  obtain ⟨hind, hsup⟩ := CFSG.LinearAlgebra.CoprimeActions.HyperplaneDecompositionOnCommSpace.decomposition
    (hp.odd_of_ne_two hp2) ρ (X ⊔ centerIn H) (centerIn H)
    (k_elementary hp hp2 H hH hexp X hXH hXp hXZ) le_sup_right hc hodd
  have heq := hyperplanes_eq hp hp2 H hH hexp X hXH hXp hXZ
  rw [heq, Set.singleton_union] at hind hsup
  have hnm := center_notMem_conjClass hp hp2 H hH hexp X hXH hXp hXZ
  have hfz : commSpace ρ (centerIn H) ⊓ fixedSpace ρ (centerIn H) = ⊥ := by
    exact fixedSpace_inf_commSpace_eq_bot ρ _ hodd
  obtain ⟨h1, h2⟩ := CFSG.GroupTheory.CoprimeActionSupport.IndependentFamilyRemoveZero.remove_zero
    (fun Y : Subgroup G => commSpace ρ (centerIn H) ⊓ fixedSpace ρ Y) (conjClass H X)
    (centerIn H) hnm hind hfz
  exact ⟨h1, h2.trans hsup⟩

theorem isInternal_on_U [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (ρ : Representation (ZMod 2) G V)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    open scoped Classical in
    DirectSum.IsInternal (fun Y : conjClass H X =>
      (commSpace ρ (centerIn H) ⊓ fixedSpace ρ (Y : Subgroup G)).comap
        (commSpace ρ (centerIn H)).subtype) := by
  classical
  obtain ⟨hind, hsup⟩ := iSupIndep_and_iSup_eq hp hp2 H hH hexp ρ X hXH hXp hXZ
  set U := commSpace ρ (centerIn H)
  have hle : ∀ Y : conjClass H X, U ⊓ fixedSpace ρ (Y : Subgroup G) ≤ U := fun Y => inf_le_left
  have hmap : ∀ Y : conjClass H X,
      ((U ⊓ fixedSpace ρ (Y : Subgroup G)).comap U.subtype).map U.subtype =
        U ⊓ fixedSpace ρ (Y : Subgroup G) := fun Y => by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.2 (hle Y)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def] at hind ⊢
    intro i
    have hi := hind i
    rw [Submodule.disjoint_def] at hi ⊢
    intro x hx hx'
    have hx2 : (U.subtype x) ∈ (⨆ j, ⨆ (_ : j ≠ i), U ⊓ fixedSpace ρ (j : Subgroup G)) := by
      have := Submodule.mem_map_of_mem (f := U.subtype) hx'
      rw [Submodule.map_iSup] at this
      simp only [Submodule.map_iSup, hmap] at this
      exact this
    have hx1 : (U.subtype x) ∈ U ⊓ fixedSpace ρ (i : Subgroup G) := by
      rw [← hmap i]; exact Submodule.mem_map_of_mem hx
    have := hi _ hx1 hx2
    exact U.injective_subtype (by simpa using this)
  · apply Submodule.map_injective_of_injective U.injective_subtype
    rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
    simp only [hmap]
    exact hsup

theorem finrank_conj [Finite G] [Module.Finite (ZMod 2) V] (H : Subgroup G)
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G) {Y : Subgroup G} (hY : Y ∈ conjClass H X) :
    Module.finrank (ZMod 2) ↥(commSpace ρ (centerIn H) ⊓ fixedSpace ρ Y) =
      Module.finrank (ZMod 2) ↥(commSpace ρ (centerIn H) ⊓ fixedSpace ρ X) := by
  classical
  have hρinv : ∀ (g : G) (w : V), ρ g⁻¹ (ρ g w) = w := by
    intro g w; rw [← rho_mul_apply, inv_mul_cancel, map_one]; rfl
  have hcomm : ∀ g ∈ H, ∀ w ∈ commSpace ρ (centerIn H), ρ g w ∈ commSpace ρ (centerIn H) := by
    intro g hg
    have hle : commSpace ρ (centerIn H) ≤ (commSpace ρ (centerIn H)).comap (ρ g : V →ₗ[ZMod 2] V) := by
      apply Submodule.span_le.2
      rintro w ⟨x, hx, v, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
      have hzc : g * (z : G) = (z : G) * g := by
        have := Subgroup.mem_center_iff.1 hz ⟨g, hg⟩
        have := congrArg Subtype.val this
        simpa using this
      show ρ g (ρ z v - v) ∈ commSpace ρ (centerIn H)
      rw [map_sub, ← rho_mul_apply, hzc, rho_mul_apply]
      exact Submodule.subset_span ⟨(z : G), hx, ρ g v, rfl⟩
    exact fun w hw => hle hw
  have key : ∀ g ∈ H, ∀ A : Subgroup G,
      Module.finrank (ZMod 2) ↥(commSpace ρ (centerIn H) ⊓ fixedSpace ρ A) ≤
      Module.finrank (ZMod 2)
        ↥(commSpace ρ (centerIn H) ⊓ fixedSpace ρ (A.map (MulAut.conj g).toMonoidHom)) := by
    intro g hg A
    have hmap : ∀ v ∈ commSpace ρ (centerIn H) ⊓ fixedSpace ρ A,
        ρ g v ∈ commSpace ρ (centerIn H) ⊓ fixedSpace ρ (A.map (MulAut.conj g).toMonoidHom) := by
      intro v hv
      rw [Submodule.mem_inf] at hv ⊢
      refine ⟨hcomm g hg v hv.1, ?_⟩
      rw [mem_fixedSpace_iff]
      intro d hd
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hd
      have hxv : ρ x v = v := (mem_fixedSpace_iff ρ A v).1 hv.2 x hx
      show ρ (g * x * g⁻¹) (ρ g v) = ρ g v
      rw [rho_mul_apply, rho_mul_apply, hρinv, hxv]
    let f := LinearMap.restrict (ρ g : V →ₗ[ZMod 2] V) hmap
    apply LinearMap.finrank_le_finrank_of_injective (f := f)
    intro a b hab
    apply Subtype.ext
    have h3 : ρ g⁻¹ (ρ g (a : V)) = ρ g⁻¹ (ρ g (b : V)) := by
      have := congrArg Subtype.val hab
      simp only [f, LinearMap.restrict_apply] at this
      rw [this]
    rwa [hρinv, hρinv] at h3
  apply le_antisymm
  · obtain ⟨h, hh, rfl⟩ := hY
    have h1 := key h⁻¹ (H.inv_mem hh) (X.map (MulAut.conj h).toMonoidHom)
    have hXX : (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom = X := by
      ext z
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
        have e : (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom x) = x := by
          simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]; group
        rw [e]; exact hx
      · intro hz
        refine ⟨(MulAut.conj h).toMonoidHom z, Subgroup.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]; group
    rw [hXX] at h1
    exact h1
  · obtain ⟨h, hh, rfl⟩ := hY
    exact key h hh X

theorem finrank_commSpace [Finite G] [Module.Finite (ZMod 2) V] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (H : Subgroup G)
    (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (ρ : Representation (ZMod 2) G V)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    Module.finrank (ZMod 2) ↥(commSpace ρ (centerIn H)) =
      Module.finrank (ZMod 2) ↥(commSpace ρ (centerIn H) ⊓ fixedSpace ρ X) * p := by
  classical
  have hI := isInternal_on_U hp hp2 H hH hexp ρ X hXH hXp hXZ
  haveI : Finite (conjClass H X) := Set.toFinite _
  haveI : Fintype (conjClass H X) := Fintype.ofFinite _
  set U := commSpace ρ (centerIn H)
  have hsum : Module.finrank (ZMod 2) U = ∑ Y : conjClass H X, Module.finrank (ZMod 2)
      ((U ⊓ fixedSpace ρ (Y : Subgroup G)).comap U.subtype) := by
    rw [← Module.finrank_directSum (ZMod 2) (fun Y : conjClass H X =>
      ((U ⊓ fixedSpace ρ (Y : Subgroup G)).comap U.subtype))]
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hI)).symm
  have hterm : ∀ Y : conjClass H X, Module.finrank (ZMod 2)
      ((U ⊓ fixedSpace ρ (Y : Subgroup G)).comap U.subtype) =
        Module.finrank (ZMod 2) ↥(U ⊓ fixedSpace ρ X) := fun Y => by
    rw [(Submodule.comapSubtypeEquivOfLe (inf_le_left : U ⊓ fixedSpace ρ (Y : Subgroup G) ≤ U)).finrank_eq]
    exact finrank_conj H ρ X Y.2
  rw [hsum, Finset.sum_congr rfl (fun Y _ => hterm Y), Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  have hc := conjClass_card hp hp2 H hH hexp X hXH hXp hXZ
  rw [Set.ncard_eq_toFinset_card'] at hc
  have hc2 : Fintype.card (conjClass H X) = p := by
    rw [← hc, Set.toFinset_card]
  rw [hc2, mul_comm]

end ExtraspecialModuleDecomposition

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC
