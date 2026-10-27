module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionLayer
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentTransport

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem corefree_involution_component_normalizes (a : G) (ha : orderOf a = 2)
    (hcorefree : componentClassificationOddCore G = ⊥)
    (K : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (L : Subgroup G) (hL : IsComponentOf L ⊤) :
    K ≤ Subgroup.normalizer (L : Set G) := by
  let C := Subgroup.centralizer ({a} : Set G)
  let E := Layer.subgroup G
  let : E.Normal := Layer.normal G
  let EC := E.subgroupOf C
  let : EC.Normal := inferInstance
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := by
    apply sSup_le
    intro M hM
    by_cases hML : M = L
    · rw [hML]
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (LocalComponents.commute_of_ne M L hM hL hML)).trans
          (Subgroup.centralizer_le_normalizer _)
  rcases LocalComponents.normal_contains_or_commutes (K.subgroupOf C) EC hK with
    hcontained | hcommutes
  · intro k hk
    exact hEN (hcontained (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk))
  · have hfixed : ⁅K, E ⊓ C⁆ = ⊥ := by
      have hmap : (⁅K.subgroupOf C, E.subgroupOf C⁆).map C.subtype = ⊥ := by
        simpa only [Subgroup.map_bot] using
          congrArg (Subgroup.map C.subtype) hcommutes
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKC,
        Subgroup.subgroupOf_map_subtype] at hmap
      exact hmap
    have hKF : ⁅K, Fitting.subgroup G⁆ = ⊥ := by
      rw [PrimeCore.fitting_eq_two_of_odd_corefree hcorefree]
      let : (PrimeCore.subgroup 2 G).Normal := PrimeCore.normal 2 G
      have hle := InvolutionLayer.component_centralizes_normal_two a ha
        (PrimeCore.subgroup 2 G) (PrimeCore.isPGroup 2 G) (K.subgroupOf C) hK
      rw [Subgroup.map_subgroupOf_eq_of_le hKC] at hle
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    let : Group.IsPerfect K :=
      ⟨((OrdinaryComponentTransport.subgroupOf_iff K C hKC).mp hK).2.1⟩
    exact GeneralizedFitting.involution_fixed_layer_centralizer_normalizes K a
      (InvolutionLayer.involution_square a ha) hKC hKF hfixed L hL

omit [Finite G] in
theorem component_not_le_solvable_kernel {Q : Type*} [Group Q] (f : G →* Q)
    [Group.IsSolvable f.ker] (L : Subgroup G) (hL : IsComponentOf L ⊤) :
    ¬ L ≤ f.ker := by
  intro hle
  let : Group.IsPerfect L := ⟨hL.2.2.1⟩
  let : Nontrivial L := Quasisimple.nontrivial hL.2.2
  let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable L inferInstance

theorem components_eq_of_equal_images {Q : Type*} [Group Q]
    (f : G →* Q) [Group.IsSolvable f.ker]
    (L M : Subgroup G) (hL : IsComponentOf L ⊤) (hM : IsComponentOf M ⊤)
    (himages : L.map f = M.map f) : L = M := by
  by_contra hne
  have hcommutes := congrArg (Subgroup.map f)
    (LocalComponents.commute_of_ne L M hL hM hne)
  rw [Subgroup.map_commutator, Subgroup.map_bot, ← himages] at hcommutes
  let : Group.IsPerfect L := ⟨hL.2.2.1⟩
  let : Group.IsPerfect (L.map f) := Group.IsPerfect.map f
  rw [Subgroup.commutator_eq_self] at hcommutes
  exact component_not_le_solvable_kernel f L hL
    ((Subgroup.map_eq_bot_iff L).mp hcommutes)

theorem involution_component_normalizes (a : G) (ha : orderOf a = 2)
    (K : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (L : Subgroup G) (hL : IsComponentOf L ⊤) :
    K ≤ Subgroup.normalizer (L : Set G) := by
  let O := componentClassificationOddCore G
  let : O.Normal := inferInstance
  let q := QuotientGroup.mk' O
  have hOodd : Odd (Nat.card q.ker) := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    exact OddCore.odd_card G
  let : Group.IsSolvable q.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
  let C := Subgroup.centralizer ({a} : Set G)
  let Cq := Subgroup.centralizer ({q a} : Set (G ⧸ O))
  have himageK : IsComponentOf ((K.map q).subgroupOf Cq) ⊤ := by
    have h := OddKernelInvolutions.component_image q (QuotientGroup.mk'_surjective O)
      hOodd a ha (K.subgroupOf C) hK
    rwa [Subgroup.map_subgroupOf_eq_of_le hKC] at h
  have himageKC : K.map q ≤ Cq := by
    rintro k ⟨lift, hlift, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg q
      (Subgroup.mem_centralizer_singleton_iff.mp (hKC hlift))
  have himageL : IsComponentOf (L.map q) ⊤ :=
    LocalComponents.image hL q (QuotientGroup.mk'_surjective O)
      (component_not_le_solvable_kernel q L hL)
  have hnormalizes := corefree_involution_component_normalizes (q a)
    (OddKernelInvolutions.image_order q hOodd a ha)
    (OddCore.quotient_corefree G) (K.map q) himageKC himageK (L.map q) himageL
  intro k hk
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply components_eq_of_equal_images q _ L
    ((LocalComponents.equiv_iff (MulAut.conj k) L).mpr hL) hL
  have heq := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (hnormalizes (Subgroup.mem_map_of_mem q hk))
  rw [Subgroup.map_map]
  have hconj : q.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj (q k)).toMonoidHom.comp q := by
    ext x
    change q (k * x * k⁻¹) = q k * q x * (q k)⁻¹
    simp only [map_mul, map_inv]
  rw [hconj, ← Subgroup.map_map]
  exact heq

theorem involution_layer_normalizes (a : G) (ha : orderOf a = 2)
    (L : Subgroup G) (hL : IsComponentOf L ⊤) :
    (Layer.subgroup (Subgroup.centralizer ({a} : Set G))).map
      (Subgroup.centralizer ({a} : Set G)).subtype ≤ Subgroup.normalizer (L : Set G) := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro K hK
  apply Subgroup.map_le_iff_le_comap.mp
  exact involution_component_normalizes a ha (K.map (Subgroup.centralizer ({a} : Set G)).subtype)
    (Subgroup.map_subtype_le _) (OrdinaryComponentTransport.subtype_image_component _ K hK) L hL

end CFSG.ComponentClassification.AschbacherComponentInvolution
