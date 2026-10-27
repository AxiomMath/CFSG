module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionLocalLayer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_preserves_layer_image (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (((Layer.subgroup H).map H.subtype : Subgroup G) : Set G) := by
  intro g hg
  let e := H.normalizerMonoidHom ⟨g, hg⟩
  have hconj : (MulAut.conj g).toMonoidHom.comp H.subtype = H.subtype.comp e.toMonoidHom := by
    ext h
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨g, hg⟩ h).symm
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_map]
  change (Layer.subgroup H).map ((MulAut.conj g).toMonoidHom.comp H.subtype) = _
  rw [hconj, ← Subgroup.map_map, Layer.equiv_invariant e]

omit [Finite G] in
theorem normalized_quasisimple_le_or_commutes (K L T : Subgroup G)
    (hK : IsQuasisimple K) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hTL : T ≤ L) (hKL : K ≤ Subgroup.normalizer (L : Set G)) :
    K ≤ L ∨ ⁅K, T⁆ = ⊥ := by
  let D := ⁅K, T⁆
  have hDK : D ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hTK
  have hDL : D ≤ L := (Subgroup.commutator_mono le_rfl hTL).trans
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hKL)
  let DK := D.subgroupOf K
  let : DK.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (Subgroup.normalizer_commutator_ge_left K T)
  rcases Quasisimple.normal_le_center_or_eq_top hK DK with hcentral | htop
  · right
    let : Group.IsPerfect K := ⟨hK.1⟩
    have hDC : D ≤ Subgroup.centralizer (K : Set G) := by
      intro d hd
      apply Subgroup.mem_centralizer_iff.mpr
      intro k hk
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp (hcentral (show (⟨d, hDK hd⟩ : K) ∈ DK from hd))
          (⟨k, hk⟩ : K))
    exact Quasisimple.perfect_double_commutator K T
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDC)
  · left
    have hD : D = K := by
      have hmap := congrArg (Subgroup.map K.subtype) htop
      change (D.subgroupOf K).map K.subtype = (⊤ : Subgroup K).map K.subtype at hmap
      simpa only [Subgroup.map_subgroupOf_eq_of_le hDK, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] using hmap
    exact hD ▸ hDL

theorem maximal_invariant_two_normalizer_normalizes (a : G) (ha : orderOf a = 2)
    (K L S : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (hL : IsComponentOf L ⊤) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hSL : S ≤ L) (htwo : IsPGroup 2 S)
    (haS : a ∈ Subgroup.normalizer (S : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G))
    (hmaximal : ∀ T : Subgroup G, T ≤ L → IsPGroup 2 T →
      a ∈ Subgroup.normalizer (T : Set G) → K ≤ Subgroup.normalizer (T : Set G) →
      S ≤ T → T = S) :
    L ⊓ Subgroup.normalizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  let A := K ⊔ Subgroup.zpowers a
  let H := L ⊔ A
  let R := S ⊔ Subgroup.zpowers a
  let C := H ⊓ Subgroup.centralizer (R : Set G)
  have hKlayer : (Layer.subgroup C).map C.subtype = K :=
    maximal_invariant_two_local_layer_eq a ha K L S hKC hK hL haL hSL htwo haS hKS hmaximal
  have hcentralizer : Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (R : Set G))).mp inferInstance
  have hNC : L ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    (le_inf (inf_le_left.trans ((show L ≤ H from le_sup_left).trans Subgroup.le_normalizer))
      (inf_le_right.trans hcentralizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  rw [← hKlayer]
  exact hNC.trans (normalizer_preserves_layer_image C)

theorem maximal_invariant_two_normalizer_alternative (a : G) (ha : orderOf a = 2)
    (K L S : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (hL : IsComponentOf L ⊤) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hSL : S ≤ L) (htwo : IsPGroup 2 S)
    (haS : a ∈ Subgroup.normalizer (S : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G))
    (hmaximal : ∀ T : Subgroup G, T ≤ L → IsPGroup 2 T →
      a ∈ Subgroup.normalizer (T : Set G) → K ≤ Subgroup.normalizer (T : Set G) →
      S ≤ T → T = S) :
    K ≤ L ∨ ⁅K, L ⊓ Subgroup.normalizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G)⁆ = ⊥ := by
  exact normalized_quasisimple_le_or_commutes K L _
    ((OrdinaryComponentTransport.subgroupOf_iff K _ hKC).mp hK).2
    (maximal_invariant_two_normalizer_normalizes a ha K L S hKC hK hL haL hSL htwo
      haS hKS hmaximal)
    inf_le_left (involution_component_normalizes a ha K hKC hK L hL)

end CFSG.ComponentClassification.AschbacherComponentInvolution
