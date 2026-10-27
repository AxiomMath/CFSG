module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMaximalTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionInvariantTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionNormalization
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProduct

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem perfect_centralizing_complement_le (L A J : Subgroup G) [Group.IsPerfect J]
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hJA : ⁅J, A⁆ = ⊥)
    (hJP : J ≤ L ⊔ A) : J ≤ L := by
  let P := L ⊔ A
  let LN := L.subgroupOf P
  let JP := J.subgroupOf P
  let : LN.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le Subgroup.le_normalizer hAL)
  let q := QuotientGroup.mk' LN
  let : Group.IsPerfect JP :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJP).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJP).symm.surjective
  let image := JP.map q
  let : Group.IsPerfect image := Group.IsPerfect.map q
  have hcenter : image ≤ Subgroup.center (P ⧸ LN) := by
    rintro y ⟨j, hj, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro x
    obtain ⟨xP, rfl⟩ := QuotientGroup.mk'_surjective LN x
    obtain ⟨l, hl, r, hr, hcoords⟩ :=
      NormalizedProduct.coordinates L A hAL xP.val xP.property
    let lP : P := ⟨l, (show L ≤ P from le_sup_left) hl⟩
    let rP : P := ⟨r, (show A ≤ P from le_sup_right) hr⟩
    have heq : xP = lP * rP := Subtype.ext hcoords.symm
    have hlq : q lP = 1 := QuotientGroup.eq_one_iff lP |>.mpr hl
    have hrj : rP * j = j * rP := Subtype.ext
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJA hj) r hr)
    change q xP * q j = q j * q xP
    rw [heq, map_mul, hlq, one_mul, ← map_mul, ← map_mul, hrj]
  have himage : image = ⊥ := Quasisimple.perfect_le_center_eq_bot image hcenter
  have hkernel : JP ≤ q.ker := (Subgroup.map_eq_bot_iff JP).mp himage
  intro j hj
  have hmem := hkernel (show (⟨j, hJP hj⟩ : P) ∈ JP from hj)
  rwa [QuotientGroup.ker_mk'] at hmem

theorem maximal_invariant_two_local_layer_eq (a : G) (ha : orderOf a = 2)
    (K L S : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (hL : IsComponentOf L ⊤) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hSL : S ≤ L) (htwo : IsPGroup 2 S)
    (haS : a ∈ Subgroup.normalizer (S : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G))
    (hmaximal : ∀ T : Subgroup G, T ≤ L → IsPGroup 2 T →
      a ∈ Subgroup.normalizer (T : Set G) → K ≤ Subgroup.normalizer (T : Set G) →
      S ≤ T → T = S) :
    (Layer.subgroup
      (↥((L ⊔ (K ⊔ Subgroup.zpowers a)) ⊓
        Subgroup.centralizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G)))).map
      ((L ⊔ (K ⊔ Subgroup.zpowers a)) ⊓
        Subgroup.centralizer ((S ⊔ Subgroup.zpowers a : Subgroup G) : Set G)).subtype = K := by
  let A := K ⊔ Subgroup.zpowers a
  let H := L ⊔ A
  let R := S ⊔ Subgroup.zpowers a
  let C := H ⊓ Subgroup.centralizer (R : Set G)
  have hKNL := involution_component_normalizes a ha K hKC hK L hL
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    sup_le hKNL (Subgroup.zpowers_le.mpr haL)
  obtain ⟨hKCR, hKlocalR⟩ := invariant_two_component_in_common_centralizer
    a ha K S hKC hK htwo haS hKS
  have hKH : K ≤ H := le_sup_left.trans le_sup_right
  have hKCfull : K ≤ C := le_inf hKH hKCR
  have hKlocal : IsComponentOf (K.subgroupOf C) ⊤ :=
    OrdinaryComponentTransport.restrict_nested K C _ hKCfull inf_le_right hKlocalR
  change (Layer.subgroup C).map C.subtype = K
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro localJ hlocalJ
    let J := localJ.map C.subtype
    have hJC : J ≤ C := Subgroup.map_subtype_le _
    have hJlocal : IsComponentOf (J.subgroupOf C) ⊤ :=
      OrdinaryComponentTransport.subtype_image_component C localJ hlocalJ
    by_cases hJK : J = K
    · exact Subgroup.map_le_iff_le_comap.mp hJK.le
    · have hquasiJ := ((OrdinaryComponentTransport.subgroupOf_iff J C hJC).mp hJlocal).2
      let : Group.IsPerfect J := ⟨hquasiJ.1⟩
      have hJKcommutes : ⁅J, K⁆ = ⊥ := OrdinaryComponentTransport.commute_local_distinct
        J K C hJC hKCfull hJlocal hKlocal hJK
      have hJS : ⁅J, S⁆ = ⊥ := by
        apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        exact (hJC.trans inf_le_right).trans (Subgroup.centralizer_le
          (show S ≤ R from le_sup_left))
      have haJ : a ∈ Subgroup.centralizer (J : Set G) := by
        apply Subgroup.mem_centralizer_iff.mpr
        intro j hj
        exact (Subgroup.mem_centralizer_iff.mp ((hJC.trans inf_le_right) hj) a
          ((show Subgroup.zpowers a ≤ R from le_sup_right) (Subgroup.mem_zpowers a))).symm
      have hJA : ⁅J, A⁆ = ⊥ := by
        apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        apply Subgroup.le_centralizer_iff.mp
        exact sup_le
          (Subgroup.le_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJKcommutes))
          (Subgroup.zpowers_le.mpr haJ)
      have hJL : J ≤ L := perfect_centralizing_complement_le L A J hAL hJA
        (hJC.trans inf_le_left)
      have hbot := maximal_invariant_two_excludes_perfect L K S J a hSL htwo haS hKS
        hmaximal hJL hJS haJ (by rwa [Subgroup.commutator_comm] at hJKcommutes)
      have hlocalBot : localJ = ⊥ := by
        apply Subgroup.map_injective C.subtype_injective
        simpa only [Subgroup.map_bot] using hbot
      exact hlocalBot ▸ bot_le
  · calc
      K = (K.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hKCfull).symm
      _ ≤ (Layer.subgroup C).map C.subtype := Subgroup.map_mono (Layer.component_le hKlocal)

end CFSG.ComponentClassification.AschbacherComponentInvolution
