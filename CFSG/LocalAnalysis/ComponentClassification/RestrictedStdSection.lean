module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H]

theorem mem_centralizer_of_commutator_zpowers_le {J M : Subgroup H} (hJ : ⁅J, J⁆ = J)
    (hJM : M ≤ centralizer (J : Set H)) {g : H} (hg : ⁅J, zpowers g⁆ ≤ M) :
    g ∈ centralizer (J : Set H) := by
  have hMJ : ⁅M, J⁆ = ⊥ := (commutator_eq_bot_iff_le_centralizer).mpr hJM
  have h1 : ⁅⁅J, zpowers g⁆, J⁆ = ⊥ := le_bot_iff.mp (hMJ ▸ commutator_mono hg le_rfl)
  have h2 : ⁅⁅zpowers g, J⁆, J⁆ = ⊥ := by rw [commutator_comm (zpowers g) J]; exact h1
  have h3 : ⁅⁅J, J⁆, zpowers g⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hJ, commutator_eq_bot_iff_le_centralizer] at h3
  rw [mem_centralizer_iff]
  intro j hj
  exact ((mem_centralizer_iff.mp (h3 hj)) g (mem_zpowers g)).symm

theorem commutator_eq_bot_of_le_of_perfect {J J' M : Subgroup H} (hJ : ⁅J, J⁆ = J)
    (hJM : M ≤ centralizer (J : Set H)) (hle : ⁅J, J'⁆ ≤ M) : ⁅J, J'⁆ = ⊥ := by
  have hMJ : ⁅M, J⁆ = ⊥ := (commutator_eq_bot_iff_le_centralizer).mpr hJM
  have h1 : ⁅⁅J, J'⁆, J⁆ = ⊥ := le_bot_iff.mp (hMJ ▸ commutator_mono hle le_rfl)
  have h2 : ⁅⁅J', J⁆, J⁆ = ⊥ := by rw [commutator_comm J' J]; exact h1
  have h3 : ⁅⁅J, J⁆, J'⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [hJ] at h3

theorem exists_mul_ne_of_isQuasisimple {Y : Type*} [Group Y] (hY : IsQuasisimple Y) :
    ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hY.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, y, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem commutator_self_eq_of_isQuasisimple {J : Subgroup H} (hJ : IsQuasisimple J) :
    ⁅J, J⁆ = J := by
  have hp : Group.IsPerfect J := hJ.1
  rw [← Subgroup.map_subtype_commutator, hp.commutator_eq_top, ← MonoidHom.range_eq_map,
    range_subtype]

variable (L : Subgroup H)

abbrev secN : Subgroup H := normalizer (L : Set H)

abbrev secD : Subgroup (secN L) := (centralizer (L : Set H)).subgroupOf (secN L)

theorem le_secN : L ≤ secN L := le_normalizer

instance secD_normal : (secD L).Normal := by
  refine ⟨fun d hd n => ?_⟩
  rw [mem_subgroupOf] at hd ⊢
  rw [mem_centralizer_iff] at hd ⊢
  intro l hl
  have hl' : (n : H)⁻¹ * l * (n : H) ∈ L := by
    have := (mem_normalizer_iff.mp (inv_mem n.2) l).mp hl
    simpa using this
  have h := hd _ hl'
  simp only [coe_mul, coe_inv]
  calc l * ((n : H) * d * (n : H)⁻¹)
      = (n : H) * ((n : H)⁻¹ * l * (n : H) * d) * (n : H)⁻¹ := by group
    _ = (n : H) * (d * ((n : H)⁻¹ * l * (n : H))) * (n : H)⁻¹ := by rw [h]
    _ = (n : H) * d * (n : H)⁻¹ * l := by group

abbrev secπ : secN L →* secN L ⧸ secD L := QuotientGroup.mk' (secD L)

abbrev secImg (X : Subgroup H) : Subgroup (secN L ⧸ secD L) := (X.subgroupOf (secN L)).map (secπ L)

variable {L}

theorem secπ_eq_one_iff (x : secN L) : secπ L x = 1 ↔ (x : H) ∈ centralizer (L : Set H) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem secπ_mem_secImg {X : Subgroup H} {x : secN L} (hx : (x : H) ∈ X) :
    secπ L x ∈ secImg L X :=
  mem_map_of_mem _ (mem_subgroupOf.mpr hx)

theorem secImg_mono {X Y : Subgroup H} (h : X ≤ Y) : secImg L X ≤ secImg L Y := by
  rintro _ ⟨x, hx, rfl⟩
  exact secπ_mem_secImg (h (mem_subgroupOf.mp hx))

instance secImg_self_normal : (secImg L L).Normal :=
  Subgroup.Normal.map normal_in_normalizer _ (QuotientGroup.mk'_surjective _)

theorem mem_centralizer_of_secπ_mem {J : Subgroup H} (hJL : J ≤ L) (hJ : ⁅J, J⁆ = J)
    {x : secN L} (hx : secπ L x ∈ centralizer (secImg L J : Set (secN L ⧸ secD L))) :
    (x : H) ∈ centralizer (J : Set H) := by
  refine mem_centralizer_of_commutator_zpowers_le (M := L ⊓ centralizer (L : Set H)) hJ
    (fun m hm => mem_centralizer_iff.mpr fun j hj =>
      (mem_centralizer_iff.mp (mem_inf.mp hm).2 j (hJL hj))) ?_
  rw [commutator_le]
  intro j hj y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hyN : ((x : H) ^ k) ∈ secN L := (x ^ k).2
  have hjN : j ∈ secN L := le_secN L (hJL hj)
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    have h1 : (x : H) ^ k * j⁻¹ * ((x : H) ^ k)⁻¹ ∈ L :=
      (mem_normalizer_iff.mp hyN j⁻¹).mp (inv_mem (hJL hj))
    have h2 := mul_mem (hJL hj) h1
    simpa [mul_assoc] using h2
  · have hxk : secπ L (x ^ k) ∈ centralizer (secImg L J : Set (secN L ⧸ secD L)) := by
      rw [map_zpow]
      exact zpow_mem hx k
    have hj' : secπ L ⟨j, hjN⟩ ∈ secImg L J := secπ_mem_secImg hj
    have hc : secπ L ⁅(⟨j, hjN⟩ : secN L), x ^ k⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.mp hxk _ hj')
    rw [secπ_eq_one_iff] at hc
    have he : ((⁅(⟨j, hjN⟩ : secN L), x ^ k⁆ : secN L) : H) = ⁅j, (x : H) ^ k⁆ := by
      simp [commutatorElement_def]
    rw [← he]
    exact hc

theorem centralizer_secImg_self (hL : ⁅L, L⁆ = L) :
    centralizer (secImg L L : Set (secN L ⧸ secD L)) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (secD L) y
  rw [mem_bot]
  exact (secπ_eq_one_iff x).mpr (mem_centralizer_of_secπ_mem le_rfl hL hy)

@[expose] noncomputable def secRes {X : Subgroup H} (hX : X ≤ secN L) : X →* secImg L X :=
  ((secπ L).subgroupMap (X.subgroupOf (secN L))).comp (subgroupOfEquivOfLe hX).symm.toMonoidHom

theorem secRes_surjective {X : Subgroup H} (hX : X ≤ secN L) :
    Function.Surjective (secRes hX) :=
  ((secπ L).subgroupMap_surjective _).comp (subgroupOfEquivOfLe hX).symm.surjective

theorem secRes_apply_coe {X : Subgroup H} (hX : X ≤ secN L) (x : X) :
    ((secRes hX x : secImg L X) : secN L ⧸ secD L) = secπ L ⟨x, hX x.2⟩ := rfl

theorem secRes_eq_one_iff {X : Subgroup H} (hX : X ≤ secN L) (x : X) :
    secRes hX x = 1 ↔ (x : H) ∈ centralizer (L : Set H) := by
  rw [← Subtype.coe_inj, secRes_apply_coe, OneMemClass.coe_one, secπ_eq_one_iff]

theorem ker_secRes_le_center {X : Subgroup H} (hXL : X ≤ L) :
    (secRes (hXL.trans (le_secN L))).ker ≤ center X := by
  intro x hx
  rw [MonoidHom.mem_ker, secRes_eq_one_iff] at hx
  rw [mem_center_iff]
  intro y
  exact Subtype.ext ((mem_centralizer_iff.mp hx) y (hXL y.2))

theorem ker_secRes_self : (secRes (le_secN L)).ker = center L := by
  refine le_antisymm (ker_secRes_le_center le_rfl) fun x hx => ?_
  rw [MonoidHom.mem_ker, secRes_eq_one_iff, mem_centralizer_iff]
  intro l hl
  exact congrArg Subtype.val ((mem_center_iff.mp hx) ⟨l, hl⟩)

noncomputable def secImgEquiv : L ⧸ center L ≃* secImg L L :=
  (QuotientGroup.quotientMulEquivOfEq ker_secRes_self.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (secRes_surjective (le_secN L)))

theorem secImg_self_isSimpleGroup (hL : IsQuasisimple L) : IsSimpleGroup (secImg L L) :=
  have : IsSimpleGroup (L ⧸ center L) := hL.2.1
  (secImgEquiv (L := L)).symm.isSimpleGroup

theorem secImg_self_nonabelian (hL : IsQuasisimple L) :
    ∃ x y : secImg L L, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := hL.2.2
  refine ⟨secImgEquiv a, secImgEquiv b, fun h => hab ?_⟩
  apply (secImgEquiv (L := L)).injective
  rw [map_mul, map_mul, h]

end CFSG.ComponentClassification.RestrictedStd
