module

public import CFSG.GroupTheory.QuasiDihedralFusion.OddKernel
public import CFSG.GroupTheory.QuasiDihedralFusion.Classes

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.Wreathed CFSG.GorensteinWalter
open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFchapter1section1

universe u v

section Conjugates

variable {A : Type u} {B : Type v} [Group A] [Group B]

theorem rightConjugate_mul' (P : Subgroup A) (a b : A) :
    rightConjugate P (a * b) = rightConjugate (rightConjugate P a) b := by
  change P.map (MulAut.conj (a * b)⁻¹).toMonoidHom =
    (P.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj b⁻¹).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply, mul_inv_rev,
    inv_inv]
  group

theorem map_rightConjugate (φ : A →* B) (P : Subgroup A) (g : A) :
    (rightConjugate P g).map φ = rightConjugate (P.map φ) (φ g) := by
  change (P.map (MulAut.conj g⁻¹).toMonoidHom).map φ =
    (P.map φ).map (MulAut.conj (φ g)⁻¹).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  simp only [map_mul, map_inv]

theorem rightConjugate_eq_of_le_centerOf {R Z : Subgroup A} (hZ : Z ≤ centerOf R) {b : A}
    (hb : b ∈ R) : rightConjugate Z b = Z := by
  have hcomm : ∀ z ∈ Z, b⁻¹ * z * b = z := by
    intro z hz
    have hzC := (Subgroup.mem_inf.mp (hZ hz)).2
    rw [Subgroup.mem_centralizer_iff] at hzC
    rw [mul_assoc, ← hzC b hb, inv_mul_cancel_left]
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    change b⁻¹ * z * b⁻¹⁻¹ ∈ Z
    rw [inv_inv, hcomm z hz]
    exact hz
  · intro z hz
    refine ⟨z, hz, ?_⟩
    change b⁻¹ * z * b⁻¹⁻¹ = z
    rw [inv_inv, hcomm z hz]

theorem map_symm_eq_of_map_eq (e : A ≃* B) {P : Subgroup A} {P' : Subgroup B}
    (h : P.map e.toMonoidHom = P') : P'.map e.symm.toMonoidHom = P := by
  rw [← h, Subgroup.map_map]
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A :=
    MonoidHom.ext fun x => by simp
  rw [hid, Subgroup.map_id]

theorem IsMaximalQuaternionIn.of_equiv {R Y : Subgroup A} {R' Y' : Subgroup B} (e : R ≃* R')
    (hY' : Y' ≤ R') (hYY : (Y.subgroupOf R).map e.toMonoidHom = Y'.subgroupOf R')
    (h : IsMaximalQuaternionIn R Y) : IsMaximalQuaternionIn R' Y' := by
  obtain ⟨-, hpos⟩ := h
  have hback := map_symm_eq_of_map_eq e hYY
  refine ⟨hY', ?_⟩
  rcases hpos with ⟨n, hn, ι, hι, himg⟩ | ⟨n, hn, ι, hι, himg⟩
  · exact Or.inl ⟨n, hn, ι.comp e.symm.toMonoidHom, hι.comp e.symm.injective,
      by rw [← Subgroup.map_map, hback, himg]⟩
  · exact Or.inr ⟨n, hn, ι.comp e.symm.toMonoidHom, hι.comp e.symm.injective,
      by rw [← Subgroup.map_map, hback, himg]⟩

theorem IsMaximalQuaternionIn.iff_of_equiv {R Y : Subgroup A} {R' Y' : Subgroup B}
    (e : R ≃* R') (hY : Y ≤ R) (hY' : Y' ≤ R')
    (hYY : (Y.subgroupOf R).map e.toMonoidHom = Y'.subgroupOf R') :
    IsMaximalQuaternionIn R Y ↔ IsMaximalQuaternionIn R' Y' :=
  ⟨of_equiv e hY' hYY, of_equiv e.symm hY (map_symm_eq_of_map_eq e hYY)⟩

theorem subgroupOf_map_of_coe (φ : A →* B) {R : Subgroup A} {R' : Subgroup B} (e : R ≃* R')
    (he : ∀ x : R, (e x : B) = φ x) {Y : Subgroup A} {Y' : Subgroup B}
    (hY : ∀ x ∈ R, x ∈ Y ↔ φ x ∈ Y') :
    (Y.subgroupOf R).map e.toMonoidHom = Y'.subgroupOf R' := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    hY _ (e.symm y).property]
  have h := he (e.symm y)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h]

theorem map_centerOf_le (φ : A →* B) (R : Subgroup A) :
    (centerOf R).map φ ≤ centerOf (R.map φ) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨hzR, hzC⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨⟨z, hzR, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hzC ⊢
  rintro _ ⟨r, hr, rfl⟩
  rw [← map_mul, ← map_mul, hzC r hr]

theorem mem_of_map_mem (φ : A →* B) {K : Subgroup A} (hK : φ.ker ≤ K) {x : A}
    (hx : φ x ∈ K.map φ) : x ∈ K := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, sup_eq_left.mpr hK] at hx
  exact hx

end Conjugates

section Kernel

variable {A : Type u} {B : Type v} [Group A] [Group B] [Finite A] (φ : A →* B)

theorem eq_of_le_of_map_eq (hker : Odd (Nat.card φ.ker)) {R : Subgroup A} (hR : IsPGroup 2 R)
    {P Q : Subgroup A} (hP : P ≤ R) (hQ : Q ≤ R) (h : P.map φ = Q.map φ) : P = Q := by
  have key : ∀ {P Q : Subgroup A}, P ≤ R → Q ≤ R → P.map φ = Q.map φ → P ≤ Q := by
    intro P Q hP hQ h x hx
    have hx' : φ x ∈ P.map φ := ⟨x, hx, rfl⟩
    rw [h] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [eq_of_mem_of_map_eq φ hker hR (hP hx) (hQ hy) hyx.symm]
    exact hy
  exact le_antisymm (key hP hQ h) (key hQ hP h.symm)

theorem weaklyClosed_center_map (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker))
    (R : Sylow 2 A)
    (h : ∀ Z₀ : Subgroup A, Z₀ ≤ centerOf (R : Subgroup A) → WeaklyClosedIn (R : Subgroup A) Z₀)
    (Z : Subgroup B) (hZ : Z ≤ centerOf ((R : Subgroup A).map φ)) :
    WeaklyClosedIn ((R : Subgroup A).map φ) Z := by
  have hR := R.isPGroup'
  obtain ⟨Z₀, hZ₀def⟩ : ∃ Z₀ : Subgroup A, Z₀ = Z.comap φ ⊓ (R : Subgroup A) := ⟨_, rfl⟩
  have hZ₀C : Z₀ ≤ centerOf (R : Subgroup A) := by
    rw [hZ₀def]
    rintro z ⟨hzZ, hzR⟩
    have hzZ' : φ z ∈ Z := hzZ
    refine Subgroup.mem_inf.mpr ⟨hzR, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hφz := (Subgroup.mem_inf.mp (hZ hzZ')).2
    rw [Subgroup.mem_centralizer_iff] at hφz
    have hc := hφz (φ r) ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul] at hc
    exact eq_of_mem_of_map_eq φ hker hR ((R : Subgroup A).mul_mem hr hzR)
      ((R : Subgroup A).mul_mem hzR hr) hc
  have hZ₀map : Z₀.map φ = Z := by
    rw [hZ₀def]
    apply le_antisymm
    · rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
      exact hz
    · intro z hz
      obtain ⟨r, hr, rfl⟩ := (Subgroup.mem_inf.mp (hZ hz)).1
      exact ⟨r, ⟨hz, hr⟩, rfl⟩
  refine ⟨hZ.trans inf_le_left, fun g' hg' => ?_⟩
  obtain ⟨g, rfl⟩ := hφ g'
  have hle : rightConjugate Z₀ g ≤ (R : Subgroup A) ⊔ φ.ker := by
    rw [← Subgroup.comap_map_eq, ← Subgroup.map_le_iff_le_comap, map_rightConjugate, hZ₀map]
    exact hg'
  have hX2 : IsPGroup 2 (rightConjugate Z₀ g) :=
    (hR.to_le (hZ₀C.trans inf_le_left)).map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨c, hc, hcX⟩ := exists_conj_le_sylow _ R le_sup_left _ hle hX2
  have hcX' : rightConjugate Z₀ (g * c⁻¹) ≤ (R : Subgroup A) := by
    have hconj : rightConjugate Z₀ (g * c⁻¹) =
        (rightConjugate Z₀ g).map (MulAut.conj c).toMonoidHom := by
      rw [rightConjugate_mul']
      change (rightConjugate Z₀ g).map (MulAut.conj c⁻¹⁻¹).toMonoidHom = _
      rw [inv_inv]
    rw [hconj]
    exact hcX
  have hfix := (h Z₀ hZ₀C).2 (g * c⁻¹) hcX'
  have hcR : φ c ∈ (R : Subgroup A).map φ := by
    rw [← Subgroup.comap_map_eq] at hc
    exact hc
  have h1 : rightConjugate Z (φ (g * c⁻¹)) = Z := by
    rw [← hZ₀map, ← map_rightConjugate, hfix]
  calc rightConjugate Z (φ g) = rightConjugate Z (φ (g * c⁻¹) * φ c) := by
        rw [map_mul, map_inv, inv_mul_cancel_right]
    _ = rightConjugate (rightConjugate Z (φ (g * c⁻¹))) (φ c) := rightConjugate_mul' _ _ _
    _ = rightConjugate Z (φ c) := by rw [h1]
    _ = Z := rightConjugate_eq_of_le_centerOf hZ hcR

theorem weaklyClosed_center_comap (hker : Odd (Nat.card φ.ker)) (R : Sylow 2 A)
    (h : ∀ Z : Subgroup B, Z ≤ centerOf ((R : Subgroup A).map φ) →
      WeaklyClosedIn ((R : Subgroup A).map φ) Z)
    (Z₀ : Subgroup A) (hZ₀ : Z₀ ≤ centerOf (R : Subgroup A)) :
    WeaklyClosedIn (R : Subgroup A) Z₀ := by
  have hR := R.isPGroup'
  have hZ₀R : Z₀ ≤ (R : Subgroup A) := hZ₀.trans inf_le_left
  refine ⟨hZ₀R, fun g hg => ?_⟩
  have hZ := h (Z₀.map φ) ((Subgroup.map_mono hZ₀).trans (map_centerOf_le φ _))
  have hfix := hZ.2 (φ g) (by rw [← map_rightConjugate]; exact Subgroup.map_mono hg)
  rw [← map_rightConjugate] at hfix
  exact eq_of_le_of_map_eq φ hker hR hg hZ₀R hfix

end Kernel

section Data

variable {A : Type u} {B : Type v} [Group A] [Group B] [Finite A] (φ : A →* B)
  (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker))

include hφ hker in
theorem IsQGroupData.map_of_oddKernel {R : Sylow 2 A} {K : Subgroup A} (h : IsQGroupData R K) :
    IsQGroupData (R.mapSurjective hφ) (K.map φ) := by
  have : Finite B := Finite.of_surjective φ hφ
  have : K.Normal := h.normal
  have hR := R.isPGroup'
  have hkerK : φ.ker ≤ K := le_of_odd_of_two_pow_index K h.index_eq_two_pow φ.ker hker
  have hsurj := φ.subgroupMap_surjective K
  have hoddK := odd_card_ker_subgroupMap φ hker K
  have hRmap : ((R.mapSurjective hφ : Sylow 2 B) : Subgroup B) = (R : Subgroup A).map φ :=
    Sylow.coe_mapSurjective hφ R
  refine ⟨h.normal.map φ hφ, ?_, (noIndexTwo_iff_of_oddKernel _ hsurj hoddK).mp h.noIndexTwo,
    ?_, ?_⟩
  · obtain ⟨k, hk⟩ := h.index_eq_two_pow
    refine ⟨k, ?_⟩
    rw [Subgroup.index_map, sup_eq_left.mpr hkerK, MonoidHom.range_eq_top.mpr hφ,
      Subgroup.index_top, mul_one, hk]
  · rw [hRmap]
    have hYY : ((K ⊓ (R : Subgroup A)).subgroupOf R).map
        (equivMapOfIsPGroup φ hker R hR).toMonoidHom =
          (K.map φ ⊓ (R : Subgroup A).map φ).subgroupOf ((R : Subgroup A).map φ) := by
      refine subgroupOf_map_of_coe φ _ (fun x => rfl) (fun x hx => ?_)
      constructor
      · rintro ⟨hxK, hxR⟩
        exact ⟨⟨x, hxK, rfl⟩, ⟨x, hxR, rfl⟩⟩
      · rintro ⟨hxK, -⟩
        exact ⟨mem_of_map_mem φ hkerK hxK, hx⟩
    exact h.quaternion.of_equiv (equivMapOfIsPGroup φ hker R hR) inf_le_right hYY
  · rw [hRmap]
    exact weaklyClosed_center_map φ hφ hker R h.center_weaklyClosed

include hφ hker in
theorem IsQGroupData.comap_of_oddKernel {R' : Sylow 2 B} {K : Subgroup B} (h : IsQGroupData R' K)
    (R : Sylow 2 A) (hRR : (R : Subgroup A).map φ = R') : IsQGroupData R (K.comap φ) := by
  have : Finite B := Finite.of_surjective φ hφ
  have hR := R.isPGroup'
  have hmap : (K.comap φ).map φ = K := Subgroup.map_comap_eq_self_of_surjective hφ K
  have hsurj : Function.Surjective ((MulEquiv.subgroupCongr hmap).toMonoidHom.comp
      (φ.subgroupMap (K.comap φ))) :=
    (MulEquiv.subgroupCongr hmap).surjective.comp (φ.subgroupMap_surjective _)
  have hoddK : Odd (Nat.card ((MulEquiv.subgroupCongr hmap).toMonoidHom.comp
      (φ.subgroupMap (K.comap φ))).ker) := by
    have hk : ((MulEquiv.subgroupCongr hmap).toMonoidHom.comp
        (φ.subgroupMap (K.comap φ))).ker = (φ.subgroupMap (K.comap φ)).ker := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
    rw [hk]
    exact odd_card_ker_subgroupMap φ hker _
  have : K.Normal := h.normal
  refine ⟨h.normal.comap φ, ?_, (noIndexTwo_iff_of_oddKernel _ hsurj hoddK).mpr h.noIndexTwo,
    ?_, ?_⟩
  · obtain ⟨k, hk⟩ := h.index_eq_two_pow
    exact ⟨k, by rw [Subgroup.index_comap_of_surjective _ hφ, hk]⟩
  · let e : (R : Subgroup A) ≃* (R' : Subgroup B) :=
      (equivMapOfIsPGroup φ hker R hR).trans (MulEquiv.subgroupCongr hRR)
    have hYY : ((K.comap φ ⊓ (R : Subgroup A)).subgroupOf R).map e.toMonoidHom =
        (K ⊓ (R' : Subgroup B)).subgroupOf R' := by
      refine subgroupOf_map_of_coe φ e (fun x => rfl) (fun x hx => ?_)
      constructor
      · rintro ⟨hxK, -⟩
        refine ⟨hxK, ?_⟩
        rw [← hRR]
        exact ⟨x, hx, rfl⟩
      · rintro ⟨hxK, -⟩
        exact ⟨hxK, hx⟩
    exact (IsMaximalQuaternionIn.iff_of_equiv e inf_le_right inf_le_right hYY).mpr h.quaternion
  · have hwc : ∀ Z : Subgroup B, Z ≤ centerOf ((R : Subgroup A).map φ) →
        WeaklyClosedIn ((R : Subgroup A).map φ) Z := by
      rw [hRR]
      exact h.center_weaklyClosed
    exact weaklyClosed_center_comap φ hker R hwc

end Data

section Classes

variable {A : Type u} {B : Type v} [Group A] [Group B] [Finite A] (φ : A →* B)
  (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker))

include hφ hker in
theorem isQDGroup_iff_of_oddKernel : IsQDGroup B ↔ IsQDGroup A := by
  have : Finite B := Finite.of_surjective φ hφ
  rw [isQDGroup_iff, isQDGroup_iff, hasQDOrWreathedSylow_iff_of_oddKernel φ hφ hker,
    noIndexTwo_iff_of_oddKernel φ hφ hker]

include hφ hker in
theorem isQGroup_iff_of_oddKernel : IsQGroup B ↔ IsQGroup A := by
  constructor
  · rintro ⟨R', K, hK⟩
    obtain ⟨R, hR⟩ := exists_sylow_map_eq φ hφ R'
    exact ⟨R, K.comap φ, hK.comap_of_oddKernel φ hφ hker R hR⟩
  · rintro ⟨R, K, hK⟩
    exact ⟨R.mapSurjective hφ, K.map φ, hK.map_of_oddKernel φ hφ hker⟩

include hφ hker in
theorem isDGroup_iff_of_oddKernel : IsDGroup B ↔ IsDGroup A := by
  have : Finite B := Finite.of_surjective φ hφ
  constructor
  · rintro (⟨hD, hN⟩ | ⟨K, hK⟩)
    · exact Or.inl ⟨(hasDihedralSylowTwo_iff_of_oddKernel φ hφ hker).mp hD,
        fun h => hN ((hasNormalPComplement_iff_of_oddKernel φ hφ hker).mpr h)⟩
    · exact Or.inr ⟨K.comap φ, hK.comap_of_oddKernel φ hφ hker⟩
  · rintro (⟨hD, hN⟩ | ⟨K, hK⟩)
    · exact Or.inl ⟨(hasDihedralSylowTwo_iff_of_oddKernel φ hφ hker).mpr hD,
        fun h => hN ((hasNormalPComplement_iff_of_oddKernel φ hφ hker).mp h)⟩
    · exact Or.inr ⟨K.map φ, hK.map_of_oddKernel φ hφ hker⟩

end Classes

section OddCore

variable {H : Type u} [Group H] [Finite H]

theorem odd_card_ker_mk'_oddCore : Odd (Nat.card (QuotientGroup.mk' (CFSG.oddCore H)).ker) := by
  rw [QuotientGroup.ker_mk']
  exact CFSG.Semidihedral.Local.odd_card_oddCore H

theorem isQDGroup_quotient_oddCore_iff :
    IsQDGroup (H ⧸ CFSG.oddCore H) ↔ IsQDGroup H :=
  isQDGroup_iff_of_oddKernel _ (QuotientGroup.mk'_surjective _) odd_card_ker_mk'_oddCore

theorem isQGroup_quotient_oddCore_iff :
    IsQGroup (H ⧸ CFSG.oddCore H) ↔ IsQGroup H :=
  isQGroup_iff_of_oddKernel _ (QuotientGroup.mk'_surjective _) odd_card_ker_mk'_oddCore

theorem isDGroup_quotient_oddCore_iff :
    IsDGroup (H ⧸ CFSG.oddCore H) ↔ IsDGroup H :=
  isDGroup_iff_of_oddKernel _ (QuotientGroup.mk'_surjective _) odd_card_ker_mk'_oddCore

end OddCore

end CFSG.QuasiDihedralFusion
