module

public import CFSG.GroupTheory.QuasiDihedralFusion.Defs

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.Wreathed CFSG.GorensteinWalter
open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFchapter1section1

universe u v

variable {H : Type u} [Group H] {H' : Type v} [Group H']

section Basic

theorem toMonoidHom_surjective (σ : H ≃* H') : Function.Surjective σ.toMonoidHom := by
  rw [MulEquiv.coe_toMonoidHom]
  exact σ.surjective

theorem noIndexTwo_of_mulEquiv {A : Type*} {B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ M : Subgroup A, M.index ≠ 2) : ∀ M : Subgroup B, M.index ≠ 2 := by
  intro M hM
  apply h (M.comap e.toMonoidHom)
  rw [Subgroup.index_comap_of_surjective _ e.surjective, hM]

theorem index_map_mulEquiv (σ : H ≃* H') (K : Subgroup H) :
    (K.map σ.toMonoidHom).index = K.index := by
  rw [Subgroup.index_map_of_injective _ σ.injective,
    MonoidHom.range_eq_top.mpr σ.surjective, Subgroup.index_top, mul_one]

theorem isMulCommutative_of_mulEquiv {A : Type*} {B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsMulCommutative A) : IsMulCommutative B := by
  rw [isMulCommutative_iff] at h ⊢
  intro a b
  apply e.symm.injective
  rw [map_mul, map_mul, h]

theorem exists_sylow_equiv [Finite H'] {p : ℕ} [Fact p.Prime] (σ : H ≃* H') (S' : Sylow p H') :
    ∃ S : Sylow p H, Nonempty ((S : Subgroup H) ≃* S') := by
  refine ⟨S'.mapSurjective (toMonoidHom_surjective σ.symm), ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _)).trans
    ((S' : Subgroup H').equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective).symm

theorem HasSemidihedralSylow.of_mulEquiv [Finite H'] (σ : H ≃* H') {n : ℕ}
    (h : HasSemidihedralSylow H n) : HasSemidihedralSylow H' n := by
  refine ⟨h.1, fun S' => ?_⟩
  obtain ⟨S, ⟨eS⟩⟩ := exists_sylow_equiv σ S'
  obtain ⟨f⟩ := h.2 S
  exact ⟨f.trans eS⟩

theorem HasWreathedSylow.of_mulEquiv [Finite H'] (σ : H ≃* H') {n : ℕ}
    (h : HasWreathedSylow H n) : HasWreathedSylow H' n := by
  refine ⟨h.1, fun S' => ?_⟩
  obtain ⟨S, ⟨eS⟩⟩ := exists_sylow_equiv σ S'
  obtain ⟨e⟩ := h.2 S
  exact ⟨eS.symm.trans e⟩

theorem HasQDOrWreathedSylowOfHeight.of_mulEquiv [Finite H'] (σ : H ≃* H') {h : ℕ}
    (hH : HasQDOrWreathedSylowOfHeight H h) : HasQDOrWreathedSylowOfHeight H' h := by
  rcases hH with ⟨h1, n, hn⟩ | hw
  · exact Or.inl ⟨h1, n, hn.of_mulEquiv σ⟩
  · exact Or.inr (hw.of_mulEquiv σ)

theorem HasQDOrWreathedSylow.of_mulEquiv [Finite H'] (σ : H ≃* H')
    (hH : HasQDOrWreathedSylow H) : HasQDOrWreathedSylow H' := by
  obtain ⟨h, hh⟩ := hH
  exact ⟨h, hh.of_mulEquiv σ⟩

theorem HasGeneralizedQuaternionSylow.of_mulEquiv [Finite H'] (σ : H ≃* H')
    (hH : HasGeneralizedQuaternionSylow H) : HasGeneralizedQuaternionSylow H' := by
  intro S'
  obtain ⟨S, ⟨eS⟩⟩ := exists_sylow_equiv σ S'
  obtain ⟨k, hk, ⟨e⟩⟩ := hH S
  exact ⟨k, hk, ⟨eS.symm.trans e⟩⟩

theorem hasNormalPComplement_of_mulEquiv [Finite H] (σ : H ≃* H')
    (h : HasNormalPComplement 2 H) : HasNormalPComplement 2 H' := by
  obtain ⟨N, hN, hcop, hq⟩ := h
  have hN' : (N.map σ.toMonoidHom).Normal := hN.map _ (toMonoidHom_surjective σ)
  refine ⟨N.map σ.toMonoidHom, hN', ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective σ.injective]
    exact hcop
  · exact hq.of_equiv (QuotientGroup.congr N (N.map σ.toMonoidHom) σ rfl)

theorem conjClassCountOfOrder_of_mulEquiv (σ : H ≃* H') (k : ℕ) :
    conjClassCountOfOrder H' k = conjClassCountOfOrder H k := by
  have himage : ConjClasses.mk '' {x : H' | orderOf x = k} =
      (ConjClasses.map σ.toMonoidHom) '' (ConjClasses.mk '' {x : H | orderOf x = k}) := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ConjClasses.mk (σ.symm x), ⟨σ.symm x, ?_, rfl⟩, ?_⟩
      · change orderOf (σ.symm x) = k
        rw [MulEquiv.orderOf_eq]
        exact hx
      · change ConjClasses.mk (σ (σ.symm x)) = _
        rw [MulEquiv.apply_symm_apply]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨σ x, ?_, rfl⟩
      change orderOf (σ x) = k
      rw [MulEquiv.orderOf_eq]
      exact hx
  rw [conjClassCountOfOrder, himage, conjClassCountOfOrder]
  apply Set.ncard_image_of_injective
  intro a b hab
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective a
  obtain ⟨y, rfl⟩ := ConjClasses.mk_surjective b
  change ConjClasses.mk (σ x) = ConjClasses.mk (σ y) at hab
  rw [ConjClasses.mk_eq_mk_iff_isConj] at hab ⊢
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
    σ.symm.toMonoidHom.map_isConj hab

end Basic

section Subgroups

theorem centerOf_map (σ : H ≃* H') (R : Subgroup H) :
    centerOf (R.map σ.toMonoidHom) = (centerOf R).map σ.toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [centerOf, Subgroup.mem_inf] at hx
    obtain ⟨⟨r, hr, rfl⟩, hc⟩ := hx
    refine ⟨r, Subgroup.mem_inf.mpr ⟨hr, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    apply σ.injective
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hc (σ y) ⟨y, hy, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨hr, hc⟩ := Subgroup.mem_inf.mp hr
    refine Subgroup.mem_inf.mpr ⟨⟨r, hr, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hc y hy]

theorem rightConjugate_map_mulEquiv (σ : H ≃* H') (Z : Subgroup H) (g : H) :
    rightConjugate (Z.map σ.toMonoidHom) (σ g) = (rightConjugate Z g).map σ.toMonoidHom := by
  change (Z.map σ.toMonoidHom).map (MulAut.conj (σ g)⁻¹).toMonoidHom =
    (Z.map (MulAut.conj g⁻¹).toMonoidHom).map σ.toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  change (σ g)⁻¹ * σ x * ((σ g)⁻¹)⁻¹ = σ (g⁻¹ * x * g⁻¹⁻¹)
  simp only [map_mul, map_inv]

theorem WeaklyClosedIn.map_mulEquiv (σ : H ≃* H') {R Z : Subgroup H} (h : WeaklyClosedIn R Z) :
    WeaklyClosedIn (R.map σ.toMonoidHom) (Z.map σ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, fun g' hg' => ?_⟩
  obtain ⟨g, rfl⟩ := σ.surjective g'
  rw [rightConjugate_map_mulEquiv] at hg' ⊢
  have hle : rightConjugate Z g ≤ R := (Subgroup.map_le_map_iff_of_injective σ.injective).mp hg'
  rw [h.2 g hle]

theorem subgroupOf_map_equivMap (σ : H ≃* H') (R Y : Subgroup H) :
    ((Y.map σ.toMonoidHom).subgroupOf (R.map σ.toMonoidHom)).map
        (R.equivMapOfInjective σ.toMonoidHom σ.injective).symm.toMonoidHom = Y.subgroupOf R := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf]
  change σ (x : H) ∈ Y.map σ.toMonoidHom ↔ (x : H) ∈ Y
  exact Subgroup.mem_map_iff_mem σ.injective

theorem IsMaximalQuaternionIn.map_mulEquiv (σ : H ≃* H') {R Y : Subgroup H}
    (h : IsMaximalQuaternionIn R Y) :
    IsMaximalQuaternionIn (R.map σ.toMonoidHom) (Y.map σ.toMonoidHom) := by
  obtain ⟨hYR, hpos⟩ := h
  let eR := R.equivMapOfInjective σ.toMonoidHom σ.injective
  refine ⟨Subgroup.map_mono hYR, ?_⟩
  rcases hpos with ⟨n, hn, ι, hι, himg⟩ | ⟨n, hn, ι, hι, himg⟩
  · refine Or.inl ⟨n, hn, ι.comp eR.symm.toMonoidHom, hι.comp eR.symm.injective, ?_⟩
    rw [← Subgroup.map_map, subgroupOf_map_equivMap, himg]
  · refine Or.inr ⟨n, hn, ι.comp eR.symm.toMonoidHom, hι.comp eR.symm.injective, ?_⟩
    rw [← Subgroup.map_map, subgroupOf_map_equivMap, himg]

end Subgroups

section Classes

theorem IsQGroupData.map_mulEquiv [Finite H] (σ : H ≃* H') {R : Sylow 2 H} {K : Subgroup H}
    (h : IsQGroupData R K) :
    IsQGroupData (R.mapSurjective (toMonoidHom_surjective σ)) (K.map σ.toMonoidHom) where
  normal := h.normal.map _ (toMonoidHom_surjective σ)
  index_eq_two_pow := by
    obtain ⟨k, hk⟩ := h.index_eq_two_pow
    exact ⟨k, by rw [index_map_mulEquiv]; exact hk⟩
  noIndexTwo := noIndexTwo_of_mulEquiv (K.equivMapOfInjective _ σ.injective) h.noIndexTwo
  quaternion := by
    rw [Sylow.coe_mapSurjective, ← Subgroup.map_inf_eq _ _ _ σ.injective]
    exact h.quaternion.map_mulEquiv σ
  center_weaklyClosed := by
    intro Z₀ hZ₀
    rw [Sylow.coe_mapSurjective] at hZ₀ ⊢
    rw [centerOf_map] at hZ₀
    have hZ : Z₀ = (Z₀.map σ.symm.toMonoidHom).map σ.toMonoidHom := by
      rw [Subgroup.map_map]
      conv_lhs => rw [← Subgroup.map_id Z₀]
      congr 1
      ext x
      simp
    rw [hZ]
    apply WeaklyClosedIn.map_mulEquiv
    apply h.center_weaklyClosed
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hZ₀ hy
    simpa using hc

theorem IsQGroup.of_mulEquiv [Finite H] [Finite H'] (e : H ≃* H') (hH : IsQGroup H) :
    IsQGroup H' := by
  obtain ⟨R, K, h⟩ := hH
  exact ⟨_, _, h.map_mulEquiv e⟩

theorem IsQDGroup.of_mulEquiv [Finite H] [Finite H'] (e : H ≃* H') (hH : IsQDGroup H) :
    IsQDGroup H' where
  sylow := hH.sylow.of_mulEquiv e
  noIndexTwo := noIndexTwo_of_mulEquiv e hH.noIndexTwo
  involutions_isConj x y hx hy := by
    have h := hH.involutions_isConj (e.symm x) (e.symm y)
      (by rw [MulEquiv.orderOf_eq]; exact hx) (by rw [MulEquiv.orderOf_eq]; exact hy)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
      e.toMonoidHom.map_isConj h

theorem IsDGroupData.map_mulEquiv [Finite H] [Finite H'] (σ : H ≃* H') {K : Subgroup H}
    (h : IsDGroupData K) :
    IsDGroupData (K.map σ.toMonoidHom) where
  normal := h.normal.map _ (toMonoidHom_surjective σ)
  index_eq_two := by rw [index_map_mulEquiv]; exact h.index_eq_two
  noIndexTwo := noIndexTwo_of_mulEquiv (K.equivMapOfInjective _ σ.injective) h.noIndexTwo
  sylow := by
    rcases h.sylow with ⟨n, hH, hK⟩ | ⟨n, hH, hK⟩
    · exact Or.inl ⟨n, hH.of_mulEquiv σ,
        hasDihedralSylowTwo_of_mulEquiv (K.equivMapOfInjective _ σ.injective).symm hK⟩
    · refine Or.inr ⟨n, hH.of_mulEquiv σ, fun P => ?_⟩
      obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_equiv (K.equivMapOfInjective _ σ.injective) P
      exact isMulCommutative_of_mulEquiv eQ (hK Q)

theorem IsDGroup.of_mulEquiv [Finite H] [Finite H'] (e : H ≃* H') (hH : IsDGroup H) :
    IsDGroup H' := by
  rcases hH with ⟨hD, hc⟩ | ⟨K, hK⟩
  · exact Or.inl ⟨hasDihedralSylowTwo_of_mulEquiv e.symm hD,
      fun h => hc (hasNormalPComplement_of_mulEquiv e.symm h)⟩
  · exact Or.inr ⟨_, hK.map_mulEquiv e⟩

end Classes

section Conjugation

theorem map_conj_eq_of_normal (K : Subgroup H) [hK : K.Normal] (g : H) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    exact hK.conj_mem k hk g
  · intro k hk
    refine ⟨g⁻¹ * k * g, ?_, ?_⟩
    · have h := hK.conj_mem k hk g⁻¹
      rwa [inv_inv] at h
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem IsQGroup.exists_data [Finite H] (hH : IsQGroup H) (R : Sylow 2 H) :
    ∃ K : Subgroup H, IsQGroupData R K := by
  obtain ⟨R₀, K, h⟩ := hH
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H R₀ R
  have h' := h.map_mulEquiv (MulAut.conj g)
  have hK : K.Normal := h.normal
  rw [map_conj_eq_of_normal K g] at h'
  have hR : R₀.mapSurjective (toMonoidHom_surjective (MulAut.conj g)) = R := by
    rw [← hg]
    apply Sylow.ext
    rw [Sylow.coe_mapSurjective, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hR] at h'
  exact ⟨K, h'⟩

end Conjugation

end CFSG.QuasiDihedralFusion
