module

public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotientsSupport
public import CFSG.GroupTheory.QuasiDihedralFusion.Defs

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral

universe u

section Model

variable {n : ℕ}

theorem z_mem_rotationSubgroup (n : ℕ) : z n ∈ rotationSubgroup n :=
  Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem sdV_mem_rotationSubgroup (n : ℕ) : r n ^ (2 ^ (n - 3)) ∈ rotationSubgroup n :=
  Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem s_not_mem_rotationSubgroup (hn : 4 ≤ n) : s n ∉ rotationSubgroup n := by
  rw [s_eq_element n (by omega), element_mem_rotationSubgroup_iff]
  decide

theorem rs_not_mem_rotationSubgroup (hn : 4 ≤ n) : r n * s n ∉ rotationSubgroup n := by
  intro h
  have hr : r n ∈ rotationSubgroup n := Subgroup.mem_zpowers _
  have hs := (rotationSubgroup n).mul_mem ((rotationSubgroup n).inv_mem hr) h
  rw [inv_mul_cancel_left] at hs
  exact s_not_mem_rotationSubgroup hn hs

theorem s_ne_z (hn : 4 ≤ n) : s n ≠ z n := fun h =>
  s_not_mem_rotationSubgroup hn (h ▸ z_mem_rotationSubgroup n)

theorem s_not_mem_zpowers_z (hn : 4 ≤ n) : s n ∉ Subgroup.zpowers (z n) := fun h =>
  s_not_mem_rotationSubgroup hn
    ((Subgroup.zpowers_le.mpr (z_mem_rotationSubgroup n)) h)

theorem two_pow_div_two (hn : 4 ≤ n) : 2 ^ (n - 1) / 2 = half n :=
  modulus_div_two n (by omega)

theorem two_pow_div_four (hn : 4 ≤ n) : 2 ^ (n - 1) / 4 = 2 ^ (n - 3) :=
  modulus_div_four n hn

theorem sdFourSubgroup_isKleinFour (hn : 4 ≤ n) : IsKleinFour (sdFourSubgroup n) := by
  have h := (Local.semidihedral_four_subgroup_centralizers n hn
    (MulEquiv.refl (SemidihedralGroup n))).1 (s n) (orderOf_s n (by omega))
  have hz : (MulEquiv.refl (SemidihedralGroup n)) (r n) ^ (2 ^ (n - 1) / 2) = z n := by
    rw [MulEquiv.refl_apply, two_pow_div_two hn]
    rfl
  rw [hz] at h
  exact (h (s_not_mem_zpowers_z hn)).2

theorem sdQuaternionEight_equiv (hn : 4 ≤ n) :
    Nonempty (sdQuaternionEight n ≃* QuaternionGroup 2) := by
  have h := (Local.quaternion_eight_subgroups_and_normalizers n hn
    (MulEquiv.refl (SemidihedralGroup n))).1 (sdQuaternionEight n)
  simp only [MulEquiv.refl_apply, two_pow_div_four hn] at h
  apply h.mpr
  refine ⟨1, odd_one, ?_⟩
  rw [zpow_one]
  rfl

theorem orderOf_rs (hn : 4 ≤ n) : orderOf (r n * s n) = 4 := by
  have h := odd_reflection_order n (by omega) 0
  simpa only [mul_zero, zero_add, zpow_one] using h

theorem orderOf_sdV (hn : 4 ≤ n) : orderOf (r n ^ (2 ^ (n - 3))) = 4 := by
  rw [r_pow_eq_element n (by omega), rotation_order_four_iff n hn]
  exact Or.inl rfl

theorem sdV_isConj_inv (hn : 4 ≤ n) : IsConj (r n ^ (2 ^ (n - 3))) (r n ^ (2 ^ (n - 3)))⁻¹ := by
  have h := quarter_inverse_conjugate n hn
  rwa [zpow_neg, zpow_natCast] at h

theorem sd_involution_cases (hn : 4 ≤ n) (g : SemidihedralGroup n) (hg : orderOf g = 2) :
    g = z n ∨ IsConj (s n) g := by
  rcases (involution_iff n (by omega) g).mp hg with h | ⟨j, rfl⟩
  · exact Or.inl h
  · refine Or.inr ?_
    have h := even_outside_conjugate n hn (j.val : ℤ)
    change IsConj (s n) (r n ^ ((2 : ℕ) * j.val : ℤ) * s n) at h
    rw [← Int.natCast_mul, zpow_natCast] at h
    exact h

theorem sd_orderFour_cases (hn : 4 ≤ n) (g : SemidihedralGroup n) (hg : orderOf g = 4) :
    IsConj (r n ^ (2 ^ (n - 3))) g ∨ IsConj (r n * s n) g := by
  have hn3 : 3 ≤ n := le_trans (by norm_num) hn
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn3).symm.surjective g
  change orderOf (element n (by omega) i e) = 4 at hg
  change IsConj (r n ^ (2 ^ (n - 3))) (element n (by omega) i e) ∨
    IsConj (r n * s n) (element n (by omega) i e)
  rcases exponent_cases e with rfl | rfl
  · exact Or.inl (rotation_four_conjugate_quarter n hn i hg).symm
  · exact Or.inr (odd_exterior_conjugate n hn i
      ((outside_order_four_iff n (by omega) i).mp hg))

theorem sd_rotation_orderFour (hn : 4 ≤ n) (g : SemidihedralGroup n) (hgr : g ∈ rotationSubgroup n)
    (hg : orderOf g = 4) : g = r n ^ (2 ^ (n - 3)) ∨ g = (r n ^ (2 ^ (n - 3)))⁻¹ := by
  have hn3 : 3 ≤ n := le_trans (by norm_num) hn
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn3).symm.surjective g
  change element n (by omega) i e ∈ rotationSubgroup n at hgr
  change orderOf (element n (by omega) i e) = 4 at hg
  change element n (by omega) i e = r n ^ (2 ^ (n - 3)) ∨
    element n (by omega) i e = (r n ^ (2 ^ (n - 3)))⁻¹
  rw [element_mem_rotationSubgroup_iff] at hgr
  subst hgr
  rcases (rotation_order_four_iff n hn i).mp hg with rfl | rfl
  · exact Or.inl (r_pow_eq_element n (by omega) _).symm
  · refine Or.inr ?_
    rw [← zpow_natCast, ← zpow_neg, negative_quarter_eq_element n hn]

theorem zpowers_sdV_normal (hn : 4 ≤ n) : (Subgroup.zpowers (r n ^ (2 ^ (n - 3)))).Normal := by
  have hconj : ∀ g : SemidihedralGroup n,
      g * r n ^ (2 ^ (n - 3)) * g⁻¹ ∈ Subgroup.zpowers (r n ^ (2 ^ (n - 3))) := by
    intro g
    have hr := (rotationSubgroup_normal n (by omega)).conj_mem _ (sdV_mem_rotationSubgroup n) g
    have ho : orderOf (g * r n ^ (2 ^ (n - 3)) * g⁻¹) = 4 := by
      rw [← orderOf_sdV hn]
      exact (conjugate_orderOf_eq (isConj_iff.mpr ⟨g, rfl⟩)).symm
    rcases sd_rotation_orderFour hn _ hr ho with h | h
    · rw [h]
      exact Subgroup.mem_zpowers _
    · rw [h]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  refine ⟨fun y hy g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  exact Subgroup.zpow_mem _ (hconj g) k

theorem z_mem_sdFourSubgroup (n : ℕ) : z n ∈ sdFourSubgroup n :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem s_mem_sdFourSubgroup (n : ℕ) : s n ∈ sdFourSubgroup n :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sdV_mem_sdQuaternionEight (n : ℕ) : r n ^ (2 ^ (n - 3)) ∈ sdQuaternionEight n :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem rs_mem_sdQuaternionEight (n : ℕ) : r n * s n ∈ sdQuaternionEight n :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end Model

section Ambient

variable {H : Type u} [Group H] {n : ℕ}

theorem map_conj_map {A : Type*} [Group A] (P : Subgroup A) (ι : A →* H) (a : A) :
    (P.map (MulAut.conj a).toMonoidHom).map ι = (P.map ι).map (MulAut.conj (ι a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem map_conj_mul (P : Subgroup H) (a b : H) :
    (P.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      P.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

theorem mem_normalizer_of_map_conj_eq {P : Subgroup H} {h : H}
    (hP : P.map (MulAut.conj h).toMonoidHom = P) : h ∈ Subgroup.normalizer (P : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hP]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hP] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at hyx
    rw [← hyx]
    exact hy

theorem ambientHom_mem (S : Subgroup H) (f : SemidihedralGroup n ≃* S)
    (x : SemidihedralGroup n) : FocalFusion.ambientHom n S f x ∈ S := (f x).property

theorem map_ambientHom_le (S : Subgroup H) (f : SemidihedralGroup n ≃* S)
    (P : Subgroup (SemidihedralGroup n)) : P.map (FocalFusion.ambientHom n S f) ≤ S := by
  rintro _ ⟨x, -, rfl⟩
  exact ambientHom_mem S f x

theorem qdFour_le (S : Subgroup H) (f : SemidihedralGroup n ≃* S) : qdFour S f ≤ S :=
  map_ambientHom_le S f _

theorem qdQuaternion_le (S : Subgroup H) (f : SemidihedralGroup n ≃* S) :
    qdQuaternion S f ≤ S :=
  map_ambientHom_le S f _

@[expose] noncomputable def mapAmbientEquiv (S : Subgroup H) (f : SemidihedralGroup n ≃* S)
    (P : Subgroup (SemidihedralGroup n)) : P ≃* P.map (FocalFusion.ambientHom n S f) :=
  P.equivMapOfInjective _ (FocalFusion.ambientHom_injective n S f)

theorem qdFour_isKleinFour (hn : 4 ≤ n) (S : Subgroup H) (f : SemidihedralGroup n ≃* S) :
    IsKleinFour (qdFour S f) := by
  have := sdFourSubgroup_isKleinFour hn
  exact Local.isKleinFour_of_mulEquiv (mapAmbientEquiv S f (sdFourSubgroup n))

theorem qdQuaternion_equiv (hn : 4 ≤ n) (S : Subgroup H) (f : SemidihedralGroup n ≃* S) :
    Nonempty (qdQuaternion S f ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := sdQuaternionEight_equiv hn
  exact ⟨(mapAmbientEquiv S f (sdQuaternionEight n)).symm.trans e⟩

theorem map_comap_ambientHom (S : Subgroup H) (f : SemidihedralGroup n ≃* S) (W : Subgroup H)
    (hWS : W ≤ S) : (W.comap (FocalFusion.ambientHom n S f)).map
      (FocalFusion.ambientHom n S f) = W := by
  apply Subgroup.map_comap_eq_self
  rw [FocalFusion.ambientHom_range]
  exact hWS

theorem exists_conj_eq_qdFour (hn : 4 ≤ n) (S : Subgroup H) (f : SemidihedralGroup n ≃* S)
    (W : Subgroup H) (hWS : W ≤ S) [IsKleinFour W] :
    ∃ w ∈ S, W = (qdFour S f).map (MulAut.conj w).toMonoidHom := by
  let ι := FocalFusion.ambientHom n S f
  let W₀ := W.comap ι
  have hW₀ : W₀.map ι = W := map_comap_ambientHom S f W hWS
  have : IsKleinFour W₀ :=
    Local.isKleinFour_of_mulEquiv ((W₀.equivMapOfInjective ι
      (FocalFusion.ambientHom_injective n S f)).trans (MulEquiv.subgroupCongr hW₀)).symm
  have := sdFourSubgroup_isKleinFour hn
  obtain ⟨g, -, hg⟩ := Local.kleinFour_conj hn (MulEquiv.refl (SemidihedralGroup n))
    (sdFourSubgroup n) W₀
  refine ⟨ι g, ambientHom_mem S f g, ?_⟩
  rw [← hW₀, hg, map_conj_map]
  rfl

theorem exists_conj_eq_qdQuaternion (hn : 4 ≤ n) (S : Subgroup H)
    (f : SemidihedralGroup n ≃* S) (W : Subgroup H) (hWS : W ≤ S)
    (hW : Nonempty (W ≃* QuaternionGroup 2)) :
    ∃ w ∈ S, W = (qdQuaternion S f).map (MulAut.conj w).toMonoidHom := by
  let ι := FocalFusion.ambientHom n S f
  let W₀ := W.comap ι
  have hW₀ : W₀.map ι = W := map_comap_ambientHom S f W hWS
  obtain ⟨eW⟩ := hW
  have hW₀Q : Nonempty (W₀ ≃* QuaternionGroup 2) :=
    ⟨((W₀.equivMapOfInjective ι (FocalFusion.ambientHom_injective n S f)).trans
      (MulEquiv.subgroupCongr hW₀)).trans eW⟩
  obtain ⟨g, -, hg⟩ := (Local.quaternion_eight_subgroups_and_normalizers n hn
    (MulEquiv.refl (SemidihedralGroup n))).2.1 (sdQuaternionEight n) W₀
    (sdQuaternionEight_equiv hn) hW₀Q
  refine ⟨ι g, ambientHom_mem S f g, ?_⟩
  rw [← hW₀, hg, map_conj_map]
  rfl

end Ambient

end CFSG.QuasiDihedralFusion
