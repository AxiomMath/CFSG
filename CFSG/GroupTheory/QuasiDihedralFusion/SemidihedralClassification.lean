module

public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralAutomizers

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.BenderSuzuki.External
open CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {H : Type u} [Group H] [Finite H] {n : ℕ}

section Focal

theorem focal_cases_ambient (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    (¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
        (FocalFusion.ambientHom n (S : Subgroup H) f (z n)) →
      ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
        (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3)))) →
      (commutator H).subgroupOf S = Subgroup.zpowers (f (r n) ^ 2)) ∧
    (IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
        (FocalFusion.ambientHom n (S : Subgroup H) f (z n)) →
      ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
        (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3)))) →
      (commutator H).subgroupOf S = Subgroup.closure {f (r n) ^ 2, f (s n)}) ∧
    (¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
        (FocalFusion.ambientHom n (S : Subgroup H) f (z n)) →
      IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
        (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3)))) →
      (commutator H).subgroupOf S = Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)}) ∧
    ((∀ K : Subgroup H, K.index ≠ 2) ↔
      IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
          (FocalFusion.ambientHom n (S : Subgroup H) f (z n)) ∧
        IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
          (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) := by
  obtain ⟨h1, h2, h3, -, h5⟩ := FocalFusion.semidihedral_focal_subgroup_four_cases n hn S f
  have hs : ((f (s n) : S) : H) = FocalFusion.ambientHom n (S : Subgroup H) f (s n) := rfl
  have hz : ((f (r n) ^ (2 ^ (n - 1) / 2) : S) : H) =
      FocalFusion.ambientHom n (S : Subgroup H) f (z n) := by
    rw [two_pow_div_two hn, ← map_pow]
    rfl
  have hrs : ((f (r n) * f (s n) : S) : H) =
      FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n) := by
    rw [← map_mul]
    rfl
  have hv : ((f (r n) ^ (2 ^ (n - 1) / 4) : S) : H) =
      FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))) := by
    rw [two_pow_div_four hn, ← map_pow]
    rfl
  rw [hs, hz, hrs, hv] at h1 h2 h3 h5
  exact ⟨h1, h2, h3, h5⟩

end Focal

section Elements

omit [Finite H] in
theorem conj_sdV_cases (hn : 4 ≤ n) (S : Subgroup H) (f : SemidihedralGroup n ≃* S) (t : H)
    (ht : t ∈ S) :
    t⁻¹ * FocalFusion.ambientHom n S f (r n ^ (2 ^ (n - 3))) * t =
        FocalFusion.ambientHom n S f (r n ^ (2 ^ (n - 3))) ∨
      t⁻¹ * FocalFusion.ambientHom n S f (r n ^ (2 ^ (n - 3))) * t =
        (FocalFusion.ambientHom n S f (r n ^ (2 ^ (n - 3))))⁻¹ := by
  obtain ⟨t₀, rfl⟩ := exists_ambientHom_eq S f t ht
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
  have hmem := (zpowers_sdV_normal (n := n) hn).conj_mem _ (Subgroup.mem_zpowers _) t₀⁻¹
  rw [inv_inv] at hmem
  have hrot : t₀⁻¹ * r n ^ (2 ^ (n - 3)) * t₀ ∈ rotationSubgroup n :=
    Subgroup.zpowers_le.mpr (sdV_mem_rotationSubgroup n) hmem
  have ho : orderOf (t₀⁻¹ * r n ^ (2 ^ (n - 3)) * t₀) = 4 := by
    rw [← orderOf_sdV hn]
    refine (conjugate_orderOf_eq (isConj_iff.mpr ⟨t₀⁻¹, ?_⟩)).symm
    rw [inv_inv]
  rcases sd_rotation_orderFour hn _ hrot ho with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

omit [Finite H] in
theorem centerOf_eq_zpowers_z (hn : 4 ≤ n) (S : Subgroup H) (f : SemidihedralGroup n ≃* S) :
    centerOf S = Subgroup.zpowers (FocalFusion.ambientHom n S f (z n)) := by
  apply le_antisymm
  · rintro x ⟨hxS, hxC⟩
    obtain ⟨x₀, rfl⟩ := exists_ambientHom_eq S f x hxS
    have hc : x₀ ∈ Subgroup.center (SemidihedralGroup n) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply FocalFusion.ambientHom_injective n S f
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hxC _ (ambientHom_mem S f y)
    rw [center_eq_zpowers n hn] at hc
    rw [← MonoidHom.map_zpowers]
    exact ⟨x₀, hc, rfl⟩
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨ambientHom_mem S f _, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := conj_ambient_z hn S f y hy
    calc y * FocalFusion.ambientHom n S f (z n) =
        y * FocalFusion.ambientHom n S f (z n) * y⁻¹ * y := by group
      _ = FocalFusion.ambientHom n S f (z n) * y := by rw [h]

end Elements

section Cases

theorem quaternion_kernel_noIndexTwo (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hb : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3)))))
    (K : Subgroup H) [K.Normal] (hK2 : K.index = 2)
    (hKS : K ⊓ (S : Subgroup H) =
      (Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)}).map (S : Subgroup H).subtype) :
    ∀ M : Subgroup K, M.index ≠ 2 := by
  intro M hM
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  let M' := M.map K.subtype
  have htop : K ⊔ (S : Subgroup H) = ⊤ :=
    normal_sup_sylow_eq_top K ⟨1, by rw [hK2, pow_one]⟩ S
  have e1 : (S : Subgroup H).subtype (f (r n) ^ 2) = ι (r n ^ 2) := by
    rw [← map_pow]
    rfl
  have e2 : (S : Subgroup H).subtype (f (r n) * f (s n)) = ι (r n * s n) := by
    rw [← map_mul]
    rfl
  have hKS' : K ⊓ (S : Subgroup H) = Subgroup.closure {ι (r n ^ 2), ι (r n * s n)} := by
    rw [hKS, MonoidHom.map_closure, Set.image_pair, e1, e2]
  have hle : Subgroup.closure {ι (r n ^ 2), ι (r n * s n)} ≤ K := by
    rw [← hKS']
    exact inf_le_left
  have hwK : ι (r n ^ 2) ∈ K := hle (Subgroup.subset_closure (Set.mem_insert _ _))
  have hyK : ι (r n * s n) ∈ K := hle (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hy3 : ι (r n ^ 3 * s n) = ι (r n ^ 2) * ι (r n * s n) := by
    rw [← map_mul, ← mul_assoc, ← pow_succ]
  have hy3K : ι (r n ^ 3 * s n) ∈ K := by
    rw [hy3]
    exact K.mul_mem hwK hyK
  have hvw : ι (r n ^ (2 ^ (n - 3))) = ι (r n ^ 2) ^ (2 ^ (n - 4)) := by
    rw [← map_pow, ← pow_mul]
    congr 2
    rw [← pow_succ']
    congr 1
    omega
  have hvK : ι (r n ^ (2 ^ (n - 3))) ∈ K := by
    rw [hvw]
    exact K.pow_mem hwK _
  have key : ∀ x : H, x ∈ K → IsConj x (ι (r n ^ (2 ^ (n - 3)))) →
      (x ∈ M' ↔ ι (r n ^ (2 ^ (n - 3))) ∈ M') := by
    intro x hx hxv
    obtain ⟨t, ht, hmem, hconj⟩ := exists_isConj_normal_of_isConj K (S : Subgroup H) htop hx hxv
    have h1 := map_subtype_mem_iff_of_isConj hM hx hmem hconj
    rcases conj_sdV_cases hn (S : Subgroup H) f t ht with h | h
    · rw [h] at h1
      exact h1
    · rw [h, Subgroup.inv_mem_iff] at h1
      exact h1
  have hy := key _ hyK hb
  have hy3v : IsConj (ι (r n ^ 3 * s n)) (ι (r n ^ (2 ^ (n - 3)))) := by
    refine IsConj.trans ?_ hb
    have h := odd_outside_conjugate n hn 1
    rw [show (2 : ℤ) * 1 + 1 = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
    exact (ι.map_isConj h).symm
  have hy3' := key _ hy3K hy3v
  have hw : ι (r n ^ 2) ∈ M' := by
    have h : ι (r n ^ 2) = ι (r n ^ 3 * s n) * (ι (r n * s n))⁻¹ := by
      rw [hy3, mul_inv_cancel_right]
    rw [h, map_subtype_mul_mem_iff hM hy3K (K.inv_mem hyK), Subgroup.inv_mem_iff, hy3', hy]
  have hv : ι (r n ^ (2 ^ (n - 3))) ∈ M' := by
    rw [hvw]
    exact M'.pow_mem hw _
  have hyM : ι (r n * s n) ∈ M' := hy.mpr hv
  apply inf_sylow_not_le_map_of_index_two S K hM
  rw [hKS', Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact hw
  · exact hyM

theorem dihedral_kernel_noIndexTwo (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (ha : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n)))
    (K : Subgroup H) [K.Normal] (hK2 : K.index = 2)
    (hKS : K ⊓ (S : Subgroup H) =
      (Subgroup.closure {f (r n) ^ 2, f (s n)}).map (S : Subgroup H).subtype) :
    ∀ M : Subgroup K, M.index ≠ 2 := by
  intro M hM
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  let M' := M.map K.subtype
  have htop : K ⊔ (S : Subgroup H) = ⊤ :=
    normal_sup_sylow_eq_top K ⟨1, by rw [hK2, pow_one]⟩ S
  have e1 : (S : Subgroup H).subtype (f (r n) ^ 2) = ι (r n ^ 2) := by
    rw [← map_pow]
    rfl
  have e2 : (S : Subgroup H).subtype (f (s n)) = ι (s n) := rfl
  have hKS' : K ⊓ (S : Subgroup H) = Subgroup.closure {ι (r n ^ 2), ι (s n)} := by
    rw [hKS, MonoidHom.map_closure, Set.image_pair, e1, e2]
  have hle : Subgroup.closure {ι (r n ^ 2), ι (s n)} ≤ K := by
    rw [← hKS']
    exact inf_le_left
  have hwK : ι (r n ^ 2) ∈ K := hle (Subgroup.subset_closure (Set.mem_insert _ _))
  have hsK : ι (s n) ∈ K := hle (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hws : ι (r n ^ 2 * s n) = ι (r n ^ 2) * ι (s n) := map_mul _ _ _
  have hwsK : ι (r n ^ 2 * s n) ∈ K := by
    rw [hws]
    exact K.mul_mem hwK hsK
  have hzw : ι (z n) = ι (r n ^ 2) ^ (2 ^ (n - 3)) := by
    rw [← map_pow, ← pow_mul]
    congr 1
    change r n ^ (2 ^ (n - 2)) = r n ^ (2 * 2 ^ (n - 3))
    congr 1
    rw [← pow_succ']
    congr 1
    omega
  have key : ∀ x : H, x ∈ K → IsConj x (ι (z n)) → (x ∈ M' ↔ ι (z n) ∈ M') := by
    intro x hx hxz
    obtain ⟨t, ht, hmem, hconj⟩ := exists_isConj_normal_of_isConj K (S : Subgroup H) htop hx hxz
    have h1 := map_subtype_mem_iff_of_isConj hM hx hmem hconj
    have hfix : t⁻¹ * ι (z n) * t = ι (z n) := by
      have h := conj_ambient_z hn (S : Subgroup H) f t⁻¹ ((S : Subgroup H).inv_mem ht)
      rwa [inv_inv] at h
    rw [hfix] at h1
    exact h1
  have hs := key _ hsK ha
  have hwsz : IsConj (ι (r n ^ 2 * s n)) (ι (z n)) := by
    refine IsConj.trans ?_ ha
    have h := even_outside_conjugate n hn 1
    rw [show (2 : ℤ) * 1 = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
    exact (ι.map_isConj h).symm
  have hws' := key _ hwsK hwsz
  have hw : ι (r n ^ 2) ∈ M' := by
    have h : ι (r n ^ 2) = ι (r n ^ 2 * s n) * (ι (s n))⁻¹ := by
      rw [hws, mul_inv_cancel_right]
    rw [h, map_subtype_mul_mem_iff hM hwsK (K.inv_mem hsK), Subgroup.inv_mem_iff, hws', hs]
  have hz : ι (z n) ∈ M' := by
    rw [hzw]
    exact M'.pow_mem hw _
  have hsM : ι (s n) ∈ M' := hs.mpr hz
  apply inf_sylow_not_le_map_of_index_two S K hM
  rw [hKS', Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact hw
  · exact hsM

omit [Finite H] in
theorem centerOf_weaklyClosed (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (ha : ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n))) :
    WeaklyClosedIn (S : Subgroup H) (centerOf (S : Subgroup H)) := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  rw [centerOf_eq_zpowers_z hn (S : Subgroup H) f]
  refine ⟨Subgroup.zpowers_le.mpr (ambientHom_mem (S : Subgroup H) f _), fun g hg => ?_⟩
  have hconj : rightConjugate (Subgroup.zpowers (ι (z n))) g =
      Subgroup.zpowers (g⁻¹ * ι (z n) * g) := by
    change (Subgroup.zpowers (ι (z n))).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [hconj] at hg ⊢
  have hmem : g⁻¹ * ι (z n) * g ∈ (S : Subgroup H) := hg (Subgroup.mem_zpowers _)
  obtain ⟨y₀, hy₀⟩ := exists_ambientHom_eq (S : Subgroup H) f _ hmem
  have ho : orderOf y₀ = 2 := by
    rw [← orderOf_ambientHom (S : Subgroup H) f, hy₀]
    have hc : IsConj (ι (z n)) (g⁻¹ * ι (z n) * g) := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
    rw [← conjugate_orderOf_eq hc, orderOf_ambientHom, orderOf_z n (by omega)]
  rcases sd_involution_cases hn y₀ ho with h | h
  · rw [← hy₀, h]
  · exfalso
    apply ha
    have h1 := ι.map_isConj h
    rw [hy₀] at h1
    exact h1.trans (isConj_iff.mpr ⟨g, by group⟩)

end Cases

section Alternatives

theorem semidihedralFusionQD_of (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (ha : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n)))
    (hb : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) :
    SemidihedralFusionQD S f where
  noIndexTwo := (focal_cases_ambient hn S f).2.2.2.mpr ⟨ha, hb⟩
  involutionClasses := involutionClassCount_eq_one hn S f ha
  orderFourClasses := orderFourClassCount_eq_one hn S f hb
  fourIndex := automizerIndex_qdFour_eq_six hn S f ha
  quaternionIndex := outerAutomizerIndex_qdQuaternion_eq_six hn S f hb

theorem semidihedralFusionQ_of (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (ha : ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n)))
    (hb : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) :
    SemidihedralFusionQ S f := by
  have hF := (focal_cases_ambient hn S f).2.2.1 ha hb
  obtain ⟨K, hK, hKindex, -, hKS⟩ := exists_focal_kernel S
  rw [hF] at hKindex hKS
  have hK2 : K.index = 2 := by
    rw [hKindex]
    exact (supplied_index_two n hn f _).mpr (Or.inr (Or.inr rfl))
  refine ⟨⟨K, hK, hK2, quaternion_kernel_noIndexTwo hn S f hb K hK2 hKS, ?_⟩,
    centerOf_weaklyClosed hn S f ha, involutionClassCount_eq_two hn S f ha,
    orderFourClassCount_eq_one hn S f hb, automizerIndex_qdFour_eq_two hn S f ha,
    outerAutomizerIndex_qdQuaternion_eq_six hn S f hb⟩
  intro P
  obtain ⟨eP⟩ := nonempty_sylow_equiv_inf S K P
  refine ⟨n - 3, by omega, ⟨eP.trans ((MulEquiv.subgroupCongr hKS).trans
    ((Subgroup.equivMapOfInjective _ _ (S : Subgroup H).subtype_injective).symm.trans
      (suppliedQuaternionEquiv n hn f).symm))⟩⟩

theorem semidihedralFusionD_of (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (ha : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n)))
    (hb : ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) :
    SemidihedralFusionD S f := by
  have hF := (focal_cases_ambient hn S f).2.1 ha hb
  obtain ⟨K, hK, hKindex, -, hKS⟩ := exists_focal_kernel S
  rw [hF] at hKindex hKS
  have hK2 : K.index = 2 := by
    rw [hKindex]
    exact (supplied_index_two n hn f _).mpr (Or.inr (Or.inl rfl))
  refine ⟨⟨K, hK, hK2, dihedral_kernel_noIndexTwo hn S f ha K hK2 hKS, ?_⟩,
    involutionClassCount_eq_one hn S f ha, orderFourClassCount_eq_two hn S f hb,
    automizerIndex_qdFour_eq_six hn S f ha, outerAutomizerIndex_qdQuaternion_eq_two hn S f hb⟩
  intro P
  obtain ⟨eP⟩ := nonempty_sylow_equiv_inf S K P
  refine ⟨n - 2, by omega, ⟨eP.trans ((MulEquiv.subgroupCongr hKS).trans
    ((Subgroup.equivMapOfInjective _ _ (S : Subgroup H).subtype_injective).symm.trans
      (suppliedDihedralEquiv n hn f).symm))⟩⟩

theorem semidihedralFusionComplement_of (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S)
    (ha : ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n)))
    (hb : ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) :
    SemidihedralFusionComplement S f := by
  have hF := (focal_cases_ambient hn S f).1 ha hb
  obtain ⟨K, hK, -, hKpow, hKS⟩ := exists_focal_kernel S
  rw [hF] at hKS
  have hcyc : IsCyclic (K ⊓ (S : Subgroup H) : Subgroup H) :=
    ((MulEquiv.subgroupCongr hKS).trans
      (Subgroup.equivMapOfInjective _ _ (S : Subgroup H).subtype_injective).symm).isCyclic.mpr
      inferInstance
  exact ⟨hasNormalPComplement_of_cyclic_kernel S K hKpow hcyc,
    involutionClassCount_eq_two hn S f ha, orderFourClassCount_eq_two hn S f hb,
    automizerIndex_qdFour_eq_two hn S f ha, outerAutomizerIndex_qdQuaternion_eq_two hn S f hb⟩

theorem semidihedral_two_fusion_classification {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    SemidihedralFusionQD S f ∨ SemidihedralFusionQ S f ∨ SemidihedralFusionD S f ∨
      SemidihedralFusionComplement S f := by
  by_cases ha : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n)) <;>
    by_cases hb : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))
  · exact Or.inl (semidihedralFusionQD_of hn S f ha hb)
  · exact Or.inr (Or.inr (Or.inl (semidihedralFusionD_of hn S f ha hb)))
  · exact Or.inr (Or.inl (semidihedralFusionQ_of hn S f ha hb))
  · exact Or.inr (Or.inr (Or.inr (semidihedralFusionComplement_of hn S f ha hb)))

end Alternatives

end CFSG.QuasiDihedralFusion
