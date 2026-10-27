module

public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterFiveTorusNormalizerSupport
public import CFSG.CharacterTheory.Semidihedral.Local.PerfectFullLocalFusion
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveSeventeenSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem perfect_parameter_five_trivial_core_three_torus_inversion_normalizer {G : Type}
    [Group G] [Finite G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (hN : N t = ⊥) :
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let M : Subgroup G := Subgroup.normalizer (V : Set G)
    n = 4 ∧ Nat.card (C t) = 240 ∧ IsCyclic W ∧ Nat.card W = 3 ∧
      (V ⊔ W = D ∧ Disjoint V W ∧ ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) ∧ Nat.card D = 12 ∧
      C t ⊓ K = D ∧ C t ⊓ H = C t ⊓ M ∧ Nat.card (C t ⊓ H : Subgroup G) = 24 ∧
      (∃ d ∈ C t ⊓ H, orderOf d = 4 ∧ d ^ 2 = t ∧ d * s₀ * d⁻¹ = t * s₀ ∧
        (∀ w ∈ W, d * w * d⁻¹ = w⁻¹) ∧
        Nonempty ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≃* DihedralGroup 4) ∧
        Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) = 8 ∧
        ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype =
          Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
      (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = V) ∧
      K.relIndex H = 2 ∧ (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      M ≤ H ∧ Nat.card M = 72 ∧ Nat.card (K ⊓ M : Subgroup G) = 36 ∧ K ⊓ D = D := by
  intro s₀ V
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨hzt, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  let sC : C t := ⟨s₀, hsC⟩
  have hsC2 : orderOf sC = 2 := by rw [← Subgroup.orderOf_coe]; exact hs2
  have hsCt : sC ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  obtain ⟨hC, hDs, hRs, hKs, hDmap, hVmap, d, hd4, hd2, hds, hinv⟩ :=
    parameter_five_trivial_core_four_group_data n hn S fS hG t ht2 hnonab hcentral hnc hmodel hN
      sC hsC2 hsCt
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have hSC : (S : Subgroup G) ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hzt]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn))
      (fS.symm ⟨x, hx⟩)
    have h' := congrArg (fun w => ((fS w : S) : G)) h
    simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using h'
  have hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t := by
    intro x hx hx4
    have hy : orderOf (fS.symm ⟨x, hx⟩) = 4 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hx4
    have h := congrArg (fun w => ((fS w : S) : G))
      (semidihedral_order_four_square n hn _ hy)
    simpa only [map_pow, Subgroup.coe_pow, MulEquiv.apply_symm_apply, hzt] using h
  have hn4 : n = 4 := by
    have h := Subgroup.card_dvd_of_le hSC
    rw [hC, ← Nat.card_congr fS.toEquiv, CFSG.Semidihedral.card n (by omega)] at h
    have h5 : ¬ 2 ^ 5 ∣ 240 := by norm_num
    by_contra hne
    exact h5 ((pow_dvd_pow 2 (by omega : 5 ≤ n)).trans h)
  have hDG : Subgroup.centralizer (V : Set G) =
      (ActualFourGroupCentralizer.D sC).map (C t).subtype := by
    rw [hDmap, centralizer_zpowers_sup_zpowers]
  have hDcard : Nat.card (Subgroup.centralizer (V : Set G)) = 12 := by
    rw [hDG, Subgroup.card_map_of_injective (C t).subtype_injective, hDs]
  set W₀ : Subgroup G := ((ActualFourGroupCentralizer.R sC).map
    (ActualFourGroupCentralizer.D sC).subtype).map (C t).subtype with hW₀def
  have hW₀D : W₀ ≤ Subgroup.centralizer (V : Set G) := by
    rw [hDG]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hW₀card : Nat.card W₀ = 3 := by
    rw [hW₀def, Subgroup.card_map_of_injective (C t).subtype_injective,
      Subgroup.card_map_of_injective (ActualFourGroupCentralizer.D sC).subtype_injective, hRs]
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hDC : Subgroup.centralizer (V : Set G) ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx t htV).symm
  have hW₀C : W₀ ≤ C t := hW₀D.trans hDC
  have hnot : ¬ C t ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro hle
    have hnormal : (W₀.subgroupOf (C t)).Normal := by
      refine ⟨fun x hx c => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (Subgroup.mem_normalizer_iff.mp (hle c.2) x).mp hx
    have hcard : Nat.card (W₀.subgroupOf (C t)) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₀C).toEquiv, hW₀card]
    have hleN : W₀.subgroupOf (C t) ≤ N t := le_sSup ⟨hnormal, by rw [hcard]; norm_num⟩
    rw [hN, le_bot_iff] at hleN
    rw [hleN, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hVS : V ≤ (S : Subgroup G) := by
    have htS : t ∈ (S : Subgroup G) := by
      rw [ht]
      exact Subgroup.pow_mem _ (fS (r n)).property _
    exact sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr (fS (s n)).property)
  have hfus := (CFSG.Semidihedral.Local.perfect_semidihedral_full_local_fusion n hn S fS).1 V
    hVS hV
  have hMcard : Nat.card (Subgroup.normalizer (V : Set G)) = 72 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V.normalizerMonoidHom.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange V.normalizerMonoidHom).toEquiv,
      hfus.2, Subgroup.normalizerMonoidHom_ker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer (V : Set G))).toEquiv, hDcard] at h1
    exact h1
  have hVle : V ≤ (C t).subtype.range := by
    rw [Subgroup.range_subtype]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      (Subgroup.zpowers_le.mpr hsC)
  have hKsC : ActualFourGroupNormalizer.K sC =
      (Subgroup.normalizer (V : Set G)).subgroupOf (C t) := by
    change Subgroup.normalizer (ActualFourGroupCentralizer.V sC : Set (C t)) = _
    rw [Subgroup.subgroupOf, Subgroup.comap_normalizer_eq_of_le_range hVle]
    congr 2
    have hVmap' : (ActualFourGroupCentralizer.V sC).map (C t).subtype = V := hVmap
    change ActualFourGroupCentralizer.V sC = V.comap (C t).subtype
    rw [← hVmap', Subgroup.comap_map_eq_self_of_injective (C t).subtype_injective]
  have hCMcard : Nat.card (C t ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) = 24 := by
    rw [← hKs, hKsC, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hdC : ((d : C t) : G) ∈ C t := (d : C t).2
  have hdM : ((d : C t) : G) ∈ Subgroup.normalizer (V : Set G) := by
    have h : ∀ x : C t, x ∈ ActualFourGroupNormalizer.K sC →
        (x : G) ∈ Subgroup.normalizer (V : Set G) := by
      intro x hx
      rw [hKsC, Subgroup.mem_subgroupOf] at hx
      exact hx
    exact h _ d.2
  have hdG4 : orderOf ((d : C t) : G) = 4 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hd4]
  have hdG2 : ((d : C t) : G) ^ 2 = t := by
    have h := congrArg (fun x : ActualFourGroupNormalizer.K sC => ((x : C t) : G)) hd2
    simp only [Subgroup.coe_pow] at h
    exact h
  have hdGs : ((d : C t) : G) * s₀ * ((d : C t) : G)⁻¹ = t * s₀ := by
    have h := congrArg (fun x : C t => (x : G)) hds
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have hdGW : ∀ w ∈ W₀, ((d : C t) : G) * w * ((d : C t) : G)⁻¹ = w⁻¹ := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have h := congrArg (fun x : C t => (x : G)) (hinv ⟨y, hy⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  exact ⟨hn4, hC, three_torus_inversion_normalizer_of_data S V rfl hSC hS4 hV hs2 hst hC hDcard
    W₀ hW₀D hW₀card hnot hMcard hCMcard hdC hdM hdG4 hdG2 hdGs hdGW⟩

end CFSG.Semidihedral.Principal
