module

public import CFSG.GroupTheory.QuasiDihedralFusion.QGroup
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.InputsQuaternion
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusInputs
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.TransitivityInputs

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Inputs

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

theorem exists_four_fusion_of_isQGroup {H : Type*} [Group H] [Finite H] (hH : IsQGroup H)
    (T : Subgroup H) (hT : ∀ t ∈ T, t * t = 1) {u v : H} (hu : u ∈ T) (hv : v ∈ T)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) :
    ∃ z ∈ T, z ≠ 1 ∧ (∀ h : H, h * z * h⁻¹ * z⁻¹ ∈ CFSG.oddCore H) ∧
      ∀ t ∈ T, t ≠ 1 → t ≠ z → ∃ h : H, h * t * h⁻¹ = t * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := fun t => ⟨1, Subtype.ext (by
    rw [pow_one, SubmonoidClass.coe_pow, pow_two]
    exact hT t t.2)⟩
  obtain ⟨R, hTR⟩ := hT2.exists_le_sylow
  obtain ⟨K, hK⟩ := hH.exists_data R
  have hcen := (hH.oddCore_sup_centralizer_center R).2
  have hTR' : ∀ t ∈ T.subgroupOf (R : Subgroup H), t * t = 1 := fun t ht =>
    Subtype.ext (hT t (Subgroup.mem_subgroupOf.mp ht))
  have hu' : (⟨u, hTR hu⟩ : (R : Subgroup H)) ∈ T.subgroupOf (R : Subgroup H) :=
    Subgroup.mem_subgroupOf.mpr hu
  have hv' : (⟨v, hTR hv⟩ : (R : Subgroup H)) ∈ T.subgroupOf (R : Subgroup H) :=
    Subgroup.mem_subgroupOf.mpr hv
  have hu1' : (⟨u, hTR hu⟩ : (R : Subgroup H)) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hv1' : (⟨v, hTR hv⟩ : (R : Subgroup H)) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have huv' : (⟨u, hTR hu⟩ : (R : Subgroup H)) ≠ ⟨v, hTR hv⟩ := fun h =>
    huv (congrArg Subtype.val h)
  have key : ∃ z ∈ T.subgroupOf (R : Subgroup H), z ≠ 1 ∧
      z ∈ Subgroup.center (R : Subgroup H) ∧ ∀ t ∈ T.subgroupOf (R : Subgroup H), t ≠ 1 →
        t ≠ z → ∃ y ∈ (K ⊓ (R : Subgroup H)).subgroupOf (R : Subgroup H),
          y * t * y⁻¹ = t * z := by
    rcases hK.quaternion.2 with ⟨n, hn, ι, hι, himg⟩ | ⟨n, hn, ι, hι, himg⟩
    · exact (sd_fourFusionModel n hn).exists_central_four ι hι _ himg _ hTR' hu' hv' hu1' hv1'
        huv'
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact (wreath_fourFusionModel k (by omega)).exists_central_four ι hι _ himg _ hTR' hu' hv'
        hu1' hv1' huv'
  obtain ⟨z, hzT, hz1, hzc, hzconj⟩ := key
  have hzC : (z : H) ∈ centerOf (R : Subgroup H) := by
    refine Subgroup.mem_inf.mpr ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨g, hg⟩)
  have hzZ : ((z : H) : H ⧸ CFSG.oddCore H) ∈ Subgroup.center (H ⧸ CFSG.oddCore H) :=
    hcen ⟨z, hzC, rfl⟩
  refine ⟨z, Subgroup.mem_subgroupOf.mp hzT, fun h => hz1 (Subtype.ext h), fun h => ?_,
    fun t ht ht1 htz => ?_⟩
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      Subgroup.mem_center_iff.mp hzZ (h : H ⧸ CFSG.oddCore H)]
    group
  · obtain ⟨y, -, hy⟩ := hzconj ⟨t, hTR ht⟩ (Subgroup.mem_subgroupOf.mpr ht)
      (fun h => ht1 (congrArg Subtype.val h)) (fun h => htz (congrArg Subtype.val h))
    exact ⟨y, congrArg Subtype.val hy⟩

theorem qGroupFourFusion (G : Type) [Group G] [Finite G] : Sec10.QGroupFourFusion G := by
  classical
  intro H hH T₁ hT₁H hK4
  have hmul : ∀ t ∈ T₁, t * t = 1 := fun t ht =>
    congrArg Subtype.val (IsKleinFour.mul_self (⟨t, ht⟩ : T₁))
  let _ : Fintype T₁ := Fintype.ofFinite _
  have hcard : Fintype.card T₁ = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact IsKleinFour.card_four
  obtain ⟨u, hu1⟩ := Fintype.exists_ne_of_one_lt_card (by rw [hcard]; norm_num) (1 : T₁)
  obtain ⟨v, hv, hvu⟩ := Finset.exists_mem_ne (s := Finset.univ.erase (1 : T₁))
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]; norm_num) u
  have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
  obtain ⟨z, hzT, hz1, hzc, hzconj⟩ := exists_four_fusion_of_isQGroup hH (T₁.subgroupOf H)
    (fun t ht => Subtype.ext (hmul t (Subgroup.mem_subgroupOf.mp ht)))
    (u := ⟨u, hT₁H u.2⟩) (v := ⟨v, hT₁H v.2⟩) (Subgroup.mem_subgroupOf.mpr u.2)
    (Subgroup.mem_subgroupOf.mpr v.2)
    (fun h => hu1 (Subtype.ext (show (u : G) = 1 from congrArg Subtype.val h)))
    (fun h => hv1 (Subtype.ext (show (v : G) = 1 from congrArg Subtype.val h)))
    (fun h => hvu (Subtype.ext (show (v : G) = u from (congrArg Subtype.val h).symm)))
  refine ⟨z, Subgroup.mem_subgroupOf.mp hzT, fun h => hz1 (Subtype.ext h), fun h hh => ?_,
    fun t ht ht1 htz => ?_⟩
  · exact ⟨_, hzc ⟨h, hh⟩, rfl⟩
  · obtain ⟨y, hy⟩ := hzconj ⟨t, hT₁H ht⟩ (Subgroup.mem_subgroupOf.mpr ht)
      (fun h => ht1 (congrArg Subtype.val h)) (fun h => htz (congrArg Subtype.val h))
    exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem dGroupFourFusion_of_wreathed (G : Type) [Group G] [Finite G] {n : ℕ}
    (S : Sylow 2 G) (e : (S : Subgroup G) ≃* CFSG.Wreathed.Wreath (2 ^ n)) (hn : 2 ≤ n) :
    Sec10.DGroupFourFusion G := by
  rintro ⟨n', hn', hSD⟩
  exfalso
  obtain ⟨f⟩ := hSD S
  let φ := f.trans e
  have hcard := Nat.card_congr φ.toEquiv
  rw [Semidihedral.card n' (by omega), Wreathed.card_wreath] at hcard
  have hn'eq : n' = 2 * n + 1 := by
    apply Nat.pow_right_injective le_rfl
    simp only [hcard]
    ring
  have hdvd : orderOf (φ (Semidihedral.r n')) ∣ 2 * 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (Wreathed.element_pow_twice_modulus _ _)
  rw [MulEquiv.orderOf_eq, Semidihedral.orderOf_r n' (by omega), Semidihedral.modulus,
    ← pow_succ'] at hdvd
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  exact absurd hn (by omega)

theorem abg_II_3_1_input (G : Type) [Group G] [Finite G] : ABG_II_3_1_Input G := by
  intro K hK S₁ hS₁
  obtain ⟨Q, rfl⟩ := hS₁
  obtain ⟨h, -⟩ := hK.oddCore_sup_centralizer_center Q
  have hle : (Subgroup.centralizer (centerOf (Q : Subgroup K) : Set K)).map K.subtype ≤
      K ⊓ Subgroup.centralizer (centerOf ((Q : Subgroup K).map K.subtype) : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    obtain ⟨hwS, hwC⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨q, hq, rfl⟩ := hwS
    have hqc : q ∈ centerOf (Q : Subgroup K) := by
      refine Subgroup.mem_inf.mpr ⟨hq, Subgroup.mem_centralizer_iff.mpr fun q' hq' => ?_⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hwC _ ⟨q', hq', rfl⟩)
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc q hqc)
  calc K = (⊤ : Subgroup K).map K.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = oddCoreIn K ⊔
        (Subgroup.centralizer (centerOf (Q : Subgroup K) : Set K)).map K.subtype := by
        rw [← h, Subgroup.map_sup]
        rfl
    _ ≤ _ := sup_le_sup_left hle _

end CFSG.ABGTheoremB.TotallyInverted.Inputs
