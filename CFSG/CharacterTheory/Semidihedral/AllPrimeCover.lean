module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts
public import CFSG.GroupTheory.QuasiDihedralFusion.Classes

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion CFSG.ABGQGroups
open scoped Pointwise

section SylowTypes

private theorem not_injective_kleinFour_quaternion {V : Type*} [Group V] [IsKleinFour V]
    {m : ℕ} [NeZero m] (ι : V →* QuaternionGroup m) (hι : Function.Injective ι) : False := by
  have hsq : ∀ v : V, ι v ^ 2 = 1 := fun v => by
    rw [← map_pow, ← IsKleinFour.exponent_two (G := V), Monoid.pow_exponent_eq_one, map_one]
  have hmem : ∀ v : V, ι v ∈ Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup m) := by
    intro v
    rcases h : ι v with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
      rw [zpow_natCast, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    · exfalso
      have h2 := hsq v
      rw [h, QuaternionGroup.xa_sq, QuaternionGroup.one_def, QuaternionGroup.a.injEq,
        ZMod.natCast_eq_zero_iff] at h2
      have hm := NeZero.ne m
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h2
      omega
  have : IsCyclic V := isCyclic_of_injective (ι.codRestrict _ hmem)
    (fun x y hxy => hι (congrArg Subtype.val hxy))
  exact IsKleinFour.not_isCyclic this

private theorem hasQDOrWreathedSylow_or_dihedral_of_kleinFour_le {G : Type} [Group G] [Finite G]
    {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    {V H : Subgroup G} (hV : IsKleinFour V) (hVH : V ≤ H) :
    HasQDOrWreathedSylow H ∨ GorensteinWalter.HasDihedralSylowTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  obtain ⟨P₀, hP₀⟩ := (hV2.comap_subtype (K := H)).exists_le_sylow
  have hP2 : IsPGroup 2 ((P₀ : Subgroup H).map H.subtype) := P₀.isPGroup'.map H.subtype
  obtain ⟨S', hPS'⟩ := hP2.exists_le_sylow
  have hVP : V ≤ (P₀ : Subgroup H).map H.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hVH]
    exact Subgroup.map_mono hP₀
  let f' : SemidihedralGroup n ≃* (S' : Subgroup G) := fS.trans (Sylow.equiv S S')
  let eP : (P₀ : Subgroup H) ≃* ((P₀ : Subgroup H).map H.subtype).subgroupOf S' :=
    ((P₀ : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (Subgroup.subgroupOfEquivOfLe hPS').symm
  by_cases htop : ((P₀ : Subgroup H).map H.subtype).subgroupOf S' = ⊤
  · left
    have hPeq : (P₀ : Subgroup H).map H.subtype = S' := by
      refine le_antisymm hPS' fun x hx => ?_
      have hx' : (⟨x, hx⟩ : (S' : Subgroup G)) ∈
          ((P₀ : Subgroup H).map H.subtype).subgroupOf S' := by
        rw [htop]
        exact Subgroup.mem_top _
      exact hx'
    let e : SemidihedralGroup n ≃* (P₀ : Subgroup H) :=
      f'.trans ((MulEquiv.subgroupCongr hPeq.symm).trans
        ((P₀ : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).symm)
    exact ⟨1, Or.inl ⟨rfl, n, hasSemidihedralSylow_of hn P₀ e⟩⟩
  · right
    have := hV
    let ι : V →* ((P₀ : Subgroup H).map H.subtype).subgroupOf S' :=
      (Subgroup.subgroupOfEquivOfLe hPS').symm.toMonoidHom.comp (Subgroup.inclusion hVP)
    have hι : Function.Injective ι :=
      (Subgroup.subgroupOfEquivOfLe hPS').symm.injective.comp (Subgroup.inclusion_injective hVP)
    rcases (Local.proper_subgroup_cyclic_dihedral_quaternion_forms n hn f'
        (((P₀ : Subgroup H).map H.subtype).subgroupOf S')).1 htop with
      hcyc | ⟨a, ha, ⟨eD⟩, -⟩ | ⟨a, ha, ⟨eQ⟩, -⟩
    · have := hcyc
      exact (IsKleinFour.not_isCyclic (isCyclic_of_injective ι hι)).elim
    · exact fun Q => ⟨a, ha, ⟨(Sylow.equiv Q P₀).trans (eP.trans eD)⟩⟩
    · have : NeZero (2 ^ a) := ⟨by positivity⟩
      exact (not_injective_kleinFour_quaternion (eQ.toMonoidHom.comp ι)
        (eQ.injective.comp hι)).elim

private theorem frontierSetting_T_isKleinFour {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    IsKleinFour (frontierSetting S fS t p f).T := by
  rw [frontierSetting_T hn S fS t ht p f]
  exact qdFour_isKleinFour hn _ fS

end SylowTypes

section Complement

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem mem_centralizer_of_odd_of_hasNormalPComplement
    (hC : HasNormalPComplement 2 X) {V : Subgroup X} (hV : IsPGroup 2 V) {x : X}
    (hx : x ∈ Subgroup.normalizer (V : Set X)) (hodd : Odd (orderOf x)) :
    x ∈ Subgroup.centralizer (V : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, hcop, hq⟩ := hC
  have hxK : x ∈ K := by
    have h1 : orderOf (QuotientGroup.mk' K x) ∣ orderOf x := orderOf_map_dvd _ x
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hq (QuotientGroup.mk' K x)
    have h2 : orderOf (QuotientGroup.mk' K x) = 1 := by
      rw [hk] at h1 ⊢
      rcases k with _ | k
      · rfl
      · exact absurd (even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h1))
          (Nat.not_even_iff_odd.mpr hodd)
    rwa [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hcV : x * v * x⁻¹ * v⁻¹ ∈ V :=
    V.mul_mem ((Subgroup.mem_normalizer_iff.mp hx v).mp hv) (V.inv_mem hv)
  have hcK : x * v * x⁻¹ * v⁻¹ ∈ K := by
    have h1 := K.mul_mem hxK (hK.conj_mem _ (K.inv_mem hxK) v)
    rwa [← mul_assoc, ← mul_assoc] at h1
  have hc1 : x * v * x⁻¹ * v⁻¹ = 1 := by
    have h2 : orderOf (x * v * x⁻¹ * v⁻¹) ∣ Nat.card K := by
      rw [← Subgroup.orderOf_mk (x * v * x⁻¹ * v⁻¹) hcK]
      exact orderOf_dvd_natCard _
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hV ⟨_, hcV⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at h2
    rcases k with _ | k
    · rwa [pow_zero, orderOf_eq_one_iff] at hk
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h2)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop)
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc1
  exact hc1.symm

private theorem not_three_dvd_automizerIndex_of_hasNormalPComplement
    (hC : HasNormalPComplement 2 X) {V : Subgroup X} (hV : IsPGroup 2 V) :
    ¬ 3 ∣ automizerIndex V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  have h3' : 3 ∣ ((Subgroup.centralizer (V : Set X)).subgroupOf
      (Subgroup.normalizer (V : Set X))).index := h3
  obtain ⟨Q⟩ : Nonempty (Sylow 3 (Subgroup.normalizer (V : Set X))) := inferInstance
  have hnot : ¬ (Q : Subgroup (Subgroup.normalizer (V : Set X))) ≤
      (Subgroup.centralizer (V : Set X)).subgroupOf (Subgroup.normalizer (V : Set X)) :=
    fun hle => Q.not_dvd_index (h3'.trans (Subgroup.index_dvd_of_le hle))
  obtain ⟨x, hxQ, hxC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  apply hxC
  have hxodd : Odd (orderOf (x : X)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp Q.isPGroup' ⟨x, hxQ⟩
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at hk
    rw [hk]
    exact Odd.pow (by decide)
  exact Subgroup.mem_subgroupOf.mpr
    (mem_centralizer_of_odd_of_hasNormalPComplement hC hV x.2 hxodd)

end Complement

section Cover

private theorem isQGroup_of_focal_eq_originalQuaternion {X : Type*} [Group X] [Finite X]
    {n : ℕ} (hn : 4 ≤ n) (SX : Sylow 2 X) (fX : SemidihedralGroup n ≃* SX)
    (hfocal : (SX : Subgroup X) ⊓ commutator X =
      QuaternionFocalFactorization.originalQuaternion n SX fX)
    (hidx : ∃ K : Subgroup X, K.index = 2) : IsQGroup X := by
  have hsub : (commutator X).subgroupOf SX =
      (quaternionSubgroup n).map (fX : SemidihedralGroup n →* SX) := by
    rw [map_quaternionSubgroup, ← QuaternionFocalFactorization.originalQuaternion_subgroupOf_sylow,
      ← hfocal, Subgroup.inf_subgroupOf_left]
  have hinj := Subgroup.map_injective (f := (fX : SemidihedralGroup n →* SX)) fX.injective
  obtain ⟨h1, h2, -, h4⟩ := focal_cases_ambient hn SX fX
  by_cases ha : IsConj (FocalFusion.ambientHom n (SX : Subgroup X) fX (s n))
      (FocalFusion.ambientHom n (SX : Subgroup X) fX (z n)) <;>
    by_cases hb : IsConj (FocalFusion.ambientHom n (SX : Subgroup X) fX (r n * s n))
      (FocalFusion.ambientHom n (SX : Subgroup X) fX (r n ^ (2 ^ (n - 3))))
  · obtain ⟨K, hK⟩ := hidx
    exact absurd hK (h4.mpr ⟨ha, hb⟩ K)
  · have h := h2 ha hb
    rw [hsub, ← map_dihedralSubgroup] at h
    exact absurd (hinj h).symm (dihedralSubgroup_ne_quaternionSubgroup n (by omega))
  · exact isQGroup_of_semidihedralFusionQ hn SX fX (semidihedralFusionQ_of hn SX fX ha hb)
  · have h := h1 ha hb
    have hz : Subgroup.zpowers (fX (r n) ^ 2) =
        (Subgroup.zpowers (r n ^ 2)).map (fX : SemidihedralGroup n →* SX) := by
      rw [MonoidHom.map_zpowers, map_pow]
      rfl
    rw [hsub, hz] at h
    have hQ := hinj h
    exfalso
    apply rotationSubgroup_ne_quaternionSubgroup n (by omega)
    symm
    have := presentation_finite n (by omega)
    apply Subgroup.eq_of_le_of_card_ge
    · rw [hQ, Subgroup.zpowers_le]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (r n)) 2
    · exact ((rotationSubgroup_natCard n (by omega)).trans
        (quaternionSubgroup_natCard n (by omega)).symm).le

private theorem layer_cover_of_subset_mul {G : Type} [Group G] (t : G) (H : Subgroup G)
    (hcov : (((localLayerPreimage t).map (C t).subtype : Subgroup G) : Set G) ⊆
      (H : Set G) * (((N t).map (C t).subtype : Subgroup G) : Set G)) :
    (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
  · intro y hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (N t) y
    have hc : c ∈ localLayerPreimage t := hy
    obtain ⟨k, hk, m, ⟨m', hm', rfl⟩, hkm⟩ := Set.mem_mul.mp (hcov ⟨c, hc, rfl⟩)
    have hkC : k ∈ C t := by
      rw [eq_mul_inv_of_mul_eq hkm]
      exact (C t).mul_mem c.2 ((C t).inv_mem m'.2)
    have hc' : c = ⟨k, hkC⟩ * m' := Subtype.ext hkm.symm
    have hm1 : nu t m' = 1 := (QuotientGroup.eq_one_iff _).mpr hm'
    have hnu : nu t ⟨k, hkC⟩ = nu t c := by rw [hc', map_mul, hm1, mul_one]
    refine ⟨⟨k, hkC⟩, ⟨hk, ?_⟩, hnu⟩
    change nu t ⟨k, hkC⟩ ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    rw [hnu]
    exact hy

private theorem hasNormalSL2_of_layer_cover {G : Type} [Group G] (t : G) {F : Type} [Field F]
    [Finite F] (eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) (H : Subgroup G)
    (hcov : (((localLayerPreimage t).map (C t).subtype : Subgroup G) : Set G) ⊆
      (H : Set G) * (((N t).map (C t).subtype : Subgroup G) : Set G))
    (hfac : ∀ x : H, ∃ a ∈ CFSG.oddCore H, ∃ c ∈ C t, (a : G) * c = (x : G))
    (hinter : (CFSG.oddCore H).map H.subtype ⊓ C t = (N t).map (C t).subtype ⊓ H) :
    HasNormalSL2 (H ⧸ CFSG.oddCore H) (Nat.card F) := by
  classical
  have := localLayerPreimage_normal t
  let L₀ : Subgroup G := (localLayerPreimage t).map (C t).subtype
  let ON : Subgroup G := (N t).map (C t).subtype
  let Λ : Subgroup H := L₀.subgroupOf H
  let π : H →* H ⧸ CFSG.oddCore H := QuotientGroup.mk' (CFSG.oddCore H)
  have hOL : ∀ x : H, (x : G) ∈ L₀ → (x ∈ CFSG.oddCore H ↔ (x : G) ∈ ON) := by
    intro x hxL
    have hxC : (x : G) ∈ C t := Subgroup.map_subtype_le _ hxL
    constructor
    · intro hx
      exact (hinter.le ⟨⟨x, hx, rfl⟩, hxC⟩).1
    · intro hx
      exact (Subgroup.mem_map_iff_mem H.subtype_injective).mp (hinter.ge ⟨hx, x.2⟩).1
  let incl : Λ →* L₀ := (H.subtype.comp Λ.subtype).codRestrict L₀ fun x => x.2
  let ψ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F := (layerQuotientHom t eta).comp incl
  have hker : ∀ y : L₀, layerQuotientHom t eta y = 1 ↔ (y : G) ∈ ON := by
    intro y
    rw [← MonoidHom.mem_ker, layerQuotientHom_ker, Subgroup.mem_subgroupOf]
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨l, rfl⟩ := layerQuotientHom_surjective t eta y
    obtain ⟨h, hh, m, hm, hhm⟩ := Set.mem_mul.mp (hcov l.2)
    have hmL : m ∈ L₀ := Subgroup.map_mono (N_le_localLayerPreimage t) hm
    have hhL : h ∈ L₀ := by
      have h1 := L₀.mul_mem l.2 (L₀.inv_mem hmL)
      rwa [← hhm, mul_inv_cancel_right] at h1
    refine ⟨⟨⟨h, hh⟩, hhL⟩, ?_⟩
    have hl : l = ⟨h, hhL⟩ * ⟨m, hmL⟩ := Subtype.ext hhm.symm
    change layerQuotientHom t eta ⟨h, hhL⟩ = layerQuotientHom t eta l
    rw [hl, map_mul, (hker ⟨m, hmL⟩).mpr hm, mul_one]
  have hkerEq : (π.subgroupMap Λ).ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Subtype.coe_inj, MonoidHom.subgroupMap_apply_coe,
      OneMemClass.coe_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change _ ↔ layerQuotientHom t eta (incl x) = 1
    rw [hker]
    exact hOL x x.2
  let e : Λ.map π ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientKerEquivOfSurjective _ (π.subgroupMap_surjective Λ)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))
  have hnormal : (Λ.map π).Normal := by
    constructor
    rintro _ ⟨l, hl, rfl⟩ q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore H) q
    obtain ⟨a, ha, c, hc, hac⟩ := hfac h
    have hca : ((a⁻¹ * h : H) : G) = c := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hac, inv_mul_cancel_left]
    refine ⟨(a⁻¹ * h) * l * (a⁻¹ * h)⁻¹, ?_, ?_⟩
    · have hl' : (l : G) ∈ L₀ := hl
      have hnorm := CFSG.ABGTheoremB.le_normalizer_map_subtype (C t) (localLayerPreimage t) hc
      change (((a⁻¹ * h) * l * (a⁻¹ * h)⁻¹ : H) : G) ∈ L₀
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hca]
      exact (Subgroup.mem_normalizer_iff.mp hnorm _).mp hl'
    · have hπa : π a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
      change π ((a⁻¹ * h) * l * (a⁻¹ * h)⁻¹) = π h * π l * (π h)⁻¹
      rw [map_mul, map_mul, map_inv, map_mul, map_inv, hπa, inv_one, one_mul]
  exact ⟨Λ.map π, F, inferInstance, inferInstance, hnormal, rfl, ⟨e⟩⟩

end Cover

theorem frontier_fusion_disjoint {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (_hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (_ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ H : Subgroup G,
      (IsQDGroup H → ¬ IsQGroup H) ∧ (IsQDGroup H → ¬ IsDGroup H) ∧
        (IsQDGroup H → ¬ HasNormalPComplement 2 H) ∧ (IsQGroup H → ¬ IsDGroup H) ∧
        (IsQGroup H → ¬ HasNormalPComplement 2 H) ∧ (IsDGroup H → ¬ HasNormalPComplement 2 H) :=
  fun _ => fusion_classes_disjoint

theorem frontier_fusion_cases {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ H : Subgroup G, H ≠ ⊤ → (frontierSetting S fS t p f).T ≤ H →
      ((frontierSetting S fS t p f).D ≤ H ∨ (frontierSetting S fS t p f).height = 1) →
      IsQDGroup H ∨ IsQGroup H ∨ IsDGroup H ∨ HasNormalPComplement 2 H := by
  intro H _ hTH _
  exact fusion_class_cases (hasQDOrWreathedSylow_or_dihedral_of_kleinFour_le hn S fS
    (frontierSetting_T_isKleinFour hn S fS t ht p f) hTH)

theorem frontier_qd_or_d_of_three {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hno3 : ∀ K : Subgroup G, IsQGroup K → ∀ T₁ : Subgroup G, T₁ ≤ K → IsKleinFour T₁ →
      ¬ 3 ∣ automizerIndex (T₁.subgroupOf K)) :
    ∀ H : Subgroup G, (frontierSetting S fS t p f).T ≤ H →
      ((frontierSetting S fS t p f).D ≤ H ∨ (frontierSetting S fS t p f).height = 1) →
      3 ∣ automizerIndex ((frontierSetting S fS t p f).T.subgroupOf H) →
      IsQDGroup H ∨ IsDGroupWrt ((frontierSetting S fS t p f).T.subgroupOf H) := by
  intro H hTH _ h3
  have hK := frontierSetting_T_isKleinFour hn S fS t ht p f
  rcases fusion_class_cases (hasQDOrWreathedSylow_or_dihedral_of_kleinFour_le hn S fS hK hTH)
    with hQD | hQ | hD | hC
  · exact Or.inl hQD
  · exact absurd h3 (hno3 H hQ _ hTH hK)
  · exact Or.inr ⟨hD, Local.isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTH).symm, h3⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hT2 : IsPGroup 2 (frontierSetting S fS t p f).T :=
      IsPGroup.of_card (n := 2) (by rw [hK.card_four]; norm_num)
    exact absurd h3
      (not_three_dvd_automizerIndex_of_hasNormalPComplement hC (hT2.comap_subtype (K := H)))

theorem frontier_cover_qgroup
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ H : Subgroup G, (frontierSetting S fS t p f).T ≤ H → oddCoreIn H ≠ ⊥ →
      ((frontierSetting S fS t p f).L₀ : Set G) ⊆
        (H : Set G) * (frontierSetting S fS t p f).ON →
      HasQCharPower H (frontierSetting S fS t p f).q ∧
        oddCoreIn H ⊔ (H ⊓ (frontierSetting S fS t p f).N) = H := by
  intro H hTH hO hcov
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hR : CFSG.pPrimeCore 2 H ≠ ⊥ := by
    intro h
    apply hO
    rw [oddCoreIn, QuaternionFocalFactorization.oddCore_eq_twoPrimeCore, h, Subgroup.map_bot]
  have hcov' : (((localLayerPreimage t).map (C t).subtype : Subgroup G) : Set G) ⊆
      (H : Set G) * (((N t).map (C t).subtype : Subgroup G) : Set G) := by
    rw [← frontierSetting_ON S fS t p f]
    exact hcov
  obtain ⟨-, -, -, hlift, hindex, -, hwitness, hfactor, hinter⟩ :=
    LocalCoverFactorization.original_layer_cover_produces_focal_and_factorization G hGnonab hrec
      n hn S fS t (fS (s n) : G) ht2 hs2 hsC hst.symm hnonab hcentral hnc p f hp hpodd hf hq.le
      hmodel H hTH hR (layer_cover_of_subset_mul t H hcov')
  refine ⟨⟨?_, hpodd.pow, ?_⟩, hfactor⟩
  · obtain ⟨SB⟩ : Nonempty (Sylow 2 (H.subgroupOf (C t))) := Sylow.nonempty
    obtain ⟨⟨fB⟩, SH, _SG, -, -, -, hpresent⟩ := hlift SB
    obtain ⟨-, -, fH, _fG, -, -, -, hfocalH⟩ := hpresent fB
    exact isQGroup_of_focal_eq_originalQuaternion hn SH fH hfocalH ⟨_, hindex⟩
  · have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
    obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
      actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf
        hmodel
    obtain ⟨eta, -, -, -⟩ := data.compatible_layer
    have h := hasNormalSL2_of_layer_cover t eta H hcov' (fun x => by
      obtain ⟨a, ha, c, hc, hac⟩ := hwitness x
      exact ⟨a, by rwa [QuaternionFocalFactorization.oddCore_eq_twoPrimeCore], c, hc, hac⟩)
      hinter
    rwa [data.field_card] at h

end CFSG.Semidihedral.AllPrime
