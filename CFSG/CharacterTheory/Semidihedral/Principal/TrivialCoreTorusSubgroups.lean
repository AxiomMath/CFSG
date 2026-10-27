module

public import CFSG.CharacterTheory.Semidihedral.Principal.TrivialCoreTorusSubgroupsSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneTorusNormalizer

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem
    perfect_trivial_core_every_torus_subgroup_has_inversion_normalizer_and_central_cyclic_odd_core
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    let q : ℕ := p ^ f
    let e : ℤ := if q % 4 = 1 then 1 else -1
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let M : Subgroup G := Subgroup.normalizer (V : Set G)
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    IsCyclic W ∧ Odd (Nat.card W) ∧ (Nat.card W : ℤ) = ((q : ℤ) + e) / 2 ∧ 1 < Nat.card W ∧
      (V ⊔ W = D ∧ Disjoint V W ∧ ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) ∧
      (∃ S₀ : Subgroup G, S₀ ≤ H ∧ Nonempty (S₀ ≃* DihedralGroup 4) ∧ Nat.card S₀ = 8 ∧
        ∀ U : Subgroup G, U ≤ W → U ≠ ⊥ →
          ∃ P : Sylow 2 (Subgroup.normalizer (U : Set G)),
            (P : Subgroup _).map (Subgroup.normalizer (U : Set G)).subtype = S₀) ∧
      ∀ U : Subgroup G, U ≤ W → U ≠ ⊥ →
        let A : Subgroup G := Subgroup.centralizer (U : Set G)
        let J : Subgroup G := Subgroup.normalizer (U : Set G)
        let R : Subgroup G := (CFSG.pPrimeCore 2 A).map A.subtype
        let π : A →* A ⧸ CFSG.pPrimeCore 2 A := QuotientGroup.mk' (CFSG.pPrimeCore 2 A)
        (∃ P : Sylow 2 A, (P : Subgroup A).map A.subtype = V) ∧
          (Subgroup.centralizer ((V.subgroupOf A : Subgroup A) : Set A)).map A.subtype = D ∧
          A ⊓ Subgroup.centralizer {t} = D ∧
          (Subgroup.normalizer ((V.subgroupOf A : Subgroup A) : Set A)).map A.subtype =
            (Subgroup.normalizer ((V.subgroupOf K : Subgroup K) : Set K)).map K.subtype ∧
          (A : Set G) * (M : Set G) = (J : Set G) ∧ A.relIndex J = 2 ∧
          (∀ j ∈ J, j ∉ A → ∀ u ∈ U, j * u * j⁻¹ = u⁻¹) ∧
          U ≤ R ∧ R ≤ W ∧ R ≤ (Subgroup.center A).map A.subtype ∧
          (CFSG.pPrimeCore 2 J).map J.subtype = R ∧
          J = Subgroup.normalizer (R : Set G) ∧ A = Subgroup.centralizer (R : Set G) ∧
          R ≠ ⊥ ∧ IsCyclic R ∧
          ∀ T : Subgroup G, R ≤ T → T ≤ W →
            (Subgroup.normalizer ((T.subgroupOf A : Subgroup A) : Set A)).map A.subtype =
                Subgroup.centralizer (T : Set G) ∧
              (Subgroup.centralizer ((T.subgroupOf A : Subgroup A) : Set A)).map A.subtype =
                Subgroup.centralizer (T : Set G) ∧
              Subgroup.normalizer (((T.subgroupOf A).map π : Subgroup (A ⧸ CFSG.pPrimeCore 2 A)) :
                  Set (A ⧸ CFSG.pPrimeCore 2 A)) =
                ((Subgroup.centralizer (T : Set G)).subgroupOf A).map π ∧
              Subgroup.centralizer (((T.subgroupOf A).map π :
                  Subgroup (A ⧸ CFSG.pPrimeCore 2 A)) : Set (A ⧸ CFSG.pPrimeCore 2 A)) =
                ((Subgroup.centralizer (T : Set G)).subgroupOf A).map π := by
  intro q e s₀ V D W M H K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hW1, hWcyc, hWodd, hWcard, ⟨hsup, hdisj, hcomm⟩, hcentW, hCH, -,
      ⟨d, hd, hd4, hd2, hds, hdW, hdih, hS₀card, P₀, hP₀⟩, hMH, -, -, -, hinvH, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hW1 : W ≠ ⊥ := hW1
  have hWcyc : IsCyclic W := hWcyc
  have hWodd : Odd (Nat.card W) := hWodd
  have hWcard : (Nat.card W : ℤ) = ((q : ℤ) + e) / 2 := hWcard
  have hsup : V ⊔ W = D := hsup
  have hdisj : Disjoint V W := hdisj
  have hcomm : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := hcomm
  have hcentW : ∀ w ∈ W, w ≠ 1 → C t ⊓ Subgroup.centralizer {w} = D := hcentW
  have hCH : C t ⊓ H = C t ⊓ M := hCH
  have hd : d ∈ C t ⊓ H := hd
  have hds : d * s₀ * d⁻¹ = t * s₀ := hds
  have hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹ := hdW
  have hdih : Nonempty ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≃*
      DihedralGroup 4) := hdih
  have hS₀card : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) = 8 :=
    hS₀card
  have hP₀ : (P₀ : Subgroup H).map H.subtype = Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ := hP₀
  have hMH : M ≤ H := hMH
  have hinvH : ∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹ := hinvH
  obtain ⟨hzt, ht2, -, -, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, -, hDK, -, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have hVD : V ≤ D := hsup ▸ le_sup_left
  have hVK : V ≤ K := hVD.trans hDK
  have hDC : D ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx t htV).symm
  obtain ⟨w₁, hw₁, hw₁1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra! hall
    exact hW1 ((Subgroup.eq_bot_iff_forall _).mpr hall)
  have hCW : C t ⊓ Subgroup.centralizer (W : Set G) = D := by
    apply le_antisymm
    · rw [← hcentW w₁ hw₁ hw₁1]
      exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw₁))
    · exact le_inf hDC hDK
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t} := by
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
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r n)).property _
  have hVS : V ≤ (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr (fS (s n)).property)
  have hsurj : Function.Surjective V.normalizerMonoidHom := MonoidHom.range_eq_top.mp
    ((CFSG.Semidihedral.Local.perfect_semidihedral_full_local_fusion n hn S fS).1 V hVS hV).1
  have hdC : d ∈ C t := (Subgroup.mem_inf.mp hd).1
  have hdM : d ∈ M := (Subgroup.mem_inf.mp (hCH ▸ hd)).2
  obtain ⟨-, -, -, -, -, hKMcard, htrans⟩ := cyclic_torus_normalizer_sylow S V rfl hSC hS4 hV
    hs2 hst W hWcyc hWodd hW1 hsup hdisj hCW hsurj hdC hdM hd4 hd2 hds hdW
  have hS₀H : Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ ≤ H := hP₀ ▸ Subgroup.map_subtype_le _
  have hS₀ : ∀ U : Subgroup G, U ≤ W → U ≠ ⊥ →
      ∃ P : Sylow 2 (Subgroup.normalizer (U : Set G)),
        (P : Subgroup _).map (Subgroup.normalizer (U : Set G)).subtype =
          Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ := by
    intro U hUW hU1
    obtain ⟨-, -, hHJ, -, -, -, -, -, k, hk, hJcard⟩ := torus_subgroup_normalizer_data V W hV htV
      hWodd hWcomm hsup hdisj hcentW hMH hinvH hKMcard hdM hdW hUW hU1
    set J := Subgroup.normalizer (U : Set G) with hJdef
    have hS₀J : Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ ≤ J := hS₀H.trans hHJ
    have hcard : Nat.card ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀).subgroupOf J) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀J).toEquiv, hS₀card]
    have hidx : ¬ 2 ∣ ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀).subgroupOf J).index := by
      intro h2
      have h := Subgroup.card_mul_index ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀).subgroupOf J)
      rw [hcard, hJcard] at h
      obtain ⟨j, hj⟩ := hk
      obtain ⟨i, hi⟩ := h2
      rw [hi] at h
      omega
    have hp2 : IsPGroup 2 ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀).subgroupOf J) :=
      IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
    refine ⟨hp2.toSylow hidx, ?_⟩
    change ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀).subgroupOf J).map J.subtype = _
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS₀J]
  refine ⟨hWcyc, hWodd, ?_, ?_, ⟨hsup, hdisj, hcomm⟩,
    ⟨_, hS₀H, hdih, hS₀card, hS₀⟩, fun U hUW hU1 => ?_⟩
  · rw [hWcard]
  · rw [Nat.one_lt_iff_ne_zero_and_ne_one]
    refine ⟨Nat.card_pos.ne', fun h1 => hW1 ?_⟩
    exact (Subgroup.card_eq_one).mp h1
  intro A J R π
  obtain ⟨hVsyl, hKA, -, hAM, hAt, hAMset, hAJ2, hinvJ, -⟩ := torus_subgroup_normalizer_data V W
    hV htV hWodd hWcomm hsup hdisj hcentW hMH hinvH hKMcard hdM hdW hUW hU1
  obtain ⟨hUR, hRW, hRZ, hJ2, hJeq, hAeq, hR1, hRcyc, hT⟩ := torus_subgroup_odd_core_data V W hV
    htV hWcyc hWodd hsup hdisj hcentW hMH hinvH hKMcard hdM hdW htrans hUW hU1
  have hDA : D ≤ A := hDK.trans hKA
  have hVA : V ≤ A := hVD.trans hDA
  refine ⟨hVsyl, ?_, hAt, ?_, hAMset, hAJ2, hinvJ, hUR, hRW, hRZ, hJ2, hJeq, hAeq, hR1, hRcyc,
    fun T hRT hTW => ?_⟩
  · rw [map_centralizer_subgroupOf hVA]
    exact inf_eq_right.mpr hDA
  · rw [map_normalizer_subgroupOf hVA, map_normalizer_subgroupOf hVK]
    exact hAM
  have hTA : T ≤ A := hTW.trans ((hsup ▸ le_sup_right : W ≤ D).trans hDA)
  have hTeq := hT T hRT hTW
  have hCTA : Subgroup.centralizer (T : Set G) ≤ A :=
    (Subgroup.centralizer_le hRT).trans hAeq.ge
  have hNT : CFSG.pPrimeCore 2 A ≤ T.subgroupOf A := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hRT ⟨x, hx, rfl⟩
  obtain ⟨hqN, hqC⟩ := quotient_normalizer_eq_of_inf_normalizer_eq (CFSG.pPrimeCore 2 A) hTA hNT
    hTeq
  refine ⟨by rw [map_normalizer_subgroupOf hTA, hTeq], ?_, hqN, hqC⟩
  rw [map_centralizer_subgroupOf hTA]
  exact inf_eq_right.mpr hCTA

end CFSG.Semidihedral.Principal
