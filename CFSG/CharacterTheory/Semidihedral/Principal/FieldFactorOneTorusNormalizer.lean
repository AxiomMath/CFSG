module

public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneTorusNormalizerSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicTorusNormalizerQuotients
public import CFSG.CharacterTheory.Semidihedral.Local.PerfectFullLocalFusion

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients
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
    let π : K →* K ⧸ CFSG.pPrimeCore 2 K := QuotientGroup.mk' (CFSG.pPrimeCore 2 K)
    Nat.card (C t) = 2 * q * (q ^ 2 - 1) ∧
      W ≠ ⊥ ∧ IsCyclic W ∧ Odd (Nat.card W) ∧ (Nat.card W : ℤ) = ((q : ℤ) + e) / 2 ∧
      (V ⊔ W = D ∧ Disjoint V W ∧ ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) ∧
      (∀ w ∈ W, w ≠ 1 → C t ⊓ Subgroup.centralizer {w} = D) ∧
      C t ⊓ H = C t ⊓ M ∧ Nat.card (C t ⊓ H : Subgroup G) = 8 * Nat.card W ∧
      (∃ d ∈ C t ⊓ H, orderOf d = 4 ∧ d ^ 2 = t ∧ d * s₀ * d⁻¹ = t * s₀ ∧
        (∀ w ∈ W, d * w * d⁻¹ = w⁻¹) ∧
        Nonempty ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≃* DihedralGroup 4) ∧
        Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) = 8 ∧
        ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype =
          Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
      M ≤ H ∧ (K : Set G) * (M : Set G) = (H : Set G) ∧
      (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = V) ∧
      K.relIndex H = 2 ∧ (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      Nat.card M = 24 * Nat.card W ∧
      Nat.card (Subgroup.normalizer ((V.subgroupOf K : Subgroup K) : Set K)) =
        12 * Nat.card W ∧
      (Subgroup.centralizer ((V.subgroupOf K : Subgroup K) : Set K)).map K.subtype = D ∧
      (CFSG.pPrimeCore 2 K).map K.subtype = W ∧ (CFSG.pPrimeCore 2 H).map H.subtype = W ∧
      W ≤ (Subgroup.center K).map K.subtype ∧
      (((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 12 * Nat.card W ∧ Nat.card H = 24 * Nat.card W) ∨
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 60 * Nat.card W ∧ Nat.card H = 120 * Nat.card W)) ∧
        ¬ ((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 12 * Nat.card W ∧ Nat.card H = 24 * Nat.card W) ∧
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 60 * Nat.card W ∧ Nat.card H = 120 * Nat.card W))) ∧
      IsKleinFour (((V ⊔ W).subgroupOf K).map π) ∧
      (∃ P : Sylow 2 (K ⧸ CFSG.pPrimeCore 2 K),
        (P : Subgroup _) = ((V ⊔ W).subgroupOf K).map π) ∧
      ∀ tK : K, (tK : G) = t → ((V ⊔ W).subgroupOf K).map π = Subgroup.centralizer {π tK} := by
  intro q e s₀ V D W M H K π
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  let sC : C t := ⟨s₀, hsC⟩
  have hsC2 : orderOf sC = 2 := by rw [← Subgroup.orderOf_coe]; exact hs2
  have hsCt : sC ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  have hC := card_centralizer_of_layer_preimage_index_two n hn S fS hG t ht2 hnonab hcentral hnc
    p f hp hpodd hf hmodel hN hY
  obtain ⟨hDs, hRs, hRcyc, hKs, hDmap, hVmap, hcentR, d, hd4, hd2, hds, hinv⟩ :=
    field_factor_one_trivial_core_four_group_data n hn S fS hG t ht2 hnonab hcentral hnc
      p f hp hpodd hf hmodel hN hC sC hsC2 hsCt
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have hVcomm : ∀ a b : V, a * b = b * a := mul_comm_of_exponent_two hV.exponent_two
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hDG : D = (ActualFourGroupCentralizer.D sC).map (C t).subtype := by
    change Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) :
      Set G) = _
    rw [hDmap, centralizer_zpowers_sup_zpowers]
  have hDcard : Nat.card D = 2 * MatrixTorus.torusSize q := by
    rw [hDG, Subgroup.card_map_of_injective (C t).subtype_injective, hDs]
  set W₀ : Subgroup G := ((ActualFourGroupCentralizer.R sC).map
    (ActualFourGroupCentralizer.D sC).subtype).map (C t).subtype with hW₀def
  have hW₀D : W₀ ≤ D := by
    rw [hDG]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hW₀card : Nat.card W₀ = MatrixTorus.torusSize q / 2 := by
    rw [hW₀def, Subgroup.card_map_of_injective (C t).subtype_injective,
      Subgroup.card_map_of_injective (ActualFourGroupCentralizer.D sC).subtype_injective, hRs]
  have hW₀cyc : IsCyclic W₀ := by
    have hinj : Function.Injective
        ((C t).subtype.comp (ActualFourGroupCentralizer.D sC).subtype) :=
      (C t).subtype_injective.comp (ActualFourGroupCentralizer.D sC).subtype_injective
    rw [hW₀def, Subgroup.map_map]
    exact isCyclic_of_surjective _ (Subgroup.equivMapOfInjective _ _ hinj).surjective
  have hqodd : Odd q := hpodd.pow
  have hmodd : Odd (MatrixTorus.torusSize q / 2) := MatrixTorus.torusSize_half_odd hqodd
  have hm2 : MatrixTorus.torusSize q = 2 * (MatrixTorus.torusSize q / 2) :=
    MatrixTorus.torusSize_two_mul_half hqodd
  have hVD : V ≤ D := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (hVcomm ⟨w, hw⟩ ⟨v, hv⟩)
  have hdisj : Disjoint V W₀ := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hV.card_four, hW₀card]
    exact (show Nat.Coprime (2 ^ 2) _ from (Nat.coprime_two_left.mpr hmodd).pow_left 2)
  have hsup : V ⊔ W₀ = D := sup_eq_of_card_eq_mul hVD hW₀D hdisj (by
    rw [hDcard, hV.card_four, hW₀card]
    omega)
  have hW₀comm : ∀ a ∈ W₀, ∀ b ∈ W₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W₀)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, hcore, hDK, -, -⟩ :=
    klein_centralizer_odd_core V W₀ hV (hW₀card ▸ hmodd) hW₀comm hsup hdisj
  have hW : W = W₀ := hcore
  have hDC : D ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx t htV).symm
  have hcentW₀ : ∀ w ∈ W₀, w ≠ 1 → C t ⊓ Subgroup.centralizer {w} = D := by
    intro w hw hw1
    apply le_antisymm
    · intro x hx
      obtain ⟨hxC, hxw⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hy
      have hr1 : (⟨r', hr'⟩ : ActualFourGroupCentralizer.R sC) ≠ 1 := by
        intro h
        apply hw1
        have h' := congrArg (fun x : ActualFourGroupCentralizer.R sC =>
          (((x : ActualFourGroupCentralizer.D sC) : C t) : G)) h
        simpa using h'
      have hcx : (⟨x, hxC⟩ : C t) * ((r' : ActualFourGroupCentralizer.D sC) : C t) =
          ((r' : ActualFourGroupCentralizer.D sC) : C t) * ⟨x, hxC⟩ := by
        apply Subtype.ext
        simpa using Subgroup.mem_centralizer_singleton_iff.mp hxw
      have hxs := hcentR ⟨r', hr'⟩ hr1 ⟨x, hxC⟩ hcx
      change x ∈ Subgroup.centralizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G)
      rw [centralizer_zpowers_sup_zpowers]
      refine Subgroup.mem_inf.mpr ⟨hxC, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa using congrArg Subtype.val hxs
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨hDC hx, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hDK hx) w hw).symm
  have hm3 : 3 ≤ MatrixTorus.torusSize q / 2 := by
    have h5 : 5 ≤ q := by
      obtain ⟨k, hk⟩ := hqodd
      omega
    have hT : 4 ≤ MatrixTorus.torusSize q := by
      unfold MatrixTorus.torusSize
      split_ifs <;> omega
    obtain ⟨k, hk⟩ := hmodd
    omega
  obtain ⟨w₁, hw₁, hw₁1⟩ : ∃ w ∈ W₀, w ≠ 1 := by
    by_contra! hall
    have h0 : W₀ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [h0, Subgroup.card_bot] at hW₀card
    omega
  have hCW : C t ⊓ Subgroup.centralizer (W₀ : Set G) = D := by
    apply le_antisymm
    · rw [← hcentW₀ w₁ hw₁ hw₁1]
      exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw₁))
    · exact le_inf hDC hDK
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
  set dG : G := ((d : C t) : G) with hdGdef
  have hdC : dG ∈ C t := (d : C t).2
  have hdM : dG ∈ Subgroup.normalizer (V : Set G) := by
    have h : ∀ x : C t, x ∈ ActualFourGroupNormalizer.K sC →
        (x : G) ∈ Subgroup.normalizer (V : Set G) := by
      intro x hx
      rw [hKsC, Subgroup.mem_subgroupOf] at hx
      exact hx
    exact h _ d.2
  have hdG4 : orderOf dG = 4 := by
    rw [hdGdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hd4]
  have hdG2 : dG ^ 2 = t := by
    have h := congrArg (fun x : ActualFourGroupNormalizer.K sC => ((x : C t) : G)) hd2
    simp only [Subgroup.coe_pow] at h
    exact h
  have hdGs : dG * s₀ * dG⁻¹ = t * s₀ := by
    have h := congrArg (fun x : C t => (x : G)) hds
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have hdGW : ∀ w ∈ W₀, dG * w * dG⁻¹ = w⁻¹ := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have h := congrArg (fun x : C t => (x : G)) (hinv ⟨y, hy⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r n)).property _
  have hVS : V ≤ (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr (fS (s n)).property)
  have hsurj : Function.Surjective V.normalizerMonoidHom := MonoidHom.range_eq_top.mp
    ((CFSG.Semidihedral.Local.perfect_semidihedral_full_local_fusion n hn S fS).1 V hVS hV).1
  have hW1 : W ≠ ⊥ := by
    rw [hW]
    intro h0
    rw [h0, Subgroup.card_bot] at hW₀card
    omega
  have hWcyc : IsCyclic W := by rw [hW]; exact hW₀cyc
  have hWodd : Odd (Nat.card W) := by rw [hW, hW₀card]; exact hmodd
  have hsup' : V ⊔ W = D := by rw [hW]; exact hsup
  have hdisj' : Disjoint V W := by rw [hW]; exact hdisj
  have hCW' : C t ⊓ Subgroup.centralizer (W : Set G) = D := by rw [hW]; exact hCW
  have hdGW' : ∀ w ∈ W, dG * w * dG⁻¹ = w⁻¹ := by rw [hW]; exact hdGW
  have hdCM : dG ∈ C t ⊓ Subgroup.normalizer (V : Set G) := Subgroup.mem_inf.mpr ⟨hdC, hdM⟩
  obtain ⟨hMH, hCH, hCHcard, hdih, hVsyl, hKMset, hKH, hinvH, hMcard, hNK, hMKcard, hCKV, hR,
      hH2, hWZ, hcases, hVWk, hVWsyl, hCX⟩ :=
    cyclic_four_group_centralizer_torus_has_two_small_normalizer_quotients n hn S fS t ht s₀ rfl
      V rfl W (Nat.card W) hW1 hWcyc rfl hWodd hsup' hdisj' hCW' hsurj dG hdCM hdG4 hdG2 hdGs
      hdGW'
  have hWD' : W ≤ D := hsup' ▸ le_sup_right
  refine ⟨hC, hW1, hWcyc, hWodd, ?_, ⟨hsup', hdisj', fun v hv w hw =>
    Subgroup.mem_centralizer_iff.mp (hWD' hw) v hv⟩, by rw [hW]; exact hcentW₀, hCH, hCHcard,
    ⟨dG, by rw [hCH]; exact hdCM, hdG4, hdG2, hdGs, hdGW', hdih⟩, hMH, hKMset, hVsyl, hKH, hinvH,
    hMcard, ?_, hCKV, hR, hH2, hWZ, hcases, hVWk, hVWsyl, hCX⟩
  · rw [hW, hW₀card, Int.natCast_ediv,
      ActualFourGroupCentralizer.torusSize_signed (by omega : 1 ≤ q)]
    rfl
  · rw [← Subgroup.card_map_of_injective K.subtype_injective, hNK]
    exact hMKcard

end CFSG.Semidihedral.Principal
