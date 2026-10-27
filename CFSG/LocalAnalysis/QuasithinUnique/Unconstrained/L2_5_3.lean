module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Setting
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Product

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem charTwo_sup_of_le_normalizer {K N : Subgroup G} (hK : CharTwo K) (hN : IsPGroup 2 N)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) : CharTwo (K ⊔ N) := by
  set J := K ⊔ N with hJ
  set P := pCoreOf 2 K with hP
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K
  have hPK : P ≤ K := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K
  have hKP : K ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 K
  have hKJ : K ≤ J := le_sup_left
  have hNJ : N ≤ J := le_sup_right
  set D := P ⊔ N with hD
  have hD2 : IsPGroup 2 ↥D := hP2.to_sup_of_normal_right' hN (hPK.trans hKN)
  have hDJ : D ≤ J := sup_le (hPK.trans hKJ) hNJ
  have hKD : K ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf hKP hKN).trans (Subgroup.inf_normalizer_le_normalizer_sup P N)
  have hND : N ≤ Subgroup.normalizer (D : Set G) := le_sup_right.trans Subgroup.le_normalizer
  have hJD : J ≤ Subgroup.normalizer (D : Set G) := sup_le hKD hND
  have hDR : D ≤ pCoreOf 2 J :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 D J hDJ
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hDJ).mpr hJD) hD2
  have hC2 : IsPGroup 2 ↥(J ⊓ Subgroup.centralizer (D : Set G)) := by
    let κ : ↥K →* MulAut ↥D := D.normalizerMonoidHom.comp (Subgroup.inclusion hKD)
    let ν : ↥N →* MulAut ↥D := D.normalizerMonoidHom.comp (Subgroup.inclusion hND)
    have hA : IsPGroup 2 ↥ν.range :=
      hN.of_surjective ν.rangeRestrict (MonoidHom.rangeRestrict_surjective ν)
    have hker : IsPGroup 2 κ.ker := by
      intro x
      have hxK : (x.1 : G) ∈ K := x.1.2
      have hxc : (x.1 : G) ∈ Subgroup.centralizer (D : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hx1 : κ x.1 = 1 := x.2
        have := congrArg (fun φ : MulAut ↥D => ((φ ⟨w, hw⟩ : ↥D) : G)) hx1
        simp only [κ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
          Subgroup.coe_inclusion, MulAut.one_apply] at this
        calc w * (x.1 : G) = (x.1 : G) * w * (x.1 : G)⁻¹ * (x.1 : G) := by rw [this]
          _ = (x.1 : G) * w := by group
      have hxP : (x.1 : G) ∈ P :=
        hK ⟨hxK, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hxc⟩
      obtain ⟨m, hm⟩ := hP2 ⟨(x.1 : G), hxP⟩
      refine ⟨m, ?_⟩
      have hm' : (x.1 : G) ^ 2 ^ m = 1 := congrArg Subtype.val hm
      apply Subtype.ext
      apply Subtype.ext
      simpa using hm'
    have hY : IsPGroup 2 (ν.range.comap κ) := hA.comap_of_ker_isPGroup κ hker
    set Y' : Subgroup G := (ν.range.comap κ).map K.subtype with hY'
    have hY'2 : IsPGroup 2 Y' := hY.map K.subtype
    have hY'N : Y' ≤ Subgroup.normalizer (N : Set G) := by
      rintro _ ⟨k, -, rfl⟩
      exact hKN k.2
    have hYN2 : IsPGroup 2 ↥(Y' ⊔ N) := hY'2.to_sup_of_normal_right' hN hY'N
    refine hYN2.to_le ?_
    intro c hc
    have hcJ : c ∈ ((K ⊔ N : Subgroup G) : Set G) := hc.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K N hKN] at hcJ
    obtain ⟨k, hk, n, hn, hkn⟩ := hcJ
    have hcc := Subgroup.mem_centralizer_iff.mp hc.2
    have hnD : n ∈ D := (le_sup_right : N ≤ P ⊔ N) hn
    have hact : ∀ w ∈ D, k * w * k⁻¹ = n⁻¹ * w * n := by
      intro w hw
      have hy : n⁻¹ * w * n ∈ D := D.mul_mem (D.mul_mem (D.inv_mem hnD) hw) hnD
      have h1 := hcc _ hy
      rw [← hkn] at h1
      calc k * w * k⁻¹ = (k * n * (n⁻¹ * w * n)) * n⁻¹ * k⁻¹ := by group
        _ = (n⁻¹ * w * n * (k * n)) * n⁻¹ * k⁻¹ := by rw [← h1]
        _ = n⁻¹ * w * n := by group
    have hkY : (⟨k, hk⟩ : ↥K) ∈ ν.range.comap κ := by
      rw [Subgroup.mem_comap]
      refine ⟨⟨n⁻¹, N.inv_mem hn⟩, ?_⟩
      ext w
      simp only [ν, κ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.coe_inclusion, inv_inv]
      exact (hact w w.2).symm
    have hkY' : k ∈ Y' := Subgroup.mem_map.mpr ⟨⟨k, hk⟩, hkY, rfl⟩
    rw [← hkn]
    exact Subgroup.mul_mem_sup hkY' hn
  have hJC : J ≤ Subgroup.normalizer ((J ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf J J _
      Subgroup.le_normalizer
      (hJD.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer D))
  have hCR : J ⊓ Subgroup.centralizer (D : Set G) ≤ pCoreOf 2 J :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ J inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hJC) hC2
  intro x hx
  exact hCR ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hDR) hx.2⟩

end Product

section Lemma253

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem lemma253_one (h : UniqueSetting G T M) {H U HU : Subgroup G} {k : ℕ}
    (B : Fin k → Subgroup G) (hB : ∀ i, B i ≤ H ∧ IsPGroup 2 (B i))
    (hH : H = ⨅ i, Subgroup.normalizer (B i : Set G)) (hpair : IsUPair M H U HU)
    (hQ : pCoreOf 2 H ≤ pCoreOf 2 HU) :
    CharTwo (H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G)) := by
  obtain ⟨-, hN0⟩ := hpair.1.1.charTwo_normalizer_core h hpair.1.2.1 hpair.1.2.2.2.1
  have hHN : ∀ i, H ≤ Subgroup.normalizer (B i : Set G) := fun i => hH.le.trans (iInf_le _ i)
  have hBN : ∀ i j, B j ≤ Subgroup.normalizer (B i : Set G) := fun i j => (hB j).1.trans (hHN i)
  have hBQ : ∀ i, B i ≤ pCoreOf 2 HU := by
    intro i
    refine le_trans ?_ hQ
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (B i) H (hB i).1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hB i).1).mpr (hHN i)) (hB i).2
  have hBM : ∀ i, B i ≤ Subgroup.normalizer (pCoreOf 2 HU : Set G) :=
    fun i => (hBQ i).trans Subgroup.le_normalizer
  have := charTwo_inf_iInf_normalizer hN0 k B (fun i => (hB i).2) hBM (fun i j _ => hBN i j)
  rw [← hH, inf_comm] at this
  exact this

omit [Finite G] in
theorem lemma253_two {M H U HU Q₁ : Subgroup G} (hpair : IsUPair M H U HU) (hQ₁H : Q₁ ≤ H)
    (hQ₁ : IsPGroup 2 Q₁) (hnorm : HU ≤ Subgroup.normalizer (Q₁ : Set G)) :
    IsUPair M H U (HU ⊔ Q₁) := by
  obtain ⟨⟨hconf, hUHU, hcore, hchar, hHUM⟩, hHUH⟩ := hpair
  have hQHU : pCoreOf 2 HU ≤ HU := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 HU
  have hQ2 : IsPGroup 2 (pCoreOf 2 HU) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 HU
  have hHUN : HU ≤ Subgroup.normalizer (pCoreOf 2 HU : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 HU
  have hQQ₁ : IsPGroup 2 ↥(pCoreOf 2 HU ⊔ Q₁) :=
    hQ2.to_sup_of_normal_right' hQ₁ (hQHU.trans hnorm)
  have hQQ₁H : pCoreOf 2 HU ⊔ Q₁ ≤ HU ⊔ Q₁ := sup_le (hQHU.trans le_sup_left) le_sup_right
  have hnormQQ₁ : HU ⊔ Q₁ ≤ Subgroup.normalizer ((pCoreOf 2 HU ⊔ Q₁ : Subgroup G) : Set G) := by
    refine sup_le ((le_inf hHUN hnorm).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)) ?_
    exact le_sup_right.trans Subgroup.le_normalizer
  have hcore' : pCoreOf 2 HU ⊔ Q₁ ≤ pCoreOf 2 (HU ⊔ Q₁) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hQQ₁H
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQQ₁H).mpr hnormQQ₁) hQQ₁
  refine ⟨⟨hconf, hUHU.trans le_sup_left, ?_, charTwo_sup_of_le_normalizer hchar hQ₁ hnorm,
    fun hM => hHUM (le_sup_left.trans hM)⟩, sup_le hHUH hQ₁H⟩
  intro hbot
  rw [hbot] at hcore'
  exact hcore (le_bot_iff.mp (le_sup_left.trans hcore'))

end Lemma253

section Fitting

variable {G : Type*} [Group G] [Finite G]

theorem centralizer_pCore_oddCore_le_of_no_component {H : Subgroup G}
    (hE : ∀ L : Subgroup G, ¬ IsComponentIn L H) :
    H ⊓ Subgroup.centralizer ((pCoreOf 2 H ⊔ oddCoreIn H : Subgroup G) : Set G) ≤
      pCoreOf 2 H ⊔ oddCoreIn H := by
  have hlayer : CFSG.layer ↥H = ⊥ := by
    refine CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => hE (K.map H.subtype) ⟨Subgroup.map_subtype_le K, ?_⟩
    have : (K.map H.subtype).subgroupOf H = K :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective K
    rw [this]
    exact hK
  have hF : CFSG.generalizedFitting ↥H = CFSG.fittingSubgroup ↥H := by
    rw [CFSG.generalizedFitting, hlayer, sup_bot_eq]
  have hfit : CFSG.fittingSubgroup ↥H ≤ CFSG.pCore 2 ↥H ⊔ CFSG.oddCore ↥H := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.1.1 = 2
    · rw [hp]
      exact le_sup_left
    · refine le_trans ?_ le_sup_right
      have hq : Nat.Prime p.1.1 := Nat.prime_of_mem_primeFactors p.1.2
      have hqodd : Odd p.1.1 := hq.odd_of_ne_two hp
      refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p.1.1) (G := ↥H)).exists_card_eq
      rw [hn]
      exact hqodd.pow
  intro x hx
  have hmap : (CFSG.pCore 2 ↥H ⊔ CFSG.oddCore ↥H).map H.subtype = pCoreOf 2 H ⊔ oddCoreIn H := by
    rw [Subgroup.map_sup, pCoreOf]
    rfl
  have hx' : (⟨x, hx.1⟩ : ↥H) ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥H : Set ↥H) := by
    rw [hF, Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : (w : G) ∈ pCoreOf 2 H ⊔ oddCoreIn H := by
      rw [← hmap]
      exact ⟨w, hfit hw, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 _ hw')
  have := CFSG.centralizer_generalizedFitting_le ↥H hx'
  rw [hF] at this
  rw [← hmap]
  exact ⟨_, hfit this, rfl⟩

end Fitting


section ComponentFree

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem oddCoreIn_inf_isPGroup_eq_bot {Q : Subgroup G} (hQ : IsPGroup 2 Q) (H : Subgroup G) :
    oddCoreIn H ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (oddCoreIn H)) (Nat.card Q) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr (odd_card_oddCoreIn H))
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

omit [Finite G] in
theorem commute_of_inverts {a u y : G} (ha : a⁻¹ * y * a = y⁻¹) (hu : u * y * u⁻¹ = y⁻¹) :
    a⁻¹ * u * y = y * (a⁻¹ * u) := by
  have h1 : a⁻¹ * y⁻¹ = y * a⁻¹ := by
    have h : a⁻¹ * y⁻¹ * a = y := by
      calc a⁻¹ * y⁻¹ * a = (a⁻¹ * y * a)⁻¹ := by group
        _ = y := by rw [ha, inv_inv]
    calc a⁻¹ * y⁻¹ = (a⁻¹ * y⁻¹ * a) * a⁻¹ := by group
      _ = y * a⁻¹ := by rw [h]
  calc a⁻¹ * u * y = a⁻¹ * (u * y * u⁻¹) * u := by group
    _ = a⁻¹ * y⁻¹ * u := by rw [hu]
    _ = y * a⁻¹ * u := by rw [h1]
    _ = y * (a⁻¹ * u) := by group

theorem exists_component_of_maximal (h : UniqueSetting G T M) {H S : Subgroup G} {z : G}
    (hT : Tuple25 T M H S z) (hX : ∀ X : Subgroup G, S ≤ X → CharTwo X → X ≤ M)
    {k : ℕ} (B : Fin k → Subgroup G) (hB : ∀ i, B i ≤ H ∧ IsPGroup 2 (B i))
    (hH : H = ⨅ i, Subgroup.normalizer (B i : Set G)) {U HU : Subgroup G}
    (hpair : IsUPair M H U HU) (hUS : U ≤ S)
    (hmax : ∀ U' HU' : Subgroup G, IsUPair M H U' HU' → U ≤ U' → HU ≤ HU' →
      U' = U ∧ HU' = HU) :
    ∃ L : Subgroup G, IsComponentIn L H := by
  by_contra hcomp
  have hE : ∀ L : Subgroup G, ¬ IsComponentIn L H := fun L hL => hcomp ⟨L, hL⟩
  have hHUH : HU ≤ H := hpair.2
  have hUHU : U ≤ HU := hpair.1.2.1
  have hQHU : pCoreOf 2 HU ≤ HU := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 HU
  have hQ2 : IsPGroup 2 (pCoreOf 2 HU) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 HU
  have hHUN : HU ≤ Subgroup.normalizer (pCoreOf 2 HU : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 HU
  have hbang : ∀ Q₁ : Subgroup G, Q₁ ≤ H → IsPGroup 2 Q₁ →
      HU ≤ Subgroup.normalizer (Q₁ : Set G) → Q₁ ≤ pCoreOf 2 HU := by
    intro Q₁ hQ₁H hQ₁ hnorm
    have h3 := (hmax U (HU ⊔ Q₁) (lemma253_two hpair hQ₁H hQ₁ hnorm) le_rfl le_sup_left).2
    have hQ₁HU : Q₁ ≤ HU := le_sup_right.trans h3.le
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 Q₁ HU hQ₁HU
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQ₁HU).mpr hnorm) hQ₁
  have hR₀2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hR₀H : pCoreOf 2 H ≤ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hHR₀ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hO2H : pCoreOf 2 H ≤ pCoreOf 2 HU := hbang _ hR₀H hR₀2 (hHUH.trans hHR₀)
  have hchar1 : CharTwo (H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G)) :=
    lemma253_one h B hB hH hpair hO2H
  have hHUHN : HU ≤ H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G) := le_inf hHUH hHUN
  have hQHN : pCoreOf 2 (H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G)) = pCoreOf 2 HU := by
    refine le_antisymm ?_ ?_
    · exact hbang _ ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_left)
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
        (hHUHN.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _))
    · exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _
        (hQHU.trans hHUHN)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hQHU.trans hHUHN)).mpr inf_le_right) hQ2
  have hpair' : IsUPair M H U (H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G)) :=
    ⟨⟨hpair.1.1, hUHU.trans hHUHN, by rw [hQHN]; exact hpair.1.2.2.1, hchar1,
      fun hM => hpair.1.2.2.2.2 (hHUHN.trans hM)⟩, inf_le_left⟩
  have hHNeq : H ⊓ Subgroup.normalizer (pCoreOf 2 HU : Set G) = HU :=
    (hmax U _ hpair' le_rfl hHUHN).2
  have hUsyl : IsSylowTwoOf U HU := by
    obtain ⟨U₁, hUU₁, hU₁⟩ := exists_isSylowTwoOf_of_le hUHU hpair.1.1.2.2.1
    have hpair₁ : IsUPair M H U₁ HU :=
      ⟨⟨hpair.1.1.of_le hU₁.isPGroup hUU₁, hU₁.le, hpair.1.2.2.1, hpair.1.2.2.2.1,
        hpair.1.2.2.2.2⟩, hHUH⟩
    have := (hmax U₁ HU hpair₁ hUU₁ le_rfl).1
    rwa [this] at hU₁
  have hQU : pCoreOf 2 HU ≤ U := hUsyl.le_of_normalizes hQHU hHUN hQ2
  have hzT : z ∈ centerOf T := hT.z_mem
  have hST : S ≤ T := hT.lt.le
  have hzS : z ∈ S := hT.center_le hzT
  have hzcS : z ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hST) hzT.2
  have hzH : z ∈ H := hT.sylow.le hzS
  have hzQc : z ∈ Subgroup.centralizer (pCoreOf 2 HU : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hQU.trans hUS)) hzcS
  have hzQ : z ∈ pCoreOf 2 HU := by
    have hzHU : z ∈ HU := by
      rw [← hHNeq]
      exact ⟨hzH, Subgroup.centralizer_le_normalizer _ hzQc⟩
    exact hpair.1.2.2.2.1 ⟨hzHU, hzQc⟩
  have hz2' : orderOf z = 2 := orderOf_eq_prime hT.z_sq hT.z_ne_one
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2', pow_one])
  have hR₀S : pCoreOf 2 H ≤ S :=
    hT.sylow.le_of_normalizes hR₀H hHR₀ hR₀2
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    refine (Subgroup.zpowers_le.mpr ?_)
    exact hHR₀ hzH
  have hD2 : IsPGroup 2 ↥(pCoreOf 2 H ⊔ Subgroup.zpowers z) :=
    hR₀2.to_sup_of_normal_left' hZ2 hzN
  have hzD : z ∈ pCoreOf 2 H ⊔ Subgroup.zpowers z :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hDQ : pCoreOf 2 H ⊔ Subgroup.zpowers z ≤ pCoreOf 2 HU :=
    sup_le hO2H (Subgroup.zpowers_le.mpr hzQ)
  have hSD : S ≤ Subgroup.normalizer ((pCoreOf 2 H ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun s hs d hd => ?_
    have key : pCoreOf 2 H ⊔ Subgroup.zpowers z ≤
        (pCoreOf 2 H ⊔ Subgroup.zpowers z).comap (MulAut.conj s).toMonoidHom := by
      refine sup_le (fun r hr => ?_) (Subgroup.zpowers_le.mpr ?_)
      · have := Subgroup.le_normalizer_iff.mp hHR₀ s (hT.sylow.le hs) r hr
        exact Subgroup.mem_sup_left (by simpa [MulAut.conj_apply] using this)
      · have hcomm : s * z * s⁻¹ = z := by
          have := Subgroup.mem_centralizer_iff.mp hzcS s hs
          calc s * z * s⁻¹ = z * s * s⁻¹ := by rw [this]
            _ = z := by group
        rw [Subgroup.mem_comap]
        simpa [MulAut.conj_apply, hcomm] using hzD
    simpa [MulAut.conj_apply] using key hd
  have hDZ : (pCoreOf 2 H ⊔ Subgroup.zpowers z) ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro hbot
    have hz' : z ∈ (pCoreOf 2 H ⊔ Subgroup.zpowers z) ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
      ⟨hzD, hzT⟩
    rw [hbot] at hz'
    exact hT.z_ne_one (Subgroup.mem_bot.mp hz')
  have hcharD : CharTwo (Subgroup.normalizer ((pCoreOf 2 H ⊔ Subgroup.zpowers z :
      Subgroup G) : Set G)) :=
    charTwo_normalizer_of_inf_center h.qtke.2.1 h.sylow hD2 hDZ
  have hNM : Subgroup.normalizer ((pCoreOf 2 H ⊔ Subgroup.zpowers z : Subgroup G) : Set G) ≤ M :=
    hX _ hSD hcharD
  obtain ⟨-, hinv⟩ := IsGamma0.centralizer_le_and_inverts_oddCoreIn h hT.gamma0 hT.sylow_inf
    h.isSylowTwoOf_M hST hzT hT.z_ne_one hT.z_sq
  have hFstar := centralizer_pCore_oddCore_le_of_no_component hE
  have hY : H ≤ Subgroup.normalizer (oddCoreIn H : Set G) := le_normalizer_oddCoreIn H
  have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hT.z_sq)
  have hzinv : ∀ y ∈ oddCoreIn H, z * y * z⁻¹ = y⁻¹ := by
    intro y hy
    calc z * y * z⁻¹ = z⁻¹ * y * z := by rw [hzz]
      _ = y⁻¹ := hinv y hy
  have hconj : ∀ g ∈ H, g * z * g⁻¹ ∈
      pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H := by
    intro g hg
    have hu : (z⁻¹ * (g * z * g⁻¹)) ∈ H ⊓ Subgroup.centralizer
        ((pCoreOf 2 H ⊔ oddCoreIn H : Subgroup G) : Set G) := by
      have hC : pCoreOf 2 H ⊔ oddCoreIn H ≤
          Subgroup.centralizer ({z⁻¹ * (g * z * g⁻¹)} : Set G) := by
        refine sup_le (fun r hr => ?_) (fun y hy => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have hr' : g⁻¹ * r * g ∈ pCoreOf 2 H := by
            have := Subgroup.le_normalizer_iff.mp hHR₀ g⁻¹ (H.inv_mem hg) r hr
            simpa using this
          have hzr : z * (g⁻¹ * r * g) = (g⁻¹ * r * g) * z :=
            (Subgroup.mem_centralizer_iff.mp hzcS _ (hR₀S hr')).symm
          have hzr' : z⁻¹ * r = r * z⁻¹ := by
            have := (Subgroup.mem_centralizer_iff.mp hzcS r (hR₀S hr))
            calc z⁻¹ * r = z⁻¹ * (r * z) * z⁻¹ := by group
              _ = z⁻¹ * (z * r) * z⁻¹ := by rw [this]
              _ = r * z⁻¹ := by group
          have hur : (g * z * g⁻¹) * r = r * (g * z * g⁻¹) := by
            calc (g * z * g⁻¹) * r = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by group
              _ = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by rw [hzr]
              _ = r * (g * z * g⁻¹) := by group
          exact (calc z⁻¹ * (g * z * g⁻¹) * r = z⁻¹ * ((g * z * g⁻¹) * r) := by group
            _ = z⁻¹ * (r * (g * z * g⁻¹)) := by rw [hur]
            _ = (z⁻¹ * r) * (g * z * g⁻¹) := by group
            _ = r * z⁻¹ * (g * z * g⁻¹) := by rw [hzr']
            _ = r * (z⁻¹ * (g * z * g⁻¹)) := by group).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have hy' : g⁻¹ * y * g ∈ oddCoreIn H := by
            have := Subgroup.le_normalizer_iff.mp hY g⁻¹ (H.inv_mem hg) y hy
            simpa using this
          have hzy := hinv y hy
          have hgy : (g * z * g⁻¹) * y * (g * z * g⁻¹)⁻¹ = y⁻¹ := by
            have h2 := hzinv _ hy'
            calc (g * z * g⁻¹) * y * (g * z * g⁻¹)⁻¹
                = g * (z * (g⁻¹ * y * g) * z⁻¹) * g⁻¹ := by group
              _ = g * (g⁻¹ * y * g)⁻¹ * g⁻¹ := by rw [h2]
              _ = y⁻¹ := by group
          exact (commute_of_inverts hzy hgy).symm
      exact ⟨H.mul_mem (H.inv_mem hzH) (H.mul_mem (H.mul_mem hg hzH) (H.inv_mem hg)),
        Subgroup.mem_centralizer_iff.mpr fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mp (hC hx)⟩
    have hw := hFstar hu
    have hle : pCoreOf 2 H ⊔ oddCoreIn H ≤ pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H :=
      sup_le_sup_right le_sup_left _
    have hmem : z⁻¹ * (g * z * g⁻¹) ∈ pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H := hle hw
    have := Subgroup.mul_mem _ (Subgroup.mem_sup_left hzD) hmem
    simpa using this
  have hDYn : H ≤ Subgroup.normalizer
      ((pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun g hg y hy => ?_
    have key : pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H ≤
        (pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (sup_le (fun r hr => ?_) (Subgroup.zpowers_le.mpr ?_)) (fun y hy => ?_)
      · have := Subgroup.le_normalizer_iff.mp hHR₀ g hg r hr
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (by simpa [MulAut.conj_apply] using this))
      · rw [Subgroup.mem_comap]
        simpa [MulAut.conj_apply] using hconj g hg
      · have := Subgroup.le_normalizer_iff.mp hY g hg y hy
        exact Subgroup.mem_sup_right (by simpa [MulAut.conj_apply] using this)
    simpa [MulAut.conj_apply] using key hy
  have hDnY : pCoreOf 2 H ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    (sup_le hR₀H (Subgroup.zpowers_le.mpr hzH)).trans hY
  have hDeq : pCoreOf 2 HU ⊓ (pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H) ≤
      pCoreOf 2 H ⊔ Subgroup.zpowers z := by
    intro q hq
    have hqDY : q ∈ ((pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H : Subgroup G) : Set G) := hq.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDnY] at hqDY
    obtain ⟨d, hd, y, hy, hdy⟩ := hqDY
    have hdy : d * y = q := hdy
    have hyQ : y ∈ pCoreOf 2 HU := by
      have : y = d⁻¹ * q := by rw [← hdy]; group
      rw [this]
      exact (pCoreOf 2 HU).mul_mem ((pCoreOf 2 HU).inv_mem (hDQ hd)) hq.1
    have hy1 : y ∈ oddCoreIn H ⊓ pCoreOf 2 HU := ⟨hy, hyQ⟩
    rw [oddCoreIn_inf_isPGroup_eq_bot hQ2 H] at hy1
    have hy1' : y = 1 := Subgroup.mem_bot.mp hy1
    rw [← hdy, hy1', mul_one]
    exact hd
  have hDeq' : pCoreOf 2 H ⊔ Subgroup.zpowers z =
      pCoreOf 2 HU ⊓ (pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H) :=
    le_antisymm (le_inf hDQ le_sup_left) hDeq
  have hHUD : HU ≤ Subgroup.normalizer ((pCoreOf 2 H ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := by
    have key : HU ≤ Subgroup.normalizer
        ((pCoreOf 2 HU ⊓ (pCoreOf 2 H ⊔ Subgroup.zpowers z ⊔ oddCoreIn H) : Subgroup G) :
          Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _ hHUN
        (hHUH.trans hDYn)
    rwa [← hDeq'] at key
  exact hpair.1.2.2.2.2 (hHUD.trans hNM)

end ComponentFree

end CFSG.QuasithinUnique
