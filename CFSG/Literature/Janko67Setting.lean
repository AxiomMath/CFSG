module

public import CFSG.Literature.Janko67ModelSub

public section

namespace CFSG.Literature.Janko67

open CFSG CFSG.RankThree.GF2n.Parrott CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial


theorem map_Q_eq {G : Type} [Group G] (S : Setting G) (f : S.M ≃* C0) :
    S.Q.map (f : S.M →* C0) = CFSG.pCore 2 C0 := by
  rw [Setting.Q_eq_pCore S]
  exact CFSG.pCore_map_iso 2 f


theorem exists_setting_mulEquiv
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 2 3 1) {x : X} (hx : orderOf x = 2)
    (hxS : ∃ S : Sylow 2 X, x ∈ (S : Subgroup X) ∧ ∀ s ∈ (S : Subgroup X), x * s = s * x)
    {G : Type} [Group G] {j : G} (hj : orderOf j = 2)
    (e : Subgroup.centralizer ({j} : Set G) ≃* Subgroup.centralizer ({x} : Set X)) :
    ∃ (S : Setting G) (f : S.M ≃* C0), S.z = j ∧ f S.zM = tC := by
  classical
  obtain ⟨φ⟩ := CFSG.ComponentClassification.CatFactsSmall.PSp43.equiv_of_lieModel hX
  let y : QP45.originalSubgroup := φ x
  have hy2 : orderOf y = 2 := by
    rw [show y = φ x from rfl, MulEquiv.orderOf_eq, hx]
  obtain ⟨Sx, hxSx, hxcent⟩ := hxS
  have hcardX : Nat.card X = 25920 := by
    rw [Nat.card_congr φ.toEquiv]
    exact card_QP45
  have hfacX : (Nat.card X).factorization 2 = 6 := by
    rw [hcardX, show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hfinX : Finite X := Nat.finite_of_card_ne_zero (by rw [hcardX]; norm_num)
  have hcardSx : Nat.card Sx = 64 := by
    rw [@Sylow.card_eq_multiplicity X _ hfinX 2 ⟨Nat.prime_two⟩ Sx, hfacX]
    norm_num
  have hmap_le : (Sx : Subgroup X).map (φ : X →* QP45.originalSubgroup) ≤
      Subgroup.centralizer ({y} : Set QP45.originalSubgroup) := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    show φ s * φ x = φ x * φ s
    rw [← map_mul, ← map_mul, hxcent s hs]
  have hdvd : 64 ∣ Nat.card (Subgroup.centralizer ({y} : Set QP45.originalSubgroup)) := by
    have hcardmap : Nat.card ((Sx : Subgroup X).map (φ : X →* QP45.originalSubgroup)) = 64 := by
      rw [Subgroup.card_map_of_injective (f := (φ : X →* QP45.originalSubgroup)) φ.injective,
        hcardSx]
    have h := Subgroup.card_subgroup_dvd_card
      (((Sx : Subgroup X).map (φ : X →* QP45.originalSubgroup)).subgroupOf
        (Subgroup.centralizer ({y} : Set QP45.originalSubgroup)))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv, hcardmap] at h
  have hyconj : IsConj y ⟨t, t_mem_Q⟩ := by
    rcases qp45_involution_classes y hy2 with h | h
    · exact h
    · exfalso
      rw [CFSG.GroupTheory.card_centralizer_eq_of_isConj h, qp45_card_centralizer_ut] at hdvd
      norm_num at hdvd
  obtain ⟨g, hg⟩ := isConj_iff.mp hyconj
  let cx : Subgroup.centralizer ({x} : Set X) ≃*
      Subgroup.centralizer ({y} : Set QP45.originalSubgroup) :=
    CFSG.Monster.GMS.centralizerMulEquiv φ x
  let cg : Subgroup.centralizer ({y} : Set QP45.originalSubgroup) ≃* C0 :=
    (CFSG.Monster.GMS.centralizerMulEquiv (MulAut.conj g) y).trans
      (MulEquiv.subgroupCongr (by
        rw [show MulAut.conj g y = ⟨t, t_mem_Q⟩ from hg]))
  let f₀ : Subgroup.centralizer ({j} : Set G) ≃* C0 := e.trans (cx.trans cg)
  have hzM_center : (⟨j, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      Subgroup.centralizer ({j} : Set G)) ∈
      Subgroup.center (Subgroup.centralizer ({j} : Set G)) :=
    Subgroup.mem_center_iff.mpr fun w => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp w.2)
  have htC_sq : tC * tC = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp [tC, t_sq]
  have hf₀ : f₀ ⟨j, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = tC := by
    have hmem : f₀ ⟨j, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈
        Subgroup.zpowers tC := by
      have h := Subgroup.mem_map_of_mem (f₀ : Subgroup.centralizer ({j} : Set G) →* C0)
        hzM_center
      rwa [Subgroup.map_center_eq f₀, center_C0] at h
    rw [Setting.mem_zpowers_iff_of_mul_self htC_sq] at hmem
    rcases hmem with h1 | h1
    · exfalso
      have hord : orderOf (f₀ ⟨j, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) = 2 := by
        rw [MulEquiv.orderOf_eq]
        simpa [Subgroup.orderOf_coe] using hj
      rw [h1, orderOf_one] at hord
      omega
    · exact h1
  let Q : Subgroup (Subgroup.centralizer ({j} : Set G)) :=
    (CFSG.pCore 2 C0).comap (f₀ : Subgroup.centralizer ({j} : Set G) →* C0)
  have hQn : Q.Normal := CFSG.pCore_normal.comap _
  have hQe : IsExtraspecialPGroup 2 Q := by
    have hmap : Q.map (f₀ : Subgroup.centralizer ({j} : Set G) →* C0) = CFSG.pCore 2 C0 := by
      dsimp only [Q]
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr f₀.surjective, top_inf_eq]
    exact CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv
      ((f₀.subgroupMap Q).trans (MulEquiv.subgroupCongr hmap)).symm
      isExtraspecialPGroup_pCore_C0
  have hQc : Subgroup.centralizer (Q : Set (Subgroup.centralizer ({j} : Set G))) ≤ Q := by
    intro u hu
    change f₀ u ∈ CFSG.pCore 2 C0
    refine centralizer_pCore_C0_le (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
    have hvQ : f₀.symm v ∈ Q := by
      change f₀ (f₀.symm v) ∈ CFSG.pCore 2 C0
      rw [MulEquiv.apply_symm_apply]
      exact hv
    have h := Subgroup.mem_centralizer_iff.mp hu (f₀.symm v) hvQ
    simpa using congrArg f₀ h
  have hQl : ∀ P : Subgroup (Subgroup.centralizer ({j} : Set G)),
      P.Normal → IsPGroup 2 P → P ≤ Q := by
    intro P hPn hPp u hu
    have hle : P.map (f₀ : Subgroup.centralizer ({j} : Set G) →* C0) ≤ CFSG.pCore 2 C0 :=
      le_sSup ⟨hPn.map _ f₀.surjective, hPp.map _⟩
    exact hle (Subgroup.mem_map_of_mem (f₀ : Subgroup.centralizer ({j} : Set G) →* C0) hu)
  exact ⟨⟨j, hj, Q, hQn, hQe, hQc, hQl⟩, f₀, rfl, hf₀⟩

theorem width_eq_two {G : Type} [Group G] (S : Setting G) (f : S.M ≃* C0) : S.width = 2 := by
  have hcardQ : Nat.card S.Q = 32 := by
    rw [← Subgroup.card_map_of_injective (f := (f : S.M →* C0)) f.injective, map_Q_eq S f,
      card_pCore_C0]
  have hcardQG : Nat.card S.QG = 32 := by
    rw [Setting.card_QG_eq_card_Q, hcardQ]
  have hQt : Nat.card S.Qt = 16 := by
    have h := Setting.card_QG_eq S
    rw [hcardQG] at h
    omega
  have hfinQt : Finite S.Qt := Nat.finite_of_card_ne_zero (by rw [hQt]; norm_num)
  have hcardQt : Nat.card S.Qt = 2 ^ Module.finrank (ZMod 2) S.Qt := by
    rw [@Module.natCard_eq_pow_finrank (ZMod 2) S.Qt _ _ _
      (@Module.Finite.of_finite (ZMod 2) S.Qt _ _ _ hfinQt), Nat.card_zmod]
  have hdim : Module.finrank (ZMod 2) S.Qt = 4 := by
    have h : 2 ^ Module.finrank (ZMod 2) S.Qt = 2 ^ 4 := by
      rw [← hcardQt, hQt]
      norm_num
    exact Nat.pow_right_injective (by norm_num) h
  unfold Setting.width
  rw [hdim]

theorem card_Mbar_eq {G : Type} [Group G] [Finite G] (S : Setting G) (f : S.M ≃* C0) :
    Nat.card S.Mbar = 18 := by
  have hcardM : Nat.card S.M = 576 := by
    rw [Nat.card_congr f.toEquiv]
    exact qp45_card_centralizer_t
  have hcardQ : Nat.card S.Q = 32 := by
    rw [← Subgroup.card_map_of_injective (f := (f : S.M →* C0)) f.injective, map_Q_eq S f,
      card_pCore_C0]
  have hquot : Nat.card (S.M ⧸ S.Q) = 18 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup S.Q
    rw [hcardM, hcardQ] at h
    have hx : Nat.card (S.M ⧸ S.Q) * 32 = 18 * 32 := by
      simpa using h.symm
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hx
  rwa [← Nat.card_congr S.quotientEquivMbar.toEquiv]

theorem exists_sylow_eq_map_P0 {G : Type} [Group G] [Finite G] (S : Setting G) (f : S.M ≃* C0)
    (hf : f S.zM = tC) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = (P0.map (f.symm : C0 →* S.M)).map S.M.subtype ∧
      ∀ c ∈ (P : Subgroup G), (∀ d ∈ (P : Subgroup G), c * d = d * c) → c = 1 ∨ c = S.z := by
  classical
  let P' : Subgroup G := (P0.map (f.symm : C0 →* S.M)).map S.M.subtype
  have hP'leM : P' ≤ S.M := Subgroup.map_subtype_le _
  have hcardP' : Nat.card P' = 64 := by
    dsimp only [P']
    rw [Subgroup.card_map_of_injective (f := S.M.subtype) S.M.subtype_injective,
      Subgroup.card_map_of_injective (f := (f.symm : C0 →* S.M)) f.symm.injective, card_P0]
  have hP'p : IsPGroup 2 P' := IsPGroup.of_card (n := 6) (by rw [hcardP']; norm_num)
  have hfac576 : (576 : ℕ).factorization 2 = 6 := by
    rw [show (576 : ℕ) = 2 ^ 6 * 9 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcardM : Nat.card S.M = 576 := by
    rw [Nat.card_congr f.toEquiv]
    exact qp45_card_centralizer_t
  let P'M : Subgroup S.M := P'.subgroupOf S.M
  have hcardP'M : Nat.card P'M = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'leM).toEquiv, hcardP']
  have hP'Mcard : Nat.card P'M = 2 ^ (Nat.card S.M).factorization 2 := by
    rw [hcardP'M, hcardM, hfac576]
    norm_num
  let hSylowM : Sylow 2 S.M := Sylow.ofCard P'M hP'Mcard
  have ha1P0 : a1C ∈ P0 := Subgroup.subset_closure (by simp)
  have htC_mem_P0 : tC ∈ P0 := by
    have h : a1C * a1C = tC := by
      apply Subtype.ext
      apply Subtype.ext
      simp [a1C, tC, alpha1_sq]
    rw [← h]
    exact P0.mul_mem ha1P0 ha1P0
  have hsymm : f.symm tC = S.zM := f.symm_apply_eq.mpr hf.symm
  have hzM_mem : S.zM ∈ P0.map (f.symm : C0 →* S.M) :=
    hsymm ▸ Subgroup.mem_map_of_mem (f.symm : C0 →* S.M) htC_mem_P0
  have hzP' : S.z ∈ P' := Subgroup.mem_map_of_mem S.M.subtype hzM_mem
  have hz_central : ∀ d ∈ P', S.z * d = d * S.z := by
    intro d hd
    have h := Subgroup.mem_center_iff.mp S.zM_mem_center (⟨d, hP'leM hd⟩ : S.M)
    exact congrArg (fun x : S.M => (x : G)) h.symm
  have hcenter : ∀ c ∈ P', (∀ d ∈ P', c * d = d * c) → c = 1 ∨ c = S.z := by
    intro c hc hcc
    obtain ⟨cM, hcM, rfl⟩ := Subgroup.mem_map.mp hc
    obtain ⟨p, hp, hp_eq⟩ := Subgroup.mem_map.mp hcM
    have hp_cent : ∀ q ∈ P0, p * q = q * p := by
      intro q hq
      have hqP' : ((f.symm q : S.M) : G) ∈ P' :=
        Subgroup.mem_map_of_mem S.M.subtype (Subgroup.mem_map_of_mem _ hq)
      have hcomm := hcc ((f.symm q : S.M) : G) hqP'
      have hcommM : cM * f.symm q = f.symm q * cM := Subtype.ext hcomm
      have h := congrArg f hcommM
      rw [← hp_eq] at h
      simpa using h
    have hcardC0 : Nat.card C0 = 576 := qp45_card_centralizer_t
    have hP0card : Nat.card P0 = 2 ^ (Nat.card C0).factorization 2 := by
      rw [card_P0, hcardC0, hfac576]
      norm_num
    let hP0Sylow : Sylow 2 C0 := Sylow.ofCard P0 hP0card
    have hP0coe : (hP0Sylow : Subgroup C0) = P0 := Sylow.coe_ofCard P0 hP0card
    have hp' : p ∈ (hP0Sylow : Subgroup C0) := by rwa [hP0coe]
    have hp_cent' : ∀ d ∈ (hP0Sylow : Subgroup C0), p * d = d * p := by
      intro d hd
      exact hp_cent d (by rwa [hP0coe] at hd)
    rcases eq_one_or_eq_tC_of_mem_sylow hP0Sylow hp' hp_cent' with hp1 | hpt
    · left
      have hcM : cM = 1 := by rw [← hp_eq, hp1, map_one]
      exact congrArg (fun x : S.M => (x : G)) hcM
    · right
      have hcM : cM = S.zM := by
        rw [← hp_eq, hpt]
        exact hsymm
      exact congrArg (fun x : S.M => (x : G)) hcM
  have hNle : Subgroup.normalizer (P' : Set G) ≤ S.M := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hg' : g⁻¹ ∈ Subgroup.normalizer (P' : Set G) := Subgroup.inv_mem _ hg
    have hz'P' : g * S.z * g⁻¹ ∈ P' := (Subgroup.mem_normalizer_iff.mp hg S.z).mp hzP'
    have hz'cent : ∀ d ∈ P', (g * S.z * g⁻¹) * d = d * (g * S.z * g⁻¹) := by
      intro d hd
      have hd' : g⁻¹ * d * g ∈ P' := by
        have := (Subgroup.mem_normalizer_iff.mp hg' d).mp hd
        simpa using this
      calc (g * S.z * g⁻¹) * d = g * (S.z * (g⁻¹ * d * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * d * g) * S.z) * g⁻¹ := by rw [hz_central _ hd']
        _ = d * (g * S.z * g⁻¹) := by group
    rcases hcenter (g * S.z * g⁻¹) hz'P' hz'cent with h1 | hz
    · exfalso
      apply S.z_ne_one
      have h2 : S.z = 1 := by
        calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := congrArg (fun w : G => g⁻¹ * w * g) h1
          _ = 1 := by group
      exact h2
    · calc g * S.z = (g * S.z * g⁻¹) * g := by group
        _ = S.z * g := by rw [hz]
  have hSylowMcoe : (hSylowM : Subgroup S.M) = P'M := Sylow.coe_ofCard P'M hP'Mcard
  have hmax : ∀ H : Subgroup S.M, P'M ≤ H → IsPGroup 2 H → H = P'M := by
    intro H hle hHp
    have h := hSylowM.is_maximal' hHp (by rwa [hSylowMcoe])
    rwa [hSylowMcoe] at h
  have hP'T : ∀ T : Sylow 2 G, P' ≤ (T : Subgroup G) → (T : Subgroup G) = P' := by
    intro T hle
    by_contra hne
    have hlt : P' < (T : Subgroup G) := lt_of_le_of_ne hle (Ne.symm hne)
    have hltT : P'.subgroupOf (T : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      exact hne (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hle)
    have hnil : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
    have hnc : NormalizerCondition (T : Subgroup G) :=
      @Group.normalizerCondition_of_isNilpotent (T : Subgroup G) _ hnil
    obtain ⟨x, hxN, hxP⟩ := SetLike.exists_of_lt (hnc (P'.subgroupOf (T : Subgroup G)) hltT)
    have hxnormT : (x : G) ∈ Subgroup.normalizer (P' : Set G) := by
      have hx' : x ∈ (Subgroup.normalizer (P' : Set G)).subgroupOf (T : Subgroup G) := by
        rw [Subgroup.subgroupOf_normalizer_eq hle]
        exact hxN
      exact Subgroup.mem_subgroupOf.mp hx'
    have hxM : (x : G) ∈ S.M := hNle hxnormT
    have hxT : (x : G) ∈ (T : Subgroup G) := x.2
    let H : Subgroup G := P' ⊔ Subgroup.zpowers (x : G)
    have hHT : H ≤ (T : Subgroup G) :=
      sup_le hle (Subgroup.zpowers_le.mpr hxT)
    have hHp : IsPGroup 2 H := T.isPGroup'.to_le hHT
    have hHM : H ≤ S.M := sup_le hP'leM (Subgroup.zpowers_le.mpr hxM)
    have hleH : P'M ≤ H.subgroupOf S.M := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy)
    have hxH : (⟨(x : G), hxM⟩ : S.M) ∈ H.subgroupOf S.M := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : G))
    have hxP' : (x : G) ∉ P' := fun h => hxP (Subgroup.mem_subgroupOf.mpr h)
    have hltH : P'M < H.subgroupOf S.M := by
      refine lt_of_le_of_ne hleH ?_
      intro heq
      have : (⟨(x : G), hxM⟩ : S.M) ∈ P'M := heq ▸ hxH
      exact hxP' (Subgroup.mem_subgroupOf.mp this)
    have hHp' : IsPGroup 2 (H.subgroupOf S.M) := hHp.comap_subtype
    exact (ne_of_gt hltH) (hmax (H.subgroupOf S.M) hleH hHp')
  obtain ⟨T, hleT⟩ := hP'p.exists_le_sylow
  refine ⟨T, hP'T T hleT, ?_⟩
  rw [hP'T T hleT]
  exact hcenter

theorem card_sylow_two {G : Type} [Group G] [Finite G] (S : Setting G) (f : S.M ≃* C0)
    (hf : f S.zM = tC) (P : Sylow 2 G) : Nat.card P = 64 := by
  obtain ⟨P₀, hP₀, -⟩ := exists_sylow_eq_map_P0 S f hf
  have h : Nat.card (P : Subgroup G) = Nat.card (P₀ : Subgroup G) :=
    P.card_eq_multiplicity.trans P₀.card_eq_multiplicity.symm
  rw [h, hP₀]
  rw [Subgroup.card_map_of_injective (f := S.M.subtype) S.M.subtype_injective,
    Subgroup.card_map_of_injective (f := (f.symm : C0 →* S.M)) f.symm.injective, card_P0]

end CFSG.Literature.Janko67
