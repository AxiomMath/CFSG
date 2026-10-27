module

public import CFSG.Quasithin.H13.KGFact14736Hat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC47c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk4

public section

namespace CFSG.Quasithin.H13.KGFFZ

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin
open scoped Pointwise commutatorElement

section Module

variable {G : Type} [Group G] {V₁ IH H : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]

end Module

section Hat

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.L32A.C CFSG.Blueprint

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem hat_center_F4 (h28 : Lemma14_7_28_F4) (h5 : Lemma14_7_5_F4) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H)
    (hhat : IsHat (cStar K) (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    (modO2Image H (l1 T L V)).Normal ∧
    (∀ x ∈ K, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → x ^ 3 ∈ pCoreOf 2 H) ∧
    (∀ x ∈ K, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → x ∉ pCoreOf 2 H →
      ∀ l ∈ l1 T L V, ∃ n : ℤ, (x ^ n)⁻¹ * l ∈ pCoreOf 2 H) ∧
    ∃ x ∈ K, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) ∧ x ∉ pCoreOf 2 H := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  set Kb := modO2Image H K with hKb
  have hcard : Nat.card (Subgroup.center ↥Kb) = 3 := by
    rw [← card_center_eq_of_mulEquiv ((cStarEquiv K).trans e)]
    exact hhat.2.1
  set Z := Subgroup.center ↥Kb with hZ
  set Zb := Z.map Kb.subtype with hZbdef
  have hKbs : Kb.IsSubnormal := A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
  have hZn : ((Z.map Kb.subtype).subgroupOf Kb).Normal := by
    rw [map_subtype_subgroupOf']
    infer_instance
  have hZs : Zb.IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (Subgroup.map_subtype_le Z) hKbs hZn
  have hZc : Nat.card Zb = 3 := by
    rw [hZbdef, Subgroup.card_map_of_injective Kb.subtype_injective, hcard]
  have hle : Zb ≤ CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) :=
    le_oddCore_of_isSubnormal hZs (by rw [hZc]; exact ⟨1, rfl⟩)
  have hO : CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = modO2Image H (l1 T L V) := by
    rcases h28 G T L V H S with h0 | h1
    · rw [h0, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at hZc
      omega
    · exact h1
  have hnorm : (modO2Image H (l1 T L V)).Normal := by
    rw [← hO]
    infer_instance
  obtain ⟨-, -, hL3, -⟩ := h5 G T L V H S hnorm
  have hZL : Zb = modO2Image H (l1 T L V) :=
    Subgroup.eq_of_le_of_card_ge (hle.trans hO.le) (hL3.trans hZc.symm).le

  have hcen : ∀ x (hx : x ∈ K), (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
      (QuotientGroup.mk (⟨x, hKH hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Zb := by
    intro x hx hxc
    have hmem : (QuotientGroup.mk (⟨x, hKH hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Kb :=
      ⟨⟨x, hKH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    refine ⟨⟨_, hmem⟩, Subgroup.mem_center_iff.mpr fun k => ?_, rfl⟩
    obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.mp k.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hkk]
    have hk'K : (k' : G) ∈ K := Subgroup.mem_subgroupOf.mp hk'
    have hc : (⟨x, hKH hx⟩ : ↥H) * k' * (⟨x, hKH hx⟩ : ↥H)⁻¹ * k'⁻¹ ∈ CFSG.pCore 2 ↥H :=
      mem_pCore_iff'.mpr (hxc _ hk'K)
    have h1 := (QuotientGroup.eq_one_iff _).mpr hc
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    exact comm_of_commutator_eq_one h1
  refine ⟨hnorm, fun x hx hxc => ?_, fun x hx hxc hxQ l hl => ?_, ?_⟩
  · have h1 := hcen x hx hxc
    have h3 : (QuotientGroup.mk (⟨x, hKH hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥Zb) (x := ⟨_, h1⟩)
      rw [hZc] at this
      exact congrArg Subtype.val this
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
    exact mem_pCore_iff'.mp h3
  · set xb := (QuotientGroup.mk (⟨x, hKH hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) with hxb
    have h1 := hcen x hx hxc
    have hxb1 : xb ≠ 1 := by
      intro h
      rw [hxb, QuotientGroup.eq_one_iff] at h
      exact hxQ (mem_pCore_iff'.mp h)

    have hzle : Subgroup.zpowers xb ≤ Zb := Subgroup.zpowers_le.mpr h1
    have hord : orderOf xb ∣ 3 := by
      rw [← hZc]
      exact Subgroup.orderOf_dvd_natCard Zb h1
    have hord3 : orderOf xb = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hxb1
      · exact h
    have hzeq : Subgroup.zpowers xb = modO2Image H (l1 T L V) := by
      rw [← hZL]
      exact Subgroup.eq_of_le_of_card_ge hzle (le_of_eq (by rw [Nat.card_zpowers, hord3, hZc]))
    have hlH : l ∈ H := le_sup_left.trans S.hz.1.1 hl
    have hlb : (QuotientGroup.mk (⟨l, hlH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
        Subgroup.zpowers xb := by
      rw [hzeq]
      exact ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hlb
    refine ⟨n, ?_⟩
    rw [hxb, ← QuotientGroup.mk_zpow] at hn
    exact mem_pCore_iff'.mp (QuotientGroup.eq.mp hn)
  ·
    have : Nontrivial ↥Zb := Finite.one_lt_card_iff_nontrivial.mp (by rw [hZc]; norm_num)
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥Zb)
    obtain ⟨w, hwZ, hwz⟩ := Subgroup.mem_map.mp z.2
    obtain ⟨h', hh'K, hh'w⟩ := Subgroup.mem_map.mp w.2
    refine ⟨(h' : G), Subgroup.mem_subgroupOf.mp hh'K, fun k hk => ?_, fun hQ => hz1 ?_⟩
    · have hkb : (QuotientGroup.mk (⟨k, hKH hk⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Kb :=
        ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      have hc : (QuotientGroup.mk (⟨k, hKH hk⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) *
          (w : ↥H ⧸ CFSG.pCore 2 ↥H) =
          (w : ↥H ⧸ CFSG.pCore 2 ↥H) * QuotientGroup.mk ⟨k, hKH hk⟩ :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hwZ (⟨_, hkb⟩ : ↥Kb))
      have hw' : (w : ↥H ⧸ CFSG.pCore 2 ↥H) = QuotientGroup.mk h' := hh'w.symm
      have hmem : h' * ⟨k, hKH hk⟩ * h'⁻¹ * (⟨k, hKH hk⟩ : ↥H)⁻¹ ∈ CFSG.pCore 2 ↥H := by
        rw [← QuotientGroup.eq_one_iff]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [← hw', ← hc]
        group
      exact mem_pCore_iff'.mp hmem
    · apply Subtype.ext
      rw [← hwz]
      show (w : ↥H ⧸ CFSG.pCore 2 ↥H) = 1
      rw [← hh'w]
      exact (QuotientGroup.eq_one_iff _).mpr (mem_pCore_iff'.mpr hQ)

end Hat

section Main

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.L32A.C CFSG.Blueprint

attribute [local instance] commGroupOfFact

theorem lemma14_7_36_hatIrr_of_F4 (h28 : Lemma14_7_28_F4)
    (h5 : Lemma14_7_5_F4) (h30 : Lemma14_7_30_F4) (h32 : Lemma14_7_32_F4) (h56 : AsB56) (hD310 : D310)
    (hD391 : D391) (hI4 : Insp4) (hFine : F918Fine4) : Lemma14_7_36_HatIrr_F4 := by
  intro G _ _ T L V H S K hK hHeq hhat J hV₁J hJU hKJ
  obtain ⟨hq, hTK, -, hF⟩ := reduce_KL1T_F4 h30 h32 S hK
  rw [← hHeq] at hF
  have hK₀ : conjClosure K T = K := conjClosure_T_eq_self hTK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := hF.T_le_H
  have hQT : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le hF.sylow_H
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hSQ := sqtkGroup_of_setting S
  obtain ⟨hnorm, hx3, hgen, x₀, hx₀K, hx₀c, hx₀Q⟩ := hat_center_F4 h28 h5 S hK hhat
  obtain ⟨-, -, -, -, -, -, h7⟩ := h5 G T L V H S hnorm

  have hHKT : H = K ⊔ T := by
    refine le_antisymm ?_ (sup_le hKH hTH)
    rw [hHeq]
    refine sup_le le_sup_left (sup_le (fun l hl => ?_) le_sup_right)
    obtain ⟨n, hn⟩ := hgen x₀ hx₀K hx₀c hx₀Q l hl
    rw [← mul_inv_cancel_left (x₀ ^ n) l]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.zpow_mem hx₀K n))
      (Subgroup.mem_sup_right (hQT hn))
  have hHeq' : H = conjClosure K T ⊔ T := by rw [hK₀]; exact hHKT
  have hKn : (K.subgroupOf H).Normal := by
    have h0 := hF.K₀_normal
    rw [hK₀] at h0
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr h0

  have hFU := factElem hF (le_conjClosure V H)
  have hV₁H : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_le_normalizer_V₁
  have hUN : conjClosure V H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure V H)
  have hUH : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H
  have hV₁U : fsuV1 T V ≤ conjClosure V H :=
    hF.toHypF98.toHypF91.V₁_le_Vp.trans (le_conjClosure V H)
  have hUQ : ∀ u ∈ conjClosure V H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ fsuV1 T V :=
    hF.toHypF98.toHypF91.commutator_conjClosure_le

  have hkey : ∀ y ∈ K, (∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → y ∉ pCoreOf 2 H →
      ⁅conjClosure V H, Subgroup.zpowers y⁆ ⊔ fsuV1 T V = conjClosure V H :=
    fun y hyK hyc hyQ =>
      commutator_zpowers_sup_eq (hKH hyK) hUH hV₁H hV₁U h7 hUQ (hgen y hyK hyc hyQ)

  obtain ⟨m, hm3, hmQ⟩ := exists_pow_three (hx3 x₀ hx₀K hx₀c) hx₀Q
  have hyK : x₀ ^ m ∈ K := K.pow_mem hx₀K m
  have hyC : x₀ ^ m ∈ centralizerMod (pCoreOf 2 H) H K :=
    (centralizerMod (pCoreOf 2 H) H K).pow_mem
      (show x₀ ∈ centralizerMod (pCoreOf 2 H) H K from ⟨hKH hx₀K, hQn (hKH hx₀K), hx₀c⟩) m
  have hU := hkey (x₀ ^ m) hyK hyC.2.2 hmQ

  have hZ : SectionFaithful T (fsuV1 T V) V H K := by
    intro F E hV₁F hFE hEU hFn hEn hnt x hx hxc hxE
    by_contra hxQ
    rw [hK₀] at hx hxc
    obtain ⟨m', hm'3, hm'Q⟩ := exists_pow_three (hx3 x hx hxc) hxQ
    have hy'C := (centralizerMod (pCoreOf 2 H) H K).pow_mem
      (show x ∈ centralizerMod (pCoreOf 2 H) H K from ⟨hKH hx, hQn (hKH hx), hxc⟩) m'
    have hy'K : x ^ m' ∈ K := K.pow_mem hx m'
    have hU' := hkey (x ^ m') hy'K hy'C.2.2 hm'Q
    have hxF : x ∈ Subgroup.normalizer (F : Set G) :=
      hFn (Subgroup.mem_sup_left (le_conjClosure K T hx))
    have hy'T := (centralizerMod F ⊤ E).pow_mem
      (show x ∈ centralizerMod F ⊤ E from ⟨Subgroup.mem_top x, hxF, hxE⟩) m'
    have hle := le_of_trivial_mod hV₁H hUN hUH hV₁U (hKH hy'K) hm'3 hU' hV₁F hFE hEU hy'T.2.1
      hy'T.2.2
    apply hnt
    intro k hk e he
    have heF := hle he
    have hkF : k ∈ Subgroup.normalizer (F : Set G) := hFn (Subgroup.mem_sup_left hk)
    exact F.mul_mem ((Subgroup.mem_normalizer_iff.mp hkF e).mp heF) (F.inv_mem heF)

  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFct := factElem hF hIU
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G) :=
    K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have h4 := (F918_4_fine' hF hSQ hK₀ hV₁I hIU W hW hirrU hD310 hD391 hI4 hFine).2
  have hHI : H ≤ Subgroup.normalizer (I : Set G) := by
    rcases h4 with h4 | (⟨hVT, -⟩ | h3)
    · exact h4
    · have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
        intro t ht
        have hst := mem_stabSub_of_eq_orbSup' hVT (actH_mem_autIH_of_mem (I := I) hF hTH ht)
        exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
          (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
          (le_conjClosure I H) ⟨t, hTH ht⟩).mp hst
      rw [hHeq']
      exact sup_le hKI hTI
    · exact (false_of_d310Two_card h3
        (Or.inr ((card_autIH_eq hF hHeq' hZ hV₁I hIU hnt).trans (card_cStar_hat hhat)))).elim
  have hcI : conjClosure I H = I :=
    le_antisymm (conjClosure_le fun _ hh i hi => (Subgroup.mem_normalizer_iff.mp (hHI hh) i).mp hi)
      (le_conjClosure I H)

  have hI := isIrrPlusTilde_of_module hF hV₁I hIU hirrT
  have hcardK : Nat.card (KBar K) = 1330560 := card_cStar_hat hhat
  have hNo : HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 H) := by
    rw [← hHeq']
    have hZK : Nat.card (Subgroup.center (KBar K)) = 3 := hhat.2.1
    refine hasNoFaithfulFF_of_kbar h56 hSQ hK hKn hTH hF.sylow_H.2.1 hHKT hq
      (by rw [hZK]; exact ⟨1, rfl⟩) (by rw [hcardK]; norm_num) fun X _ _ hX hL => ?_
    exact false_of_b56List hL (m := 10395) (by decide) (by decide) (by rw [hX, hcardK]; norm_num)
  have h7' := F918_7'' hF hHeq' hZ hV₁I hIU hI hNo
  rw [hcI] at h7'
  have hcomm : ⁅conjClosure V H, conjClosure K T⁆ ⊔ fsuV1 T V = conjClosure V H := by
    refine le_antisymm (sup_le ?_ hV₁U) (hU.symm.le.trans (sup_le_sup_right
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr (le_conjClosure K T hyK))) _))
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hF.K₀_le_H.trans hUH)
  have hIUeq : I = conjClosure V H := by
    have hcN : ⁅conjClosure V H, conjClosure K T⁆ ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
      (le_sup_left.trans hcomm.le).trans hUN
    have h2 : tildeOf (fsuV1 T V) (⁅conjClosure V H, conjClosure K T⁆ ⊔ fsuV1 T V) =
        tildeOf (fsuV1 T V) ⁅conjClosure V H, conjClosure K T⁆ := by
      rw [tildeOf_sup' hcN (hV₁U.trans hUN), tildeOf_eq_bot_of_le le_rfl, sup_bot_eq]
    have ht : tildeOf (fsuV1 T V) I = tildeOf (fsuV1 T V) (conjClosure V H) := by
      rw [h7', ← h2, hcomm]
    exact eq_of_secImg_eq hV₁I hV₁U ((le_conjClosure I H).trans
      (hF.conjClosure_le_normalizer_V₁ hIU)) hUN ht

  have hC : centralizerMod (fsuV1 T V) I (conjClosure K T) = fsuV1 T V := by
    refine le_antisymm (fun a ha => ?_) (le_centralizerMod hF.H_le_normalizer_V₁ hF.K₀_le_H hV₁I)
    obtain ⟨haI, -, hac⟩ := ha
    have h1 := (fsuV1 T V).inv_mem (hac _ (le_conjClosure K T hyK))
    have e : (a * x₀ ^ m * a⁻¹ * (x₀ ^ m)⁻¹)⁻¹ = x₀ ^ m * a * (x₀ ^ m)⁻¹ * a⁻¹ := by group
    rw [e] at h1
    exact mem_of_comm_mem hV₁H hUN hUH hV₁U (hKH hyK) hm3 hU (hIU haI) h1
  have hK₀J : conjClosure K T ≤ Subgroup.normalizer (J : Set G) := by rw [hK₀]; exact hKJ
  rcases hI.2.2.2 J hV₁J (hJU.trans hIUeq.ge) hK₀J (hC.le.trans hV₁J) with h | h
  · exact Or.inl (h.trans hC)
  · exact Or.inr (h.trans hIUeq)

end Main

end CFSG.Quasithin.H13.KGFFZ
