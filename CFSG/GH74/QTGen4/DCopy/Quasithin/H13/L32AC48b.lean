module

public import CFSG.Quasithin.H13.L32AC48b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A767n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem exists_mem_cComp_F4 (h29 : Thm14_7_29_F4) (S : Setting147 G T L V H) : ∃ K, K ∈ cComp H := by
  have hns : ¬ Group.IsSolvable ↥H := fun hs =>
    S.hz.2.2 (h29 G T L V S.hyp H S.hz.1.1 S.hz.2.1 hs)
  have hn : (H.subgroupOf H).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  obtain ⟨K, hK, -⟩ := exists_cComp_le_of_not_solvable le_rfl hn hns
  exact ⟨K, hK⟩

theorem le_commutator_l1_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h : Hyp147 G T L V) : V ≤ ⁅V, l1 T L V⁆ := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨V₂, z, a, b, x, y, hV2, hz0, hz1, ha, haV, hb, hbV, hxL, hyL, hxa, hxb, hya⟩ :=
    exists_basis_l1_of_F4 h hMod h1222 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14_F4 h1222 h1332 h1334 hV2
  have e : l1 T L V = L₁Of L (fsuV1 T V) := by rw [L₁Of, oTwoRes_eq_oTwoUpper]
  rw [e]
  have hcomm : ∀ {v l : G}, v ∈ V → l ∈ L₁Of L (fsuV1 T V) →
      l * v * l⁻¹ * v⁻¹ ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    intro v l hv hl
    have h2 := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hv hl)
    rwa [commutatorElement_inv, commutatorElement_def] at h2
  have haV' : a ∈ V := hV2.2.1 ha
  have ha_mem : a ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    have h2 := hcomm hb hxL
    rwa [hxb, mul_inv_cancel_right] at h2
  have hba : b * a⁻¹ ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    have h2 := hcomm haV' hxL
    rwa [hxa] at h2
  have hz_mem : z ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    have h2 := hcomm haV' hyL
    rwa [hya, mul_inv_cancel_right] at h2
  have hb_mem : b ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    have h2 := Subgroup.mul_mem _ hba ha_mem
    rwa [inv_mul_cancel_right] at h2
  have hV1 : ∀ w ∈ fsuV1 T V, w ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    intro w hw
    rcases S14.eq_of_mem_V1_F4 hz0 hz1 hw with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hz_mem
  have hV2' : ∀ w ∈ V₂, w ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    intro w hw
    rcases S14.mem_V2_F4 ha haV hw with hw1 | hw1
    · exact hV1 w hw1
    · have e2 : w = a⁻¹ * (a * w) := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha_mem) (hV1 _ hw1)
  intro v hv
  rcases S14.mem_V_F4 hb hbV hv with hv2 | hv2
  · exact hV2' v hv2
  · have e2 : v = b⁻¹ * (b * v) := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb_mem) (hV2' _ hv2)

theorem centralizer_eq_bot_F4 (h28 : Lemma14_7_28_F4) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : cComp H = {K}) (hL1K : l1 T L V ≤ K) (hKbn : (modO2Image H K).Normal)
    (hZ : Subgroup.center ↥(modO2Image H K) = ⊥) :
    Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) = ⊥ := by
  set Q := ↥H ⧸ CFSG.pCore 2 ↥H with hQ
  set Kb := modO2Image H K with hKb
  set C := Subgroup.centralizer (Kb : Set Q) with hCdef
  have hCK : C ⊓ Kb = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxK⟩
    have hx : (⟨x, hxK⟩ : ↥Kb) ∈ Subgroup.center ↥Kb := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hx
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hKmem : K ∈ cComp H := by rw [hK]; exact Set.mem_singleton K
  have hsolv : Group.IsSolvable ↥C := by
    by_contra hns
    have hn : (C.subgroupOf ⊤).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
      rw [Subgroup.normalizer_eq_top_iff.mpr hCn]
    obtain ⟨K', hK', hK'C⟩ := exists_cComp_le_of_not_solvable le_top hn hns
    rw [cComp_top_eq hK, Set.mem_singleton_iff] at hK'
    rw [hK'] at hK'C
    have hb : Kb = ⊥ := le_bot_iff.mp (hCK ▸ le_inf hK'C le_rfl)
    exact (modO2Image_mem_cComp hKmem).1 hb
  have hO2 : CFSG.pCore 2 Q = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hoK : CFSG.oddCore Q ≤ Kb := by
    rcases h28 G T L V H S with h0 | h1
    · rw [h0]
      exact bot_le
    · rw [h1]
      exact Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hL1K (Subgroup.mem_subgroupOf.mp hx))
  have hcore : ∀ p : ℕ, p.Prime → CFSG.pCore p ↥C = ⊥ := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    have hPn : ((CFSG.pCore p ↥C).map C.subtype).Normal := map_subtype_normal_of_char _
    have hPp : IsPGroup p ↥((CFSG.pCore p ↥C).map C.subtype) :=
      CFSG.pCore_isPGroup.map C.subtype
    have hPC : (CFSG.pCore p ↥C).map C.subtype ≤ C := Subgroup.map_subtype_le _
    have hPK : (CFSG.pCore p ↥C).map C.subtype ≤ Kb := by
      by_cases hp2 : p = 2
      · subst hp2
        have h1 : (CFSG.pCore 2 ↥C).map C.subtype ≤ CFSG.pCore 2 Q := le_sSup ⟨hPn, hPp⟩
        rw [hO2] at h1
        exact h1.trans bot_le
      · obtain ⟨k, hk⟩ := hPp.exists_card_eq
        have hodd : Odd (Nat.card ↥((CFSG.pCore p ↥C).map C.subtype)) := by
          rw [hk]
          exact (hp.odd_of_ne_two hp2).pow
        have h1 : (CFSG.pCore p ↥C).map C.subtype ≤ CFSG.oddCore Q := le_sSup ⟨hPn, hodd⟩
        exact h1.trans hoK
    have hbot : (CFSG.pCore p ↥C).map C.subtype = ⊥ := le_bot_iff.mp (hCK ▸ le_inf hPC hPK)
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hbot
  have hF : CFSG.fittingSubgroup ↥C = ⊥ := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    exact iSup_eq_bot.mpr fun p => hcore p (Nat.prime_of_mem_primeFactors p.2)
  have hcard := (CFSG.fitting_eq_bot_iff_card_eq_one_of_solvable ↥C).mp hF
  exact Subgroup.eq_bot_of_card_eq C hcard

theorem lemma14_7_48_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h37 : A37ForSQTK) (h28 : Lemma14_7_28_F4) (h29 : Thm14_7_29_F4) (h30 : Lemma14_7_30_F4)
    (h47 : Lemma14_7_47_F4) : Lemma14_7_48_F4 := by
  intro G _ _ T L V H S
  have hL3 := relIndex_l1_F4 h1222 h1332 h1334 S.hyp
  obtain ⟨K, hK⟩ := exists_mem_cComp_F4 h29 S
  have hq : ∀ K' ∈ cComp H, CFSG.IsQuasisimple (cStar K') := fun K' hK' =>
    (h30 G T L V H S K' hK').1
  have hlist : ∀ K' ∈ cComp H, IsList47 (cStar K') := fun K' hK' =>
    (h47 G T L V H S K' hK').2
  have hl1 : ∀ K' ∈ cComp H, l1 T L V ≤ K' := fun K' hK' => (h47 G T L V H S K' hK').1
  have hZ : ∀ K' ∈ cComp H, Subgroup.center (cStar K') = ⊥ := fun K' hK' =>
    center_eq_bot_of_list47 (hq K' hK') (hlist K' hK')
  have huniq : cComp H = {K} := by
    ext K'
    rw [Set.mem_singleton_iff]
    constructor
    · intro hK'
      exact eq_of_mem_cComp h37 S hL3 hK' hK (hl1 K' hK') (hl1 K hK) (hZ K' hK')
    · rintro rfl
      exact hK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    apply mem_normalizer_of_map_conj_eq
    have h1 := map_conj_mem_cComp hK hg
    rw [huniq, Set.mem_singleton_iff] at h1
    exact h1
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  have hKbn : (modO2Image H K).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := modO2_mulEquiv hK
  let e' : cStar K ≃* ↥(modO2Image H K) :=
    (QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf_eq_pCore K)).trans e
  have hqb : CFSG.IsQuasisimple ↥(modO2Image H K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e' (hq K hK)
  have hlb : IsList47 ↥(modO2Image H K) := (hlist K hK).of_mulEquiv e'
  have hZb := center_eq_bot_of_list47 hqb hlb
  have hC := centralizer_eq_bot_F4 h28 S huniq (hl1 K hK) hKbn hZb
  have hdvd := index_dvd_card_outer hC
  have : Finite (MulAut ↥(modO2Image H K)) :=
    Finite.of_injective (fun f : MulAut ↥(modO2Image H K) => (f : ↥(modO2Image H K) → _))
      DFunLike.coe_injective
  obtain ⟨m, hm⟩ := (isPGroup_two_outer_of_list47 hqb hlb).exists_card_eq
  rw [hm] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨K, huniq, eq_sup_of_index S hKH hKbn hj,
    conjClosure_eq_commutator (le_commutator_l1_F4 h1222 h1332 h1334 S.hyp) hKH hHK (hl1 K hK)⟩

end Main

end CFSG.Quasithin.H13.L32A.C
