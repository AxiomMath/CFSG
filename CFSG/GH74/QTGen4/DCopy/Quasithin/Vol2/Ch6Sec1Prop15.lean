module

public import CFSG.Quasithin.Vol2.Ch6Sec1Prop15
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem stmt6_1_15_F4 (h432 : Stmt4_3_2_F4) (h6110 : Stmt6_1_10_F4) (h6111 : Stmt6_1_11_F4)
    (h6112 : Stmt6_1_12_F4) (h6113 : Stmt6_1_13_F4) (h6114 : Stmt6_1_14_F4) : Stmt6_1_15_F4 := by
  intro G _ _ T M L V n h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hZ : Subgroup.centralizer (ch6ZS T L V : Set G) ≤ M
  swap
  · exact Or.inl hZ
  right
  obtain ⟨h12a, h12b, -⟩ := h6112 G T M L V n h
  by_cases hW : Subgroup.normalizer (wClos V 0 T : Set G) ≤ M
  ·
    have hC1 : ¬ Subgroup.centralizer (cClos V 1 T : Set G) ≤ M :=
      h12a.resolve_left (not_not.mpr hW)
    have hZC : ¬ ch6ZS T L V ≤ cClos V 1 T := fun hle =>
      hC1 ((Subgroup.centralizer_le
        (show (ch6ZS T L V : Set G) ⊆ (cClos V 1 T : Set G) from hle)).trans hZ)
    have hn : n = 2 := by
      by_contra hne
      exact hZC (h12b (by have := h.two_le; omega))
    refine ⟨hn, Or.inr fun hW1 => hZC ?_⟩
    refine le_inf (h.ZS_le.trans h.toHyp611.le_T) fun z hz => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hW1 hw).2 z hz).symm
  by_cases hn : n = 2
  · exact ⟨hn, Or.inl hW⟩
  exfalso
  have hn2 : 2 < n := by have := h.two_le; omega
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hU := h.toHyp611.isUniqueM_F4 h432
  have hV := h.toHyp611.isElemAbelian
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV

  have hQ := h.toHyp611.centralizer_eq
  have hQ1 : ch6Q T V ≠ ⊥ := by rw [hQ]; exact h.maximal.1.2.2.2
  have hQ2 : IsPGroup 2 (ch6Q T V) := h.sylow.1.to_le inf_le_left
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hNQ : IsUniqueM (Subgroup.normalizer (ch6Q T V : Set G)) M :=
    ⟨⟨h.maxTwoLocal, le_of_isUniqueM_of_le_twoLocal hU hLTQ ⟨_, hQ1, hQ2, rfl⟩⟩,
      fun M' hM' => hU.2 M' ⟨hM'.1, hLTQ.trans hM'.2⟩⟩

  have hVW : V ≤ wClos V 0 T :=
    le_wClos (mem_gammaSet_iff.mpr ⟨h.toHyp611.le_T, 1, (conjSubgroup_one V).ge,
      by rw [conjSubgroup_one, mQuot_self]⟩)
  have hW0 : wClos V 0 T ≠ ⊥ := fun h0 => h.toHyp611.ne_bot (eq_bot_iff.mpr (h0 ▸ hVW))
  have hTT : IsSylowIn 2 T T :=
    E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
      le_rfl le_top
  have hWQ : ¬ wClos V 0 T ≤ ch6Q T V := fun hle =>
    hW (e3_16_one hTT inf_le_left hQ2 hle hW0 hNQ).2

  obtain ⟨A, hA, hAQ⟩ : ∃ A ∈ gammaSet V 0 T, ¬ A ≤ ch6Q T V := by
    by_contra hcon
    push Not at hcon
    exact hWQ (wClos_le_of_forall hcon)
  obtain ⟨hAT, g, hAg, hm0⟩ := hA
  have hAeq : A = conjSubgroup V g := (mQuot_eq_zero_iff (isPGroup_conjSubgroup hV2 g) hAg).mp hm0
  rw [hAeq] at hAT hAQ
  have hVgN : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) :=
    hAT.trans h.toHyp611.T_le_normalizer
  have hVgC : ¬ conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) := fun hle =>
    hAQ (le_inf hAT hle)
  have hcomm1 : ⁅conjSubgroup V g, V⁆ ≠ ⊥ := fun h0 =>
    hVgC (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0)
  by_cases hVN : V ≤ Subgroup.normalizer (conjSubgroup V g : Set G)
  ·
    have hle1 : ⁅V, conjSubgroup V g⁆ ≤ V :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hVgN
    have hle2 : ⁅V, conjSubgroup V g⁆ ≤ conjSubgroup V g :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hVN
    obtain ⟨-, -, c, hc, hgc⟩ := h6111 G T M L V n h g hAT
      (by rw [Subgroup.commutator_comm]; exact hcomm1) (le_inf hle1 hle2)
    have hcN : c ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (h.normal (hZ hc))
    have hle : conjSubgroup V c ≤ pCoreOf 2 L := by
      rw [← conjSubgroup_eq_iff_mem_normalizer.mpr hcN]
      exact conjSubgroup_mono_left c h.le_pCoreOf_L
    apply hVgC
    rw [hgc]
    exact hle.trans h.toHyp611.pCoreOf_le_centralizer

  obtain ⟨U', hU'⟩ : ∃ U' : Subgroup G,
      U' = V ⊓ Subgroup.centralizer (conjSubgroup V g⁻¹ : Set G) := ⟨_, rfl⟩
  have hU'g : conjSubgroup U' g = conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hU', conjSubgroup_inf, conjSubgroup_centralizer, conjSubgroup_inv_conj]
  have hU'V : U' ≤ V := by rw [hU']; exact inf_le_left
  have hmU' : mQuot V U' = n := by
    rw [← mQuot_conjSubgroup V U' g, hU'g]
    exact (h6110 G T M L V n h).2.2 g hVgN hVgC
  have hU'card : Nat.card U' = 2 ^ n := by
    have h1 := card_eq_two_pow_mul hV2 hU'V
    rw [hmU', h.natural.card_eq] at h1
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm
  have hU'1 : U' ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hU'card
    omega

  have hVCU : V ≤ Subgroup.centralizer (conjSubgroup U' g : Set G) := by
    rw [hU'g]
    exact fun v hv => Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hu.2 v hv).symm
  have hkey : ¬ Subgroup.centralizer (U' : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro hC
    apply hVN
    have h1 := conjSubgroup_mono_left g hC
    rw [conjSubgroup_centralizer, conjSubgroup_normalizer] at h1
    exact hVCU.trans h1
  rcases h6113 G T M L V n h U' hU'V hmU' with hC | ⟨l, hl, hl'⟩ | ⟨hev, t, htM, hinv, htU⟩
  ·
    exact hkey hC
  ·
    apply hkey
    have hlM : l ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer (h.L_le hl)
    have hCM : Subgroup.centralizer (U' : Set G) ≤ M := by
      have h1 := conjSubgroup_mono_left l hZ
      rw [conjSubgroup_centralizer, conjSubgroup_eq_iff_mem_normalizer.mpr hlM] at h1
      rw [hl']
      exact h1
    exact fun x hx =>
      (h.normalizer_le hU'1 hU'V ⟨hCM hx, Subgroup.centralizer_le_normalizer _ hx⟩).2

  obtain ⟨t₂, ht₂M, ⟨k, hk⟩, hinv₂, hCt⟩ :=
    h.exists_two_element_fieldAut htM hinv (le_of_eq (by rw [← htU, hU'card]))
  have htU₂ : U' = V ⊓ Subgroup.centralizer ({t₂} : Set G) := htU.trans hCt
  have ht₂N : t₂ ∈ M ⊓ Subgroup.normalizer (U' : Set G) := by
    refine ⟨ht₂M, Subgroup.centralizer_le_normalizer _ ?_⟩
    rw [htU₂]
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hu.2 t₂ rfl).symm

  have hzP : IsPGroup 2 (Subgroup.zpowers t₂) := by
    intro x
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨P, hP, hzP'⟩ := exists_isSylowIn_ge 2 (Subgroup.zpowers_le.mpr ht₂N) hzP
  obtain ⟨m, hm, hPT⟩ := h.toHyp611.exists_conj_sylow
    (hP.le.trans (h.normalizer_le hU'1 hU'V)) hP.isPGroup
  have h₁ := h.conj_of_mem hm.1 hm.2
  have hZ₁ := h.toHyp611.centralizer_ZS_map_le hm.1 hm.2 hZ
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : Subgroup G, T₁ = T.map (MulAut.conj m).toMonoidHom := ⟨_, rfl⟩
  rw [← hT₁] at hPT h₁ hZ₁
  have hSyl : IsSylowIn 2 (T₁ ⊓ Subgroup.normalizer (U' : Set G))
      (M ⊓ Subgroup.normalizer (U' : Set G)) := by
    refine ⟨inf_le_inf_right _ h₁.T_le, h₁.sylow.1.to_le inf_le_left,
      fun h2 => hP.not_dvd_relIndex ?_⟩
    exact h2.trans (Subgroup.relIndex_dvd_of_le_left _ (le_inf hPT (hP.le.trans inf_le_right)))

  have h14 := h6114 G T₁ M L V n h₁ hev t₂ (hPT (hzP' (Subgroup.mem_zpowers t₂))) hinv₂ U' htU₂
    hSyl
  obtain ⟨-, -, -, -, h5⟩ := h14
  have ha : conjSubgroup V g⁻¹ ≤ Subgroup.centralizer (U' : Set G) := by
    rw [hU']
    exact fun x hx => Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hu.2 x hx).symm
  have hb : V ≤ Subgroup.normalizer (conjSubgroup V g⁻¹ : Set G) := by
    have h1 := conjSubgroup_mono_left g⁻¹ hVgN
    rwa [conjSubgroup_conj_inv, conjSubgroup_normalizer] at h1
  have hc : ⁅V, conjSubgroup V g⁻¹⁆ ≠ ⊥ := by
    intro h0
    apply hcomm1
    have h1 := congrArg (fun X => conjSubgroup X g) h0
    simp only [conjSubgroup_commutator, conjSubgroup_inv_conj, conjSubgroup_bot] at h1
    exact h1
  exact h5 hn2 g⁻¹ ha hb hc hZ₁

end CFSG.Quasithin.H13
