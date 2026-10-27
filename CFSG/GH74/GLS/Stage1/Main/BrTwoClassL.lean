module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassB

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

section Coset

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {q : ℕ}

theorem Pz_le_LC (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂)
    (hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂) : Pz S z ≤ LC z := by
  intro p hp
  have hpS : p ∈ S := hp.1
  have hpK : p ∈ K₁ ⊔ K₂ := by
    have := hp.2
    rwa [hs.rigidProduct_eq] at this
  have hpC : p ∈ centralizer ({z} : Set G) := hs.sylow.le hpS
  obtain ⟨k, hk⟩ := hs.sylow.isPGroup ⟨p, hpS⟩
  have hk' : (⟨p, hpC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hLC : p ∈ LC z ↔ toBar z ⟨p, hpC⟩ ∈ LBar z := mem_LC_iff_of_pElt (z := z) ⟨p, hpC⟩ hk'
  rw [hLC, hLB, ← map_K12 hII hs]
  exact ⟨⟨p, hpC⟩, hpK, rfl⟩

theorem coset_of_prop72 (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂)
    (hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂) {t u w : G} (hw : Concl72abcf z S K₁ K₂ t q w)
    (hde : Concl72de z t u w) : ∀ g ∈ LC z ⊔ S, ∃ l ∈ LC z, IsConj z (g * l) := by
  have hM := m4_of_std hII hs
  have hSC : S ≤ Cen z := hs.sylow.le
  have hzS : z ∈ S := hM.z_mem_S
  have hzC : z ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hSn : S ≤ normalizer ((LC z : Subgroup G) : Set G) := by
    intro s hs'
    have hsC : s ∈ Cen z := hSC hs'
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      exact LC_conj_mem hsC hl
    · intro hl
      have := LC_conj_mem (inv_mem hsC) hl
      have e : s⁻¹ * (s * l * s⁻¹) * (s⁻¹)⁻¹ = l := by group
      rw [e] at this
      exact this
  have hPn : S ≤ normalizer ((Pz S z : Subgroup G) : Set G) := by
    intro s hs'
    have hsC : s ∈ Cz z := hSC hs'
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ {s : G}, s ∈ S → ∀ {p : G}, p ∈ Pz S z → s * p * s⁻¹ ∈ Pz S z := by
      intro s hs' p hp
      refine ⟨S.mul_mem (S.mul_mem hs' hp.1) (S.inv_mem hs'), ?_⟩
      have hpK : p ∈ K₁ ⊔ K₂ := by
        have := hp.2
        rwa [hs.rigidProduct_eq] at this
      rw [hs.rigidProduct_eq]
      exact hM.C_norm_K (hSC hs') hpK
    intro p
    constructor
    · exact fun hp => key hs' hp
    · intro hp
      have := key (S.inv_mem hs') hp
      have e : s⁻¹ * (s * p * s⁻¹) * (s⁻¹)⁻¹ = p := by group
      rw [e] at this
      exact this
  obtain ⟨hwS, hwo, htw, ⟨-, hSPY⟩, -, -, -⟩ := hw
  have ht2 : t * t = 1 := mul_self_of_isConj hs.orderOf_z hde.1.1
  have hw2 : w * w = 1 := by
    rcases hwo with h | h
    · rw [h, mul_one]
    · have := pow_orderOf_eq_one w
      rwa [h, pow_two] at this
  have hYS : Ysub t w ≤ S := by
    have ht : t ∈ S := by
      have := hSPY
      have h2 : t ∈ Ysub t w := Subgroup.mem_sup_left (mem_zpowers t)
      rw [hSPY]
      exact Subgroup.mem_sup_right h2
    exact sup_le (Subgroup.zpowers_le.2 ht) (Subgroup.zpowers_le.2 hwS)
  have hYconj : ∀ y ∈ Ysub t w, y = 1 ∨ IsConj z y := by
    intro y hy
    have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ zpowers w, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow (show Commute t w from htw) k m).eq
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hy
    rcases eq_one_or_eq_of_mem_zpowers_sq ht2 ha with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers_sq hw2 hb with rfl | rfl
    · left
      simp
    · by_cases hw1 : b = 1
      · left
        simp [hw1]
      · right
        simpa using hde.2.2 hw1
    · right
      simpa using hde.1.1
    · right
      exact hde.1.2
  intro g hg
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (LC z) S hSn
  have hg' : g ∈ ((LC z : Subgroup G) : Set G) * (S : Set G) := by
    rw [← hmul]
    exact hg
  obtain ⟨l₀, hl₀, s₀, hs₀, rfl⟩ := Set.mem_mul.1 hg'
  have hmulPY := Subgroup.coe_mul_of_right_le_normalizer_left (Pz S z) (Ysub t w)
    (hYS.trans hPn)
  have hs₀' : s₀ ∈ ((Pz S z : Subgroup G) : Set G) * ((Ysub t w : Subgroup G) : Set G) := by
    rw [← hmulPY, ← hSPY]
    exact hs₀
  obtain ⟨p, hp, y, hy, rfl⟩ := Set.mem_mul.1 hs₀'
  have hl₁ : l₀ * p ∈ LC z := (LC z).mul_mem hl₀ (Pz_le_LC hII hs hLB hp)
  have hyC : y ∈ Cen z := hSC (hYS hy)
  rcases hYconj y hy with rfl | hyz
  ·
    refine ⟨(l₀ * (p * 1))⁻¹ * z, ?_, ?_⟩
    · refine (LC z).mul_mem ((LC z).inv_mem (by simpa using hl₁)) ?_
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (⟨z, hzC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
        refine ⟨1, ?_⟩
        apply Subtype.ext
        have : z ^ 2 = 1 := by
          have := pow_orderOf_eq_one z
          rwa [hs.orderOf_z] at this
        simpa using this
      have hLC : z ∈ LC z ↔ toBar z ⟨z, hzC⟩ ∈ LBar z := mem_LC_iff_of_pElt (z := z) ⟨z, hzC⟩ hk
      rw [hLC, hLB]
      exact Subgroup.mem_sup_left (zbar_facts4 hII hs).1.1
    · rw [mul_inv_cancel_left]
  ·
    refine ⟨y⁻¹ * (l₀ * p)⁻¹ * y, ?_, ?_⟩
    · have h2 := LC_conj_mem (inv_mem hyC) ((LC z).inv_mem hl₁)
      simpa using h2
    · have e : l₀ * (p * y) * (y⁻¹ * (l₀ * p)⁻¹ * y) = y := by group
      rw [e]
      exact hyz

end Coset

section Core

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}

theorem twoClass_core_cfg (hII : II4_4_4_center) (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6)
    (hpnf : P_normal_four) (hL44 : Lemma4_4) (hL45 : Lemma4_5) (h31 : IVK_3_1a_lifted) (h72 : Prop7_2)
    (h73 : Lemma7_3) (h74 : Lemma7_4) (h77 : Lemma7_7) (hcen : Cen2 G z S) {w : G}
    (hT : Term7Out G z S q w) {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hpair : Stage1Pair G z S q L₁ L₂) :
    ∃ (K₁ K₂ : Subgroup G) (t u : G), Cfg7 G z S K₁ K₂ t u q ∧
      ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {imgBar z K₁, imgBar z K₂} ∧
      TwoClassCore G z S L₁ L₂ q u := by
  have hnf := nonfused_of_term7 hII h41 hT
  obtain ⟨K₁, K₂, hstd, hodd, h5, hK₁, hK₂, hT7⟩ := hT
  obtain ⟨t, u, hcfg⟩ := cfg7_of_std hII h41 h61 h66 hpnf hL44 hL45 hstd hnf hodd h5 hK₁ hK₂
  have ht := hcfg.ch
  have h73' := h73 G z S K₁ K₂ t u q hcfg
  obtain ⟨-, h74c⟩ := h74 G z S K₁ K₂ t u q hcfg h73'
  have hM := m4_of_std hII hstd
  have huS : u ∈ S := ht.u_mem.1
  have htS : t ∈ S := ht.t_mem
  have hSC : S ≤ Cen z := hstd.sylow.le
  have htC : t ∈ Cen z := hSC htS
  have hu_tz : IsConj (t * z) u := ht.t_fus u ht.u_mem ht.u_ord ht.u_ne
  have hAcomps := comps_of_std4 hII h41 hstd
  have hsets : ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {imgBar z K₁, imgBar z K₂} :=
    hpair.comps.symm.trans hAcomps
  have hA12 : imgBar z K₁ ≠ imgBar z K₂ := by
    intro h
    rw [h] at hsets
    have h1 : L₁ ∈ ({imgBar z K₂, imgBar z K₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hsets]
      exact Or.inl rfl
    have h2 : L₂ ∈ ({imgBar z K₂, imgBar z K₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hsets]
      exact Or.inr rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at h1 h2
    exact hpair.ne (h1.trans h2.symm)
  have hsw : Swaps z t (imgBar z K₁) (imgBar z K₂) :=
    swaps_of_interchanges hM.K₁_le hM.K₂_le htC ht.t_swap
  have hsw_match : ∀ t₀, Swaps z t₀ L₁ L₂ → Swaps z t₀ (imgBar z K₁) (imgBar z K₂) := by
    intro t₀ h
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact h
    · rw [← h1, ← h2]
      exact swaps_symm h
  have hcfg_of : ∀ t₀ ∈ S, IsConj z t₀ → Swaps z t₀ L₁ L₂ → Cfg7 G z S K₁ K₂ t₀ u q := by
    intro t₀ ht₀S ht₀c hsw₀
    have ht₀C : t₀ ∈ Cen z := hSC ht₀S
    have hint := interchanges_of_swaps hstd hA12 hM.K₁_le hM.K₂_le ht₀C (hsw_match t₀ hsw₀)
    have ht₀ne : t₀ ≠ z := by
      intro h
      rw [h] at hint
      exact hstd.ne ((conjugate_self_of_le hM.K₁_le).symm.trans hint.1)
    exact cfg7_of_swap hII hL45 hcfg ht₀S ht₀c ht₀ne hint
  refine ⟨K₁, K₂, t, u, hcfg, hsets, huS, ht.u_ord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hcu
    have hSG : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := sylow_top_of_central hcen.central hcen.sylow
    obtain ⟨hu2, T, huT, hTc⟩ := hcu
    have hTG : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup G) ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨le_top, T.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact T.not_dvd_index
    obtain ⟨c, -, hc⟩ :=
      CFSG.ComponentClassification.AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hSG hTG
    have hu'S : c⁻¹ * u * c ∈ S := by
      rw [← hc]
      exact CFSG.ComponentClassification.AschbacherTheorem3.conj_mem_rightConjugate huT c
    have hu'c : ∀ s ∈ S, s * (c⁻¹ * u * c) = (c⁻¹ * u * c) * s := by
      intro s hs
      rw [← hc] at hs
      have hs' : c * s * c⁻¹ ∈ T := by
        have := (CFSG.ComponentClassification.AschbacherTightEmbedding.mem_rightConjugate_iff
          (T : Subgroup G) c s).1 hs
        exact this
      have := hTc _ hs'
      calc s * (c⁻¹ * u * c) = c⁻¹ * ((c * s * c⁻¹) * u) * c := by group
        _ = c⁻¹ * (u * (c * s * c⁻¹)) * c := by rw [this]
        _ = (c⁻¹ * u * c) * s := by group
    have hu'o : orderOf (c⁻¹ * u * c) = 2 := by
      have := SemiconjBy.orderOf_eq c (x := c⁻¹ * u * c) (y := u) (by
        show c * (c⁻¹ * u * c) = u * c
        group)
      rw [this]
      exact ht.u_ord
    have hz := hpair.base.zcen _ hu'S hu'c hu'o
    have hconj : IsConj z u := by
      rw [isConj_iff]
      refine ⟨c, ?_⟩
      rw [← hz]
      group
    exact ht.tz_ne (hconj.trans hu_tz.symm)
  ·
    intro v hv
    exact (h74c.1 v hv).imp id (fun h => hu_tz.symm.trans h)
  ·
    intro s hs w hw
    have hsC : s ∈ Cen z := hSC hs
    have hz_s : s * z * s⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hsC
      rw [this]
      group
    have hu_s : s * u * s⁻¹ ∈ zpowers z ⊔ zpowers u := by
      rcases ht.u_norm s hs with h | h
      · rw [h]
        exact Subgroup.mem_sup_right (mem_zpowers u)
      · rw [h]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers u))
          (Subgroup.mem_sup_left (mem_zpowers z))
    have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers u, a * b = b * a := by
      have hzu : z * u = u * z :=
        (Subgroup.mem_centralizer_singleton_iff.1 (hSC huS)).symm
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow (show Commute z u from hzu) k m).eq
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have e : s * (z ^ k * u ^ m) * s⁻¹ = (s * z * s⁻¹) ^ k * (s * u * s⁻¹) ^ m := by
      rw [conj_zpow, conj_zpow]
      group
    rw [e, hz_s]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (zpow_mem (mem_zpowers z) k))
      (zpow_mem hu_s m)
  ·
    obtain ⟨w₇, hw₇, hde₇⟩ := h72 G z S K₁ K₂ t u q hcfg
    exact coset_of_prop72 hII hstd (LBar_eq_imgBar hII h41 hstd) hw₇ hde₇
  ·
    have hK : K₁ ⊔ K₂ ≤ Cz z := sup_le hM.K₁_le hM.K₂_le
    have hLB : ((K₁ ⊔ K₂).subgroupOf (Cz z)).map (piC z) = LBar z :=
      (map_K12 hII hstd).trans (LBar_eq_imgBar hII h41 hstd).symm
    have huK : u ∈ K₁ ⊔ K₂ := by
      have := ht.u_mem.2
      rwa [hstd.rigidProduct_eq] at this
    exact invol_L_of_lift (h31 G z S K₁ K₂ hstd) hK hLB huK ht.u_ord ht.u_ne
  ·
    refine ⟨t, htS, ht.t_conj, ?_⟩
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hsw
    · rw [h1, h2]
      exact swaps_symm hsw
  ·
    intro t₀ ht₀S ht₀c hsw₀
    have hcfg₀ := hcfg_of t₀ ht₀S ht₀c hsw₀
    exact (hcfg₀.ch.t_fus u ht.u_mem ht.u_ord ht.u_ne).symm
  ·
    intro t₀ ht₀S ht₀c hsw₀
    exact swap_b_of_pair hpair hsw₀ (mul_self_of_isConj hstd.orderOf_z ht₀c)
  ·
    intro t₀ ht₀S ht₀c hsw₀
    have hcfg₀ := hcfg_of t₀ ht₀S ht₀c hsw₀
    have h73₀ := h73 G z S K₁ K₂ t₀ u q hcfg₀
    obtain ⟨⟨D, hD⟩, h74c₀⟩ := h74 G z S K₁ K₂ t₀ u q hcfg₀ h73₀
    refine ⟨?_, D, hD.prod, ?_⟩
    · exact centralizer_eq_normalizer hstd.orderOf_z ht₀S
        (fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (hSC hs)) hcfg₀.ch.t_conj
        hcfg₀.ch.t_ne hcfg₀.ch.tz_ne
    · have hr1 := h73₀.1
      have hrne : (Pz S z).relIndex (S1 S K₁) ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases (by omega : (Pz S z).relIndex (S1 S K₁) = 1 ∨ (Pz S z).relIndex (S1 S K₁) = 2) with
        h1 | h2
      · have hid := hD.index_eq
        rw [h1, Subgroup.relIndex_eq_one] at hid
        have hDP : D ⊓ Pz S z = D := le_antisymm inf_le_left hid
        obtain ⟨n, hn⟩ := hD.inter_dih
        rw [hDP] at hn
        exact ⟨n, hn⟩
      · obtain ⟨n, hn⟩ := h77 G z S K₁ K₂ t₀ u q hcfg₀ h73₀ h74c₀ h2 D hD
        exact ⟨2 ^ n, hn.2⟩
  ·
    intro t₀ ht₀S ht₀c hsw₀
    exact swapE_of_pair hpair hsw₀ (mul_self_of_isConj hstd.orderOf_z ht₀c)

end Core

end CFSG.GH74.GLS.Stage1.Main
