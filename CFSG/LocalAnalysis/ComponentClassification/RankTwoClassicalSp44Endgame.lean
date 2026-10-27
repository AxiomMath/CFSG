module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44EndgameTools

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

section Endgame

variable {G : Type} [Group G]

theorem mem_centralizer_zpowers_iff {z g : G} :
    g ∈ centralizer (zpowers z : Set G) ↔ g * z = z * g := by
  constructor
  · intro h
    exact (mem_centralizer_iff.mp h z (mem_zpowers z)).symm
  · intro h
    rw [mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    show z ^ k * g = g * z ^ k
    exact (Commute.zpow_right (show Commute g z from h) k).eq.symm

theorem commutator_eq_self_of_perfect {M : Subgroup G} (h : commutator ↥M = ⊤) : ⁅M, M⁆ = M := by
  have h1 := congrArg (Subgroup.map M.subtype) h
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1
  exact h1

theorem conjAut_pow {A : Subgroup G} {s : G} (hs : s ∈ normalizer (A : Set G)) (n : ℕ) :
    conjAut hs ^ n = conjAut (Subgroup.pow_mem _ hs n) := by
  have key : ∀ (k : ℕ) (x : ↥A), ((conjAut hs ^ k) x : G) = s ^ k * x * (s ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, conjAut_apply, pow_succ]
      group
  ext x
  rw [key, conjAut_apply]

variable [Finite G]

theorem Cfg76.facts_at {A R Y L Z : Subgroup G} (hc : Cfg76 A R Y L)
    (h32 : Lemma32) (hZA : Z ≤ A) (hLZ : L ≤ centralizer (Z : Set G))
    (hstd : standardComponentIsStandard (L.subgroupOf (centralizer (Z : Set G))))
    (hnn : ¬ (L.subgroupOf (centralizer (Z : Set G))).Normal)
    (hnoZ : NoInvolutoryCentralizing A (Z ⊔ L)) :
    RankTwoHyp ↥(centralizer (Z : Set G)) (L.subgroupOf (centralizer (Z : Set G))) ∧
      center ↥(L.subgroupOf (centralizer (Z : Set G))) = ⊥ ∧
      Nat.card (L.subgroupOf (centralizer (Z : Set G))) = 60 ∧
      ⁅L.subgroupOf (centralizer (Z : Set G)), L.subgroupOf (centralizer (Z : Set G))⁆ =
        L.subgroupOf (centralizer (Z : Set G)) ∧
      IsElemAbelian 2 (R.subgroupOf (centralizer (Z : Set G))) ∧
      4 ≤ Nat.card (R.subgroupOf (centralizer (Z : Set G))) ∧
      R.subgroupOf (centralizer (Z : Set G)) ≤ centralizer
        ((L.subgroupOf (centralizer (Z : Set G)) : Subgroup ↥(centralizer (Z : Set G))) :
          Set ↥(centralizer (Z : Set G))) ∧
      IsSylowOf 2 (R.subgroupOf (centralizer (Z : Set G))) (centralizer
        ((L.subgroupOf (centralizer (Z : Set G)) : Subgroup ↥(centralizer (Z : Set G))) :
          Set ↥(centralizer (Z : Set G)))) ∧
      (∀ x : ↥(centralizer (Z : Set G)), ¬ rightConjugate (R.subgroupOf
        (centralizer (Z : Set G))) x ≤ L.subgroupOf (centralizer (Z : Set G))) ∧
      Nonempty (rankTwoQuot (L.subgroupOf (centralizer (Z : Set G))) ≃*
        alternatingGroup (Fin 5)) ∧
      Odd (Nat.card (center ↥(L.subgroupOf (centralizer (Z : Set G))))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (Z : Set G) with hCdef
  have hRC : R ≤ C := hc.sylowR.le.trans (centralizer_le hZA)
  set e := subgroupOfEquivOfLe hLZ
  obtain ⟨f⟩ := hc.a5
  have ha5 : Nonempty (rankTwoQuot (L.subgroupOf C) ≃* alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.congr (center _) (center _) e (Subgroup.map_center_eq e)).trans f⟩
  have hodd : Odd (Nat.card (center ↥(L.subgroupOf C))) := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hc.oddCenter
  obtain ⟨hZ, h60⟩ := center_eq_bot_of_a5 hstd.1 hodd ha5
  have hH : RankTwoHyp ↥C (L.subgroupOf C) :=
    ⟨LocalAnalysis.ComponentInitial.kProper_subgroup
        (fun e h => SectionRank.catalog_of_mulEquiv e h) hc.kProper _, hstd, hnn,
      two_le_pRank_centralizer_subgroupOf' hZA hc.L_le_A hc.rank⟩
  have hRL : IsSylowOf 2 R (C ⊓ centralizer (L : Set G)) := by
    refine Lemma37.isSylowOf_of_isSylowOf_inf_normalizer ?_
    refine isSylowOf_of_noInvolutory hc.hyp hc.sylowR hnoZ
      (le_inf (le_inf hRC hc.R_le_centralizer_L) le_normalizer) ?_ inf_le_right
    intro x hx
    obtain ⟨⟨hxZ, hxL⟩, -⟩ := mem_inf.mp hx
    exact mem_centralizer_sup hxZ hxL
  refine ⟨hH, hZ, h60, commutator_eq_self_of_perfect hstd.1.1,
    ?_, ?_, ?_, ?_, ?_, ha5, hodd⟩
  · have hV := h32 G A hc.hyp R hc.sylowR
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val (hV.1.is_comm.comm ⟨((a : C) : G), a.2⟩ ⟨((b : C) : G), b.2⟩)
    · rw [mem_subgroupOf] at ha
      exact Subtype.ext (by simpa using hV.2 _ ha)
  · rw [Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv]
    exact Lemma36.four_le_card hc.hyp hc.sylowR
  · rw [Lemma37.centralizer_subgroupOf hLZ]
    intro r hr
    exact mem_subgroupOf.mpr (hc.R_le_centralizer_L (mem_subgroupOf.mp hr))
  · rw [Lemma37.centralizer_subgroupOf hLZ,
      ← Subgroup.inf_subgroupOf_left (centralizer (L : Set G)) C,
      Lemma37.isSylowOf_subgroupOf_iff hRC inf_le_left]
    exact hRL
  · intro x hle
    apply hc.not_le (x : G)
    intro r hr
    rw [mem_rightConjugate_iff] at hr
    have hrC : r ∈ C := by
      have h1 : (x : G) * r * (x : G)⁻¹ ∈ C := hRC hr
      have h2 : r = (x : G)⁻¹ * ((x : G) * r * (x : G)⁻¹) * (x : G) := by group
      rw [h2]
      exact mul_mem (mul_mem (inv_mem x.2) h1) x.2
    have h2 : (⟨r, hrC⟩ : ↥C) ∈ rightConjugate (R.subgroupOf C) x := by
      rw [mem_rightConjugate_iff, mem_subgroupOf]
      simpa using hr
    exact hc.L_le_A (mem_subgroupOf.mp (hle h2))

end Endgame

section Main

theorem sp44Endgame_of
    (h32 : Lemma32) (h5 : Asc08Lemma310) (hJ : J2A4Facts) (hM : M12AutThreeFive) :
    Sp44Endgame := by
  intro G _ _ A R W L y s y₃ hc hsp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLA : L ≤ A := hc.L_le_A
  have hsN : s ∈ normalizer (A : Set G) := le_normalizer hsp.s_mem
  have hWA : W ≤ A := by
    rw [← hsp.conj_L, ← (rightConjugate_eq_self_iff A s).mpr hsN]
    exact map_mono hLA
  have hy₃A : y₃ ∈ A := hWA hsp.y₃_mem
  set x := s⁻¹ * y * s with hxdef
  have hxL : x ∈ L := by
    rw [← hsp.conj_W, mem_rightConjugate_iff]
    simpa [hxdef, mul_assoc] using hsp.y_mem
  have hx5 : orderOf x = 5 := by
    have := orderOf_injective (MulAut.conj s⁻¹).toMonoidHom (MulAut.conj s⁻¹).injective y
    simpa [MulAut.conj_apply, hsp.orderOf_y, hxdef] using this
  have hcx : Cfg76 A R (zpowers x) W := by
    have h := hc.conj hsp.s_mem
    rwa [rightConjugate_zpowers, hsp.conj_L] at h
  obtain ⟨f, hfA, ⟨k, hk⟩, hfRN, hfR⟩ : ∃ f : G, f ∈ centralizer (A : Set G) ∧
      (∃ k : ℕ, f ^ 3 ^ k = 1) ∧ f ∈ normalizer (R : Set G) ∧ f ∉ centralizer (R : Set G) := by
    have hLCy : L ≤ centralizer (zpowers y : Set G) := hc.L_le_centralizer
    obtain ⟨hHy, hZ, h60, hp, hRe, hR4, hRM, -⟩ :=
      hc.facts_at h32 hc.Y_le hLCy hc.standard hc.not_normal hc.noInv
    have hxM : (⟨x, hLCy hxL⟩ : ↥(centralizer (zpowers y : Set G))) ∈
        L.subgroupOf (centralizer (zpowers y : Set G)) := mem_subgroupOf.mpr hxL
    obtain ⟨f, hfM, hfN, ⟨k, hk⟩, hfR⟩ := exists_three_of_j2A4 hJ hHy
      (hc.isSporadic_j2 h5) hRe hR4 hRM hZ hp h60 hxM (by rw [Subgroup.orderOf_mk, hx5])
    have hfL : (f : G) ∈ centralizer (L : Set G) := by
      rw [Lemma37.centralizer_subgroupOf hLCy, mem_subgroupOf] at hfM
      exact hfM
    have hfRN : (f : G) ∈ normalizer (R : Set G) := by
      rw [← subgroupOf_normalizer_eq hc.R_le_centralizer_Y] at hfN
      exact hfN
    have hfR' : (f : G) ∉ centralizer (R : Set G) := by
      intro h
      apply hfR
      rw [mem_centralizer_iff]
      intro r hr
      exact Subtype.ext (mem_centralizer_iff.mp h r (mem_subgroupOf.mp hr))
    have hk' : (f : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hfNA : (f : G) ∈ normalizer (A : Set G) := by
      have h := Lemma36.normalizer_le hc.hyp hc.sylowR 1
      rw [rightConjugate_one, rightConjugate_one] at h
      exact h hfRN
    have hfYL := mem_centralizer_sup f.2 hfL
    have hσ := hsp.noThree (conjAut hfNA) ⟨k, by
        rw [conjAut_pow]
        ext z
        simp [conjAut_apply, hk']⟩
      fun z hz => Subtype.ext (by
        rw [conjAut_apply, ← mem_centralizer_iff.mp hfYL z hz, mul_inv_cancel_right])
    refine ⟨f, ?_, ⟨k, hk'⟩, hfRN, hfR'⟩
    rw [mem_centralizer_iff]
    intro a ha
    have h := congrArg (fun σ : MulAut ↥A => ((σ ⟨a, ha⟩ : ↥A) : G)) hσ
    simp only [conjAut_apply, MulAut.one_apply] at h
    calc a * f = f * a * (f : G)⁻¹ * f := by rw [h]
      _ = f * a := by group
  have hLC₃ : L ≤ centralizer (zpowers y₃ : Set G) := by
    intro l hl
    rw [mem_centralizer_zpowers_iff]
    exact mem_centralizer_iff.mp (hsp.W_le hsp.y₃_mem) l hl
  obtain ⟨hH₃, hZ₃, h60₃, hp₃, hRe₃, hR4₃, hRM₃, hRsyl₃, hno₃, ha5₃, hodd₃⟩ :=
    hc.facts_at h32 (zpowers_le.mpr hy₃A) hLC₃ hsp.standard₃ hsp.not_normal₃ hsp.noInv₃
  have hRC₃ : R ≤ centralizer (zpowers y₃ : Set G) :=
    hc.sylowR.le.trans (centralizer_le (zpowers_le.mpr hy₃A))
  have hxM₃ : (⟨x, hLC₃ hxL⟩ : ↥(centralizer (zpowers y₃ : Set G))) ∈
      L.subgroupOf (centralizer (zpowers y₃ : Set G)) := mem_subgroupOf.mpr hxL
  have hx5₃ : orderOf (⟨x, hLC₃ hxL⟩ : ↥(centralizer (zpowers y₃ : Set G))) = 5 := by
    rw [Subgroup.orderOf_mk, hx5]
  have hfC₃ : f ∈ centralizer (zpowers y₃ : Set G) := centralizer_le (zpowers_le.mpr hy₃A) hfA
  obtain ⟨e₃⟩ := ha5₃
  rcases h5 _ _ (rankTwoHyp_map hH₃) standardComponentOddCore_quotient_eq_bot
      ⟨(quotCenterMap hH₃).symm.trans e₃⟩ (odd_card_center_map hH₃ hodd₃) _
      (isSylowOf_map hH₃ hRsyl₃) (not_conj_le_map hH₃ hRsyl₃.isPGroup hno₃) with hJ₃ | ⟨hM₃, -⟩
  ·
    obtain ⟨S, hSx, hS⟩ := exists_five_of_j2A4 hJ hH₃ hJ₃ hRe₃ hR4₃ hRM₃ hZ₃ hp₃ h60₃ hxM₃ hx5₃
    set Cx := centralizer (zpowers x : Set G) with hCx
    set Ox : Subgroup G := (standardComponentOddCore ↥Cx).map Cx.subtype with hOx
    have hSCx : ∀ c ∈ S, (c : G) ∈ Cx := by
      intro c hc'
      have h1 := mem_centralizer_singleton_iff.mp (hSx hc')
      rw [mem_centralizer_zpowers_iff]
      exact congrArg Subtype.val h1
    have hOxN : ∀ c : G, c ∈ Cx → ∀ o ∈ Ox, c * o * c⁻¹ ∈ Ox := by
      rintro c hc' _ ⟨o, ho, rfl⟩
      exact ⟨⟨c, hc'⟩ * o * ⟨c, hc'⟩⁻¹,
        (inferInstance : (standardComponentOddCore ↥Cx).Normal).conj_mem o ho _, rfl⟩
    set N := S ⊓ Ox.comap (centralizer (zpowers y₃ : Set G)).subtype with hN
    have hSN : S ≤ normalizer (N : Set ↥(centralizer (zpowers y₃ : Set G))) := by
      intro c hc'
      refine mem_normalizer_inf (le_normalizer hc') ?_
      rw [mem_normalizer_iff]
      intro z
      simp only [mem_comap, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      constructor
      · exact hOxN _ (hSCx c hc') _
      · intro h
        have := hOxN _ (inv_mem (hSCx c hc')) _ h
        simpa [mul_assoc] using this
    have hNodd : Odd (Nat.card N) := by
      have hle : N.map (centralizer (zpowers y₃ : Set G)).subtype ≤ Ox := by
        rintro _ ⟨z, hz, rfl⟩
        exact mem_comap.mp (mem_inf.mp hz).2
      have h1 := Subgroup.card_dvd_of_le hle
      rw [card_map_of_injective (centralizer (zpowers y₃ : Set G)).subtype_injective,
        hOx, card_map_of_injective Cx.subtype_injective] at h1
      exact (odd_card_standardComponentOddCore (G := ↥Cx)).of_dvd_nat h1
    obtain ⟨h, hhS, ⟨j, hj⟩, hhN⟩ := hS N inf_le_left hSN hNodd
    have hhOx : (h : G) ∉ Ox := fun hmem => hhN (mem_inf.mpr ⟨hhS, mem_comap.mpr hmem⟩)
    have hWCx : W ≤ Cx := hcx.L_le_centralizer
    obtain ⟨hHx, hZx, h60x, hpx, hRex, hR4x, hRMx, -⟩ :=
      hcx.facts_at h32 hcx.Y_le hWCx hcx.standard hcx.not_normal hcx.noInv
    have ht := mk'_eq_one_of_j2A4 hJ hHx (hcx.isSporadic_j2 h5) hRex hR4x hRMx hZx hpx h60x
      (w := ⟨y, hWCx hsp.y_mem⟩) (mem_subgroupOf.mpr hsp.y_mem)
      (by rw [Subgroup.orderOf_mk, hsp.orderOf_y]) (z := ⟨y₃, hWCx hsp.y₃_mem⟩)
      (mem_subgroupOf.mpr hsp.y₃_mem) (by rw [Subgroup.orderOf_mk, hsp.orderOf_y₃])
      (t := ⟨(h : G), hSCx h hhS⟩) ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩
      (Subtype.ext (mem_centralizer_zpowers_iff.mp h.2))
    apply hhOx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ht
    exact ⟨_, ht, rfl⟩
  ·
    have ht := mk'_eq_one_of_m12 hM hH₃ hM₃ hZ₃ hxM₃ hx5₃ (t := ⟨f, hfC₃⟩)
      ⟨k, Subtype.ext (by simpa using hk)⟩
      (Subtype.ext (mem_centralizer_iff.mp hfA x (hLA hxL)).symm)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ht
    apply hfR
    have hfN₃ : (⟨f, hfC₃⟩ : ↥(centralizer (zpowers y₃ : Set G))) ∈
        normalizer ((R.subgroupOf (centralizer (zpowers y₃ : Set G)) :
          Subgroup ↥(centralizer (zpowers y₃ : Set G))) :
            Set ↥(centralizer (zpowers y₃ : Set G))) := by
      rw [← subgroupOf_normalizer_eq hRC₃]
      exact hfRN
    have hc' := mem_centralizer_of_mem_oddCore (isPGroup_of_isElemAbelian hRe₃) ht hfN₃
    rw [mem_centralizer_iff]
    intro r hr
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc' ⟨r, hRC₃ hr⟩ (mem_subgroupOf.mpr hr))

end Main

end CFSG.ComponentClassification.RankTwoClassical
