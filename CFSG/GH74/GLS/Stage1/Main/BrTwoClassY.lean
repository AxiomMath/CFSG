module

public import CFSG.GH74.GLS.Stage1.Main.BridgeField
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassX

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

section Bridge

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem RC_le_Pz (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂)
    (hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂) : RC S z ≤ Pz S z := by
  intro r hr
  have hrS : r ∈ S := hr.1
  have hSC : S ≤ Cz z := hs.sylow.le
  have hrC : r ∈ Cz z := hSC hrS
  have hM := m4_of_std hII hs
  obtain ⟨k, hk⟩ := hs.sylow.isPGroup ⟨r, hrS⟩
  have hk' : (⟨r, hrC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hbar : toBar z ⟨r, hrC⟩ ∈ LBar z := (mem_LC_iff_of_pElt (z := z) ⟨r, hrC⟩ hk').1 hr.2
  rw [hLB, ← map_K12 hII hs] at hbar
  obtain ⟨y, hy, hyr⟩ := hbar
  have hker : (((y⁻¹ * ⟨r, hrC⟩ : ↥(Cz z)) : ↥(Cz z)) : G) ∈ Oz z := by
    refine (hatMk_eq_one_iff (Cz z) _).1 ?_
    rw [map_mul, map_inv, hyr]
    exact inv_mul_cancel (toBar z ⟨r, hrC⟩)
  have hn : ((K₁ ⊔ K₂).subgroupOf (Cz z)).Normal := by
    constructor
    intro n hn g
    exact hM.C_norm_K g.2 hn
  let φ := QuotientGroup.mk' ((K₁ ⊔ K₂).subgroupOf (Cz z))
  have hφ : φ ⟨r, hrC⟩ = φ (y⁻¹ * ⟨r, hrC⟩) := by
    rw [map_mul]
    have : φ y⁻¹ = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.inv_mem _ hy)
    rw [this, one_mul]
  have hord1 : orderOf (φ ⟨r, hrC⟩) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨r, hrC⟩ : ↥(Cz z)) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, map_one]
  have hord2 : orderOf (φ ⟨r, hrC⟩) ∣ Nat.card (Oz z) := by
    rw [hφ]
    refine (orderOf_map_dvd φ _).trans ?_
    rw [← Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard (Oz z) hker
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Oz z)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 card_Oz_odd)
  have h1 : orderOf (φ ⟨r, hrC⟩) = 1 := Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd hord1 hord2)
  have hr1 : φ ⟨r, hrC⟩ = 1 := orderOf_eq_one_iff.1 h1
  have hrN : (⟨r, hrC⟩ : ↥(Cz z)) ∈ (K₁ ⊔ K₂).subgroupOf (Cz z) := (QuotientGroup.eq_one_iff _).1 hr1
  refine ⟨hrS, ?_⟩
  rw [hs.rigidProduct_eq]
  exact hrN

end Bridge

section Main

theorem l4nfField_proved (hII : II4_4_4_center) (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6)
    (hpnf : P_normal_four) (hL44 : Lemma4_4) (hL45 : Lemma4_5) (h31 : IVK_3_1a_lifted)
    (h72 : Prop7_2) (h73 : Lemma7_3) (h74 : Lemma7_4) (h77 : Lemma7_7) (h31c : IVK_3_1c_lifted) :
    L4NFField := by
  intro G _ _ z S q w ε hcen hT hw hε L₁ L₂ hpair x₀ hx
  obtain ⟨K₁, K₂, t, u, hcfg, hsets, hcore⟩ :=
    twoClass_core_cfg hII h41 h61 h66 hpnf hL44 hL45 h31 h72 h73 h74 h77 hcen hT hpair
  have hs : Std4 G z S K₁ K₂ := hcfg.std.std
  have hM := m4_of_std hII hs
  have hSC : S ≤ Cz z := hs.sylow.le
  obtain ⟨w₇, hw₇, hde₇⟩ := h72 G z S K₁ K₂ t u q hcfg
  have hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂ := by
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← hpair.prod.1, h1, h2]
    · rw [← hpair.prod.1, h1, h2, sup_comm]
  have hw₇' := hw₇
  obtain ⟨hwS, hwo, htw, ⟨hPY, hSPY⟩, hS1, hint, hf⟩ := hw₇
  have htS : t ∈ S := hcfg.ch.t_mem
  have htC : t ∈ Cz z := hSC htS
  have ht2 : t * t = 1 := mul_self_of_isConj hs.orderOf_z hde₇.1.1
  have hw71 : w₇ ≠ 1 := by
    intro h1
    have hY : Ysub t w₇ = zpowers t := by
      rw [h1]
      simp [Ysub]
    have hSP : S = Pz S z ⊔ zpowers t := by
      have := hSPY
      rwa [hY] at this
    exact w7_ne_one hII h41 hT hw hs hLB hcfg.ch.t_mem ht2 hSP
  have hwo2 : orderOf w₇ = 2 := hwo.resolve_left hw71
  have hw2 : w₇ * w₇ = 1 := mul_self_eq_one_of_orderOf_eq_two hwo2
  have hwC : w₇ ∈ Cz z := hSC hwS
  have hwN₁ : w₇ ∈ normalizer (K₁ : Set G) := by
    have : w₇ ∈ CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₁ := by
      rw [hS1]
      exact Subgroup.mem_sup_right (mem_zpowers w₇)
    exact this.2
  have hwN₂ : w₇ ∈ normalizer (K₂ : Set G) := mem_normalizer_swap hs hwC hwN₁
  have hwz : IsConj z w₇ := hde₇.2.2 hw71
  have hSL : HasSL2Model ↥(imgBar z K₁) (fun r => r = q) ∧
      HasSL2Model ↥(imgBar z K₂) (fun r => r = q) :=
    sets_transfer hsets (fun L => HasSL2Model ↥L (fun r => r = q)) hpair.sl₁ hpair.sl₂
  have hPGL : ∀ K, (K = K₁ ∨ K = K₂) → HasSL2Model ↥(imgBar z K) (fun r => r = q) →
      PGLOver (imgBar z K) (barOf z (zpowers w₇)) q := by
    intro K hK hL
    have hKmem : K ∈ ({K₁, K₂} : Set (Subgroup G)) := by
      rcases hK with h | h
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        exact Or.inr rfl
    obtain ⟨Fq, iF, fF, hq, hpgl⟩ := hf hw71 K hKmem
    have hwNK : w₇ ∈ normalizer (K : Set G) := by
      rcases hK with h | h
      · rw [h]
        exact hwN₁
      · rw [h]
        exact hwN₂
    exact pglOver_of_pglQuot hII hs hK hL hwC hw2 hwNK hq hpgl
  have hgood : GoodInvolution z S L₁ L₂ q w₇ := by
    have := sets_transfer hsets.symm (fun L => PGLOver L (barOf z (zpowers w₇)) q)
      (hPGL K₁ (Or.inl rfl) hSL.1) (hPGL K₂ (Or.inr rfl) hSL.2)
    exact ⟨hwS, hwo2, this.1, this.2⟩
  have hsw : Swaps z t L₁ L₂ := by
    have h0 : Swaps z t (imgBar z K₁) (imgBar z K₂) :=
      swaps_of_interchanges hM.K₁_le hM.K₂_le htC hint
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact h0
    · rw [h1, h2]
      exact swaps_symm h0
  have hux : IsConj x₀ u := by
    rcases hx.classes u hcfg.ch.u_ord with h | h
    · exact absurd (isCentralInvolution_of_isConj_Y hcen.central h) hcore.x_nonCentral
    · exact h
  have hnot : w₇ ∉ RC S z ⊔ zpowers t := by
    intro hmem
    have hP : w₇ ∈ Pz S z ⊔ zpowers t := sup_le_sup_right (RC_le_Pz hII hs hLB) _ hmem
    have hzt : zpowers t ≤ normalizer ((Pz S z : Subgroup G) : Set G) :=
      (Subgroup.zpowers_le.2 htS).trans (S_le_normalizer_Pz hII hs)
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (Pz S z) (zpowers t) hzt
    have hP' : w₇ ∈ ((Pz S z : Subgroup G) : Set G) * ((zpowers t : Subgroup G) : Set G) := by
      rw [← hmul]
      exact hP
    obtain ⟨p, hp, a, ha, hpa⟩ := Set.mem_mul.1 hP'
    have hwY : w₇ ∈ Ysub t w₇ := by
      unfold Ysub
      exact Subgroup.mem_sup_right (mem_zpowers w₇)
    have htY : t ∈ Ysub t w₇ := by
      unfold Ysub
      exact Subgroup.mem_sup_left (mem_zpowers t)
    rcases eq_one_or_eq_of_mem_zpowers_sq ht2 ha with h | h
    · rw [h, mul_one] at hpa
      have hmem2 : w₇ ∈ Pz S z ⊓ Ysub t w₇ := ⟨hpa ▸ hp, hwY⟩
      rw [hPY, Subgroup.mem_bot] at hmem2
      exact hw71 hmem2
    · rw [h] at hpa
      have hpY : p ∈ Pz S z ⊓ Ysub t w₇ := by
        refine ⟨hp, ?_⟩
        have : p = w₇ * t⁻¹ := by rw [← hpa]; group
        rw [this]
        exact Subgroup.mul_mem _ hwY (Subgroup.inv_mem _ htY)
      rw [hPY, Subgroup.mem_bot] at hpY
      have hwt : w₇ = t := by
        have : w₇ = p * t := hpa.symm
        rw [this, hpY, one_mul]
      have hK : K₂ = K₁ := by
        rw [← hint.1]
        ext y
        rw [mem_conjugate_iff, ← hwt]
        exact (Subgroup.mem_normalizer_iff.1 hwN₁ y).symm
      exact hs.ne hK.symm
  have hcoset : ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∃ r ∈ RC S z, y = r * w₇) → IsConj z y := by
    rintro y hyS hy2 hy1 ⟨r, hr, rfl⟩
    have hyo : orderOf (r * w₇) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    have hpw : r * w₇ * w₇⁻¹ ∈ Pz S z := by
      rw [mul_inv_cancel_right]
      exact RC_le_Pz hII hs hLB hr
    have hw1' : w₇ * w₇⁻¹ ∈ Pz S z := by
      rw [mul_inv_cancel]
      exact (Pz S z).one_mem
    obtain ⟨c, -, hc⟩ := h31c G z S K₁ K₂ t u q w₇ hcfg hw₇' hw71 w₇ hwS (r * w₇) hyS hw1' hpw hwo2 hyo
    exact hwz.trans (isConj_iff.2 ⟨c, hc⟩)
  exact ⟨t, htS, hde₇.1.1, hsw, w₇, hwS, hwo2, htw, hnot, hgood, hwz, hde₇.1.2,
    hux.trans hde₇.2.1.2, hcoset⟩

end Main

end CFSG.GH74.GLS.Stage1.Main
