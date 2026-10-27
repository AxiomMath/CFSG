module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WCaseA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar.BenderNormal
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YLemma42T1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding

section Z4

variable {T : Type} [Group T] [Finite T] {R : Subgroup T}

theorem one_lt_pRank_of_z4sq (e : ↥R ≃* Multiplicative (ZMod 4 × ZMod 4)) :
    1 < CFSG.Open.pRank 2 R := by
  have hclosed : ∀ x ∈ {x : Multiplicative (ZMod 4 × ZMod 4) | x ^ 2 = 1},
      ∀ y ∈ {x : Multiplicative (ZMod 4 × ZMod 4) | x ^ 2 = 1},
        x * y⁻¹ ∈ {x : Multiplicative (ZMod 4 × ZMod 4) | x ^ 2 = 1} := by
    have : ∀ x y : Multiplicative (ZMod 4 × ZMod 4), x ^ 2 = 1 → y ^ 2 = 1 → (x * y⁻¹) ^ 2 = 1 := by
      decide
    exact fun x hx y hy => this x y hx hy
  set E₀ : Subgroup (Multiplicative (ZMod 4 × ZMod 4)) :=
    Subgroup.ofDiv {x | x ^ 2 = 1} ⟨1, one_pow 2⟩ hclosed with hE₀def
  have hE₀ : Nat.card E₀ = 4 := by
    show Nat.card {x : Multiplicative (ZMod 4 × ZMod 4) // x ^ 2 = 1} = 4
    rw [Nat.card_eq_fintype_card]
    decide
  set E : Subgroup T := (E₀.map e.symm.toMonoidHom).map R.subtype with hEdef
  have hER : E ≤ R := Subgroup.map_subtype_le _
  have hEcard : Nat.card E = 2 ^ 2 := by
    rw [hEdef, Subgroup.card_map_of_injective R.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hE₀]
    norm_num
  have hmem : ∀ a ∈ E, ∃ x : Multiplicative (ZMod 4 × ZMod 4), x ^ 2 = 1 ∧ ((e.symm x : ↥R) : T) = a := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hEab : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨x, -, hx⟩ := hmem a a.2
      obtain ⟨y, -, hy⟩ := hmem b b.2
      show (a : T) * b = b * a
      rw [← hx, ← hy, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨x, hx2, rfl⟩ := hmem a ha
      rw [← Subgroup.coe_pow, ← map_pow, hx2, map_one, Subgroup.coe_one]
  have hbdd : BddAbove {k | ∃ E : Subgroup T, E ≤ R ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card T, fun k hk => ?_⟩
    obtain ⟨E', -, -, hk⟩ := hk
    have h1 : 2 ^ k ≤ Nat.card T := hk ▸ Subgroup.card_le_card_group E'
    have h2 : k < 2 ^ k := Nat.lt_two_pow_self
    show k ≤ Nat.card T
    omega
  have := le_csSup hbdd ⟨E, hER, hEab, hEcard⟩
  show 1 < sSup {k | ∃ E : Subgroup T, E ≤ R ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}
  omega

theorem not_isElemAbelian_of_z4sq (e : ↥R ≃* Multiplicative (ZMod 4 × ZMod 4)) :
    ¬ IsElemAbelian 2 R := by
  intro h
  have hx := h.2 ((e.symm (Multiplicative.ofAdd ((1 : ZMod 4), (0 : ZMod 4))) : ↥R) : T)
    (e.symm _).2
  have h1 : (e.symm (Multiplicative.ofAdd ((1 : ZMod 4), (0 : ZMod 4)))) ^ 2 = 1 :=
    Subtype.ext (by simpa using hx)
  rw [← map_pow, map_eq_one_iff _ e.symm.injective] at h1
  exact absurd h1 (by decide)

end Z4

theorem W192.w192W_mul_comm {u v : G192} (hu : u ∈ W192.w192W) (hv : v ∈ W192.w192W) :
    u * v = v * u := by
  have h : W192.w192WEquiv (⟨u, hu⟩ * ⟨v, hv⟩) = W192.w192WEquiv (⟨v, hv⟩ * ⟨u, hu⟩) := by
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val (W192.w192WEquiv.injective h)

namespace WCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem not_fstar_le_wQ [CaseIAmbient T] (cfg : WCfg K z J zJ H S) :
    ¬ genFittingFStar T ≤ wQ K := by
  intro hFQ
  haveI hFn : (genFittingFStar T).Normal := genFittingFStar_normal T
  have hFHt : genFittingFStar T ≤ firstFactor K := hFQ.trans (wQ_le K)
  obtain ⟨e⟩ := cfg.ht
  let ψ : ↥(genFittingFStar T) →* G192 := e.toMonoidHom.comp
    ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
      (Subgroup.inclusion hFHt))
  have hψW : ∀ f : ↥(genFittingFStar T), ψ f ∈ W192.w192W :=
    fun f => cfg.mk_mem_W_of_mem_Q e (hFQ f.2)
  rcases ψ.normal_ker.eq_bot_or_eq_top with hk | hk
  ·
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hk
    obtain ⟨a, b, hab⟩ :=
      (CaseIAmbient.fstar_nonabelian : ∃ a b : ↥(genFittingFStar T), a * b ≠ b * a)
    exact hab (hinj (by rw [map_mul, map_mul]; exact W192.w192W_mul_comm (hψW a) (hψW b)))
  ·
    have hle : (genFittingFStar T).subgroupOf (firstFactor K) ≤
        classicalInvolutionOddCore ↥(firstFactor K) := by
      intro x hx
      have h1 : ψ ⟨(x : T), hx⟩ = 1 := by
        have : (⟨(x : T), hx⟩ : ↥(genFittingFStar T)) ∈ ψ.ker := hk ▸ Subgroup.mem_top _
        exact this
      have h2 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)))
          (Subgroup.inclusion hFHt ⟨(x : T), hx⟩) = 1 :=
        e.injective (h1.trans e.map_one.symm)
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact h2
    have hodd : Odd (Nat.card ↥(genFittingFStar T)) := by
      have h := Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥(firstFactor K))
        (Subgroup.card_dvd_of_le hle)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFHt).toEquiv] at h
    have hFO : genFittingFStar T ≤ classicalInvolutionOddCore T :=
      CFSG.ComponentClassification.OddCore.maximal T _ hFn hodd
    rw [CaseIAmbient.oddCore_eq_bot (T := T), le_bot_iff] at hFO
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hFO

theorem false_of_thm1 [CaseIAmbient T]
    (h1 : CFSG.ComponentClassification.Asc76.Asc76Theorem1) (cfg : WCfg K z J zJ H S) : False := by
  have hz := cfg.datum.unique
  have hzQ : z ∈ wQ K := cfg.z_mem_Q
  haveI hFn : (genFittingFStar T).Normal := genFittingFStar_normal T
  obtain ⟨G₁, hG₁⟩ : ∃ G₁ : Subgroup T, genFittingFStar T ⊔ wQ K = G₁ := ⟨_, rfl⟩
  have hFG : genFittingFStar T ≤ G₁ := hG₁ ▸ le_sup_left
  have hQG : wQ K ≤ G₁ := hG₁ ▸ le_sup_right
  haveI hF₁n : ((genFittingFStar T).subgroupOf G₁).Normal := hFn.subgroupOf G₁
  haveI : IsSimpleGroup ↥((genFittingFStar T).subgroupOf G₁) :=
    (Subgroup.subgroupOfEquivOfLe hFG).isSimpleGroup
  have hC₁ : Subgroup.centralizer
      (((genFittingFStar T).subgroupOf G₁ : Subgroup ↥G₁) : Set ↥G₁) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgC : (g : T) ∈ Subgroup.centralizer (genFittingFStar T : Set T) := by
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro x hx
      exact congrArg Subtype.val
        (hg ⟨x, hFG hx⟩ (show (⟨x, hFG hx⟩ : ↥G₁) ∈ (genFittingFStar T).subgroupOf G₁ from hx))
    rw [CaseIAmbient.centralizer_fstar_eq_bot, Subgroup.mem_bot] at hgC
    exact Subgroup.mem_bot.mpr (Subtype.ext hgC)
  have hnc : Subgroup.normalClosure (((wQ K).subgroupOf G₁ : Subgroup ↥G₁) : Set ↥G₁) = ⊤ := by
    have hQN : (wQ K).subgroupOf G₁ ≤
        Subgroup.normalClosure (((wQ K).subgroupOf G₁ : Subgroup ↥G₁) : Set ↥G₁) :=
      Subgroup.subset_normalClosure
    have hN1 : Subgroup.normalClosure (((wQ K).subgroupOf G₁ : Subgroup ↥G₁) : Set ↥G₁) ≠ ⊥ := by
      intro h
      have hz₁ := hQN (show (⟨z, hQG hzQ⟩ : ↥G₁) ∈ (wQ K).subgroupOf G₁ from hzQ)
      rw [h, Subgroup.mem_bot] at hz₁
      exact hz.ne_one (congrArg Subtype.val hz₁)
    have hFN := le_of_normal_of_ne_bot hC₁ Subgroup.normalClosure_normal hN1
    have htop : (genFittingFStar T).subgroupOf G₁ ⊔ (wQ K).subgroupOf G₁ = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hFG hQG, hG₁, Subgroup.subgroupOf_self]
    rw [eq_top_iff, ← htop]
    exact sup_le hFN hQN
  have hO : CFSG.Open.standardComponentOddCore ↥G₁ = ⊥ := by
    refine sSup_eq_bot.mpr fun N hN => ?_
    obtain ⟨hNn, hodd⟩ := hN
    by_contra hN1
    have hle := le_of_normal_of_ne_bot hC₁ hNn hN1
    have hoddF : Odd (Nat.card ↥(genFittingFStar T)) := by
      have h := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFG).toEquiv] at h
    have hFO : genFittingFStar T ≤ classicalInvolutionOddCore T :=
      CFSG.ComponentClassification.OddCore.maximal T _ hFn hoddF
    rw [CaseIAmbient.oddCore_eq_bot (T := T), le_bot_iff] at hFO
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hFO
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨syl⟩ : Nonempty (Sylow 2 ↥(wQ K)) := inferInstance
  have hR : CFSG.ABGLocalTools.IsSylowOf 2 ((syl : Subgroup ↥(wQ K)).map (wQ K).subtype) (wQ K) :=
    ⟨syl, rfl⟩
  obtain ⟨eR⟩ := cfg.sylow_Q hR
  let eR₁ : ↥(((syl : Subgroup ↥(wQ K)).map (wQ K).subtype).subgroupOf G₁) ≃*
      Multiplicative (ZMod 4 × ZMod 4) :=
    (Subgroup.subgroupOfEquivOfLe (hR.le.trans hQG)).trans eR
  rcases h1 ↥G₁ ((wQ K).subgroupOf G₁)
      (CFSG.ComponentClassification.Asc76.Sec4.tightlyEmbedded_subgroupOf cfg.tight hQG) hnc
      (by rw [CFSG.ComponentClassification.Asc76.Sec4.oUpperTwoPrime_subgroupOf hQG,
        oUpperTwoPrime_wQ K]) hO
      (CFSG.ComponentClassification.Asc76.Sec4.sylowNormalizes_subgroupOf hQG
        (fun g hg => cfg.star g hg)) _
      (CFSG.ComponentClassification.Asc76.Sec4.isSylowOf_subgroupOf hR hQG)
      (one_lt_pRank_of_z4sq eR₁) with htop | hEA | ⟨hSz, -⟩
  ·
    exact cfg.not_fstar_le_wQ (hFG.trans (Subgroup.subgroupOf_eq_top.mp htop))
  · exact not_isElemAbelian_of_z4sq eR₁ hEA
  ·
    have hB₁ := CFSG.ComponentClassification.Asc76X.isBenderGroup_of_isSzOrU3 hSz
    haveI : IsSimpleGroup ↥G₁ := CFSG.GH74.Uniqueness.isSimpleGroup_of_isBenderGroup hB₁
    have hFeq : genFittingFStar T = G₁ := by
      rcases hF₁n.eq_bot_or_eq_top with h | h
      · exfalso
        have hbot : genFittingFStar T = ⊥ :=
          (inf_eq_left.mpr hFG).symm.trans (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h))
        exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hbot
      · exact le_antisymm hFG (Subgroup.subgroupOf_eq_top.mp h)
    exact FStar.frame_not_bender_normal cfg.datum (genFittingFStar T)
      CaseIAmbient.centralizer_fstar_eq_bot (hFeq ▸ hQG hzQ) (hFeq ▸ hB₁)

end WCfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
