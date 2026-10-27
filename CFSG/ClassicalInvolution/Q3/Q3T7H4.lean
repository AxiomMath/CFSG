module

public import CFSG.ClassicalInvolution.Q3.Q3T7M03
public import CFSG.ClassicalInvolution.Q3.Q3T7ExNbr
public import CFSG.ClassicalInvolution.Q3.Q3T7ExGen
public import CFSG.ClassicalInvolution.Q3.Q3T6AutUni
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreRestr
public import CFSG.ClassicalInvolution.Q3.Q3T7Thm3Sect
public import CFSG.ClassicalInvolution.Q3.Q3T7FUEH
public import CFSG.ClassicalInvolution.Asc77.AscE184Cent

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3T7 CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement


section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_trivialOnQuot_of_le_centralizer3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : IsSylow2In R K) {w : G} (hw1 : w ≠ 1) (hw2 : w * w = 1)
    (hRw : R ≤ Subgroup.centralizer ({w} : Set G)) : w ∈ trivialOnQuot K := by
  have hΩg := modU_toGen3 hΩ
  have h8 : 8 ≤ Nat.card R :=
    Sec6Gen.eight_le_of_mem_RSet hΩg (mem_RSet_of_isSylow2In hK hR)
  have hRKw : R ≤ conjSub w K := by
    intro r hr
    rw [mem_conjSub_iff]
    have h1 : w * r = r * w := (Subgroup.mem_centralizer_singleton_iff.mp (hRw hr)).symm
    have : w⁻¹ * r * w = r := by rw [mul_assoc, ← h1]; group
    rw [this]
    exact hR.1 hr
  have hwK : conjSub w K = K :=
    Sec6Gen.eq_of_le_of_le hΩg (hΩg.conjInvariant w K hK) hK hR.2.1 (by omega) hRKw hR.1
  have hwN : w ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hwK
  have hV2 : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1]
      norm_num)
  have hcomm : ⁅Subgroup.zpowers w, K⁆ ≤ oddCoreOf K :=
    Subgroup.commutator_le.mpr fun v hv k hk =>
      Q3T6.centSylow_three_of_memberU hΩ.classical hK hR hV2
        (fun y hy => mem_normalizer_iff_conjSub_eq.mp
          ((Subgroup.zpowers_le.mpr hwN) hy))
        (fun r hr u hu => by
          obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
          exact (Commute.zpow_right
            (show Commute r w from Subgroup.mem_centralizer_singleton_iff.mp (hRw hr))
            k').eq) k hk v hv
  refine mem_trivialOnQuot_iff.mpr ⟨hwN, fun x hx => hcomm ?_⟩
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers w) hx

end Basic

section Dichotomy

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem dichotomy_of_thm4 {n : ℕ} (h4 : Thm4Below n) (hlt : Nat.card G < n)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hO : classicalInvolutionOddCore G = ⊥)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) {L : Subgroup G} (hL : L ∈ Ω) :
    (∀ M ∈ Ω, M ∈ dstarComp Ω L) ∨ (∀ M ∈ Ω, ∃ y : G, conjSub y L = M) := by
  have hΩg := modU_toGen3 hΩ
  by_cases hall : ∀ M ∈ Ω, ∃ y : G, conjSub y L = M
  · exact Or.inr hall
  left
  push Not at hall
  obtain ⟨M₀, hM₀, hM₀c⟩ := hall
  have hLM₀ : M₀ ≠ L := fun h => hM₀c 1 (by rw [conjSub_one, h])
  have hc0 : Commutes L M₀ := h4 G hlt Ω hΩ hO hA L hL M₀ hM₀ (fun ⟨g, hg⟩ => hM₀c g hg)
  have hadj0 : dstarAdj Ω L M₀ := dstarAdj_of_commutes hΩ hM₀ hLM₀ hc0.symm
  intro M hM
  by_cases hMc : ∃ y : G, conjSub y L = M
  · obtain ⟨y, rfl⟩ := hMc
    have hnot : ¬ ∃ g : G, conjSub g (conjSub y L) = M₀ := by
      rintro ⟨g, hg⟩
      exact hM₀c (g * y) (by rw [conjSub_mul]; exact hg)
    have hc1 : Commutes (conjSub y L) M₀ := h4 G hlt Ω hΩ hO hA _ hM M₀ hM₀ hnot
    have hne : M₀ ≠ conjSub y L := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj0)
      (dstarAdj_of_commutes hΩ hM hne.symm hc1)
  · have hc : Commutes L M := h4 G hlt Ω hΩ hO hA L hL M hM (fun ⟨g, hg⟩ => hMc ⟨g, hg⟩)
    have hne : M ≠ L := fun h => hMc ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.single (dstarAdj_of_commutes hΩ hM hne hc.symm)

end Dichotomy

section SectionTheorem

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem MinCex.section_le_H (c : MinCex Ω K S R W H) {Y : Subgroup G} (hY : Y ≠ ⊤)
    {Λ : Set (Subgroup ↥Y)} (hΛ : HypOmegaModU (.sl2 3 1) Λ) (S₁ : Sylow 2 ↥Y)
    {K₁ K₁' R₁ R₁' : Subgroup ↥Y} (hK₁ : K₁ ∈ Λ) (hK₁' : K₁' ∈ twinSet Λ K₁) (hne : K₁' ≠ K₁)
    (hR₁ : R₁ ∈ RSet Λ) (hR₁K : R₁ ≤ K₁) (hR₁S : R₁ ≤ (S₁ : Subgroup ↥Y))
    (hR₁' : R₁' ∈ RSet Λ) (hR₁'K : R₁' ≤ K₁') (hR₁'S : R₁' ≤ (S₁ : Subgroup ↥Y))
    (hNH : oddCoreOf Y ≤ H) (hgen : Y ≤ ⨆ L ∈ Λ, L.map Y.subtype)
    (hY1 : (∀ J ∈ Λ, ∃ y : ↥Y, conjSub y K₁ = J) →
      ∀ J ∈ dstarComp Λ K₁, ∃ h ∈ H.subgroupOf Y, conjSub h K₁ = J)
    (hcent : CentralizersSylowPairs Λ K₁ (H.subgroupOf Y))
    (good : Subgroup ↥Y → Prop) (hgood₀ : good K₁)
    (hgood : ∀ L ∈ Λ, ∀ L' ∈ Λ, good L → dstarAdj Λ L L' → good L')
    (hgoodH : ∀ L ∈ Λ, good L → L.map Y.subtype ≤ H)
    (hA3 : (¬ ∀ L ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
        ∀ J ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
          J ∈ dstarComp (quotFamily Λ (classicalInvolutionOddCore ↥Y)) L) →
      ∀ L ∈ Λ, AEmpty Λ L) : Y ≤ H := by
  have hΛg := modU_toGen3 hΛ
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ' : HypOmegaModU (.sl2 3 1) (quotFamily Λ N₀) := T3CII.hypOmegaModU_oddQuotientFamily hΛ
  have hΛ'g := modU_toGen3 hΛ'
  have hltY := natCard_lt_of_ne_top hY
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (↥Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
  have hN₀H : ∀ n ∈ N₀, (n : G) ∈ H := fun n hn => hNH ⟨n, hn, rfl⟩
  by_cases hconn : ∀ M ∈ quotFamily Λ N₀,
      M ∈ dstarComp (quotFamily Λ N₀) (K₁.map (QuotientGroup.mk' N₀))
  ·
    have hmem := E187C.section_connected_of Y.subtype hΛg.conjInvariant
      (fun hL hL' hadj => exists_conj_omegaStarNbr hΛ hΛ' hN₀odd hL hL' hadj) (fun hK hL h => exists_conj_of_map_eq hΛ hN₀odd hK hL h) hN₀H hK₁ good hgood₀ hgood hgoodH hconn
    exact hgen.trans (iSup₂_le fun L hL => hmem L hL)
  ·
    have hdis : ¬ ∀ L ∈ quotFamily Λ N₀, ∀ J ∈ quotFamily Λ N₀,
        J ∈ dstarComp (quotFamily Λ N₀) L :=
      fun h => hconn fun M hM => h _ (map_mem_quotFamily hK₁) M hM
    have hΛA : ∀ L ∈ Λ, AEmpty Λ L := hA3 hdis
    have hAΛ' := aEmpty_quotFamily hΛ hΛ' hN₀odd hΛA
    rcases dichotomy_of_thm4 (thm4Below_of_ih c.stand.ih) hlt hΛ' hOq hAΛ'
      (map_mem_quotFamily hK₁) with hc' | horb
    · exact absurd hc' hconn
    have hall := E187C.section_hall_of hΛg.conjInvariant
      (fun hK hL h => exists_conj_of_map_eq hΛ hN₀odd hK hL h) hK₁ horb
    obtain ⟨W₁, hW₁, hW₁S, hW₁n⟩ := exists_W_of_hypOmega hΛ S₁
    have hEStand : EStand Λ K₁ S₁ R₁ W₁ :=
      { hyp := hΛ
        ob := c.stand.ob
        below := CFSG.ClassicalInvolution.Q3.Q3T8.Generic.CITBelowU.mono
          (Subgroup.card_le_card_group Y) c.stand.below
        ih := ih8T_mono (Subgroup.card_le_card_group Y) c.stand.ih
        mem := hK₁
        aEmpty := hΛA K₁ hK₁
        twin := ⟨K₁', hK₁', hne, R₁', hR₁', hR₁'K, hR₁'S⟩
        hR := ⟨hR₁, hR₁K, hR₁S⟩
        hW := ⟨hW₁, hW₁S, hW₁n⟩ }
    have key := c.minimal ↥Y hltY Λ K₁ S₁ R₁ W₁ (H.subgroupOf Y) hEStand ⟨hY1 hall, hcent⟩
    exact Subgroup.subgroupOf_eq_top.mp key

end SectionTheorem

section NormalTwo

variable {G : Type} [Group G] [Finite G]

theorem commutes_of_commutator_commutes {N : Subgroup G} (hN : IsPGroup 2 N) {y : G}
    (hyN : ∀ g ∈ N, y * g * y⁻¹ ∈ N) (hy : Odd (orderOf y)) {g : G} (hg : g ∈ N)
    (hd : y * (g⁻¹ * (y * g * y⁻¹)) = (g⁻¹ * (y * g * y⁻¹)) * y) : y * g = g * y :=
  CFSG.ClassicalInvolution.T7FU.Asc77.commutes_of_commutator_commutes hN hyN hy hg hd

theorem centralizes_of_isSubnormal {Q : Subgroup G} [Q.Normal] (hQ2 : IsPGroup 2 ↥Q) {T : Set G}
    (hT : ∀ x ∈ T, Odd (orderOf x)) {M K : Subgroup G} (h : IsSubnormal M K)
    (hTM : ∀ x ∈ T, x ∈ M) (h0 : ∀ x ∈ T, ∀ q ∈ M ⊓ Q, x * q = q * x) :
    ∀ x ∈ T, ∀ q ∈ K ⊓ Q, x * q = q * x :=
  CFSG.ClassicalInvolution.T7FU.Asc77.centralizes_of_isSubnormal hQ2 hT h hTM h0

theorem normal_two_central3 {Ω : Set (Subgroup G)} (hΩ : Q3T7M.HM Ω) {Q : Subgroup G}
    [Q.Normal] (hQ2 : IsPGroup 2 ↥Q) {J : Subgroup G} (hJ : J ∈ Ω) (hJQ : J ⊓ Q = ⊥) :
    J ≤ Subgroup.centralizer (Q : Set G) := by
  have hΩg := modU_toGen3 hΩ
  obtain ⟨z, hz'⟩ := hΩ.classical J hJ
  have hz : IsUniqueInvolution J z := hz'.isUniqueInvolution_sl2
  obtain ⟨R, hR⟩ := exists_isSylow2In J
  have hRΩ : R ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hR
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩg hRΩ
  have hzR : z ∈ R := AscL62.mem_of_uniqueInvolution_of_pGroup hz hR.1 hR.2.1 (by omega)
  have hRQ : R ⊓ Q = ⊥ := by
    rw [eq_bot_iff, ← hJQ]
    exact inf_le_inf_right _ hR.1
  have h613 := (l6_13_on hΩ (l6_7On_of_l6_7 l6_7_proved hΩ) R hRΩ ⊤ Q le_top le_top
    (fun y _ => AscQuot.conjSub_eq_of_normal Q y) hRQ).2
  rw [CFSG.ClassicalInvolution.Asc77.AscE186.oddCoreOf_eq_bot_of_isPGroup hQ2, le_bot_iff] at h613
  have hzQ : ∀ q ∈ Q, z * q = q * z := by
    intro q hq
    have hmem : ⁅z, q⁆ ∈ ⁅R, Q⁆ := Subgroup.commutator_mem_commutator hzR hq
    rw [h613, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hQC : Q ≤ Subgroup.centralizer ({z} : Set G) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzQ q hq).symm
  have hJC : J ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hz'.subnormal
  have hsub : IsSubnormal J (J ⊔ Q) := by
    have := isSubnormal_inf hz'.subnormal (J ⊔ Q)
    rwa [inf_eq_left.mpr le_sup_left, inf_eq_right.mpr (sup_le hJC hQC)] at this
  obtain ⟨e⟩ := hz'.nonempty_equiv_sl2Three
    (CFSG.ClassicalInvolution.Uniform.MemberType.isSolvableType_sl2.mpr (by norm_num))
  obtain ⟨π, hπs, hπk⟩ := Q3T7T2.exists_proj e
  have hcl := Q3T7T2.odd_closure_of_proj π hπs hπk
  have hodd : ∀ x ∈ {x : G | x ∈ J ∧ Odd (orderOf x)}, ∀ q ∈ Q, x * q = q * x :=
    fun x hx q hq =>
      centralizes_of_isSubnormal hQ2 (T := {x : G | x ∈ J ∧ Odd (orderOf x)})
        (fun x hx => hx.2) hsub (fun x hx => hx.1)
        (fun x _ q hq => by
          have : q = 1 := Subgroup.mem_bot.mp (hJQ ▸ hq)
          rw [this]
          simp) x hx q ⟨(le_sup_right : Q ≤ J ⊔ Q) hq, hq⟩
  rw [← hcl]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro q hq
  exact (hodd x hx q hq).symm

end NormalTwo

section Restrict

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H Y : Subgroup G}

theorem MinCex.trans_restrict (c : MinCex Ω K S R W H) (hKY : K ≤ Y)
    (hall : ∀ J ∈ restrictFamily Ω Y, ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = J) :
    ∀ J ∈ dstarComp (restrictFamily Ω Y) (K.subgroupOf Y),
      ∃ h ∈ H.subgroupOf Y, conjSub h (K.subgroupOf Y) = J :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.trans_restrict c.toU hKY hall

theorem MinCex.cent_restrict (c : MinCex Ω K S R W H) (hKY : K ≤ Y) :
    CentralizersSylowPairs (restrictFamily Ω Y) (K.subgroupOf Y) (H.subgroupOf Y) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.cent_restrict c.toU hKY

@[expose] def restrictGood (Ω : Set (Subgroup G)) (Y K : Subgroup G) (L : Subgroup ↥Y) : Prop :=
  ∃ J ∈ Ω, J ≤ Y ∧ L = J.subgroupOf Y ∧ J ∈ dstarComp Ω K

theorem restrictGood_step {K : Subgroup G} {L L' : Subgroup ↥Y}
    (hL' : L' ∈ restrictFamily Ω Y) (hgood : restrictGood Ω Y K L)
    (hadj : dstarAdj (restrictFamily Ω Y) L L') : restrictGood Ω Y K L' :=
  CFSG.ClassicalInvolution.T7FU.Asc77.restrictGood_step hL' hgood hadj

theorem MinCex.restrictGood_le_H (c : MinCex Ω K S R W H) {L : Subgroup ↥Y}
    (hgood : restrictGood Ω Y K L) : L.map Y.subtype ≤ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.restrictGood_le_H c.toU hgood

end Restrict

section ExactSection

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G} {w : G}

theorem MinCex.trans_exactFamily (c : MinCex Ω K S R W H) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    (hKm : K ∈ tqMembers3 Ω w)
    (hall : ∀ J ∈ restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w),
      ∃ y : ↥(exactLayer3 Ω w),
        conjSub y ((exactCore3 w K).subgroupOf (exactLayer3 Ω w)) = J) :
    ∀ J ∈ dstarComp (restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w))
        ((exactCore3 w K).subgroupOf (exactLayer3 Ω w)),
      ∃ h ∈ (H.subgroupOf (exactLayer3 Ω w)),
        conjSub h ((exactCore3 w K).subgroupOf (exactLayer3 Ω w)) = J := by
  have hΩ := c.stand.modU
  have hKY : exactCore3 w K ≤ exactLayer3 Ω w := exactCore3_le_exactLayer3 hKm
  intro J hJ
  have hJΛ : J ∈ restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w) := by
    rcases dstarComp_subset_insert _ hJ with h | h
    · rw [h]
      exact subgroupOf_mem_restrictFamily (exactCore3_mem_exactFamily3 hKm) hKY
    · exact h
  obtain ⟨y, rfl⟩ := hall J hJΛ
  refine ⟨y, ?_, rfl⟩
  have hyC : (y : G) ∈ Subgroup.centralizer ({w} : Set G) := exactLayer3_le_centralizer Ω w y.2
  have h1 := dstarComp_map hJ
  rw [Subgroup.map_subgroupOf_eq_of_le hKY] at h1
  have h2 : (conjSub y ((exactCore3 w K).subgroupOf (exactLayer3 Ω w))).map
      (exactLayer3 Ω w).subtype = conjSub (y : G) (exactCore3 w K) := by
    rw [conjSub_subgroupOf (exactLayer3 Ω w) y (exactCore3 w K),
      Subgroup.map_subgroupOf_eq_of_le]
    have := conjSub_mono (n := (y : G)) hKY
    rwa [conjSub_eq_self_of_mem y.2] at this
  have h3 := exactCore3_conjSub (y : G) w K
  rw [conj_eq_of_mem_centralizer_singleton hyC] at h3
  rw [h2, ← h3] at h1
  have h4 := mem_dstarComp_of_dstarComp_exactFamily3 hΩ hc2 hKm h1 _
    (conjSub_mem_tqMembers3 hΩ.conjInvariant hyC hKm) rfl
  exact Subgroup.mem_subgroupOf.mpr ((e18_1 G Ω K S R W H c).1 y h4)

theorem mem_kPerp_of_exactFamily3 (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers w)) {L J : Subgroup G} (hL : L ∈ tqMembers3 Ω w)
    (hJ : J ∈ tqMembers3 Ω w)
    (h : exactCore3 w J ∈ KPerp (exactFamily3 Ω w) (exactCore3 w L)) : J ∈ KPerp Ω L := by
  rcases h with h | h
  · exact Or.inl (eq_of_exactCore3_eq (modU_toGen3 hΩ) hc2 hJ hL h)
  · exact Or.inr (mem_omegaNbr_of_exactFamily3 hΩ hc2 hL hJ h)

theorem exists_of_mem_restrict_exactFamily3 {L : Subgroup ↥(exactLayer3 Ω w)}
    (hL : L ∈ restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w)) :
    ∃ J ∈ tqMembers3 Ω w, L = (exactCore3 w J).subgroupOf (exactLayer3 Ω w) := by
  obtain ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩ := hL
  exact ⟨J, hJ, rfl⟩

theorem MinCex.cent_exactFamily (c : MinCex Ω K S R W H) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    (hKm : K ∈ tqMembers3 Ω w) :
    CentralizersSylowPairs (restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w))
      ((exactCore3 w K).subgroupOf (exactLayer3 Ω w)) (H.subgroupOf (exactLayer3 Ω w)) := by
  have hΩ := c.stand.modU
  have hΩg := c.stand.hypGen
  have hKY : exactCore3 w K ≤ exactLayer3 Ω w := exactCore3_le_exactLayer3 hKm
  intro L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hc a ha ha1 ha2
  obtain ⟨L₀, hL₀, rfl⟩ := exists_of_mem_restrict_exactFamily3 hL.1
  obtain ⟨J₀, hJ₀, rfl⟩ : ∃ J₀ ∈ tqMembers3 Ω w,
      J = (exactCore3 w J₀).subgroupOf (exactLayer3 Ω w) := by
    refine exists_of_mem_restrict_exactFamily3 ?_
    rcases hJ with rfl | h
    · exact hL.1
    · exact h.1
  have hL₀Y : exactCore3 w L₀ ≤ exactLayer3 Ω w := exactCore3_le_exactLayer3 hL₀
  have hJ₀Y : exactCore3 w J₀ ≤ exactLayer3 Ω w := exactCore3_le_exactLayer3 hJ₀
  have hLm := twinSet_map hKY hL
  rw [Subgroup.map_subgroupOf_eq_of_le hL₀Y] at hLm
  have hJm := kPerp_map hJ
  rw [Subgroup.map_subgroupOf_eq_of_le hL₀Y, Subgroup.map_subgroupOf_eq_of_le hJ₀Y] at hJm
  have hLtw : L₀ ∈ twinSet Ω K := mem_twinSet_of_exactCore3 hΩg hKm hL₀ hLm
  have hJperp : J₀ ∈ KPerp Ω L₀ := mem_kPerp_of_exactFamily3 hΩ hc2 hL₀ hJ₀ hJm
  have hR₁Ω : R₁.map (exactLayer3 Ω w).subtype ∈ RSet Ω :=
    mem_RSet_of_mem_RSet_exactFamily3 hc2 (map_mem_RSet_restrict hR₁)
  have hR₂Ω : R₂.map (exactLayer3 Ω w).subtype ∈ RSet Ω :=
    mem_RSet_of_mem_RSet_exactFamily3 hc2 (map_mem_RSet_restrict hR₂)
  have hR₁L₀ : R₁.map (exactLayer3 Ω w).subtype ≤ L₀ := by
    refine (Subgroup.map_mono hR₁L).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hL₀Y]
    exact exactCore3_le_left w L₀
  have hR₂J₀ : R₂.map (exactLayer3 Ω w).subtype ≤ J₀ := by
    refine (Subgroup.map_mono hR₂J).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJ₀Y]
    exact exactCore3_le_left w J₀
  have hcm : Commutes (R₁.map (exactLayer3 Ω w).subtype) (R₂.map (exactLayer3 Ω w).subtype) ∨
      R₂.map (exactLayer3 Ω w).subtype = R₁.map (exactLayer3 Ω w).subtype := by
    rcases hc with hc | rfl
    · left
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hc x hx y hy)
    · right
      rfl
  have haG : (a : G) ∈
      R₁.map (exactLayer3 Ω w).subtype ⊔ R₂.map (exactLayer3 Ω w).subtype := by
    have : (a : G) ∈ (R₁ ⊔ R₂).map (exactLayer3 Ω w).subtype := ⟨a, ha, rfl⟩
    rwa [Subgroup.map_sup] at this
  have hC := c.hyp.cent L₀ hLtw J₀ hJperp _ _ hR₁Ω hR₁L₀ hR₂Ω hR₂J₀ hcm (a : G) haG
    (fun h => ha1 (Subtype.ext h)) (congrArg Subtype.val ha2)
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have : (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hx
  exact Subgroup.mem_subgroupOf.mpr (hC this)

@[expose] def exactGood (Ω : Set (Subgroup G)) (w : G) (K : Subgroup G)
    (L : Subgroup ↥(exactLayer3 Ω w)) : Prop :=
  ∃ J ∈ tqMembers3 Ω w, L = (exactCore3 w J).subgroupOf (exactLayer3 Ω w) ∧
    J ∈ dstarComp Ω K

theorem exactGood_step (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {K : Subgroup G} {L L' : Subgroup ↥(exactLayer3 Ω w)}
    (hL' : L' ∈ restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w))
    (hgood : exactGood Ω w K L)
    (hadj : dstarAdj (restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w)) L L') :
    exactGood Ω w K L' := by
  obtain ⟨J, hJ, rfl, hJK⟩ := hgood
  obtain ⟨J', hJ', rfl⟩ := exists_of_mem_restrict_exactFamily3 hL'
  have h1 := dstarAdj_map hadj
  rw [Subgroup.map_subgroupOf_eq_of_le (exactCore3_le_exactLayer3 hJ),
    Subgroup.map_subgroupOf_eq_of_le (exactCore3_le_exactLayer3 hJ')] at h1
  exact ⟨J', hJ', rfl, hJK.tail (dstarAdj_of_exactFamily3 hΩ hc2 hJ hJ' h1)⟩

theorem MinCex.exactGood_le_H (c : MinCex Ω K S R W H) {L : Subgroup ↥(exactLayer3 Ω w)}
    (hgood : exactGood Ω w K L) : L.map (exactLayer3 Ω w).subtype ≤ H := by
  obtain ⟨J, hJ, rfl, hJK⟩ := hgood
  rw [Subgroup.map_subgroupOf_eq_of_le (exactCore3_le_exactLayer3 hJ)]
  exact (exactCore3_le_left w J).trans (c.le_H_of_mem_dstarComp hJK)

theorem MinCex.e18_4C_inv (c : MinCex Ω K S R W H)
    {K' : Subgroup G} (hK'tw : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K) {R' : Subgroup G}
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) (hw1 : w ≠ 1)
    (hw2 : w * w = 1) (hRw : R ⊔ R' ≤ Subgroup.centralizer ({w} : Set G))
    (hX : Subgroup.centralizer ({w} : Set G) ≠ ⊤)
    (hS : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({w} : Set G))
      (Subgroup.centralizer ({w} : Set G))) : Subgroup.centralizer ({w} : Set G) ≤ H := by
  have hΩ := c.stand.modU
  have hΩg := c.stand.hypGen
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1]
      norm_num)
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩg hK hRR hRK
  have hR'syl : IsSylow2In R' K' := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩg hK'Ω hR' hR'K'
  have hRC : R ≤ Subgroup.centralizer ({w} : Set G) := le_sup_left.trans hRw
  have hR'C : R' ≤ Subgroup.centralizer ({w} : Set G) := le_sup_right.trans hRw
  have hKm : K ∈ tqMembers3 Ω w :=
    ⟨hK, mem_trivialOnQuot_of_le_centralizer3 hΩ hK hRsyl hw1 hw2 hRC⟩
  have hK'm : K' ∈ tqMembers3 Ω w :=
    ⟨hK'Ω, mem_trivialOnQuot_of_le_centralizer3 hΩ hK'Ω hR'syl hw1 hw2 hR'C⟩
  have hYC : exactLayer3 Ω w ≤ Subgroup.centralizer ({w} : Set G) :=
    exactLayer3_le_centralizer Ω w
  have hYtop : exactLayer3 Ω w ≠ ⊤ := fun h => hX (top_le_iff.mp (h ▸ hYC))
  have hKY : exactCore3 w K ≤ exactLayer3 Ω w := exactCore3_le_exactLayer3 hKm
  have hK'Y : exactCore3 w K' ≤ exactLayer3 Ω w := exactCore3_le_exactLayer3 hK'm
  have hRKc : R ≤ exactCore3 w K := le_inf hRK hRC
  have hR'Kc : R' ≤ exactCore3 w K' := le_inf hR'K' hR'C
  have hRY : R ≤ exactLayer3 Ω w := hRKc.trans hKY
  have hR'Y : R' ≤ exactLayer3 Ω w := hR'Kc.trans hK'Y
  have hnorm : Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (exactLayer3 Ω w : Set G) :=
    le_normalizer_exactLayer3 hΩ.conjInvariant
  have hSY : IsSylow2In ((S : Subgroup G) ⊓ exactLayer3 Ω w) (exactLayer3 Ω w) := by
    have := isSylow2In_inf_of_le_normalizer hS hYC hnorm
    rwa [inf_assoc, inf_eq_right.mpr hYC] at this
  have hEA : EtaAbelian Ω := EtaAbelian.of_l6_9 l6_9_proved hΩ
  have hEM : EtaMeet Ω := EtaMeet.of_l6_11 l6_11_proved hΩ
  have hNH : oddCoreOf (exactLayer3 Ω w) ≤ H :=
    c.oddCoreOf_le hEA hEM hK'tw hK'ne hR' hR'K' hR'S (sup_le hRY hR'Y)
  have hΛ : HypOmegaModU (.sl2 3 1) (restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w)) :=
    (exactPair3_eq Ω w) ▸ hypOmegaModU_exactPair3_of_modU hΩ hc2 ⟨K, hKm⟩
  have hgen : exactLayer3 Ω w ≤
      ⨆ L ∈ restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w),
        L.map (exactLayer3 Ω w).subtype := by
    refine iSup₂_le fun L hL => ?_
    have hLY : L ≤ exactLayer3 Ω w := le_centralizingLayer hL
    refine le_iSup₂_of_le (L.subgroupOf (exactLayer3 Ω w))
      (subgroupOf_mem_restrictFamily hL.1 hLY) ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hLY]
  have hK₁' : (exactCore3 w K').subgroupOf (exactLayer3 Ω w) ∈
      twinSet (restrictFamily (exactFamily3 Ω w) (exactLayer3 Ω w))
        ((exactCore3 w K).subgroupOf (exactLayer3 Ω w)) :=
    twinSet_subgroupOf hKY hK'Y (exactCore3_mem_twinSet hΩ hc2 hKm hK'm hK'tw)
  have hne₁ : (exactCore3 w K').subgroupOf (exactLayer3 Ω w) ≠
      (exactCore3 w K).subgroupOf (exactLayer3 Ω w) :=
    subgroupOf_ne_of_ne hKY hK'Y fun h => hK'ne (eq_of_exactCore3_eq hΩg hc2 hK'm hKm h)
  have hYH : exactLayer3 Ω w ≤ H :=
    c.section_le_H hYtop hΛ (AscQuot.sylowOfIsSylow2In' hSY)
      (subgroupOf_mem_restrictFamily (exactCore3_mem_exactFamily3 hKm) hKY) hK₁' hne₁
      (mem_RSet_restrict (exactCore3_mem_exactFamily3 hKm) hKY
        (isSylow2In_exactCore3_of_le_centralizer hc2 hKm.2 hRsyl hRC))
      (Subgroup.subgroupOf_mono _ hRKc)
      (Subgroup.subgroupOf_mono _ (le_inf hRS hRY))
      (mem_RSet_restrict (exactCore3_mem_exactFamily3 hK'm) hK'Y
        (isSylow2In_exactCore3_of_le_centralizer hc2 hK'm.2 hR'syl hR'C))
      (Subgroup.subgroupOf_mono _ hR'Kc)
      (Subgroup.subgroupOf_mono _ (le_inf hR'S hR'Y)) hNH hgen (c.trans_exactFamily hc2 hKm)
      (c.cent_exactFamily hc2 hKm) (exactGood Ω w K) ⟨K, hKm, rfl, Relation.ReflTransGen.refl⟩
      (fun L _ L' hL' hg hadj => exactGood_step hΩ hc2 hL' hg hadj)
      (fun L _ hg => c.exactGood_le_H hg)
      (Q3T7E.thm3SectBelow3_of_ih c.stand.below _ (natCard_lt_of_ne_top hYtop) _ hΛ)
  exact fun x hx => c.normalizer_le_of_le hEA hEM hRY hYH (hnorm hx)

end ExactSection

section Assembly

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem e18_4C3 : E187E4C := by
  intro G _ _ Ω K S R W H c K' hK'tw hK'ne R' hR' hR'K' hR'S A hA hAcyc hRA hX hS
  obtain ⟨w, hw1, hw2, rfl⟩ := hAcyc
  rw [centralizer_zpowers_eq_singleton'] at hRA hX hS ⊢
  exact c.e18_4C_inv hK'tw hK'ne hR' hR'K' hR'S hw1 hw2 hRA hX hS

theorem e18_5_of_layer3 : E18_5 := by
  intro G _ _ Ω K S R W H c
  by_contra hX
  set Y : Subgroup G := ⨆ J ∈ Ω, J with hYdef
  have hΩ := c.stand.hyp
  have hΩg := c.stand.hypGen
  have hEA : EtaAbelian Ω := EtaAbelian.of_l6_9 l6_9_proved hΩ
  have hEM : EtaMeet Ω := EtaMeet.of_l6_11 l6_11_proved hΩ
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hK : K ∈ Ω := c.stand.mem
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hKY : K ≤ Y := le_iSup₂_of_le K hK le_rfl
  have hK'Y : K' ≤ Y := le_iSup₂_of_le K' hK'Ω le_rfl
  have hnorm : Y.Normal := omegaGen_normal hΩ.conjInvariant
  have hYtop : Y ≠ ⊤ := hX
  have hRY : R ≤ Y := hRK.trans hKY
  have hR'Y : R' ≤ Y := hR'K'.trans hK'Y
  have hSY : IsSylow2In ((S : Subgroup G) ⊓ Y) Y := by
    refine isSylow2In_inf_of_le_normalizer ?_ le_top ?_
    · exact ⟨le_top, S.isPGroup', fun V' _ hV'2 hSV' => (S.is_maximal' hV'2 hSV')⟩
    · intro x _
      exact mem_normalizer_iff_conjSub_eq.mpr (AscQuot.conjSub_eq_of_normal _ x)
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩg hK hRR hRK
  have hR'syl : IsSylow2In R' K' := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩg hK'Ω hR' hR'K'
  have hNH : oddCoreOf Y ≤ H :=
    c.oddCoreOf_le hEA hEM hK'tw hK'ne hR' hR'K' hR'S (sup_le hRY hR'Y)
  have hΛ : Q3T7M.HM (restrictFamily Ω Y) := Q3T6.hypOmegaModU_restrict hΩ Y
  have hgen : Y ≤ ⨆ L ∈ restrictFamily Ω Y, L.map Y.subtype := by
    refine iSup₂_le fun J hJ => ?_
    have hJY : J ≤ Y := le_iSup₂_of_le J hJ le_rfl
    refine le_iSup₂_of_le (J.subgroupOf Y) (subgroupOf_mem_restrictFamily hJ hJY) ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJY]
  have hYH : Y ≤ H :=
    c.section_le_H hYtop hΛ (AscQuot.sylowOfIsSylow2In' hSY)
      (subgroupOf_mem_restrictFamily hK hKY) (twinSet_subgroupOf hKY hK'Y hK'tw)
      (subgroupOf_ne_of_ne hKY hK'Y hK'ne)
      (mem_RSet_restrict hK hKY hRsyl) (Subgroup.subgroupOf_mono _ hRK)
      (Subgroup.subgroupOf_mono _ (le_inf hRS hRY))
      (mem_RSet_restrict hK'Ω hK'Y hR'syl) (Subgroup.subgroupOf_mono _ hR'K')
      (Subgroup.subgroupOf_mono _ (le_inf hR'S hR'Y)) hNH hgen (c.trans_restrict hKY)
      (c.cent_restrict hKY) (restrictGood Ω Y K) ⟨K, hK, hKY, rfl, Relation.ReflTransGen.refl⟩
      (fun L _ L' hL' hg hadj => restrictGood_step hL' hg hadj)
      (fun L _ hg => c.restrictGood_le_H hg)
      (Q3T7E.thm3SectBelow3_of_ih c.stand.below _ (natCard_lt_of_ne_top hYtop) _ hΛ)
  obtain ⟨u, huR, hu4⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hRR
  refine c.proper (eq_top_iff.mpr fun g _ => ?_)
  have hle : conjSub g K ≤ Y :=
    le_iSup₂_of_le (conjSub g K) (hΩ.conjInvariant g K hK) le_rfl
  exact c.mem_of_conj_mem hEA hEM (hRK huR) hu4 (hYH (hle (conj_mem_conjSub (hRK huR))))

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
