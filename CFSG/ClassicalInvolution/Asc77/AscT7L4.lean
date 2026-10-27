module

public import CFSG.ClassicalInvolution.Asc77.AscT7L2
public import CFSG.ClassicalInvolution.Asc77.AscT7L6
import CFSG.ClassicalInvolution.Asc77.AscIHSectF
public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE
public import CFSG.ClassicalInvolution.Asc77.AscT7HC4
public import CFSG.ClassicalInvolution.Asc77.AscT7L1
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SExact

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement

namespace T7L

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}


omit [Finite G] in
theorem kPerp_conj_pair (hΩ : ConjInvariant Ω) {K K' : Subgroup G} (h : KPerp Ω K = {K, K'})
    (g : G) : KPerp Ω (conjSub g K) = {conjSub g K, conjSub g K'} := by
  ext J
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hJ
    have h1 := KPerp_conj hΩ hJ g⁻¹
    rw [conjSub_inv_conjSub, h] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h1 | h1
    · left
      rw [← h1, conjSub_conjSub_inv]
    · right
      rw [← h1, conjSub_conjSub_inv]
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · have : K' ∈ KPerp Ω K := by rw [h]; simp
      exact KPerp_conj hΩ this g

variable [IsSimpleGroup G]


theorem layer_u_frame (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∃ (a₂ b₂ v' : G) (ha₂Y : a₂ ∈ exactLayer Ω u) (hb₂Y : b₂ ∈ exactLayer Ω u)
      (hv'Y : v' ∈ exactLayer Ω u) (htY : u * e ∈ exactLayer Ω u),
      (v' = z ∨ v' = u * z) ∧
      GenSection p f (oddQuotientFamily (exactPair Ω u)) ∧
      Nat.card (↥(exactLayer Ω u) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω u)) < Nat.card G ∧
      TwinSect (oddQuotientFamily (exactPair Ω u)) (T7H.exactImg Ω u (conjSub g K))
        (T7H.exactImg Ω u (conjSub g K')) (T7H.toBar Ω u (u * e) htY) (T7H.toBar Ω u a₂ ha₂Y)
        (T7H.toBar Ω u b₂ hb₂Y) (T7H.toBar Ω u v' hv'Y) ∧
      (∀ h ∈ Subgroup.centralizer ({u} : Set G), ∃ B ∈ oddQuotientFamily (exactPair Ω u),
        ∃ hmem : h * (u * e) * h⁻¹ ∈ exactLayer Ω u,
          IsUniqueInvolution B (T7H.toBar Ω u (h * (u * e) * h⁻¹) hmem)) := by
  classical
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hKΩ : K ∈ Ω := hst.mem
  have hzK : IsUniqueInvolution K z := hs.hz
  have hcpg : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨R₂, R₂', a₂, b₂, v', hK₂, hK₂', hS₂, hS₂', hcomm₂, ha₂, hb₂, ha₂sq, hb₂sq, hv'def,
    hzv'⟩ := exists_uFrame hs hd
  obtain ⟨hKnt, hK'nt⟩ := not_mem_tqMembers_u hs hd
  have hzK₂ : IsUniqueInvolution (conjSub g K) (u * e) := by
    have := hzK.conj g
    rwa [hd.hgt] at this
  have hzK₂' : IsUniqueInvolution (conjSub g K') (u * e) := by
    have := (isUniqueInvolution_of_mem_twinSet hs.hz hs.hK').conj g
    rwa [hd.hgt] at this
  have hperp₂ : KPerp Ω (conjSub g K) = {conjSub g K, conjSub g K'} :=
    kPerp_conj_pair hΩ.conjInvariant hs.perp g
  have hperp' : KPerp Ω K' = {K', K} := by rw [hs.perp_of_twin hs.hK', Set.pair_comm]
  have hperp₂' : KPerp Ω (conjSub g K') = {conjSub g K', conjSub g K} :=
    kPerp_conj_pair hΩ.conjInvariant hperp' g
  set Y := exactLayer Ω u with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f (exactPair Ω u) := hypOmegaMod_exactPair hp hq hΩ hcpg
  have hΦ : HypOmegaMod p f (oddQuotientFamily (exactPair Ω u)) :=
    oddQuotHyp p f hp hq ↥Y (exactPair Ω u) hΛ N₀ hN₀odd
  have ht₂ : u * e ∈ exactCore u (conjSub g K) :=
    (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hK₂ hzK₂).mem
  have htY : u * e ∈ Y := exactCore_le_exactLayer hK₂ ht₂
  have ha₂c : a₂ ∈ exactCore u (conjSub g K) := hS₂.1 ha₂
  have hb₂c : b₂ ∈ exactCore u (conjSub g K') := hS₂'.1 hb₂
  have ha₂Y : a₂ ∈ Y := exactCore_le_exactLayer hK₂ ha₂c
  have hb₂Y : b₂ ∈ Y := exactCore_le_exactLayer hK₂' hb₂c
  have hv'Y : v' ∈ Y := by
    rcases hv'def with h | h
    · rw [h]
      exact Y.mul_mem ha₂Y hb₂Y
    · rw [h]
      exact Y.mul_mem (Y.mul_mem ha₂Y hb₂Y) htY
  have hzu : z * u = u * z := (T7K.comm_uz hs hd).symm
  have hzv : ∀ y ∈ Y, z * y * z⁻¹ = v' * y * v'⁻¹ := by
    intro y hy
    rcases hzv' with h | h
    · rw [h]
    · have hw : v' * y * v'⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hv'Y hy) (Y.inv_mem hv'Y)
      have hcw : (v' * y * v'⁻¹) * u = u * (v' * y * v'⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω u hw)
      rw [h]
      calc u * v' * y * (u * v')⁻¹ = u * (v' * y * v'⁻¹) * u⁻¹ := by group
        _ = v' * y * v'⁻¹ := by rw [← hcw]; group
  have hA : T7H.exactImg Ω u (conjSub g K) ∈ oddQuotientFamily (exactPair Ω u) :=
    T7H.exactImg_mem hK₂
  have hA' : T7H.exactImg Ω u (conjSub g K') ∈ oddQuotientFamily (exactPair Ω u) :=
    T7H.exactImg_mem hK₂'
  have hzA := T7H.exactImg_isUnique hp hΩ hcpg hK₂ hzK₂ htY
  have hzA' := T7H.exactImg_isUnique hp hΩ hcpg hK₂' hzK₂' htY
  have hne : T7H.exactImg Ω u (conjSub g K) ≠ T7H.exactImg Ω u (conjSub g K') := by
    refine map_ne_of_commutes_sylow (N := N₀) hp hΦ hN₀odd
      (M₁ := (exactCore u (conjSub g K)).subgroupOf Y)
      (M₂ := (exactCore u (conjSub g K')).subgroupOf Y)
      (V₁ := R₂.subgroupOf Y) (V₂ := R₂'.subgroupOf Y)
      ⟨_, exactCore_mem_exactFamily hK₂, exactCore_le_exactLayer hK₂, rfl⟩
      (hS₂.subgroupOf (exactCore_le_exactLayer hK₂))
      (hS₂'.subgroupOf (exactCore_le_exactLayer hK₂')) ?_
    intro x hx y hy
    exact Subtype.ext (hcomm₂ x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hnbA : ∀ M ∈ oddQuotientFamily (exactPair Ω u),
      M ∈ omegaNbr (oddQuotientFamily (exactPair Ω u)) (T7H.exactImg Ω u (conjSub g K)) →
        M = T7H.exactImg Ω u (conjSub g K') := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := T7H.exists_exactImg_of_mem hM
    exact T7H.exactImg_nbr_eq hp hq hΩ hcpg hK₂ hperp₂ hJ hMn
  have hnbA' : ∀ M ∈ oddQuotientFamily (exactPair Ω u),
      M ∈ omegaNbr (oddQuotientFamily (exactPair Ω u)) (T7H.exactImg Ω u (conjSub g K')) →
        M = T7H.exactImg Ω u (conjSub g K) := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := T7H.exists_exactImg_of_mem hM
    exact T7H.exactImg_nbr_eq hp hq hΩ hcpg hK₂' hperp₂' hJ hMn
  have hgen : omegaGen (oddQuotientFamily (exactPair Ω u)) = ⊤ :=
    omegaGen_quotFamily_eq_top (exactPair Ω u) N₀
      (omegaGen_restrictFamily_eq_top (exactFamily Ω u) Y (exactLayer_eq_iSup Ω u).symm)
  have hAΩ : ∀ M ∈ Ω, AEmpty Ω M := hst.aEmpty
  have hAΛ : ∀ L ∈ exactPair Ω u, AEmpty (exactPair Ω u) L := by
    have h0 := aEmpty_exactPair hp hq hΩ hAΩ hcpg
    have e0 : centralizingMembers (exactFamily Ω u) {u} = exactFamily Ω u :=
      centMembers_exactFamily Ω u
    rw [e0] at h0
    exact h0
  have hAΦ : ∀ L ∈ oddQuotientFamily (exactPair Ω u),
      AEmpty (oddQuotientFamily (exactPair Ω u)) L :=
    aEmpty_quotFamily hp hq hΛ hΦ hN₀odd hAΛ
  have hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨z₀, hz₀⟩ := hΩ.classical K hKΩ
    obtain ⟨x, -, y, -, hxy⟩ := ih8_exists_noncomm hz₀
    have hucen : u ∈ Subgroup.center G := hsub (Set.mem_singleton u)
    exact hd.hu1 (T7B.eq_one_of_central ⟨x, y, hxy⟩
      (fun g' => Subgroup.mem_center_iff.mp hucen g'))
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    have h2 : Nat.card ↥Y < Nat.card G := card_exactLayer_lt hnc
    omega
  have haB : T7H.toBar Ω u a₂ ha₂Y ∈ T7H.exactImg Ω u (conjSub g K) := T7H.mem_exactImg ha₂c ha₂Y
  have hbB : T7H.toBar Ω u b₂ hb₂Y ∈ T7H.exactImg Ω u (conjSub g K') :=
    T7H.mem_exactImg hb₂c hb₂Y
  have haBsq : T7H.toBar Ω u a₂ ha₂Y * T7H.toBar Ω u a₂ ha₂Y = T7H.toBar Ω u (u * e) htY := by
    have h1 : (⟨a₂, ha₂Y⟩ : ↥Y) * ⟨a₂, ha₂Y⟩ = ⟨u * e, htY⟩ := Subtype.ext ha₂sq
    unfold T7H.toBar
    rw [← map_mul, h1]
  have hbBsq : T7H.toBar Ω u b₂ hb₂Y * T7H.toBar Ω u b₂ hb₂Y = T7H.toBar Ω u (u * e) htY := by
    have h1 : (⟨b₂, hb₂Y⟩ : ↥Y) * ⟨b₂, hb₂Y⟩ = ⟨u * e, htY⟩ := Subtype.ext hb₂sq
    unfold T7H.toBar
    rw [← map_mul, h1]
  have hzB2 : T7H.toBar Ω u (u * e) htY * T7H.toBar Ω u (u * e) htY = 1 := hzA.sq
  have hainv : (T7H.toBar Ω u a₂ ha₂Y)⁻¹ =
      T7H.toBar Ω u a₂ ha₂Y * T7H.toBar Ω u (u * e) htY := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc T7H.toBar Ω u a₂ ha₂Y * (T7H.toBar Ω u a₂ ha₂Y * T7H.toBar Ω u (u * e) htY)
        = (T7H.toBar Ω u a₂ ha₂Y * T7H.toBar Ω u a₂ ha₂Y) * T7H.toBar Ω u (u * e) htY := by
          rw [mul_assoc]
      _ = 1 := by rw [haBsq, hzB2]
  have hw : T7H.toBar Ω u v' hv'Y = T7H.toBar Ω u a₂ ha₂Y * T7H.toBar Ω u b₂ hb₂Y ∨
      T7H.toBar Ω u v' hv'Y = (T7H.toBar Ω u a₂ ha₂Y)⁻¹ * T7H.toBar Ω u b₂ hb₂Y := by
    rcases hv'def with h | h
    · left
      subst h
      exact T7H.toBar_mul ha₂Y hb₂Y
    · right
      subst h
      have h1 := T7H.toBar_mul (Y.mul_mem ha₂Y hb₂Y) htY
      have h2 := T7H.toBar_mul ha₂Y hb₂Y
      rw [h1, h2, hainv]
      have hc : T7H.toBar Ω u (u * e) htY * T7H.toBar Ω u b₂ hb₂Y =
          T7H.toBar Ω u b₂ hb₂Y * T7H.toBar Ω u (u * e) htY :=
        hzA'.commute_of_mem hbB
      calc T7H.toBar Ω u a₂ ha₂Y * T7H.toBar Ω u b₂ hb₂Y * T7H.toBar Ω u (u * e) htY
          = T7H.toBar Ω u a₂ ha₂Y * (T7H.toBar Ω u b₂ hb₂Y * T7H.toBar Ω u (u * e) htY) := by
            rw [mul_assoc]
        _ = T7H.toBar Ω u a₂ ha₂Y * (T7H.toBar Ω u (u * e) htY * T7H.toBar Ω u b₂ hb₂Y) := by
            rw [hc]
        _ = T7H.toBar Ω u a₂ ha₂Y * T7H.toBar Ω u (u * e) htY * T7H.toBar Ω u b₂ hb₂Y := by
            rw [mul_assoc]
  have hF : ∀ L ∈ oddQuotientFamily (exactPair Ω u),
      ∃ m ∈ L, T7H.toBar Ω u v' hv'Y * m ≠ m * T7H.toBar Ω u v' hv'Y := by
    intro L hL
    obtain ⟨J, hJ, rfl⟩ := T7H.exists_exactImg_of_mem hL
    obtain ⟨m, hm, hmn⟩ := no_member_commutes hp hq hΩ hKΩ hzK hs.perp hKnt hK'nt hd.hu2 hzu
      hzv hJ
    have hmY : m ∈ Y := exactCore_le_exactLayer hJ hm
    refine ⟨T7H.toBar Ω u m hmY, T7H.mem_exactImg hm hmY, fun h => hmn ?_⟩
    have h1 : (⟨v', hv'Y⟩ : ↥Y) * ⟨m, hmY⟩ * ((⟨m, hmY⟩ : ↥Y) * ⟨v', hv'Y⟩)⁻¹ ∈ N₀ := by
      have h2 : QuotientGroup.mk' N₀
          ((⟨v', hv'Y⟩ : ↥Y) * ⟨m, hmY⟩ * ((⟨m, hmY⟩ : ↥Y) * ⟨v', hv'Y⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul]
        exact mul_inv_eq_one.mpr h
      exact (QuotientGroup.eq_one_iff _).mp h2
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp [commutatorElement_def, mul_assoc]⟩
  have hv'z : v' = z ∨ v' = u * z := by
    rcases hzv' with h | h
    · exact Or.inl h.symm
    · right
      rw [h, ← mul_assoc, hd.hu2, one_mul]
  have hconj : ∀ h ∈ Subgroup.centralizer ({u} : Set G), ∃ B ∈ oddQuotientFamily (exactPair Ω u),
      ∃ hmem : h * (u * e) * h⁻¹ ∈ exactLayer Ω u,
        IsUniqueInvolution B (T7H.toBar Ω u (h * (u * e) * h⁻¹) hmem) := by
    intro h hh
    have hY' : conjSub h (exactLayer Ω u) = exactLayer Ω u :=
      conjSub_exactLayer hΩ.conjInvariant hh
    have hmem : h * (u * e) * h⁻¹ ∈ exactLayer Ω u := by
      have := conj_mem_conjSub (n := h) htY
      rwa [hY'] at this
    have hK₂h : conjSub h (conjSub g K) ∈ tqMembers Ω u :=
      conjSub_mem_tqMembers hΩ.conjInvariant hh hK₂
    have hzh : IsUniqueInvolution (conjSub h (conjSub g K)) (h * (u * e) * h⁻¹) := hzK₂.conj h
    exact ⟨T7H.exactImg Ω u (conjSub h (conjSub g K)), T7H.exactImg_mem hK₂h, hmem,
      T7H.exactImg_isUnique hp hΩ hcpg hK₂h hzh hmem⟩
  exact ⟨a₂, b₂, v', ha₂Y, hb₂Y, hv'Y, htY, hv'z,
    ⟨hΦ, CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y, hgen, hAΦ⟩, hlt,
    ⟨hA, hA', hne, hzA, hzA', haB, hbB, haBsq, hbBsq, hw, hF, hnbA, hnbA'⟩, hconj⟩

theorem layer_u_tag (htcf : TwinCentralFact p) (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) :
    u * e ∈ zStarOf (exactLayer Ω u) ∨ LayerOrthType p f Ω u 5 true ∨
      LayerOrthType p f Ω u 6 (!piSign p f) := by
  classical
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hBelow : CITBelowU p f (Nat.card G) := hst.below f hq
  obtain ⟨a₂, b₂, v', ha₂Y, hb₂Y, hv'Y, htY, -, hS, hlt, T, -⟩ := layer_u_frame hs hd
  rcases twinSection_cases htcf hp hq hBelow hlt hS T with hconn | ⟨D, hcard, i, hE4⟩
  · left
    exact Subgroup.mem_map.mpr ⟨⟨u * e, htY⟩, twinSection_central T.hzA T.hzA' hconn hS.gen, rfl⟩
  · right
    rcases hE4 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inl ⟨rfl, h1, h2⟩, D, hcard, i, rfl, rfl⟩
    · right
      have hπ : piSign p f = false := by
        unfold piSign
        simp [h3]
      rw [hπ]
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩), D, hcard, i, rfl, rfl⟩
    · right
      have hπ : piSign p f = true := by
        unfold piSign
        simp [h3]
      rw [hπ]
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩)), D, hcard, i, rfl, rfl⟩

end T7L

end CFSG.ClassicalInvolution.Asc77
