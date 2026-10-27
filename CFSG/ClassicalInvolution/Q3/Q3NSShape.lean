module

public import CFSG.ClassicalInvolution.Q3.Q3NLCtx
public import CFSG.ClassicalInvolution.Q3.Q3NSModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3NL


section Shapes

variable {G : Type} [Group G]

@[expose] def ChainShape3 (K : Subgroup G) (z : G) : Prop :=
  ∃ (t : StatedLieTag) (n : ℕ), (t = .PSL ∨ t = .PSU) ∧ (n = 3 ∨ n = 4) ∧
    Q3W.LocalShapeC3 1 (CompData.model t n) (conjClass3 K) z

@[expose] def TwinShape3 (K : Subgroup G) (z : G) : Prop :=
  (∃ (t : StatedLieTag) (n : ℕ), ListedTwin3 t n ∧
    Q3W.LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z) ∧
  ∃ T ∈ conjClass3 K, Commutes K T ∧ IsClassicalMember3 T z

@[expose] def NTShape3 (K : Subgroup G) (z : G) : Prop :=
  ChainShape3 K z ∨ TwinShape3 K z

end Shapes

section Residuals

structure FuzzyPair3 {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G)
    (N₁ N₂ : Subgroup G) (n₁ n₂ : G) : Prop where
  mem₁ : N₁ ∈ centralizingMembers (conjClass3 K) {z}
  mem₂ : N₂ ∈ centralizingMembers (conjClass3 K) {z}
  cls₁ : IsClassicalMember3 N₁ n₁
  cls₂ : IsClassicalMember3 N₂ n₂
  commute : Commutes (locImg (conjClass3 K) z N₁) (locImg (conjClass3 K) z N₂)
  indep : IndepModOdd (conjClass3 K) z n₁ n₂

@[expose] def NTNoCommImages3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTHyps3 K z →
    ∀ (N₁ N₂ : Subgroup G) (n₁ n₂ : G), FuzzyPair3 K z N₁ N₂ n₁ n₂ → False

@[expose] def NTFuzzyTriple3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTCommon3 K z →
    ∀ (N₁ N₂ : Subgroup G) (n₁ n₂ : G), FuzzyPair3 K z N₁ N₂ n₁ n₂ → IndepTriple3 (conjClass3 K)

theorem ntNoCommImages3_of_fuzzyTriple3 (h : NTFuzzyTriple3) : NTNoCommImages3 :=
  fun G _ _ _ K z hyps N₁ N₂ n₁ n₂ hp => hyps.noTriple (h G K z hyps.common N₁ N₂ n₁ n₂ hp)

@[expose] def NTTwinsCommute3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTHyps3 K z →
    ∀ T : Subgroup G, T ∈ centralizingMembers (conjClass3 K) {z} → IsClassicalMember3 T z →
      Commutes (locImg (conjClass3 K) z K) (locImg (conjClass3 K) z T) → Commutes K T

@[expose] def NTShapeExcluded3 (S : ℕ → CompData → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTHyps3 K z →
    ∀ (a : ℕ) (c : CompData), S a c → ¬ Q3W.LocalShapeC3 a c (conjClass3 K) z

@[expose] def NTNoAllA1_3 : Prop := NTShapeExcluded3 fun _ c => c = CompData.sl23

@[expose] def NTNoM11_3 : Prop := NTShapeExcluded3 fun _ c => c = CompData.m11

@[expose] def NTNoG2D4_3 : Prop :=
  NTShapeExcluded3 fun _ c => ∃ (t : StatedLieTag) (n : ℕ), (t = .G2 ∨ t = .trialityD4) ∧
    c = CompData.model t n

@[expose] def NTNoM3Twin_3 : Prop :=
  NTShapeExcluded3 fun a c => 2 ≤ a ∧ ∃ (t : StatedLieTag) (n : ℕ), (t = .PSL ∨ t = .PSU) ∧
    n = 3 ∧ c = CompData.model t n

@[expose] def NTNoSmallSingle_3 : Prop :=
  NTShapeExcluded3 fun a c => a = 1 ∧ ∃ (t : StatedLieTag) (n : ℕ), ((t = .PSp ∧ n = 2) ∨
    (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaPlus ∧ n = 4) ∨ (t = .POmegaMinus ∧ n = 4)) ∧
    c = CompData.model t n

@[expose] def NTNoManyTwins_3 : Prop :=
  NTShapeExcluded3 fun a c => 3 ≤ a ∧ ∃ (t : StatedLieTag) (n : ℕ), ListedTwin3 t n ∧
    c = CompData.model t n

structure NTResiduals3 : Prop where
  commImages : NTNoCommImages3
  twinsCommute : NTTwinsCommute3
  noAllA1 : NTNoAllA1_3
  noM11 : NTNoM11_3
  noG2D4 : NTNoG2D4_3
  noM3Twin : NTNoM3Twin_3
  noSmallSingle : NTNoSmallSingle_3
  noManyTwins : NTNoManyTwins_3

end Residuals

section Analysis

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {ι : Type} (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z))

theorem locImg_le_range_of_corr {i : ι} {N : Subgroup G} {R : Subgroup (D.kind i).G}
    (hc : Q3W.Corr3 (conjClass3 K) z D i N R) : locImg (conjClass3 K) z N ≤ (D.hom i).range := by
  obtain ⟨-, -, hNR⟩ := hc
  rw [hNR]
  exact Subgroup.map_le_range _ _

theorem locElt_ne_central_of_nonA1 (hMFZ : RouteD.Gaps.FundNoncentral 3) {i : ι}
    (hi : D.kind i ≠ CompData.sl23) {N : Subgroup G} {R : Subgroup (D.kind i).G}
    (hc : Q3W.Corr3 (conjClass3 K) z D i N R) {n : G} (hn : IsClassicalMember3 N n)
    {zb : locQuot (conjClass3 K) z} (hzb : ∀ w, w * zb = zb * w) :
    locElt (conjClass3 K) z n (mem_locLayer_of_member hc.1 hn) ≠ zb := by
  obtain ⟨y, hy⟩ := exists_noncommute_of_nonA1 D hMFZ hi hc hn
  intro e
  apply hy
  rw [e]
  exact (hzb _).symm

theorem locElt_mul_self {Ω : Set (Subgroup G)} {x n : G} (hn : n ∈ locLayer Ω x)
    (h : n * n = 1) : locElt Ω x n hn * locElt Ω x n hn = 1 := by
  rw [locElt_mul hn hn]
  have h1 : (⟨n * n, (locLayer Ω x).mul_mem hn hn⟩ : ↥(locLayer Ω x)) = 1 := Subtype.ext h
  unfold locElt
  rw [h1]
  exact map_one _

theorem eq_of_nonA1 (hB : NTNoCommImages3) (h : NTHyps3 K z) {j k : ι}
    (hj : D.kind j ≠ CompData.sl23) (hk : D.kind k ≠ CompData.sl23) : j = k := by
  by_contra hjk
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hΩ := h.common.inClass
  have hz := h.common.mem_locLayer
  obtain ⟨N, R, hc⟩ := exists_corr_of_meets D j
  obtain ⟨M, S, hd⟩ := exists_corr_of_meets D k
  obtain ⟨n, hn⟩ := hΩ.classical N hc.1.1
  obtain ⟨m, hm⟩ := hΩ.classical M hd.1.1
  have hzc := locElt_self_central (Ω := conjClass3 K) (z := z) hz
  have h1 := indep_images_of_nonA1 D hMFZ hjk hj hc hn hd.1 (locImg_le_range_of_corr D hd) hm hzc
  have h2 := indep_images_of_nonA1 D hMFZ (Ne.symm hjk) hk hd hm hc.1
    (locImg_le_range_of_corr D hc) hn hzc
  exact hB G K z h N M n m ⟨hc.1, hd.1, hn, hm,
    commutes_locImg_of_ne D hjk (locImg_le_range_of_corr D hc) (locImg_le_range_of_corr D hd),
    indepModOdd_of_images _ _ hz h1.1 h2.1 h1.2.1 h1.2.2⟩

theorem eq_involution_of_twin (hB : NTNoCommImages3) (h : NTHyps3 K z) {j k : ι} (hjk : j ≠ k)
    (hj : D.kind j ≠ CompData.sl23) {M : Subgroup G}
    (hM : M ∈ centralizingMembers (conjClass3 K) {z})
    (hMk : locImg (conjClass3 K) z M ≤ (D.hom k).range) {m : G} (hm : IsClassicalMember3 M m) :
    m = z := by
  by_contra hmz
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hΩ := h.common.inClass
  have hz := h.common.mem_locLayer
  have hzc := locElt_self_central (Ω := conjClass3 K) (z := z) hz
  have hne : locElt (conjClass3 K) z m (mem_locLayer_of_member hM hm) ≠
      locElt (conjClass3 K) z z hz := fun e =>
    hmz (eq_of_locElt_eq (mem_locLayer_of_member hM hm) hz (mul_self_eq_one_of_member hm)
      (mul_self_eq_one_of_member h.common.cls) (mul_comm_of_member hM hm) e)
  obtain ⟨N, R, hc⟩ := exists_corr_of_meets D j
  obtain ⟨n, hn⟩ := hΩ.classical N hc.1.1
  have h1 := indep_images_of_nonA1 D hMFZ hjk hj hc hn hM hMk hm hzc
  exact hB G K z h N M n m ⟨hc.1, hM, hn, hm,
    commutes_locImg_of_ne D hjk (locImg_le_range_of_corr D hc) hMk,
    indepModOdd_of_images _ _ hz h1.1 hne h1.2.1 h1.2.2⟩

theorem false_of_connected (hB : NTNoCommImages3) (h : NTHyps3 K z) {j : ι}
    (hj : D.kind j ≠ CompData.sl23) {t : StatedLieTag} {n : ℕ} (hk : D.kind j = CompData.model t n)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hconn : CommFamilyConnected (ModelFund 3 t n 1)) : False := by
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hΩ := h.common.inClass
  have hz := h.common.mem_locLayer
  have hsc := singleClass_of_eq_model hk hfund hadm hG2 hD4
  have hconn' := commFamilyConnected_of_eq_model hk hconn
  obtain ⟨M₀, R₀, hc₀⟩ := exists_corr_of_meets D j
  have hzc := locElt_self_central (Ω := conjClass3 K) (z := z) hz
  obtain ⟨R, hR, S, hS, hRS, key⟩ := exists_pair_indep_images hk hfund hadm hG2 hD4
    (not_psl_two_of_admissible hadm) hconn' hc₀.2.1 (D.hom j) (D.ker_le_center j)
    (zb := locElt (conjClass3 K) z z hz) (fun y => hzc (D.hom j y))
  obtain ⟨N₁, hc₁⟩ := Q3W.exists_corr_right3 hΩ D hsc hR
  obtain ⟨N₂, hc₂⟩ := Q3W.exists_corr_right3 hΩ D hsc hS
  obtain ⟨n₁, hn₁⟩ := hΩ.classical N₁ hc₁.1.1
  obtain ⟨n₂, hn₂⟩ := hΩ.classical N₂ hc₂.1.1
  obtain ⟨r, hrR, hr⟩ := exists_hom_elt_of_corr D hc₁ hn₁.mem
  obtain ⟨s, hsS, hs⟩ := exists_hom_elt_of_corr D hc₂ hn₂.mem
  have hsq₁ : D.hom j r * D.hom j r = 1 := by
    rw [hr]
    exact locElt_mul_self _ (mul_self_eq_one_of_member hn₁)
  have hsq₂ : D.hom j s * D.hom j s = 1 := by
    rw [hs]
    exact locElt_mul_self _ (mul_self_eq_one_of_member hn₂)
  have hne₁ : D.hom j r ≠ 1 := by
    rw [hr]
    intro e
    have h2 := orderOf_locElt_of_member hc₁.1 hn₁
    rw [e, orderOf_one] at h2
    omega
  have hne₂ : D.hom j s ≠ 1 := by
    rw [hs]
    intro e
    have h2 := orderOf_locElt_of_member hc₂.1 hn₂
    rw [e, orderOf_one] at h2
    omega
  obtain ⟨hrs, hrs'⟩ := key r hrR s hsS hsq₁ hsq₂ hne₁ hne₂
  rw [hr, hs] at hrs hrs'
  have ha := locElt_ne_central_of_nonA1 D hMFZ hj hc₁ hn₁ hzc
  have hb := locElt_ne_central_of_nonA1 D hMFZ hj hc₂ hn₂ hzc
  have hcomm : Commutes (locImg (conjClass3 K) z N₁) (locImg (conjClass3 K) z N₂) := by
    have h3 := commutes_map_of_commutes (D.hom j) hRS
    rw [← hc₁.2.2, ← hc₂.2.2] at h3
    exact h3
  exact hB G K z h N₁ N₂ n₁ n₂ ⟨hc₁.1, hc₂.1, hn₁, hn₂, hcomm,
    indepModOdd_of_images _ _ hz ha hb hrs hrs'⟩

theorem localShape_of_unique [Finite ι] {j : ι}
    (huniq : ∀ k, k ≠ j → D.kind k = CompData.sl23) :
    Q3W.LocalShapeC3 (Nat.card ι - 1) (D.kind j) (conjClass3 K) z := by
  have : Nonempty ι := ⟨j⟩
  exact ⟨ι, inferInstance, D, by have := Nat.card_pos (α := ι); omega, j, rfl, huniq⟩

end Analysis

theorem localShapeC3_congr {G : Type} [Group G] {a a' : ℕ} {c c' : CompData}
    {Ω : Set (Subgroup G)} {x : G} (ha : a = a') (hc : c = c')
    (h : Q3W.LocalShapeC3 a c Ω x) : Q3W.LocalShapeC3 a' c' Ω x := by
  subst ha hc
  exact h


section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem ntShape3_of_residuals (res : NTResiduals3) (h : NTHyps3 K z) : NTShape3 K z := by
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hΩ := h.common.inClass
  obtain ⟨ι, hι, ⟨D⟩⟩ := h.common.lieSystems {z} h.common.not_subset_center
  obtain ⟨i₀, hi₀, hKi₀⟩ := exists_kind_eq_sl23 hMFZ D h.common.mem_centralizingMembers
    h.common.cls
  have hFin : Finite ι := hι
  have hNe : Nonempty ι := ⟨i₀⟩
  by_cases hex : ∃ j, D.kind j ≠ CompData.sl23
  swap
  · push Not at hex
    exact (res.noAllA1 G K z h (Nat.card ι - 1) CompData.sl23 rfl
      (localShapeC3_congr rfl (hi₀ : D.kind i₀ = CompData.sl23)
        (localShape_of_unique D (j := i₀) fun k _ => hex k))).elim
  obtain ⟨j, hj⟩ := hex
  have hne : i₀ ≠ j := fun e => hj (e ▸ hi₀)
  have hcard : 2 ≤ Nat.card ι := by
    have : Nontrivial ι := ⟨⟨i₀, j, hne⟩⟩
    have := Finite.one_lt_card (α := ι)
    omega
  have huniq : ∀ k, k ≠ j → D.kind k = CompData.sl23 := fun k hkj => by
    by_contra hk
    exact hkj (eq_of_nonA1 D res.commImages h hk hj)
  have hshape := localShape_of_unique D huniq
  rcases D.valid j with ⟨t, n, hfund, hadm, hk⟩ | hsl | hm11
  swap
  · exact (hj hsl).elim
  swap
  · exact (res.noM11 G K z h (Nat.card ι - 1) (D.kind j) hm11 hshape).elim
  by_cases hg : t = .G2 ∨ t = .trialityD4
  · exact (res.noG2D4 G K z h (Nat.card ι - 1) (D.kind j) ⟨t, n, hg, hk⟩ hshape).elim
  push Not at hg
  obtain ⟨hG2, hD4⟩ := hg
  have hnA1 := not_psl_two_of_admissible hadm
  rcases tag_cases3 hfund hadm hG2 hD4 hnA1 with hconn | hm3 | htw
  · exact (false_of_connected D res.commImages h hj hk hfund hadm hG2 hD4 hconn).elim
  · have ha : Nat.card ι - 1 < 2 := by
      by_contra hcon
      exact res.noM3Twin G K z h (Nat.card ι - 1) (D.kind j)
        ⟨by omega, t, n, hm3.1, hm3.2, hk⟩ hshape
    have ha1 : Nat.card ι - 1 = 1 := by omega
    exact Or.inl ⟨t, n, hm3.1, Or.inl hm3.2, localShapeC3_congr ha1 hk hshape⟩
  · have ha : Nat.card ι - 1 < 3 := by
      by_contra hcon
      exact res.noManyTwins G K z h (Nat.card ι - 1) (D.kind j)
        ⟨by omega, t, n, htw, hk⟩ hshape
    have hcases : Nat.card ι - 1 = 1 ∨ Nat.card ι - 1 = 2 := by omega
    rcases hcases with ha1 | ha2
    · by_cases hch : (t = .PSL ∨ t = .PSU) ∧ n = 4
      · exact Or.inl ⟨t, n, hch.1, Or.inr hch.2, localShapeC3_congr ha1 hk hshape⟩
      · exfalso
        have hsmall : (t = .PSp ∧ n = 2) ∨ (t = .POmegaOdd ∧ n = 3) ∨
            (t = .POmegaPlus ∧ n = 4) ∨ (t = .POmegaMinus ∧ n = 4) := by
          rcases htw with h1 | h1 | h1 | h1 | h1 | h1
          · exact Or.inl h1
          · exact absurd ⟨Or.inl h1.1, h1.2⟩ hch
          · exact absurd ⟨Or.inr h1.1, h1.2⟩ hch
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl h1))
          · exact Or.inr (Or.inr (Or.inr h1))
        exact res.noSmallSingle G K z h (Nat.card ι - 1) (D.kind j) ⟨ha1, t, n, hsmall, hk⟩ hshape
    · refine Or.inr ⟨⟨t, n, htw, localShapeC3_congr ha2 hk hshape⟩, ?_⟩
      obtain ⟨k, hki, hkj⟩ : ∃ k, k ≠ i₀ ∧ k ≠ j := by
        by_contra hcon
        push Not at hcon
        have hle : Nat.card ι ≤ 2 := by
          classical
          have := Fintype.ofFinite ι
          rw [Nat.card_eq_fintype_card]
          calc Fintype.card ι = (Finset.univ : Finset ι).card := Finset.card_univ.symm
            _ ≤ ({i₀, j} : Finset ι).card := by
              apply Finset.card_le_card
              intro k _
              by_cases hk0 : k = i₀
              · simp [hk0]
              · simp [hcon k hk0]
            _ ≤ 2 := Finset.card_le_two
        omega
      obtain ⟨M, S, hd⟩ := exists_corr_of_meets D k
      obtain ⟨m, hm⟩ := hΩ.classical M hd.1.1
      have hmz : m = z := eq_involution_of_twin D res.commImages h (Ne.symm hkj) hj hd.1
        (locImg_le_range_of_corr D hd) hm
      rw [hmz] at hm
      have hcomm : Commutes (locImg (conjClass3 K) z K) (locImg (conjClass3 K) z M) :=
        commutes_locImg_of_ne D (Ne.symm hki) (le_of_eq hKi₀) (locImg_le_range_of_corr D hd)
      exact ⟨M, hd.1.1, res.twinsCommute G K z h M hd.1 hm hcomm, hm⟩

theorem ntShape3_cover (res : NTResiduals3) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
        3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
        BootData3 (conjClass3 K) → ¬ IndepTriple3 (conjClass3 K) → NTShape3 K z :=
  fun _ _ _ _ hnab _ _ hz hBelow h3 h4 hΔ hB hT =>
    ntShape3_of_residuals res ⟨⟨hnab, hz, hBelow, h3, h4, hΔ⟩, hB, hT⟩

end Main

end CFSG.ClassicalInvolution.Q3.Q3NS
