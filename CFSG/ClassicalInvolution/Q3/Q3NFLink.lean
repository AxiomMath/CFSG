module

public import CFSG.ClassicalInvolution.Q3.Q3KCLink
public import CFSG.ClassicalInvolution.Q3.Q3NFClosure
public import CFSG.ClassicalInvolution.Q3.Q3NFPair
public import CFSG.ClassicalInvolution.Q3.Q3YAbs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3KC CFSG.Assembly.LowTwoRank


section Conj

variable {G : Type} [Group G]

theorem isClassicalMember3In_conj {Y M : Subgroup G} {z : G} (h : IsClassicalMember3In Y M z)
    {w : G} (hw : w ∈ Y) : IsClassicalMember3In Y (conjSub w M) (w * z * w⁻¹) := by
  obtain ⟨hz, hc⟩ := h
  refine ⟨Y.mul_mem (Y.mul_mem hw hz) (Y.inv_mem hw), ?_⟩
  have := hc.conj (⟨w, hw⟩ : ↥Y)
  rw [conjSub_subgroupOf] at this
  exact this

end Conj

section Link

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem exists_conj_involution_of_fund3_in {ι : Type}
    (D : LieSystemData3 ι (LocalQuot Φ a) (localFamily Φ a)) {i : ι}
    {R R' : Subgroup (D.kind i).G} (hR : R ∈ (D.kind i).fund) (hR' : R' ∈ (D.kind i).fund)
    {M K : Subgroup G} (hM : M ∈ centralizingMembers Φ {a}) (hK : K ∈ centralizingMembers Φ {a})
    (hMR : modOddIn (centralizingLayer Φ {a}) M = R.map (D.hom i))
    (hKR' : modOddIn (centralizingLayer Φ {a}) K = R'.map (D.hom i)) {z z' : G}
    (hz : IsClassicalMember3In (centralizingLayer Φ {a}) M z)
    (hz' : IsClassicalMember3In (centralizingLayer Φ {a}) K z') :
    ∃ w ∈ centralizingLayer Φ {a}, z' * (w * z * w⁻¹) ∈ oddCoreIn (centralizingLayer Φ {a}) := by
  set Y := centralizingLayer Φ {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hKY : K ≤ Y := le_centralizingLayer hK
  obtain ⟨hzY, hz0⟩ := id hz
  obtain ⟨hz'Y, hz0'⟩ := id hz'
  by_cases hspecial : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
      StatedLieAdmissible t n 3 1 ∧ D.kind i = CompData.model t n ∧ (t = .G2 ∨ t = .trialityD4)
  · obtain ⟨t, n, hadm, hc, hG⟩ := hspecial
    set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
    set zY : ↥Y := ⟨z, hzY⟩ with hzYdef
    set zY' : ↥Y := ⟨z', hz'Y⟩ with hzY'def
    have hzz : zY * zY = 1 := hz0.isCentralInvolution.sq
    have hzz' : zY' * zY' = 1 := hz0'.isCentralInvolution.sq
    have hz2 : z * z = 1 := congrArg Subtype.val hzz
    have hz'2 : z' * z' = 1 := congrArg Subtype.val hzz'
    have hzne : z ≠ 1 := fun h => hz0.isCentralInvolution.ne_one (Subtype.ext h)
    have hz'ne : z' ≠ 1 := fun h => hz0'.isCentralInvolution.ne_one (Subtype.ext h)
    have hζ2 : π zY * π zY = 1 := by rw [← map_mul, hzz, map_one]
    have hζ'2 : π zY' * π zY' = 1 := by rw [← map_mul, hzz', map_one]
    have hζ1 : π zY ≠ 1 := Q3Y.mk_ne_one_of_involution Y hzY hz2 hzne
    have hζ'1 : π zY' ≠ 1 := Q3Y.mk_ne_one_of_involution Y hz'Y hz'2 hz'ne
    have hζmem : π zY ∈ R.map (D.hom i) := by
      rw [← hMR]
      exact ⟨zY, hz0.mem, rfl⟩
    have hζ'mem : π zY' ∈ R'.map (D.hom i) := by
      rw [← hKR']
      exact ⟨zY', hz0'.mem, rfl⟩
    have hcentral : ∀ {M₀ : Subgroup G} {w₀ : G} (hw₀Y : w₀ ∈ Y)
        (hw₀ : IsClassicalMember3 (M₀.subgroupOf Y) (⟨w₀, hw₀Y⟩ : ↥Y)),
        ∀ y ∈ modOddIn Y M₀, π ⟨w₀, hw₀Y⟩ * y = y * π ⟨w₀, hw₀Y⟩ := by
      intro M₀ w₀ hw₀Y hw₀ y hy
      obtain ⟨m, hm, rfl⟩ := hy
      rw [← map_mul, ← map_mul]
      exact congrArg _ (hw₀.isCentralInvolution.central m hm)
    obtain ⟨g, hg⟩ := exists_conj_image_of_special (D.hom i) (D.ker_le_center i) hG hadm hc hR hR'
      hζmem hζ'mem hζ2 hζ'2 hζ1 hζ'1
      (fun y hy => hcentral hzY hz0 y (by rw [hMR]; exact hy))
      (fun y hy => hcentral hz'Y hz0' y (by rw [hKR']; exact hy))
    obtain ⟨wT, hwT⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) (D.hom i g)
    have h5 : π (wT * zY * wT⁻¹) = π zY' := by
      rw [map_mul, map_mul, map_inv, hwT]
      exact hg
    have h6 : (wT * zY * wT⁻¹)⁻¹ * zY' ∈ classicalInvolutionOddCore ↥Y :=
      QuotientGroup.eq.mp h5
    have hU : ((wT : G) * z * (wT : G)⁻¹)⁻¹ * z' ∈ oddCoreIn Y := ⟨_, h6, rfl⟩
    refine ⟨(wT : G), wT.2, ?_⟩
    have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
    have := (oddCoreIn Y).inv_mem hU
    rwa [mul_inv_rev, inv_inv, hz'inv] at this
  · have hSC : (D.kind i).SingleClass := by
      rcases D.valid i with ⟨t, n, hfund, hadm, hc⟩ | hc | hc
      · have ht : ¬ (t = .G2 ∨ t = .trialityD4) := fun h => hspecial ⟨t, n, hadm, hc, h⟩
        push Not at ht
        rw [hc]
        exact ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three hfund hadm ht.1 ht.2
      · rw [hc]
        intro S₁ hS₁ S₂ hS₂
        rw [Set.mem_singleton_iff.mp hS₁, Set.mem_singleton_iff.mp hS₂]
        exact ⟨1, by simp⟩
      · rw [hc]
        exact Uniform.m11_singleClass
    obtain ⟨g, hg⟩ := hSC R hR R' hR'
    obtain ⟨w, hwY, hmod⟩ := exists_conj_modOddIn_of_fund3 D hMR hKR' g hg
    exact ⟨w, hwY, mul_mem_oddCoreIn_of_modOddIn_eq3_in hz'
      (isClassicalMember3In_conj hz hwY) hmod⟩

end Link

section Cover

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

@[expose] def ExactCovers3 (Ω : Set (Subgroup G)) (S : Set (Subgroup G)) (a : G) : Prop :=
  ∀ (ι : Type) (D : LieSystemData3 ι (LocalQuot (exactFamily3 Ω a) a)
      (localFamily (exactFamily3 Ω a) a)) (i : ι),
    ∃ K ∈ S, a ∈ trivialOnQuot K ∧
      modOddIn (exactLayer3 Ω a) (exactCore3 a K) ≤ (D.hom i).range

theorem involutionLinkSpan3_of_exactCovers3 (hΩ : InClass3 Ω) {a : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers a)) (hIH : LieSystemMod3 (exactPair3 Ω a))
    (hS : S ⊆ Ω) (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z)
    (hlay : exactLayer3 Ω a ≤ rankTwoSpan A) (hcov : ExactCovers3 Ω S a) :
    InvolutionLinkSpan3 Ω A S a := by
  intro M hMmem z hz
  have hΦ : SecData3 a (exactFamily3 Ω a) :=
    secData3_exactFamily hΩ hc2 ⟨M, centralizingMembers_subset_tqMembers3 hMmem⟩
  obtain ⟨ι, -, ⟨D⟩⟩ := hIH
  set Y := exactLayer3 Ω a with hY
  have hMΦ : M ∈ centralizingMembers (exactFamily3 Ω a) {a} :=
    ⟨centralizingMembers_subset_exactFamily3 hMmem, hMmem.2⟩
  have hMY : M ≤ Y := le_centralizingLayer hMΦ
  have hMfam : modOddIn Y M ∈ localFamily (exactFamily3 Ω a) a :=
    ⟨M.subgroupOf Y, ⟨M, hMΦ, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  obtain ⟨K, hKS, haK, hKi⟩ := hcov ι D i
  have hKtq : K ∈ tqMembers3 Ω a := ⟨hS hKS, haK⟩
  obtain ⟨z', hz'A, hKz'⟩ := hinv K hKS
  have hK'Φ : exactCore3 a K ∈ centralizingMembers (exactFamily3 Ω a) {a} :=
    ⟨exactCore3_mem_exactFamily3 hKtq, exactCore3_le_centralizer a K⟩
  have hK'Y : exactCore3 a K ≤ Y := exactCore3_le_exactLayer3 hKtq
  have hK'In : IsClassicalMember3In Y (exactCore3 a K) z' :=
    isClassicalMember3In_exactCore3 hKz' hc2 haK hK'Y (exactLayer3_le_centralizer Ω a)
  have hK'fam : modOddIn Y (exactCore3 a K) ∈ localFamily (exactFamily3 Ω a) a :=
    ⟨(exactCore3 a K).subgroupOf Y, ⟨exactCore3 a K, hK'Φ, hK'Y, rfl⟩, rfl⟩
  obtain ⟨j, R', hR', hK'R'⟩ := D.fundamental _ hK'fam
  have hij : j = i := by
    by_contra hne
    refine hK'In.2.map_oddQuotient.not_le_center ?_
    have h1 : modOddIn Y (exactCore3 a K) ≤ (D.hom j).range := hK'R' ▸ Subgroup.map_le_range _ _
    exact (le_inf hKi h1).trans (range_inf_range_le_center3 D (Ne.symm hne))
  subst hij
  have hMIn : IsClassicalMember3In Y M z := ⟨hMY hz.mem, hz.subgroupOf hMY⟩
  obtain ⟨w, hwY, hU⟩ := exists_conj_involution_of_fund3_in D hR hR' hMΦ hK'Φ hMR hK'R' hMIn
    hK'In
  have hK'' : IsClassicalMember3 (conjSub w M) (w * z * w⁻¹) := hz.conj w
  obtain ⟨o, ho, hoz⟩ := exists_conj_of_mul_mem hK''.isCentralInvolution.sq
    hKz'.isCentralInvolution.sq (odd_card_oddCoreIn _) hU
  have hoY : o ∈ Y := oddCoreIn_le _ ho
  refine ⟨K, hKS, z', hz'A, hKz', w⁻¹ * o⁻¹, mul_mem (hlay (inv_mem hwY)) (hlay (inv_mem hoY)),
    ?_⟩
  rw [hoz]
  group

end Cover

end CFSG.ClassicalInvolution.Q3.Q3NF
