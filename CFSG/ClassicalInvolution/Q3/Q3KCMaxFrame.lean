module

public import CFSG.ClassicalInvolution.Q3.Q3KCSat
public import CFSG.ClassicalInvolution.Q3.Q3TIYTPShape

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3KC

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NG


section Defs

variable {G : Type} [Group G]

@[expose] def frameGroup (𝒦 : Set (Subgroup G)) : Subgroup G :=
  Subgroup.closure {w | ∃ L ∈ 𝒦, IsClassicalMember3 L w}

structure CommFamily (Ω : Set (Subgroup G)) (𝒦 : Set (Subgroup G)) : Prop where
  subset : 𝒦 ⊆ Ω
  comm : ∀ L ∈ 𝒦, ∀ L' ∈ 𝒦, L ≠ L' → Commutes L L'

@[expose] def frameCommFamily (Ω : Set (Subgroup G)) (𝒦 : Set (Subgroup G))
    (K₁ K₂ : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ (∃ w ∈ frameGroup 𝒦, IsClassicalMember3 L w) ∧
    (L = K₁ ∨ L = K₂ ∨ (Commutes K₁ L ∧ Commutes K₂ L))}

end Defs

section Family

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isElemAbelian_frameGroup {𝒦 : Set (Subgroup G)} (h : CommFamily Ω 𝒦) :
    IsElemAbelian 2 (frameGroup 𝒦) := by
  have hsq : ∀ s ∈ {w | ∃ L ∈ 𝒦, IsClassicalMember3 L w}, s * s = 1 := by
    rintro s ⟨L, -, hs⟩
    exact hs.isCentralInvolution.sq
  have hc : ∀ s ∈ {w | ∃ L ∈ 𝒦, IsClassicalMember3 L w},
      ∀ t ∈ {w | ∃ L ∈ 𝒦, IsClassicalMember3 L w}, s * t = t * s := by
    rintro s ⟨L, hL, hs⟩ t ⟨L', hL', ht⟩
    by_cases hLL : L = L'
    · subst hLL
      rw [involution_unique3 hs ht]
    · exact h.comm L hL L' hL' hLL s hs.mem t ht.mem
  exact Balance.Theorem5.isElemAbelian_closure_of_commuting_involutions hsq hc

theorem exists_maximal_commFamily {𝒦₀ : Set (Subgroup G)} (h₀ : CommFamily Ω 𝒦₀) :
    ∃ 𝒦 : Set (Subgroup G), 𝒦₀ ⊆ 𝒦 ∧ CommFamily Ω 𝒦 ∧
      ∀ M ∈ Ω, (∀ L ∈ 𝒦, L ≠ M → Commutes L M) → ∀ w, IsClassicalMember3 M w →
        w ∈ frameGroup 𝒦 := by
  classical
  let C : Set (Set (Subgroup G)) := {𝒦 | 𝒦₀ ⊆ 𝒦 ∧ CommFamily Ω 𝒦}
  have hCne : C.Nonempty := ⟨𝒦₀, subset_rfl, h₀⟩
  obtain ⟨𝒦, h𝒦C, hmax⟩ :=
    Set.exists_max_image C (fun 𝒦 => Nat.card (frameGroup 𝒦)) (Set.toFinite C) hCne
  refine ⟨𝒦, h𝒦C.1, h𝒦C.2, fun M hM hc w hw => ?_⟩
  by_cases hMK : M ∈ 𝒦
  · exact Subgroup.subset_closure ⟨M, hMK, hw⟩
  · have hne : ∀ L ∈ 𝒦, L ≠ M := fun L hL h => hMK (h ▸ hL)
    have h' : CommFamily Ω (insert M 𝒦) :=
      { subset := Set.insert_subset hM h𝒦C.2.subset
        comm := by
          intro L hL L' hL' hLL
          rcases hL with rfl | hL <;> rcases hL' with rfl | hL'
          · exact absurd rfl hLL
          · exact (hc L' hL' (hne L' hL')).symm
          · exact hc L hL (hne L hL)
          · exact h𝒦C.2.comm L hL L' hL' hLL }
    have hle : frameGroup 𝒦 ≤ frameGroup (insert M 𝒦) :=
      Subgroup.closure_mono fun x ⟨L, hL, hx⟩ => ⟨L, Set.mem_insert_of_mem _ hL, hx⟩
    have hcard := hmax (insert M 𝒦) ⟨h𝒦C.1.trans (Set.subset_insert _ _), h'⟩
    have heq : frameGroup 𝒦 = frameGroup (insert M 𝒦) :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    rw [heq]
    exact Subgroup.subset_closure ⟨M, Set.mem_insert _ _, hw⟩

theorem mem_frameCommFamily_of_mem (hΩ : InClass3 Ω) {𝒦 : Set (Subgroup G)}
    (h𝒦 : CommFamily Ω 𝒦) {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ 𝒦) (hK₂ : K₂ ∈ 𝒦)
    {L : Subgroup G} (hL : L ∈ 𝒦) : L ∈ frameCommFamily Ω 𝒦 K₁ K₂ := by
  obtain ⟨w, hw⟩ := hΩ.classical L (h𝒦.subset hL)
  refine ⟨h𝒦.subset hL, ⟨w, Subgroup.subset_closure ⟨L, hL, hw⟩, hw⟩, ?_⟩
  by_cases h1 : L = K₁
  · exact Or.inl h1
  by_cases h2 : L = K₂
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr ⟨h𝒦.comm K₁ hK₁ L hL (Ne.symm h1), h𝒦.comm K₂ hK₂ L hL (Ne.symm h2)⟩)

end Family

section Cover

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem lieCovers3_of_maximal (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP : ∀ {a : G} {L : Subgroup G}, L ∈ Ω → IsClassicalMember3 L a →
      LocalOddCentral Ω {a} ∧ Q3W.LocalOddThreeFree3 Ω a)
    {𝒦 : Set (Subgroup G)} (h𝒦 : CommFamily Ω 𝒦)
    (hmax : ∀ M ∈ Ω, (∀ L ∈ 𝒦, L ≠ M → Commutes L M) → ∀ w, IsClassicalMember3 M w →
      w ∈ frameGroup 𝒦)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ 𝒦) (hK₂ : K₂ ∈ 𝒦) {a : G} (ha : a ∈ frameGroup 𝒦)
    (hfa : IsFrameInvolution3 (frameCommFamily Ω 𝒦 K₁ K₂) a) :
    LieCovers3 Ω (frameCommFamily Ω 𝒦 K₁ K₂) a := by
  intro ι D i
  have hΩc := hΩ.conjInvariant
  obtain ⟨L₀, hL₀S, hL₀a⟩ := hfa
  obtain ⟨hP1, hO3⟩ := hP hL₀S.1 hL₀a
  have hA : IsElemAbelian 2 (frameGroup 𝒦) := isElemAbelian_frameGroup h𝒦
  have hKa : ∀ L ∈ 𝒦, L ≤ Subgroup.centralizer ({a} : Set G) := by
    intro L hL
    have h1 : L ≤ Subgroup.centralizer ((frameGroup 𝒦 : Subgroup G) : Set G) := by
      unfold frameGroup
      rw [Subgroup.centralizer_closure]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      rintro w ⟨L', hL', hw⟩
      by_cases hLL : L = L'
      · subst hLL
        exact (Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hw.subnormal hx)).symm
      · exact (h𝒦.comm L hL L' hL' hLL x hx w hw.mem).symm
    exact h1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hKmem : ∀ L ∈ 𝒦, L ∈ centralizingMembers Ω {a} := fun L hL => ⟨h𝒦.subset hL, hKa L hL⟩
  set Y := centralizingLayer Ω {a} with hY
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hAY : frameGroup 𝒦 ≤ Y := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨L, hL, hw⟩
    exact le_centralizingLayer (hKmem L hL) hw.mem
  have hΦ : ∀ {M : Subgroup G}, M ∈ centralizingMembers Ω {a} →
      modOddIn Y M ∈ localFamily Ω a :=
    fun {M} hM => ⟨M.subgroupOf Y, ⟨M, hM, le_centralizingLayer hM, rfl⟩, rfl⟩
  have hKS : ∀ L ∈ 𝒦, L ∈ frameCommFamily Ω 𝒦 K₁ K₂ := fun L hL =>
    mem_frameCommFamily_of_mem hΩ h𝒦 hK₁ hK₂ hL
  by_cases hmv : ∃ L ∈ 𝒦, ∃ w, IsClassicalMember3 L w ∧ ∃ hwY : w ∈ Y,
      ¬ ∀ q ∈ (D.hom i).range, π ⟨w, hwY⟩ * q = q * π ⟨w, hwY⟩
  ·
    obtain ⟨L, hL, w, hw, hwY, hnc⟩ := hmv
    exact ⟨L, hKS L hL, hKa L hL, le_range_of_not_centralizes D (hΦ (hKmem L hL))
      (m := π ⟨w, hwY⟩) ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩ hnc⟩
  push Not at hmv
  have hfix : ∀ (f : G) (hf : f ∈ frameGroup 𝒦), ∀ q ∈ (D.hom i).range,
      π ⟨f, hAY hf⟩ * q = q * π ⟨f, hAY hf⟩ := by
    set Q : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y) := (D.hom i).range with hQ
    let Cq : Subgroup G := ((Subgroup.centralizer (Q : Set _)).comap π).map Y.subtype
    have hCq : ∀ (f : G) (hf : f ∈ Y), (∀ q ∈ Q, π ⟨f, hf⟩ * q = q * π ⟨f, hf⟩) → f ∈ Cq :=
      fun f hf h => ⟨⟨f, hf⟩, Subgroup.mem_centralizer_iff.mpr fun q hq => (h q hq).symm, rfl⟩
    have hsub : frameGroup 𝒦 ≤ Cq := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro w ⟨L, hL, hw⟩
      exact hCq w (hAY (Subgroup.subset_closure ⟨L, hL, hw⟩)) (hmv L hL w hw _)
    intro f hf q hq
    obtain ⟨c, hc, hcf⟩ := hsub hf
    have hcf' : c = ⟨f, hAY hf⟩ := Subtype.ext hcf
    subst hcf'
    exact (Subgroup.mem_centralizer_iff.mp hc q hq).symm
  obtain ⟨R, hR, hmeet⟩ := D.meets i
  obtain ⟨_, ⟨M, hMmem, hMY, rfl⟩, hS⟩ := hmeet
  have hMbar : modOddIn Y M ≤ (D.hom i).range := by
    have h1 : modOddIn Y M = R.map (D.hom i) := hS
    rw [h1]
    exact Subgroup.map_le_range _ _
  obtain ⟨z, hz⟩ := hΩ.classical M hMmem.1
  have hzY : z ∈ Y := hMY hz.mem
  have hz2 : z * z = 1 := hz.isCentralInvolution.sq
  have hzbar : π ⟨z, hzY⟩ ∈ (D.hom i).range :=
    hMbar ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
  obtain ⟨w, hwY, hwC, hw2, hwπ⟩ := exists_involution_lift_group hA hAY hzY hz2 hz.ne_one
    (fun f hf => hfix f hf _ hzbar)
  obtain ⟨o, ho, hzo⟩ := Q3Y.exists_conj_of_mk_eq Y hwY hzY hw2 hz2 hwπ
  have hoY : o ∈ Y := oddCoreIn_le _ ho
  have hoC : o ∈ Subgroup.centralizer ({a} : Set G) := centralizingLayer_le_centralizer Ω {a} hoY
  have hK' : IsClassicalMember3 (conjSub o⁻¹ M) w := by
    have h1 := hz.conj o⁻¹
    have e : o⁻¹ * z * (o⁻¹)⁻¹ = w := by rw [hzo]; group
    rwa [e] at h1
  have hKmem' : conjSub o⁻¹ M ∈ centralizingMembers Ω {a} :=
    conjSub_mem_centralizingMembers hΩc (Subgroup.inv_mem _ hoC) hMmem
  have hM'bar : modOddIn Y (conjSub o⁻¹ M) ≤ (D.hom i).range := by
    refine le_trans ?_ hMbar
    rintro _ ⟨c, hc, rfl⟩
    have hc' : (c : G) ∈ conjSub o⁻¹ M := Subgroup.mem_subgroupOf.mp hc
    rw [mem_conjSub_iff] at hc'
    have hm : o * (c : G) * o⁻¹ ∈ M := by simpa using hc'
    have hmY : o * (c : G) * o⁻¹ ∈ Y := hMY hm
    have hπo : π ⟨o, hoY⟩ = 1 := by
      obtain ⟨x, hx, hxo⟩ := ho
      have hxo' : x = ⟨o, hoY⟩ := Subtype.ext hxo
      rw [hxo'] at hx
      exact (QuotientGroup.eq_one_iff _).mpr hx
    have hπo' : π ⟨o⁻¹, Y.inv_mem hoY⟩ = 1 := by
      have : (⟨o⁻¹, Y.inv_mem hoY⟩ : ↥Y) = (⟨o, hoY⟩ : ↥Y)⁻¹ := rfl
      rw [this, map_inv, hπo, inv_one]
    have hceq : c = ⟨o⁻¹, Y.inv_mem hoY⟩ * ⟨o * (c : G) * o⁻¹, hmY⟩ * ⟨o, hoY⟩ :=
      Subtype.ext (by
        show (c : G) = o⁻¹ * (o * (c : G) * o⁻¹) * o
        group)
    refine ⟨⟨o * (c : G) * o⁻¹, hmY⟩, Subgroup.mem_subgroupOf.mpr hm, ?_⟩
    calc π ⟨o * (c : G) * o⁻¹, hmY⟩
        = π ⟨o⁻¹, Y.inv_mem hoY⟩ * π ⟨o * (c : G) * o⁻¹, hmY⟩ * π ⟨o, hoY⟩ := by
          rw [hπo, hπo', one_mul, mul_one]
      _ = π c := by rw [← map_mul, ← map_mul, ← hceq]
  set M' := conjSub o⁻¹ M with hM'
  have hM'fund : ∃ R' ∈ (D.kind i).fund, modOddIn Y M' = R'.map (D.hom i) := by
    obtain ⟨i', R', hR', hM'R'⟩ := D.fundamental _ (hΦ hKmem')
    have hii : i' = i := by
      by_contra hne
      refine not_le_center_of_mem3 hΩ hKmem' ?_
      have h1 : modOddIn Y M' ≤ (D.hom i').range := hM'R' ▸ Subgroup.map_le_range _ _
      exact (le_inf hM'bar h1).trans (range_inf_range_le_center3 D (Ne.symm hne))
    subst hii
    exact ⟨R', hR', hM'R'⟩
  obtain ⟨R', hR', hM'R'⟩ := hM'fund
  have hCj : ∀ L ∈ 𝒦, M' = L ∨ Commutes L M' := by
    intro L hL
    obtain ⟨zL, hzL⟩ := hΩ.classical L (h𝒦.subset hL)
    have hLmem := hKmem L hL
    obtain ⟨jL, RL, hRL, hLR⟩ := D.fundamental _ (hΦ hLmem)
    by_cases hj : jL = i
    · left
      have hLfund : ∃ RL' ∈ (D.kind i).fund, modOddIn Y L = RL'.map (D.hom i) := by
        subst hj
        exact ⟨RL, hRL, hLR⟩
      obtain ⟨RL, hRL, hLR⟩ := hLfund
      have hzLY : zL ∈ Y := le_centralizingLayer hLmem hzL.mem
      have hz1 : π ⟨zL, hzLY⟩ ≠ 1 :=
        Q3Y.mk_ne_one_of_involution Y hzLY hzL.isCentralInvolution.sq hzL.ne_one
      have hzLbar : π ⟨zL, hzLY⟩ ∈ modOddIn Y L :=
        ⟨⟨zL, hzLY⟩, Subgroup.mem_subgroupOf.mpr hzL.mem, rfl⟩
      rw [hLR] at hzLbar
      obtain ⟨r, hrR, hr⟩ := hzLbar
      have htop := Q3TIY.fund_eq_top_of_central_image (D.valid i) (D.hom i)
        (D.ker_le_center i) hRL hrR (by rw [hr]; exact hz1) (fun y => by
          rw [hr]
          exact (hmv L hL zL hzL hzLY _ ⟨y, rfl⟩).symm)
      have hRLtop : RL = ⊤ := htop RL hRL
      have hR'top : R' = ⊤ := htop R' hR'
      have himg : RouteD.locImg Ω a M' = RouteD.locImg Ω a L := by
        show modOddIn Y M' = modOddIn Y L
        rw [hM'R', hLR, hRLtop, hR'top]
      exact Q3W.locImg_injOn3 hΩ hex hP1 hO3 hKmem' hLmem himg
    · right
      refine Q3W.commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hLmem hKmem' ?_
      intro x hx y hy
      have hx' : x ∈ modOddIn Y L := hx
      have hy' : y ∈ modOddIn Y M' := hy
      rw [hLR] at hx'
      rw [hM'R'] at hy'
      obtain ⟨r, -, rfl⟩ := hx'
      obtain ⟨r', -, rfl⟩ := hy'
      exact D.commute jL i hj r r'
  have hcomm_all : ∀ L ∈ 𝒦, L ≠ M' → Commutes L M' := by
    intro L hL hne
    rcases hCj L hL with h | h
    · exact absurd h.symm hne
    · exact h
  have hwA : w ∈ frameGroup 𝒦 := hmax M' hKmem'.1 hcomm_all w hK'
  refine ⟨M', ⟨hKmem'.1, ⟨w, hwA, hK'⟩, ?_⟩, hKmem'.2, hM'bar⟩
  rcases hCj K₁ hK₁ with h1 | h1
  · exact Or.inl h1
  rcases hCj K₂ hK₂ with h2 | h2
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr ⟨h1, h2⟩)

end Cover

end CFSG.ClassicalInvolution.Q3.Q3KC
