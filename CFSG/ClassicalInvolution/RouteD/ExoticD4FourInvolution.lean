module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourGen

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps

section Lift

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem locMk_ne_one_of_involution {w : G} {T : Subgroup G} {a : G}
    (ha : IsClassicalMember p f T a) (haY : a ∈ locLayer Ω w) :
    locMk Ω w ⟨a, haY⟩ ≠ 1 := by
  intro h
  have hO : (⟨a, haY⟩ : ↥(locLayer Ω w)) ∈ classicalInvolutionOddCore ↥(locLayer Ω w) :=
    (QuotientGroup.eq_one_iff _).mp h
  have h2 : orderOf (⟨a, haY⟩ : ↥(locLayer Ω w)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ha.orderOf_eq_two
  have h3 := orderOf_dvd_natCard
    (⟨⟨a, haY⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω w))
  have h4 : orderOf (⟨⟨a, haY⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω w)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  rw [h4] at h3
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card
    (↥(locLayer Ω w)))) (even_iff_two_dvd.mpr h3)

theorem exists_central_preimage {w : G}
    {D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)} {i : Fin D.card}
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {T : Subgroup G} {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hR : Corr Ω w D i T R) {a : G} (ha : IsClassicalMember p f T a)
    (haY : a ∈ locLayer Ω w) :
    ∃ c ∈ R, (∀ r ∈ R, c * r = r * c) ∧ D.hom i c = locMk Ω w ⟨a, haY⟩ ∧ c ≠ 1 := by
  have hmem : locMk Ω w ⟨a, haY⟩ ∈ locImg Ω w T :=
    ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha.mem, rfl⟩
  rw [hR.2.2] at hmem
  obtain ⟨c, hcR, hc⟩ := hmem
  have hRperf : ⁅R, R⁆ = R := le_antisymm
    (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy))
    (hperf R hR.2.1)
  have hcent : c ∈ Subgroup.centralizer (R : Set _) :=
    Models.Transfer.mem_centralizer_of_map (D.ker_le_center i) hRperf (g := c) (by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [← hR.2.2] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [hc]
      show locMk Ω w t * locMk Ω w ⟨a, haY⟩ = locMk Ω w ⟨a, haY⟩ * locMk Ω w t
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_isClassicalMember ha (Subgroup.mem_subgroupOf.mp ht)))
  refine ⟨c, hcR, fun r hr => (Subgroup.mem_centralizer_iff.mp hcent r hr).symm, hc, ?_⟩
  rintro rfl
  exact locMk_ne_one_of_involution ha haY (by rw [← hc, map_one])


theorem mul_commutes_of_mem_comp (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {w : G} (hP1 : LocalOddCentral Ω {w})
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) {i₁ : Fin D.card}
    (ht : D.tag i₁ = .POmegaPlus) (hr : D.rank i₁ = 4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) {T T' L : Subgroup G}
    (hT : T ∈ compMembers Ω w D i₁) (hT' : T' ∈ compMembers Ω w D i₁) (hc : Commutes T T')
    (hL : L ∈ compMembers Ω w D i₁) {a b : G} (ha : IsClassicalMember p f T a)
    (hb : IsClassicalMember p f T' b) : ∀ y ∈ L, a * b * y = y * (a * b) := by
  have hq4 : 4 ≤ p ^ f := by omega
  have hperf := D.fundPerfect hp2 hq4
    (trialityD4_vacuous D (by decide : StatedLieTag.POmegaPlus ≠ .trialityD4) ht hrest) i₁
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h (by decide)
  obtain ⟨R, hR⟩ := exists_corr_left hΩ hex D hT
  obtain ⟨R', hR'⟩ := exists_corr_left hΩ hex D hT'
  have haY : a ∈ locLayer Ω w := le_centralizingLayer hT.1 ha.mem
  have hbY : b ∈ locLayer Ω w := le_centralizingLayer hT'.1 hb.mem
  obtain ⟨c, hcR, hcz, hca, hc1⟩ := exists_central_preimage hperf hR ha haY
  obtain ⟨c', hcR', hcz', hcb, hc1'⟩ := exists_central_preimage hperf hR' hb hbY
  have hRR' : Commutes R R' := (corr_commutes hΩ hP1 hperf hR hR').mp hc
  have hcen : c * c' ∈ Subgroup.center (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K :=
    fund_pair_mul_central_of_eq hp2 hq ht hr hexp (D.admissible i₁) hR.2.1 hR'.2.1 hRR' hcR hcR'
      hcz hcz' hc1 hc1'
  have habY : a * b ∈ locLayer Ω w := (locLayer Ω w).mul_mem haY hbY
  have himg : locMk Ω w ⟨a * b, habY⟩ = D.hom i₁ (c * c') := by
    rw [map_mul, hca, hcb]
    exact map_mul (locMk Ω w) ⟨a, haY⟩ ⟨b, hbY⟩
  intro y hy
  have := commutes_elem_of_commutes_locImg hΩ hP1 hL.1 habY (by
    intro x hx
    obtain ⟨k, hk⟩ := hL.2 hx
    rw [himg, ← hk, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen k]) y hy
  exact this.symm

end Lift

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {a : ℕ} {K : Subgroup G}
  {z : G}

omit [Finite G] in
theorem center_eq_bot_of_simple [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    have hx : x ∈ Subgroup.center G := by
      rw [h]
      trivial
    exact hxy (Subgroup.mem_center_iff.mp hx y).symm

theorem isClassicalMember_of_twin [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : RouteDSetup p f K z) (hloc : LocalShapeT p f a .POmegaPlus 4 (conjClass K) z)
    {N T : Subgroup G} (hN : N ∈ conjClass K) (hT : T ∈ conjClass K)
    (htw : cnbhd (conjClass K) T = cnbhd (conjClass K) N) {w : G}
    (hw : IsClassicalMember p f N w) : IsClassicalMember p f T w := by
  set Ω := conjClass K with hΩdef
  by_cases hTN : T = N
  · rw [hTN]
    exact hw
  obtain ⟨w', hw'⟩ := S.inClass.classical T hT
  have hcTN : Commutes T N := by
    have : T ∈ cnbhd Ω N := htw ▸ self_mem_cnbhd hT
    exact this.2.resolve_left hTN
  obtain ⟨M, hM⟩ := outerSet_nonempty_of_shape S hloc hN
  have hMΩ : M ∈ Ω := hM.1.1
  have hNM : N ∈ outerSet Ω M := mem_outerSet_symm hN hM
  have hTM : T ∈ outerSet Ω M := by
    have hMT : M ∈ cnbhd Ω T := htw ▸ hM.1
    exact ⟨mem_cnbhd_symm hT hMT, fun e => hM.2 (e.symm.trans htw)⟩
  obtain ⟨wM, hwM, hP1M, D, i₁, -, ht, hr, hrest⟩ := exists_D4At S hloc hMΩ
  have hout := outerSet_eq_compMembers S.odd (routeD_f_pos S) S.five S.inClass S.exact hwM hMΩ
    hP1M (single_class_of_mem hMΩ) D ht hr hrest
  have hcM : ∀ L ∈ outerSet Ω M, ∀ y ∈ L, w * w' * y = y * (w * w') := by
    intro L hL
    exact mul_commutes_of_mem_comp S.odd S.five S.inClass S.exact hP1M D ht hr hrest
      (hout ▸ hNM) (hout ▸ hTM) hcTN.symm (hout ▸ hL) hw hw'
  have hcN : ∀ L ∈ outerSet Ω N, ∀ y ∈ L, w * w' * y = y * (w * w') := by
    intro L hL y hy
    have hLN : Commutes L N := hL.1.2.resolve_left fun e => hL.2 (e ▸ rfl)
    have hLT : Commutes L T := by
      have : L ∈ cnbhd Ω T := htw ▸ hL.1
      exact this.2.resolve_left fun e => hL.2 (e ▸ htw)
    have h1 : y * w = w * y := hLN y hy w hw.mem
    have h2 : y * w' = w' * y := hLT y hy w' hw'.mem
    calc w * w' * y = w * (w' * y) := by group
      _ = w * (y * w') := by rw [h2]
      _ = (w * y) * w' := by group
      _ = (y * w) * w' := by rw [h1]
      _ = y * (w * w') := by group
  have hle : ∀ N' : Subgroup G, (∀ L ∈ outerSet Ω N', ∀ y ∈ L, w * w' * y = y * (w * w')) →
      outerGen Ω N' ≤ Subgroup.centralizer ({w * w'} : Set G) := fun N' h =>
    iSup₂_le fun L hL y hy => Subgroup.mem_centralizer_singleton_iff.mpr (h L hL y hy).symm
  have htop := eq_top_of_outerGen_le S hloc hN hM (hle N hcN) (hle M hcM)
  have hcentral : w * w' ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({w * w'} : Set G) := by
      rw [htop]
      trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rw [center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hcentral
  have hsq : w * w = 1 := by
    have h2 := hw.orderOf_eq_two
    have h3 : w ^ 2 = 1 := by
      rw [← h2]
      exact pow_orderOf_eq_one _
    simpa [pow_two] using h3
  have : w' = w := mul_left_cancel (hcentral.trans hsq.symm)
  rw [← this]
  exact hw'

end Main

end CFSG.ClassicalInvolution.RouteD.Exotic
