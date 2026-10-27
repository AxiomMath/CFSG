module

public import CFSG.ClassicalInvolution.Q3.Q3TD3ZSide
public import CFSG.ClassicalInvolution.Q3.Q3TD3Scen
public import CFSG.ClassicalInvolution.Q3.Q3TD3Nodes
public import CFSG.ClassicalInvolution.RouteD.GapsPatternDMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


section Pat

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} {m : ℕ}

theorem exists_moved_layer_member3
    (hF : OrthFacts
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (c : TCtx3 .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) (hfix : HasFixedMember Ω K β z) :
    ∃ N ∈ centralizingMembers Ω {z}, ¬ locImg Ω z N ≤ c.d.Q₁ ∧ Commutes K N ∧
      ¬ Commutes β N := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨M, hMΩ, hKM, hβM, -⟩ := hfix
  obtain ⟨W, hW⟩ := hKβ
  obtain ⟨xM, hxM⟩ := hΩ.classical M hMΩ
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hMΩ hxM
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hKL := IsLayerMember3.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember3.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K) RK Rβ :=
    cx.modelAdj_of_adj3 hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  obtain ⟨S₁, hS₁, S₂, hS₂, hS12, hc₁, hc₂, hn₁, hn₂⟩ := hF.perp2 RK hRK Rβ hRβ hadj hlinR
  obtain ⟨N₁, hN₁, -, -, hN₁R⟩ := cx.exists_member_of_fund hS₁
  obtain ⟨N₂, hN₂, -, -, hN₂R⟩ := cx.exists_member_of_fund hS₂
  have hN12 : N₁ ≠ N₂ := fun h => hS12 (eq_of_map_eq_of_pow3 cx.d.ψ cx.d.ker_le
    cx.ker_cop (cx.hY.pow3 S₁ hS₁) (cx.hY.pow3 S₂ hS₂) (by rw [← hN₁R, ← hN₂R, h]))
  have hKN₁ : Commutes K N₁ := (cx.commutes_iff_fund hKx hN₁ hRK hKR hN₁R).mpr hc₁
  have hKN₂ : Commutes K N₂ := (cx.commutes_iff_fund hKx hN₂ hRK hKR hN₂R).mpr hc₂
  have hβN₁ : ¬ Commutes β N₁ := fun h =>
    hn₁ ((cx.commutes_iff_fund hβx hN₁ hRβ hβR hN₁R).mp h)
  have hβN₂ : ¬ Commutes β N₂ := fun h =>
    hn₂ ((cx.commutes_iff_fund hβx hN₂ hRβ hβR hN₂R).mp h)
  have hz₁ : N₁ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN₁.1 c.hz.mem (commutes_symm hKN₁)
  have hz₂ : N₂ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN₂.1 c.hz.mem (commutes_symm hKN₂)
  by_cases h₁ : locImg Ω z N₁ ≤ c.d.Q₁
  · by_cases h₂ : locImg Ω z N₂ ≤ c.d.Q₁
    · exact absurd (c.eq_of_locImg_le_Q₁ hz₁ hz₂ h₁ h₂) hN12
    · exact ⟨N₂, hz₂, h₂, hKN₂, hβN₂⟩
  · exact ⟨N₁, hz₁, h₁, hKN₁, hβN₁⟩

theorem PartnerPatternPlus3.of_toral_normal_of_adapted (hm : 5 ≤ m) (hMFZ : Gaps.FundNoncentral 3)
    (hF : OrthFacts
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (c : TCtx3 .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : ToralNormalD3 c (partner_involution_commutes_z3 c.hz ht hKβ))
    (hadapt : ∀ (nd : DNodes3 m Ω K) {β : Subgroup G} {t : G}, β ∈ Ω →
      IsClassicalMember3 β t → (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) →
      ∀ {pp : Fin m}, (∀ a, a ≠ pp → Commutes β (nd.J a)) → ¬ Commutes β (nd.J pp) →
        conjSub t (nd.J pp) = nd.J pp →
        pp.val = 0 ∧ ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β (nd.J pp)) :
    PartnerPatternPlus3 m Ω K β t := by
  classical
  have hΩ := c.hΩ
  have htz : t * z * t⁻¹ = z := partner_involution_commutes_z3 c.hz ht hKβ
  have hadm : StatedLieAdmissible .POmegaPlus m 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ m; omega⟩
  obtain ⟨n, H, hct, -⟩ := ModelFacts.hasBruhatDatum .POmegaPlus m 3 1 Nat.prime_three trivial hadm
  obtain ⟨e, he⟩ := exists_equiv_cartan_plus (p := 3) (f := 1) (by omega : 3 ≤ m)
  obtain ⟨j, hj, hjimg, hjK, hjc, hjp⟩ := c.exists_nodes_plus3 (by omega : 4 ≤ m) e he
  have hPat : PatternLemma (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.cartan :=
    PatternLemma.of_equiv e (fun a b => by rw [he, cartanD_eq]) (patternLemma_D (by omega))
  obtain ⟨k₀, v, hTT⟩ := hT
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨N, hNz, hNQ, hKN, hβN⟩ :=
      exists_moved_layer_member3 hF c hsingle hβ ht hKβ hfixM
    have hNK : N ≠ K := fun h => by
      rw [h] at hKN
      exact not_commutes_self3 c.hz hKN
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK hNQ
    have hgen := Balance.iSup_rankOneImage_eq_range .POmegaPlus m 3 1 Nat.prime_three trivial
      hadm c.d.ψ k₀
    have hfixrange : ∀ x ∈ c.d.ψ.range, locAut hΩ.conjInvariant htz x = x := by
      intro x hx
      rw [← hgen] at hx
      let Fix : Subgroup (locQuot Ω z) :=
        MonoidHom.eqLocus (locAut hΩ.conjInvariant htz).toMonoidHom (MonoidHom.id _)
      have hle : (⨆ γ ∈ (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D.roots,
          Balance.rankOneImage (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D c.d.ψ k₀ γ) ≤
          Fix := by
        refine iSup₂_le fun γ hγ y hy => ?_
        exact ((hTT γ hγ).2).mpr (by simp [hv0, charOf]) y hy
      exact hle hx
    have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
      (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hNz).mpr fun x hx => hfixrange x (by
        rw [hNR] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact ⟨r, rfl⟩)
    exact hβN (c.commutes_partner_of_centralizes3 hMFZ hsingle D hβ ht hKβ hNz hNt hKN)
  obtain ⟨y, hy, p₀, hfixed⟩ := exists_adapted_y_normal hΩ.conjInvariant c.d.ψ hct hPat htz v hv k₀
    hTT hjimg
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hmemy : ∀ a, conjSub y (j a) ∈ centralizingMembers Ω {z} := fun a => by
    have := centralizingMembers_conj hΩ.conjInvariant y z
    rw [hyz] at this
    rw [this]
    exact ⟨j a, (hj a).1, rfl⟩
  have hmemt : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have := centralizingMembers_conj hΩ.conjInvariant t z
    rw [htz] at this
    rw [this]
    exact ⟨L, hL, rfl⟩
  have hex : ∀ a : Fin m, ∃ w, IsClassicalMember3 (conjSub y (j (e.symm a))) w := fun a => by
    obtain ⟨w₀, hw₀⟩ := hΩ.classical (j (e.symm a)) (hj _).1.1
    exact ⟨_, hw₀.conj y⟩
  choose w hw using hex
  let nd : DNodes3 m Ω K :=
    { J := fun a => conjSub y (j (e.symm a))
      w := w
      mem := fun a => hΩ.conjInvariant y _ (hj _).1.1
      cl := hw
      commK := fun a => commutes_conjSub_of_mem_normalizer (c.locLayer_le_normalizer hy) (hjK _)
      comm := fun a b hab h1 h2 =>
        (hjc _ _ (fun hh => hab (e.symm.injective hh)) (by simpa using h1)
          (by simpa using h2)).conjSub y
      pair := fun a b h => by
        obtain ⟨W, hW⟩ := hjp (e.symm a) (e.symm b) (by simpa using h)
        exact ⟨_, ModelFacts.linearBlockStandardPair_map_conj hW y⟩ }
  have hfix' : ∀ a, a ≠ e p₀ → Commutes β (nd.J a) := fun a ha => by
    have hne : e.symm a ≠ p₀ := fun h => ha (by rw [← h]; exact (e.apply_symm_apply a).symm)
    have h1 := (hfixed (e.symm a)).1.mpr hne
    have hNt := (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hmemy (e.symm a))).mpr h1
    exact c.commutes_partner_of_centralizes3 hMFZ hsingle D hβ ht hKβ (hmemy _) hNt
      (commutes_conjSub_of_mem_normalizer (c.locLayer_le_normalizer hy) (hjK _))
  have hmov' : ¬ Commutes β (nd.J (e p₀)) := fun h => by
    have hJ : nd.J (e p₀) = conjSub y (j p₀) := by
      show conjSub y (j (e.symm (e p₀))) = _
      rw [Equiv.symm_apply_apply]
    rw [hJ] at h
    have hNt : conjSub y (j p₀) ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h t ht.mem n hn).symm
    have := (hfixed p₀).1.mp ((locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hmemy p₀)).mp hNt)
    exact this rfl
  have hnorm' : conjSub t (nd.J (e p₀)) = nd.J (e p₀) := by
    have hJ : nd.J (e p₀) = conjSub y (j p₀) := by
      show conjSub y (j (e.symm (e p₀))) = _
      rw [Equiv.symm_apply_apply]
    rw [hJ]
    have h1 := (hfixed p₀).2
    rw [locAut_locImg hΩ.conjInvariant htz] at h1
    exact locImg_injOn3 hΩ c.hex c.hP1 c.hO3 (hmemt _ (hmemy p₀)) (hmemy p₀) h1
  obtain ⟨hp0, hlin⟩ := hadapt nd hβ ht hKβ hfix' hmov' hnorm'
  have hFix : ∀ a : Fin m, 1 ≤ a.val → ∀ x ∈ locImg Ω z (conjSub y (j (e.symm a))),
      locAut hΩ.conjInvariant htz x = x := fun a ha => by
    refine (hfixed (e.symm a)).1.mpr fun h => ?_
    have h1 : a = e p₀ := by rw [← h]; exact (e.apply_symm_apply a).symm
    have := congrArg Fin.val h1
    omega
  refine PartnerPatternPlus3.of_locAut c (j := fun a : Fin m => j (e.symm a)) (fun a => (hj _).1)
    (fun a => hjK _) ?_ ?_ hy htz hFix ?_
  · intro a b hab h1 h2
    exact hjc _ _ (fun hh => hab (e.symm.injective hh)) (by simpa using h1) (by simpa using h2)
  · intro a b h
    exact hjp (e.symm a) (e.symm b) (by simpa using h)
  · intro a ha
    have h1 : a = e p₀ := Fin.ext (by omega)
    subst h1
    have hJ : nd.J (e p₀) = conjSub y (j p₀) := by
      show conjSub y (j (e.symm (e p₀))) = _
      rw [Equiv.symm_apply_apply]
    rw [hJ] at hlin
    simpa using hlin

theorem PartnerPatternPlus3.of_toral_normal (hm : 7 ≤ m) (hMFZ : Gaps.FundNoncentral 3)
    (hF : OrthFacts
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (c : TCtx3 .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : ToralNormalD3 c (partner_involution_commutes_z3 c.hz ht hKβ)) :
    PartnerPatternPlus3 m Ω K β t :=
  PartnerPatternPlus3.of_toral_normal_of_adapted (by omega) hMFZ hF c hsingle D hβ ht hKβ hfixM hT
    fun nd {_ _} hβ' ht' hKβ' {_} hfix hmov hnorm =>
      adapted_pattern_D3 hm hF c hsingle nd hβ' ht' hKβ' hfix hmov hnorm

end Pat

end CFSG.ClassicalInvolution.Q3.Q3TD
