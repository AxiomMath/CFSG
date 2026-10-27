module

public import CFSG.ClassicalInvolution.Q3.Q3URChart3
public import CFSG.ClassicalInvolution.Q3.Q3URThree1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups

section Hexagon


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCtx3.exists_hexagon_closure {ι : Type} (c : UCtx3 3 Ω K z) (nd : UNodes3 c)
    (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember3 β t)
    (hnK : ¬ Commutes K β)
    (hW2 : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W β (nd.j 0))
    (hfirst : ¬ Commutes β (nd.j 0)) (hlast : Commutes β (nd.j 2))
    {N : Subgroup G} (hNz : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K)
    {wN : G} (hwN : IsClassicalMember3 N wN)
    (hW3 : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (nd.j 0) N)
    (hn03 : ¬ Commutes (nd.j 0) N) (hn32 : ¬ Commutes N (nd.j 2)) :
    ∃ H : Subgroup G, H ∈ Ω ∧ Commutes H β ∧ Commutes H (nd.j 0) ∧ Commutes H N := by
  classical
  have h2 := two_ne_zero_gf9
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  obtain ⟨g₀, hg₀⟩ := hsingle (nd.j 0) (nd.mem 0 (by omega)).1
  obtain ⟨W₂, hW₂⟩ := hW2
  obtain ⟨W₃, hW₃⟩ := hW3
  have hw0 : nd.w 0 = g₀ * z * g₀⁻¹ :=
    involution_unique3 (nd.isCl 0 (by omega)) (hg₀ ▸ c.hz.conj g₀)
  have htw : t * nd.w 0 = nd.w 0 * t :=
    unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW₂ hwβ.mem
      (nd.isCl 0 (by omega)).mem hwβ.orderOf_eq_two (nd.isCl 0 (by omega)).orderOf_eq_two
  have hwNw : nd.w 0 * wN = wN * nd.w 0 :=
    unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW₃
      (nd.isCl 0 (by omega)).mem hwN.mem (nd.isCl 0 (by omega)).orderOf_eq_two
      hwN.orderOf_eq_two
  have hconjz : ∀ s : G, s * nd.w 0 = nd.w 0 * s →
      (g₀⁻¹ * s * g₀) * z * (g₀⁻¹ * s * g₀)⁻¹ = z := by
    intro s hs
    have h1 : s * (g₀ * z * g₀⁻¹) * s⁻¹ = g₀ * z * g₀⁻¹ := by
      rw [← hw0]
      exact mul_inv_eq_iff_eq_mul.mpr hs
    calc (g₀⁻¹ * s * g₀) * z * (g₀⁻¹ * s * g₀)⁻¹
        = g₀⁻¹ * (s * (g₀ * z * g₀⁻¹) * s⁻¹) * g₀ := by group
      _ = g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀ := by rw [h1]
      _ = z := by group
  have ht'z : (g₀⁻¹ * t * g₀) * z * (g₀⁻¹ * t * g₀)⁻¹ = z := hconjz t htw
  have htN'z : (g₀⁻¹ * wN * g₀) * z * (g₀⁻¹ * wN * g₀)⁻¹ = z := hconjz wN hwNw.symm
  have hcl : ∀ {L : Subgroup G} {w : G}, IsClassicalMember3 L w →
      IsClassicalMember3 (conjSub g₀⁻¹ L) (g₀⁻¹ * w * g₀) := by
    intro L w h
    have := IsClassicalMember3.conj h g₀⁻¹
    rwa [inv_inv] at this
  have hβ' : conjSub g₀⁻¹ β ∈ Ω := hconj g₀⁻¹ β hβ
  have hN' : conjSub g₀⁻¹ N ∈ Ω := hconj g₀⁻¹ N hNz.1
  have hwβ' := hcl hwβ
  have hwN' := hcl hwN
  have hKiff : ∀ B : Subgroup G, Commutes K (conjSub g₀⁻¹ B) ↔ Commutes (nd.j 0) B := by
    intro B
    constructor
    · intro h
      have := (commutes_conjSub_iff g₀).mpr h
      rwa [conjSub_conjSub_inv, ← hg₀] at this
    · intro h
      have := (commutes_conjSub_iff g₀⁻¹).mpr h
      rwa [hg₀, conjSub_inv_conjSub] at this
  have hnK₁ : ¬ Commutes K (conjSub g₀⁻¹ β) := fun h =>
    hfirst (Gaps.commutes_symm ((hKiff β).mp h))
  have hnK₂ : ¬ Commutes K (conjSub g₀⁻¹ N) := fun h => hn03 ((hKiff N).mp h)
  have attach₁ := fun (M : Subgroup G) (hM : M ∈ Ω) (hMK : Commutes M K) =>
    c.commutes_partner_iff hMFZ D hsingle hβ' hwβ' hnK₁ hM hMK
  have attach₂ := fun (M : Subgroup G) (hM : M ∈ Ω) (hMK : Commutes M K) =>
    c.commutes_partner_iff hMFZ D hsingle hN' hwN' hnK₂ hM hMK
  obtain ⟨hKm, hKne, R₁, i₁, hR₁, hKR, -, -⟩ := c.exists_rootData_conj hg₀ c.hK
    (nd.commK 0 (by omega)) (nd.ne_K 0 (by omega)).symm c.hz
  obtain ⟨hJm, hJne, R₀, i₀, hR₀, hJR, -, -⟩ := c.exists_rootData_conj hg₀
    (nd.mem 2 (by omega)).1 (nd.far 0 (by omega) 2 (by omega) (by omega)).symm
    (nd.inj 2 (by omega) 0 (by omega) (by omega)) (nd.isCl 2 (by omega))
  have hne : i₀ ≠ i₁ := c.ne_of_rootInv hJm hKm
    (fun h => nd.ne_K 2 (by omega) (conjSub_injective g₀⁻¹ h)) hR₀ hR₁ hJR hKR
  have hR01 : Commutes R₀ R₁ :=
    (c.commutes_iff_root hJm hKm hR₀ hJR hKR).mp
      ((commutes_conjSub_iff g₀⁻¹).mpr (Gaps.commutes_symm (nd.commK 2 (by omega))))
  obtain ⟨g, hRg0, hRg1⟩ :=
    exists_chart_of_commuting_roots card_gf9 (by norm_num) hR₀ hR₁ hne hR01
  obtain ⟨θ, hθ⟩ : ∃ θ : Su (GaloisField 3 2) 3 1 (3 + 1) →* locQuot Ω z,
      θ = c.d.ψ.comp (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hθapp : ∀ x, θ x = c.d.ψ (g * x * g⁻¹) := fun x => by rw [hθ]; rfl
  have hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (3 + 1)) := by
    rw [hθ]
    exact ker_comp_conj_le_center c.d.ψ c.d.ker_le g
  have hrange : θ.range = c.d.ψ.range := by
    rw [hθ]
    exact range_comp_conj c.d.ψ g
  have hblk2 : ∀ A : Su (GaloisField 3 2) 3 1 2,
      θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A) ∈
        locImg Ω z (conjSub g₀⁻¹ (nd.j 2)) := by
    intro A
    rw [hJR, hRg0, hθapp]
    refine ⟨g * blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A * g⁻¹,
      ⟨blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A, ?_, rfl⟩, rfl⟩
    rw [← range_blockEmb2_eq_LcU_nodePair h2 (by norm_num : 2 < 3)]
    exact ⟨A, rfl⟩
  have hblk0 : ∀ A : Su (GaloisField 3 2) 3 1 2,
      θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A) ∈ locImg Ω z (conjSub g₀⁻¹ K) := by
    intro A
    rw [hKR, hRg1, hθapp]
    refine ⟨g * blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A * g⁻¹,
      ⟨blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A, ?_, rfl⟩, rfl⟩
    rw [← range_blockEmb2_eq_LcU_nodePair h2 (by norm_num : 0 < 3)]
    exact ⟨A, rfl⟩
  have hloc2 : ∀ a ∈ locImg Ω z (conjSub g₀⁻¹ (nd.j 2)), ∃ A : Su (GaloisField 3 2) 3 1 2,
      a = θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A) := by
    intro a ha
    rw [hJR, hRg0] at ha
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := ha
    rw [← range_blockEmb2_eq_LcU_nodePair h2 (by norm_num : 2 < 3)] at hx
    obtain ⟨A, rfl⟩ := hx
    exact ⟨A, (hθapp _).symm⟩
  have hloc0 : ∀ a ∈ locImg Ω z (conjSub g₀⁻¹ K), ∃ A : Su (GaloisField 3 2) 3 1 2,
      a = θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A) := by
    intro a ha
    rw [hKR, hRg1] at ha
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := ha
    rw [← range_blockEmb2_eq_LcU_nodePair h2 (by norm_num : 0 < 3)] at hx
    obtain ⟨A, rfl⟩ := hx
    exact ⟨A, (hθapp _).symm⟩
  have hJK : Commutes (conjSub g₀⁻¹ (nd.j 2)) K :=
    Gaps.commutes_symm (commutes_K_of_neU3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hJm hJne)
  have hKK : Commutes (conjSub g₀⁻¹ K) K :=
    Gaps.commutes_symm (commutes_K_of_neU3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hKm hKne)
  have hσ₁ := locAut_locAut hconj ht'z (mul_self_of_isClassicalMember3 hwβ')
  have hstab₁ : ∀ x, locAut hconj ht'z (θ x) ∈ θ.range := by
    intro x
    rw [hrange, hθapp]
    exact c.locAut_stab nd ht'z _
  have hJle₁ : conjSub g₀⁻¹ (nd.j 2) ≤ Subgroup.centralizer ({g₀⁻¹ * t * g₀} : Set G) :=
    (attach₁ _ hJm.1 hJK).mp
      ((commutes_conjSub_iff g₀⁻¹).mpr (Gaps.commutes_symm hlast))
  have hfix₁ : ∀ A : Su (GaloisField 3 2) 3 1 2,
      locAut hconj ht'z (θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A)) =
        θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A) := fun A =>
    (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 ht'z hJm).mp hJle₁ _ (hblk2 A)
  have hmove₁ : ∃ A : Su (GaloisField 3 2) 3 1 2,
      locAut hconj ht'z (θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A)) ≠
        θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (conjSub g₀⁻¹ K), locAut hconj ht'z a = a := by
      intro a ha
      obtain ⟨A, rfl⟩ := hloc0 a ha
      exact hcon A
    have hle := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 ht'z hKm).mpr hfx
    exact hnK ((commutes_conjSub_iff g₀⁻¹).mp ((attach₁ _ hKm.1 hKK).mpr hle))
  have hσ₂ := locAut_locAut hconj htN'z (mul_self_of_isClassicalMember3 hwN')
  have hstab₂ : ∀ x, locAut hconj htN'z (θ x) ∈ θ.range := by
    intro x
    rw [hrange, hθapp]
    exact c.locAut_stab nd htN'z _
  have hKle₂ : conjSub g₀⁻¹ K ≤ Subgroup.centralizer ({g₀⁻¹ * wN * g₀} : Set G) :=
    (attach₂ _ hKm.1 hKK).mp
      ((commutes_conjSub_iff g₀⁻¹).mpr
        (commutes_K_of_neU3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hNz hNK))
  have hfix₂ : ∀ A : Su (GaloisField 3 2) 3 1 2,
      locAut hconj htN'z (θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A)) =
        θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨0, by omega⟩ A) := fun A =>
    (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htN'z hKm).mp hKle₂ _ (hblk0 A)
  have hmove₂ : ∃ A : Su (GaloisField 3 2) 3 1 2,
      locAut hconj htN'z (θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A)) ≠
        θ (blockEmb2 (GaloisField 3 2) 3 1 3 ⟨2, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (conjSub g₀⁻¹ (nd.j 2)), locAut hconj htN'z a = a := by
      intro a ha
      obtain ⟨A, rfl⟩ := hloc2 a ha
      exact hcon A
    have hle := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htN'z hJm).mpr hfx
    exact hn32 (Gaps.commutes_symm
      ((commutes_conjSub_iff g₀⁻¹).mp ((attach₂ _ hJm.1 hJK).mpr hle)))
  obtain ⟨h, hh⟩ := unitary_two_partner_chart3 card_gf9 (by norm_num) le_rfl
    su2_pow_three_mem_commutator (fun x hx => center_orderOf_not_dvd_three_su3 (by omega) hx)
    θ hker (locAut hconj ht'z) (locAut hconj htN'z) hσ₁ hσ₂ hstab₁ hstab₂ hfix₁ hmove₁ hfix₂
    hmove₂
  have hroot : IsLongRootSU2 (GaloisField 3 2) 3 1 c.hn
      ((LcU (GaloisField 3 2) 3 1 pair13).map (MulAut.conj (g * h)).toMonoidHom)
      ((g * h) * zEltU (GaloisField 3 2) 3 1 pair13 * (g * h)⁻¹) :=
    (isLongRootSU2_LcU h2 c.hn pair13).conj (g * h)
  obtain ⟨H', hH'm, hH'K, hH'R⟩ := exists_member_of_rootU3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d
    (R := (LcU (GaloisField 3 2) 3 1 pair13).map (MulAut.conj (g * h)).toMonoidHom) ⟨_, hroot⟩
  have hfixH : ∀ a ∈ locImg Ω z H', locAut hconj ht'z a = a ∧ locAut hconj htN'z a = a := by
    intro a ha
    rw [hH'R] at ha
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := ha
    have e : c.d.ψ ((MulAut.conj (g * h)).toMonoidHom x) = θ (h * x * h⁻¹) := by
      rw [hθapp]
      congr 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hh x hx
  have hHK : Commutes K H' :=
    commutes_K_of_neU3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hH'm hH'K
  have hle₁ := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 ht'z hH'm).mpr fun a ha => (hfixH a ha).1
  have hle₂ := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htN'z hH'm).mpr fun a ha => (hfixH a ha).2
  have hHβ' : Commutes H' (conjSub g₀⁻¹ β) :=
    (attach₁ H' hH'm.1 (Gaps.commutes_symm hHK)).mpr hle₁
  have hHN' : Commutes H' (conjSub g₀⁻¹ N) :=
    (attach₂ H' hH'm.1 (Gaps.commutes_symm hHK)).mpr hle₂
  refine ⟨conjSub g₀ H', hconj g₀ H' hH'm.1, ?_, ?_, ?_⟩
  · have := (commutes_conjSub_iff g₀).mpr hHβ'
    rwa [conjSub_conjSub_inv] at this
  · have := (commutes_conjSub_iff g₀).mpr (Gaps.commutes_symm hHK)
    rwa [← hg₀] at this
  · have := (commutes_conjSub_iff g₀).mpr hHN'
    rwa [conjSub_conjSub_inv] at this

end Hexagon

end CFSG.ClassicalInvolution.Q3.Q3W
