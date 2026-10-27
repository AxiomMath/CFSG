module

public import CFSG.ClassicalInvolution.Q3.Q3TIVLayer
public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinA
public import CFSG.ClassicalInvolution.Q3.Q3NGInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Asc77.S28 (FalseTwinPure)
open scoped MatrixGroups commutatorElement


section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} (c : TwinLoc3 tY nY Ω z)

include c

theorem TwinLoc3.exists_central_lift {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    {wL : G} (hw : IsClassicalMember3 L wL)
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω z L = R.map c.d.ψ) :
    ∃ hY : wL ∈ locLayer Ω z, ∃ r ∈ R, (∀ s ∈ R, r * s = s * r) ∧ r ≠ 1 ∧
      locElt Ω z wL hY = c.d.ψ r := by
  obtain ⟨hY, ha, -, ha1, hac⟩ := image_involution_facts3 hL hw
  refine ⟨hY, ?_⟩
  rw [hLR] at ha hac
  obtain ⟨r, hrR, hr⟩ := ha
  refine ⟨r, hrR, ?_, ?_, by unfold locElt; exact hr.symm⟩
  · intro s hs
    refine commutes_of_map_commute_exponent3 c.d.ψ c.d.ker_le c.ker_cop
      (A := Subgroup.zpowers r) (L := R) (c.rf.y.pow3 R hR) ?_ r (Subgroup.mem_zpowers r) s hs
    intro a ha' s' hs'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    have h1 : c.d.ψ r * c.d.ψ s' = c.d.ψ s' * c.d.ψ r := by
      rw [hr]
      exact hac _ ⟨s', hs', rfl⟩
    rw [map_zpow]
    exact (Commute.zpow_left (show Commute (c.d.ψ r) (c.d.ψ s') from h1) k).eq
  · rintro rfl
    apply ha1
    rw [← hr, map_one]

end Lift

section Core

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K T : Subgroup G} {z w : G}
  {tY : StatedLieTag} {nY : ℕ} (c : TwinLoc3 tY nY Ω z) (hFT : FalseTwinPure Ω K T z w)
  (hcls : IsClassicalMember3 K z) (hclsT : IsClassicalMember3 T w)

include c hFT hcls hclsT

theorem u_central3 (hmf : TwinProductCentral3 tY nY) {g₀ : G}
    (hM : conjSub g₀ K ∈ centralizingMembers Ω {z}) (hMK : conjSub g₀ K ≠ K)
    (hMT : conjSub g₀ K ≠ T) :
    ∀ y ∈ locLayer Ω z, g₀ * (z * w) * g₀⁻¹ * y = y * (g₀ * (z * w) * g₀⁻¹) := by
  have hM₂ := hFT.M₂_mem hM hMK hMT
  have hM₂K := hFT.M₂_ne_K hMT
  have hM₂T := hFT.M₂_ne_T hMK
  have hMc : IsClassicalMember3 (conjSub g₀ K) (g₀ * z * g₀⁻¹) := hcls.conj g₀
  have hM₂c : IsClassicalMember3 (conjSub g₀ T) (g₀ * w * g₀⁻¹) := hclsT.conj g₀
  obtain ⟨R, hR, hMR⟩ := c.big_of_ne hFT.K_mem hFT.T_mem hFT.hKT hFT.commK hFT.commT hM hMK hMT
  obtain ⟨R₂, hR₂, hM₂R⟩ :=
    c.big_of_ne hFT.K_mem hFT.T_mem hFT.hKT hFT.commK hFT.commT hM₂ hM₂K hM₂T
  obtain ⟨hzY, r, hrR, hrc, hr1, hr⟩ := c.exists_central_lift hM hMc hR hMR
  obtain ⟨hwY, r₂, hr₂R, hr₂c, hr₂1, hr₂⟩ := c.exists_central_lift hM₂ hM₂c hR₂ hM₂R
  have hRR₂ : R ≠ R₂ := by
    intro e
    rw [e] at hMR
    exact hFT.M₂_ne_M (locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hM₂ hM (hM₂R.trans hMR.symm))
  have hcomm : Commutes R R₂ :=
    (c.commutes_iff_fund hM hM₂ hR hMR hM₂R).mp hFT.commutes_M_M₂
  have hnbhd : ∀ S ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      (S = R ∨ Commutes S R) ↔ (S = R₂ ∨ Commutes S R₂) := by
    intro S hS
    by_cases hSR : S = R
    · subst hSR
      exact ⟨fun _ => Or.inr hcomm, fun _ => Or.inl rfl⟩
    by_cases hSR₂ : S = R₂
    · subst hSR₂
      exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr hcomm.symm⟩
    obtain ⟨L, hL, hLS⟩ := mem_locFamily_iff.mp (c.d.mem_fam S hS)
    have hLM : L ≠ conjSub g₀ K := by
      rintro rfl
      exact hSR (eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.rf.y.pow3 S hS)
        (c.rf.y.pow3 R hR) (hLS.symm.trans hMR))
    have hLM₂ : L ≠ conjSub g₀ T := by
      rintro rfl
      exact hSR₂ (eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.rf.y.pow3 S hS)
        (c.rf.y.pow3 R₂ hR₂) (hLS.symm.trans hM₂R))
    have h1 := c.commutes_iff_fund hL hM hS hLS hMR
    have h2 := c.commutes_iff_fund hL hM₂ hS hLS hM₂R
    have h3 := hFT.graphTwin hL hLM hLM₂
    simp only [hSR, hSR₂, false_or]
    rw [← h1, ← h2]
    exact h3
  have hcen : r * r₂ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K :=
    hmf R hR R₂ hR₂ hRR₂ hcomm hnbhd r hrR hrc hr1 r₂ hr₂R hr₂c hr₂1
  have hUY : (g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹) ∈ locLayer Ω z :=
    (locLayer Ω z).mul_mem hzY hwY
  have hŪ : locElt Ω z ((g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹)) hUY = c.d.ψ (r * r₂) := by
    rw [← locElt_mul hzY hwY, hr, hr₂, map_mul]
  have hLcomm : ∀ L ∈ centralizingMembers Ω {z}, ∀ ℓ ∈ L,
      (g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹) * ℓ = ℓ * ((g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹)) := by
    intro L hL ℓ hℓ
    have hzM : g₀ * z * g₀⁻¹ ∈ conjSub g₀ K := conj_mem_conjSub hFT.hz.mem
    have hwM : g₀ * w * g₀⁻¹ ∈ conjSub g₀ T := conj_mem_conjSub hFT.hw.mem
    have fin : ∀ (a b : G), ℓ * a = a * ℓ → ℓ * b = b * ℓ → a * b * ℓ = ℓ * (a * b) := by
      intro a b ha hb
      calc a * b * ℓ = a * (b * ℓ) := by group
        _ = a * (ℓ * b) := by rw [hb]
        _ = (a * ℓ) * b := by group
        _ = (ℓ * a) * b := by rw [ha]
        _ = ℓ * (a * b) := by group
    by_cases hLK : L = K
    · subst hLK
      exact fin _ _ (hFT.commK _ hM hMK ℓ hℓ _ hzM) (hFT.commK _ hM₂ hM₂K ℓ hℓ _ hwM)
    by_cases hLT : L = T
    · subst hLT
      exact fin _ _ (hFT.commT _ hM hMT ℓ hℓ _ hzM) (hFT.commT _ hM₂ hM₂T ℓ hℓ _ hwM)
    obtain ⟨S, hS, hLS⟩ :=
      c.big_of_ne hFT.K_mem hFT.T_mem hFT.hKT hFT.commK hFT.commT hL hLK hLT
    obtain ⟨zL, hzL⟩ := c.hΩ.classical L hL.1
    have hLY : L ≤ locLayer Ω z := le_centralizingLayer hL
    obtain ⟨e⟩ := hzL.nonempty_equiv_sl2 (c.hex L hL.1)
    have hK' : Nonempty (↥(L.subgroupOf (locLayer Ω z)) ≃* SL(2, ZMod 3)) :=
      ⟨(Subgroup.subgroupOfEquivOfLe hLY).trans e⟩
    have hbot := commutes_of_equiv_sl2Three c.hP1 c.hO3 hK'
      (L := Subgroup.zpowers (⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ : ↥(locLayer Ω z)))
      (fun a ha b hb => by
        rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥(locLayer Ω z))]
        change QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ⁅a, b⁆ = 1
        rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [map_zpow]
        refine Commute.zpow_right ?_ k
        have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) a ∈
            locImg Ω z L := ⟨a, ha, rfl⟩
        rw [hLS] at hmk
        obtain ⟨s, -, hs⟩ := hmk
        have e1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))
            ⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ = c.d.ψ (r * r₂) := hŪ
        show QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) a *
            QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))
              ⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ = _
        rw [e1, ← hs, ← map_mul, ← map_mul]
        congr 1
        exact (Subgroup.mem_center_iff.mp hcen s))
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have h1 := Subgroup.mem_centralizer_iff.mp
      (hle (Subgroup.mem_subgroupOf.mpr hℓ :
        (⟨ℓ, hLY hℓ⟩ : ↥(locLayer Ω z)) ∈ L.subgroupOf (locLayer Ω z)))
      ⟨(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹), hUY⟩ (Subgroup.mem_zpowers _)
    exact congrArg Subtype.val h1
  have hle : locLayer Ω z ≤ Subgroup.centralizer
      ({(g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹)} : Set G) := by
    refine iSup₂_le fun L hL ℓ hℓ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hLcomm L hL ℓ hℓ).symm
  intro y hy
  have hy' := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have e : g₀ * (z * w) * g₀⁻¹ = (g₀ * z * g₀⁻¹) * (g₀ * w * g₀⁻¹) := by group
  rw [e]
  exact hy'.symm

theorem claimA3 (hmf : TwinProductCentral3 tY nY) :
    ∃ ε : G, ∀ g₁ : G, conjSub g₁ K ∈ centralizingMembers Ω {z} → conjSub g₁ K ≠ K →
      conjSub g₁ K ≠ T → g₁ * (z * w) * g₁⁻¹ = ε := by
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member hFT.commK hFT.commT
  obtain ⟨g₀, rfl⟩ := hFT.trans J hJ.1
  refine ⟨g₀ * (z * w) * g₀⁻¹, fun g₁ h1 h1K h1T => ?_⟩
  obtain ⟨y, hyY, hy⟩ := c.link_big hFT.K_mem hFT.T_mem hFT.hKT hFT.commK hFT.commT hJ hJK hJT
    h1 h1K h1T
  have hconj : conjSub (y * g₀) K = conjSub g₁ K := by
    rw [conjSub_mul]
    exact hy
  have hu := u_central3 c hFT hcls hclsT hmf hJ hJK hJT y hyY
  rw [← hFT.conj_zw_eq hconj]
  calc y * g₀ * (z * w) * (y * g₀)⁻¹ = y * (g₀ * (z * w) * g₀⁻¹) * y⁻¹ := by group
    _ = (g₀ * (z * w) * g₀⁻¹ * y) * y⁻¹ := by rw [← hu]
    _ = g₀ * (z * w) * g₀⁻¹ := by group

omit hcls hclsT in
theorem exists_member3 : ∃ g₀ : G, conjSub g₀ K ∈ centralizingMembers Ω {z} ∧
    conjSub g₀ K ≠ K ∧ conjSub g₀ K ≠ T := by
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member hFT.commK hFT.commT
  obtain ⟨g₀, rfl⟩ := hFT.trans J hJ.1
  exact ⟨g₀, hJ, hJK, hJT⟩

end Core

end CFSG.ClassicalInvolution.Q3.Q3TIV
