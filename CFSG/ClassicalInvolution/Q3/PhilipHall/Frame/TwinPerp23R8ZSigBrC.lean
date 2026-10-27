module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigN

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance


section BranchC

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g x : Y}

namespace ZCtx

variable (H : ZCtx n Y R S t K' W u e g x)
include H

theorem centralizes_E_of_odd_centralizes_twin {z : Y} (hzC : z * e = e * z) {m : ℕ}
    (hzm : z ^ 3 ^ m = 1) (hzK' : ∀ b ∈ K', z * b = b * z) :
    ∀ y ∈ rLayer (Om R) e, z * y = y * z := by
  obtain ⟨f, hfinj, hfrange, hlab, hκ⟩ := H.hat.labels
  have hEn : ∀ g ∈ Subgroup.centralizer ({e} : Set Y), ∀ y ∈ rLayer (Om R) e,
      g * y * g⁻¹ ∈ rLayer (Om R) e := by
    intro g hg y hy
    have := conj_mem_conjSub (n := g) hy
    rwa [H.hat.normal g hg] at this
  have hzC' : z ∈ Subgroup.centralizer ({e} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr hzC
  obtain ⟨w, hw⟩ := hκ z hzC'
  obtain ⟨w', hw', hodd⟩ := exists_odd_acts hfrange hEn hzC' hw hzm
  obtain ⟨α, hα, b, hb⟩ := hlab.label K' H.cfg.std.hK'.1 H.K'_le_E
  have hw'c : ∀ a ∈ memAt α hα b, w' * a = a * w' := by
    intro a ha
    rw [← hb] at ha
    obtain ⟨⟨b₀, hb₀E⟩, hb₀, rfl⟩ := ha
    have hb₀K' : b₀ ∈ K' := Subgroup.mem_subgroupOf.mp hb₀
    have hx' : z * b₀ * z⁻¹ ∈ rLayer (Om R) e := hEn z hzC' b₀ hb₀E
    have h1 := hw' b₀ hb₀E hx'
    have h2 : (⟨z * b₀ * z⁻¹, hx'⟩ : ↥(rLayer (Om R) e)) = ⟨b₀, hb₀E⟩ := by
      apply Subtype.ext
      show z * b₀ * z⁻¹ = b₀
      rw [hzK' b₀ hb₀K']
      group
    rw [h2] at h1
    calc w' * f ⟨b₀, hb₀E⟩ = (w' * f ⟨b₀, hb₀E⟩ * w'⁻¹) * w' := by group
      _ = f ⟨b₀, hb₀E⟩ * w' := by rw [← h1]
  have hw1 : w' = 1 := mFL_holds α hα b w' hodd hw'c
  subst hw1
  intro y hy
  have hy' : z * y * z⁻¹ ∈ rLayer (Om R) e := hEn z hzC' y hy
  have h1 := hw' y hy hy'
  rw [one_mul, inv_one, mul_one] at h1
  have h2 : z * y * z⁻¹ = y := congrArg Subtype.val (hfinj h1)
  calc z * y = (z * y * z⁻¹) * z := by group
    _ = y * z := by rw [h2]

theorem exists_three_elt_of_longFund
    (h : LongFundSet3 (secImage (p23XE R e x) (tightCore R))
      (secInv (p23XE R e x) ⟨t, H.t_mem_N⟩)) :
    ∃ x₀ ∈ p23XE R e x, x₀ * t = t * x₀ ∧ (∃ m : ℕ, x₀ ^ 3 ^ m = 1) ∧
      (∀ b ∈ K', x₀ * b = b * x₀) ∧ ∃ k ∈ tightCore R, x₀ * k ≠ k * x₀ := by
  classical
  set N := p23XE R e x with hN
  have hoc : classicalInvolutionOddCore ↥N ≤ Subgroup.center ↥N := H.oc mFA_holds
  have hNodd := CFSG.ComponentClassification.OddCore.odd_card ↥N
  have hK2 : IsPGroup 2 (tightCore R) := H.two _ (CoreAssembly.mem_conjClass_self _)
  have hK'2 : IsPGroup 2 K' := H.two _ H.cfg.std.hK'.1
  have htc : tightCore (secImage N (tightCore R)) = secImage N (tightCore R) :=
    tightCore_eq_self_of_isPGroup (SectionThmD.isPGroup_secImage hK2)
  obtain ⟨Λ, hΛ, hcomm, -⟩ := h
  rw [htc] at hΛ hcomm
  have hzbar : IsUniqueInvolution (secImage N (tightCore R)) (secInv N ⟨t, H.t_mem_N⟩) :=
    SectionThmD.isUniqueInvolution_secImage H.K_le_N hK2 H.hz
  have hzbar' : IsUniqueInvolution (secImage N K') (secInv N ⟨t, H.t_mem_N⟩) :=
    SectionThmD.isUniqueInvolution_secImage H.K'_le_N hK'2
      (isUniqueInvolution_of_mem_twinSet H.hz H.cfg.std.hK')
  have hmem : secImage N (tightCore R) ∈ twinSet
      (CoreAssembly.conjClass (secImage N (tightCore R))) (secImage N (tightCore R)) :=
    ⟨CoreAssembly.mem_conjClass_self _, _, hzbar, hzbar⟩
  obtain ⟨y, hy, hyK⟩ := H.exists_conj_of_le_Ce H.cfg.std.hK'.1 H.K'_le_Ce
  have hmem' : secImage N K' ∈ twinSet
      (CoreAssembly.conjClass (secImage N (tightCore R))) (secImage N (tightCore R)) := by
    refine ⟨?_, _, hzbar, hzbar'⟩
    exact SectionThmD.mem_secClass_iff.mpr
      ⟨⟨y, (le_sup_left : rLayer (Om R) e ≤ N) hy⟩, by rw [hyK]⟩
  have hne : secImage N (tightCore R) ≠ secImage N K' := fun heq =>
    H.cfg.std.hne (H.eq_of_secImage_eq hoc H.cfg.std.hK'.1 (CoreAssembly.mem_conjClass_self _)
      H.K'_le_N H.K_le_N heq.symm)
  obtain ⟨hKL, hLcl⟩ := hΛ _ hmem
  obtain ⟨hK'L', hL'cl⟩ := hΛ _ hmem'
  have hLL' := hcomm _ hmem _ hmem' hne
  have hK8 : 8 ≤ Nat.card (secImage N (tightCore R)) := by
    rw [SectionThmD.natCard_secImage H.K_le_N hK2, H.card_K]
  obtain ⟨ω, hωL, ⟨k, hωk⟩, q, hqK, hωq⟩ :=
    hLcl.exists_three_elt_moving hKL (SectionThmD.isPGroup_secImage hK2) hK8
  have hωt : ω * secInv N ⟨t, H.t_mem_N⟩ = secInv N ⟨t, H.t_mem_N⟩ * ω :=
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hLcl.subnormal hωL)
  set φ := QuotientGroup.mk' (classicalInvolutionOddCore ↥N) with hφ
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥N) ω
  have htN2 : (⟨t, H.t_mem_N⟩ : ↥N) * ⟨t, H.t_mem_N⟩ = 1 := Subtype.ext H.hz.sq
  obtain ⟨x₁, hx₁φ, ⟨m, hxm⟩, hx₁t⟩ := exists_lift_three φ
    (by rw [hφ, QuotientGroup.ker_mk']; exact hoc) htN2 (k := k) (y := y₀)
    (by rw [hy₀]; exact hωk) (by rw [hy₀]; exact hωt)
  have hωφ : φ x₁ = ω := hx₁φ.trans hy₀
  refine ⟨(x₁ : Y), x₁.2, congrArg Subtype.val hx₁t, ⟨m, by simpa using congrArg Subtype.val hxm⟩,
    ?_, ?_⟩
  ·
    intro b hb
    have hbN : b ∈ N := H.K'_le_N hb
    have hbm : φ ⟨b, hbN⟩ ∈ secImage N K' := ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have hc := hLL' ω hωL _ (hK'L' hbm)
    obtain ⟨k₂, hk₂⟩ := OddQuot.two_elt hK'2 hb
    have hya : (⟨b, hbN⟩ : ↥N) ^ 2 ^ k₂ = 1 := Subtype.ext (by simpa using hk₂)
    exact congrArg Subtype.val
      (AAE7.comm_of_mk_comm hoc hNodd hya (k := x₁) (by rw [hωφ]; exact hc))
  ·
    obtain ⟨kN, hkN, rfl⟩ := hqK
    refine ⟨(kN : Y), Subgroup.mem_subgroupOf.mp hkN, fun hcomm' => hωq ?_⟩
    have h1 : x₁ * kN = kN * x₁ := Subtype.ext hcomm'
    have h2 := congrArg φ h1
    rw [map_mul, map_mul, hωφ] at h2
    exact h2

theorem x0_of_longFund
    (h : LongFundSet3 (secImage (p23XE R e x) (tightCore R))
      (secInv (p23XE R e x) ⟨t, H.t_mem_N⟩)) :
    ∃ x₀ ∈ p23XE R e x, x₀ * t = t * x₀ ∧ IsPGroup 3 (Subgroup.zpowers x₀) ∧
      x₀ * e * x₀⁻¹ ≠ e := by
  obtain ⟨x₀, hx₀N, hx₀t, ⟨m, hx₀m⟩, hx₀K', k, hkK, hk⟩ := H.exists_three_elt_of_longFund h
  refine ⟨x₀, hx₀N, hx₀t, isPGroup_three_zpowers hx₀m, fun hmove => hk ?_⟩
  have hxe : x₀ * e = e * x₀ := by
    calc x₀ * e = (x₀ * e * x₀⁻¹) * x₀ := by group
      _ = e * x₀ := by rw [hmove]
  exact H.centralizes_E_of_odd_centralizes_twin hxe hx₀m hx₀K' k (H.K_le_E hkK)

end ZCtx

end BranchC

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig
