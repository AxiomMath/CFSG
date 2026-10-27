module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23PfSetup
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner

namespace Perp23

namespace Two

abbrev Fr4 {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (W : Subgroup Y) : Type :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4 Ω W

structure TwoFrame {Y : Type} [Group Y] [Finite Y] (Ω : Set (Subgroup Y)) (W K K' : Subgroup Y)
    (t : Y) where
  F : Fr4 Ω W
  e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)
  he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap
  hρK : F.ρ.K = K
  hρ'K : F.ρ'.K = K'
  hzt : F.z = t
  S₀ : Sylow 2 Y
  hWS : W ≤ (S₀ : Subgroup Y)
  hρS : F.ρ.R ≤ (S₀ : Subgroup Y)
  hρ'S : F.ρ'.R ≤ (S₀ : Subgroup Y)
  hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ'
  hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ
  hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ
  x₁ : Y
  x₂ : Y
  x₃ : Y
  m : ℕ
  hm : 0 < m
  h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W
  h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W
  h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W
  o₁ : orderOf x₁ = 4 * m
  o₂ : orderOf x₂ = 4 * m
  o₃ : orderOf x₃ = 4 * m
  z₁ : x₁ ^ (2 * m) = t
  z₂ : x₂ ^ (2 * m) = t
  z₃ : x₃ ^ (2 * m) = F.j
  r₁ : F.ρ.r * x₁ * F.ρ.r⁻¹ = x₁⁻¹
  r₂ : F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂
  r₃ : F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁
  t₁ : F.ρ'.r * x₁ * F.ρ'.r⁻¹ = x₁
  t₂ : F.ρ'.r * x₂ * F.ρ'.r⁻¹ = x₂⁻¹
  t₃ : F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂
  s₁ : F.ρ₃.r * x₁ * F.ρ₃.r⁻¹ = x₁ * x₃
  s₂ : F.ρ₃.r * x₂ * F.ρ₃.r⁻¹ = x₂ * x₃
  s₃ : F.ρ₃.r * x₃ * F.ρ₃.r⁻¹ = x₃⁻¹

section Exists

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_twoFrame (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW : t ∈ W)
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W) :
    ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R ∧
      Nonempty (TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set K := tightCore R with hKdef
  obtain ⟨K', hK', hne⟩ := h.core.twin
  refine ⟨K', hK', hne, ?_⟩
  have hs : CFSG.ClassicalInvolution.T7F25.Asc77.Hyp23Setting Ω K K' t :=
    (h.hyp23 h2 hK' hne).setting
  have hst := hs.stand
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K t := hs.hz
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hP : Q3CL.PartIHypG Ω := h.partIHypG
  haveI : Fact (Q3CL.ClassicalClause Ω) := ⟨h.partIHypG.cls⟩
  have c : Q3CL.Thompson.Ctx Ω W :=
    CFSG.ClassicalInvolution.T7F25.Asc77.T7D.ctx_of_stand hst hW
  obtain ⟨e, he⟩ :=
    TwinPerp23.exists_swap_equiv hP hW hK hst.trans hz hs.hK' hs.hne hs.perp hS4
  obtain ⟨S₀, R₁, R₁', hWS, hRsyl, hR'syl, hRS, hR'S⟩ :=
    CFSG.ClassicalInvolution.T7F25.Asc77.T7D.exists_sylow_frame hs hW htW
  have hRD : R₁ ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : R₁' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK'Ω hR'syl) hR'S
  obtain ⟨ρ, hρK, hρR⟩ :=
    CFSG.ClassicalInvolution.T7F25.Asc77.T7D.exists_rep hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, hρ'R⟩ :=
    CFSG.ClassicalInvolution.T7F25.Asc77.T7D.exists_rep hΩ hW hK'Ω hR'syl hR'D
  have hzρ : IsUniqueInvolution ρ.K t := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K t := by rw [hρ'K]; exact hz'
  have hne' : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne'.symm hcomm.symm
  have hab : T7D.imgQ ρ ≠ T7D.imgQ ρ' := fun h =>
    hne' (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := Subtype.ext hcomm
  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ :=
    S4.exists_third he (T7D.imgQ_mem ρ) (T7D.imgQ_mem ρ') hab hcommQ
  obtain ⟨ρ₃, hρ₃⟩ := Thompson.exists_rep_of_mem_muDelta hc₃Δ
  have hc₃ : T7D.imgQ ρ₃ = c₃ := Subtype.ext hρ₃
  have hac' : T7D.imgQ ρ * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ := by rw [hc₃]; exact hac
  have hbc' : T7D.imgQ ρ' * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ' := by rw [hc₃]; exact hbc
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac' (by
    have h1 : T7D.imgQ ρ = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ ρ₃ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc' (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ' ρ₃ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ ρ₃.hK
  let F : Fr4 Ω W :=
    ⟨ρ, ρ', ρ₃, t, j, hzρ, hzρ', hj, hρnbr, hρnbr', hne₁, hne₂,
      fun h => hac' (Subtype.ext (c.comm_of_omega ρ ρ₃ h)),
      fun h => hbc' (Subtype.ext (c.comm_of_omega ρ' ρ₃ h)),
      fun h => hac' (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm),
      fun h => hbc' (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)⟩
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  exact ⟨⟨F, e, he, hρK, hρ'K, rfl, S₀, hWS, hρR ▸ hRS, hρ'R ▸ hR'S, hab, hcommQ, hac', x₁, x₂,
    x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩⟩

end Exists

end Two

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
