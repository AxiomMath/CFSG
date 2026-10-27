module

public import CFSG.ClassicalInvolution.Asc77.AscT7EC24

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7X

section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

structure Frame24 (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (W : Subgroup G) : Type where
  c : Thompson.Ctx p f Ω W
  F : T7E.Frame4 Ω W
  φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)
  hφ : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (φ x).IsSwap
  hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ'
  hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ
  hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ
  x₁ : G
  x₂ : G
  x₃ : G
  m : ℕ
  hm : 0 < m
  h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W
  h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W
  h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W
  r₁ : F.ρ.r * x₁ * F.ρ.r⁻¹ = x₁⁻¹
  r₂ : F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂
  r₃ : F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁
  t₁ : F.ρ'.r * x₁ * F.ρ'.r⁻¹ = x₁
  t₂ : F.ρ'.r * x₂ * F.ρ'.r⁻¹ = x₂⁻¹
  t₃ : F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂
  s₁ : F.ρ₃.r * x₁ * F.ρ₃.r⁻¹ = x₁ * x₃
  s₂ : F.ρ₃.r * x₂ * F.ρ₃.r⁻¹ = x₂ * x₃
  s₃ : F.ρ₃.r * x₃ * F.ρ₃.r⁻¹ = x₃⁻¹
  o₁ : orderOf x₁ = 4 * m
  o₂ : orderOf x₂ = 4 * m
  o₃ : orderOf x₃ = 4 * m
  z₁ : x₁ ^ (2 * m) = F.z
  z₂ : x₂ ^ (2 * m) = F.z
  z₃ : x₃ ^ (2 * m) = F.j
  hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G)

theorem exists_frame24 [IsSimpleGroup G] {K K' : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) :
    ∃ D : Frame24 p f Ω W, D.F.ρ.K = K ∧ D.F.ρ'.K = K' ∧ D.F.ρ.R = R ∧ D.F.ρ'.R = R' ∧
      D.F.z = z := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hW : W ∈ WSet Ω := hd.hW
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hd.hR'.1 hd.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR.1 hd.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR'.1 hd.hR'.2.2
  obtain ⟨e, F, he, hFK, hFK', hFR, hFR', hFz, hab, hcomm, hac, -⟩ :=
    T7E.exists_frame4_of_sylow hs hW hd.hS4 hRsyl hR'syl hRD hR'D
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  refine ⟨{
    c := c, F := F, φ := e, hφ := he, hab := hab, hcomm := hcomm, hac := hac,
    x₁ := x₁, x₂ := x₂, x₃ := x₃, m := m, hm := hm, h₁ := h₁, h₂ := h₂, h₃ := h₃,
    r₁ := r₁, r₂ := r₂, r₃ := r₃, t₁ := t₁, t₂ := t₂, t₃ := t₃, s₁ := s₁, s₂ := s₂, s₃ := s₃,
    o₁ := o₁, o₂ := o₂, o₃ := o₃, z₁ := z₁, z₂ := z₂, z₃ := z₃,
    hgen := F.W_le_closure c he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃ },
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals assumption

end Frame

end T7X

end CFSG.ClassicalInvolution.Asc77
