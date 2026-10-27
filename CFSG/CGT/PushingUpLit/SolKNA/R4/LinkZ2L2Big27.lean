module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big16
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big26
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big29

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section L1

theorem z2BigModelL1_holds (r : ℕ) :
    4 ≤ r → ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), Z2BigLinkModel r X p f →
      ∀ (Q : Subgroup X) (_ : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (H : Subgroup (MulAut X)),
        IsPGroup 2 ↥H → (∃ S : Subgroup X, IsSylow2In S ⊤ ∧
          S.map (MulAut.conj : X →* MulAut X) ≤ H) →
          ∀ y ∈ H, y ∉ innGrp X → ∃ s ∈ H ⊓ innGrp X, 2 ^ padicValNat 2 f < orderOf (y * s) := by
  intro hr X _ _ p f hL Q eQ H hH hSyl y hy _
  obtain ⟨S, hS, hSH⟩ := hSyl
  obtain ⟨Q', eQ', hQ'S⟩ := exists_quat_le_sylow Q eQ hS
  obtain ⟨F, _, _, hF, h4, hp, E, hz⟩ :=
    exists_normalized_emb hL.simple hL.odd hL.even hL.model
      (quatInvolution_sq hr eQ') (quatInvolution_ne_one hr eQ')
      (quatInvolution_mem_fstar hL.index hr eQ')
  haveI : Fact p.Prime := ⟨hp⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at h4
    omega
  obtain ⟨σ₀, hσ₀1, hσ₀2, hq⟩ := exists_frob_half hF hL.even hf0
  let φ : X →* PGammaL2 F := E.ρ.comp (MulAut.conj : X →* MulAut X)
  have hφ : Function.Injective φ := E.inj.comp E.conjInj
  have hfix : ∀ h ∈ H, h (quatInvolution r eQ') = quatInvolution r eQ' :=
    fix_quatInvolution E eQ' hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq hS hQ'S hSH hH
  have hHM' : H.map E.ρ ≤ monGrp F := by
    rintro g ⟨h, hh, rfl⟩
    exact isMon_rho_of_fix E eQ' hF hL.odd h4 hz (hfix h hh)
  have hSH' : S.map φ ≤ H.map E.ρ := by
    rintro g ⟨s, hs, rfl⟩
    exact Subgroup.mem_map_of_mem E.ρ
      (hSH (Subgroup.mem_map_of_mem (MulAut.conj : X →* MulAut X) hs))
  have hN1 : ∀ g : PGammaL2 F, g.right = 1 → g.left ∈ pslRange F → g ∈ φ.range := by
    intro g hg hgl
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp hgl
    obtain ⟨n, _, hn⟩ := E.onto γ
    refine ⟨n, ?_⟩
    rw [TL4.MF163.eq_inl_of_right_eq_one hg, ← hγ]
    change E.ρ (MulAut.conj n) = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL γ)
    exact hn
  haveI : (φ.range).Normal := normal_of_psl_le hF hL.odd h4 φ.range hN1
  have hN2 : ∃ y : Fˣ, ¬ IsSquare y ∧ (gD y σ₀ ∈ φ.range ∨ gA y σ₀ ∈ φ.range) := by
    have h2 : (2 : F) ≠ 0 := (field_facts hp hL.odd hF h4).2
    have hcard : Nat.card Fˣ = p ^ (f / 2) * p ^ (f / 2) - 1 :=
      card_units_eq_sq_sub_one hF hL.even
    obtain ⟨x₀, y₀, hx₀, _, hcase⟩ :=
      quat_structure E eQ' hF hL.odd h4 hL.index hr hz hσ₀1 hσ₀2
    let b : X := ((eQ'.symm (QuaternionGroup.xa 0) : ↥Q') : X)
    have hbq : qEmb E eQ' (QuaternionGroup.xa 0) = φ b := by
      rw [qEmb_apply]
      rfl
    have hbmem : φ b ∈ φ.range := ⟨b, rfl⟩
    rcases hcase with ⟨hBd, hxd, hyd⟩ | ⟨hBa, hxa, hya⟩
    · refine ⟨y₀, not_isSquare_y_diag h2 hq hcard hr hx₀ hxd hyd, Or.inl ?_⟩
      rw [← hBd, hbq]
      exact hbmem
    · refine ⟨y₀, not_isSquare_y_anti h2 hq hcard hr hx₀ hxa hya, Or.inr ?_⟩
      rw [← hBa, hbq]
      exact hbmem
  have hy' : E.ρ y ∈ H.map E.ρ := Subgroup.mem_map_of_mem E.ρ hy
  obtain ⟨s', hs', hord⟩ :=
    l1_gamma hF hL.odd hL.even hr hL.arith hσ₀1 hσ₀2 hq φ.range hN1 hN2
      (hH.map E.ρ) hHM' hSH' (isSylow2In_map_of_injective φ hφ hS) hy'
  obtain ⟨s, hs, rfl⟩ := hs'
  refine ⟨MulAut.conj s, ⟨hSH (Subgroup.mem_map_of_mem (MulAut.conj : X →* MulAut X) hs),
    ⟨s, rfl⟩⟩, ?_⟩
  have horder : orderOf (y * MulAut.conj s) = orderOf (E.ρ y * φ s) := by
    have h1 : E.ρ y * φ s = E.ρ (y * MulAut.conj s) := by
      change E.ρ y * E.ρ (MulAut.conj s) = E.ρ (y * MulAut.conj s)
      rw [map_mul]
    rw [h1]
    exact (orderOf_injective E.ρ E.inj (y * MulAut.conj s)).symm
  rwa [horder]

end L1

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
