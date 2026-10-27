module

public import CFSG.ClassicalInvolution.Asc77.AscR10Nc
public import CFSG.ClassicalInvolution.Asc77.AscR10Rho
public import CFSG.ClassicalInvolution.Asc77.AscT3SInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}




theorem Std20.r_noConj [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    (h9 : p ^ f ≠ 9) {b : G} (hb : FieldInv20 S K K' W z t b) (g : G) :
    g⁻¹ * b * g ∉ sec20X (CoreAssembly.conjClass K) z K K' := by
  obtain ⟨u, k, hk, hu, huo, hact | hact⟩ := hb.modular
  · exact d.r_noConj_plus c7 c9 h8 h9 hb hk hu huo hact g
  · obtain ⟨ρ, hρKK, hρS, hρ2, hρ1, hρz, hbρ, hb', hplus'⟩ :=
      d.r_exists_plus_rho c7 c9 h8 hb hk hu huo hact
    have hX1 : (1 : G) ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
      (sec20X (CoreAssembly.conjClass K) z K K').one_mem
    obtain ⟨m, hm, hmt⟩ := T3S.exists_conj_of_involutions_sup_mod d.branch.odd d.branch.five
      d.hyp d.late_mem_K d.late_mem_K' d.ne d.viol.hzK d.late_hzK' d.htKK d.viol.hzJ.sq
      d.viol.hzJ.ne_one d.late_ne_inv hρKK hρ2 hρ1 hρz
    obtain ⟨c, -, hcz⟩ := hb.fuse
    have hρzG : ∃ g' : G, ρ = g' * z * g'⁻¹ := ⟨m * c, by
      calc ρ = m * t * m⁻¹ := hmt.symm
        _ = m * (c * z * c⁻¹) * m⁻¹ := by rw [hcz]
        _ = m * c * z * (m * c)⁻¹ := by group⟩
    have hρb' : ρ * (b * ρ) = (b * ρ) * ρ := by
      calc ρ * (b * ρ) = (ρ * b) * ρ := by group
        _ = (b * ρ) * ρ := by rw [← hbρ]
    have hρN : ρ ∈ Subgroup.normalizer (K : Set G) :=
      (c9 h8).2.2 ρ hρS (by rw [hρ2]; exact hX1)
    obtain ⟨c₁, hc₁b, hc₁⟩ := d.r_fusion_S c7 c9 h8 h9 hb' hk hu huo hplus' hρ2 hρb' hρN hρzG
    have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
    obtain ⟨v₀, -, -, -, huz, -⟩ := d.v_W_gen hu huo
    have hb'sq := hb'.sq
    have hbρρ : b * ρ * ρ = b := by
      calc b * ρ * ρ = b * (ρ * ρ) := by group
        _ = b := by rw [hρ2, mul_one]
    have hu1 : (b * ρ) * u * (b * ρ)⁻¹ = z * u := by
      rw [hplus' u huKW, zpow_add_one]
      have e : ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) := by push_cast; ring
      rw [e, zpow_natCast, huz]
    have hub : u * (b * ρ) * u⁻¹ = (b * ρ) * z := by
      have hbi : (b * ρ)⁻¹ = b * ρ := inv_eq_of_mul_eq_one_right hb'sq
      rw [hbi] at hu1
      calc u * (b * ρ) * u⁻¹ = (b * ρ) * ((b * ρ)⁻¹ * u * (b * ρ)) * u⁻¹ := by group
        _ = (b * ρ) * ((b * ρ) * u * (b * ρ)⁻¹) * u⁻¹ := by rw [hbi]
        _ = (b * ρ) * (z * u) * u⁻¹ := by rw [hbi] at *; rw [hu1]
        _ = (b * ρ) * z := by group
    have hy : b = (c₁ * u) * (b * ρ) * (c₁ * u)⁻¹ := by
      calc b = (b * ρ) * ρ := hbρρ.symm
        _ = (b * ρ) * (c₁ * z * c₁⁻¹) := by rw [← hc₁]
        _ = c₁ * ((b * ρ) * z) * c₁⁻¹ := by
          calc (b * ρ) * (c₁ * z * c₁⁻¹) = ((b * ρ) * c₁) * z * c₁⁻¹ := by group
            _ = (c₁ * (b * ρ)) * z * c₁⁻¹ := by rw [← hc₁b]
            _ = c₁ * ((b * ρ) * z) * c₁⁻¹ := by group
        _ = c₁ * (u * (b * ρ) * u⁻¹) * c₁⁻¹ := by rw [hub]
        _ = (c₁ * u) * (b * ρ) * (c₁ * u)⁻¹ := by group
    intro ha'
    refine d.r_noConj_plus c7 c9 h8 h9 hb' hk hu huo hplus' ((c₁ * u)⁻¹ * g) ?_
    have e : ((c₁ * u)⁻¹ * g)⁻¹ * (b * ρ) * ((c₁ * u)⁻¹ * g) = g⁻¹ * b * g := by
      conv_rhs => rw [hy]
      group
    rw [e]
    exact ha'

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
