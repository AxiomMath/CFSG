module

public import CFSG.ClassicalInvolution.Asc77.AscT7XLat
import CFSG.ClassicalInvolution.Asc77.AscT7HC4
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement

namespace T7X

section Rep

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem rep_le_centralizer (c : Thompson.Ctx p f Ω W) (σ : Thompson.Rep Ω W) {ε : G}
    (hε : ε ∈ W) (h : σ.r * ε * σ.r⁻¹ = ε) : σ.R ≤ Subgroup.centralizer ({ε} : Set G) := by
  intro ρ hρ
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hWab := Thompson.commutes_of_mem_WSet c.hp c.hq c.hΩ c.hW
  by_cases hρW : ρ ∈ W
  · exact hWab ρ hρW ε hε
  · have hw : σ.r⁻¹ * ρ ∈ W :=
      Thompson.D_inv_mul_mem c.hp c.hq c.hΩ c.hW σ.hR σ.hr hρ σ.hrW hρW
    have hρeq : ρ = σ.r * (σ.r⁻¹ * ρ) := by group
    have h1 : (σ.r⁻¹ * ρ) * ε = ε * (σ.r⁻¹ * ρ) := hWab _ hw ε hε
    calc ρ * ε = σ.r * ((σ.r⁻¹ * ρ) * ε) := by rw [← mul_assoc, ← hρeq]
      _ = σ.r * (ε * (σ.r⁻¹ * ρ)) := by rw [h1]
      _ = (σ.r * ε * σ.r⁻¹) * ρ := by group
      _ = ε * ρ := by rw [h]

end Rep

namespace Frame24

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G} (D : Frame24 p f Ω W)

omit [Finite G] in
theorem x₂_pow_eq_z {c : ℕ} (hc : 2 * c = D.m) : D.x₂ ^ (-(4 * (c : ℤ))) = D.F.z := by
  have hm : (D.m : ℤ) = 2 * (c : ℤ) := by exact_mod_cast hc.symm
  have h2 : D.x₂ ^ (-(4 * (c : ℤ))) = D.x₂ ^ (2 * (D.m : ℤ)) := by
    refine D.zpow_shift D.pow₂ (a := -(4 * (c : ℤ))) (b := 2 * (D.m : ℤ)) ?_
    rw [hm]
    ring
  rw [h2, show 2 * (D.m : ℤ) = ((2 * D.m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, D.z₂]

theorem eEl_t_eq {c : ℕ} (hc : 2 * c = D.m) :
    D.F.ρ'.r * D.eEl c * D.F.ρ'.r⁻¹ = D.eEl c * D.F.z := by
  rw [D.eEl_t c, D.x₂_pow_eq_z hc]

theorem eEl_cent_R {c : ℕ} : D.F.ρ.R ≤ Subgroup.centralizer ({D.eEl c} : Set G) :=
  rep_le_centralizer D.c D.F.ρ (D.eEl_mem c) (D.eEl_r c)

theorem eEl_cent_R₃ {c : ℕ} : D.F.ρ₃.R ≤ Subgroup.centralizer ({D.eEl c} : Set G) :=
  rep_le_centralizer D.c D.F.ρ₃ (D.eEl_mem c) (D.eEl_s c)


theorem eEl_isPGroup {c : ℕ} (hc : 2 * c = D.m)
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    IsPGroup 2 ↥(Subgroup.zpowers (D.eEl c)) :=
  isPGroup_zpowers_of_sq_eq_one (D.eEl_sq hc hZ)

theorem K_mem_tq {c : ℕ} (hc : 2 * c = D.m)
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    D.F.ρ.K ∈ tqMembers Ω (D.eEl c) :=
  (mem_tqMembers_iff_exists_sylow D.c.hp D.c.hq D.c.hΩ (D.eEl_isPGroup hc hZ)).mpr
    ⟨D.F.ρ.hK, D.F.ρ.R, D.F.ρ.hRK, D.eEl_cent_R⟩

theorem J_mem_tq {c : ℕ} (hc : 2 * c = D.m)
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    D.F.ρ₃.K ∈ tqMembers Ω (D.eEl c) :=
  (mem_tqMembers_iff_exists_sylow D.c.hp D.c.hq D.c.hΩ (D.eEl_isPGroup hc hZ)).mpr
    ⟨D.F.ρ₃.hK, D.F.ρ₃.R, D.F.ρ₃.hRK, D.eEl_cent_R₃⟩

theorem K'_not_mem_tq {c : ℕ} (hc : 2 * c = D.m)
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    D.F.ρ'.K ∉ tqMembers Ω (D.eEl c) := by
  intro h
  have hc2 := D.eEl_isPGroup hc hZ
  obtain ⟨hK'Ω, R'', hsyl, hcent⟩ :=
    (mem_tqMembers_iff_exists_sylow D.c.hp D.c.hq D.c.hΩ hc2).mp h
  have htriv : D.eEl c ∈ Balance.Bootstrap.trivialOnQuot D.F.ρ'.K :=
    (mem_trivialOnQuot_iff_exists_sylow D.c.hp D.c.hq D.c.hΩ hc2 hK'Ω).mpr ⟨R'', hsyl, hcent⟩
  have hr : D.F.ρ'.r ∈ D.F.ρ'.K := D.F.ρ'.hRK.1 D.F.ρ'.hr
  have h1 : ⁅D.eEl c, D.F.ρ'.r⁆ ∈ Balance.oddCoreIn D.F.ρ'.K := htriv.2 _ hr
  have he2 := D.eEl_sq hc hZ
  have hei : (D.eEl c)⁻¹ = D.eEl c := inv_eq_of_mul_eq_one_right he2
  have h2 : ⁅D.eEl c, D.F.ρ'.r⁆ = D.F.z := by
    have h3 := D.eEl_t_eq hc
    calc ⁅D.eEl c, D.F.ρ'.r⁆ = D.eEl c * (D.F.ρ'.r * D.eEl c * D.F.ρ'.r⁻¹) := by
          rw [commutatorElement_def, hei]
          group
      _ = (D.eEl c * D.eEl c) * D.F.z := by rw [h3]; group
      _ = D.F.z := by rw [he2, one_mul]
  rw [h2] at h1
  exact D.F.hz'.ne_one (T7H.eq_one_of_mem_odd_of_sq (Balance.odd_card_oddCoreIn _) h1
    D.F.hz'.sq)

end Frame24

end T7X

end CFSG.ClassicalInvolution.Asc77
