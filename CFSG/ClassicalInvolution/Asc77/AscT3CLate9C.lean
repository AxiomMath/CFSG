module

import CFSG.ClassicalInvolution.Asc77.AscT3CLate9CEng
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexMain
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateSwap

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

private theorem Std20.late_toG (d : Std20 p f K K' J S R R' W V z t) :
    Std20G K K' J S R R' W V z t :=
  { toStd20F :=
      { d with
        hyp := d.late_hΩ
        late_ne_inv := d.late_ne_inv
        late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.branch.odd d.hyp d.viol.star d.viol.hzJ
        late_card2 := fun hU hK hR =>
          Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hU hK hR }
    late_hWc := d.late_hWc
    late_t_mem_W := d.late_t_mem_W
    late_z_mem_W := d.late_z_mem_W
    late_hW := d.late_hW
    late_JW := d.late_JW
    late_exists_swap := d.late_exists_swap
    late_swap_data := fun hu huK => d.late_swap_data hu huK }

theorem Std20.late_S_act_z (d : Std20 p f K K' J S R R' W V z t) {g : G}
    (hg : g ∈ (S : Subgroup G)) : g * z * g⁻¹ = z := by
  exact d.late_toG.late_S_act_z hg

theorem Std20.late_S_act_t (d : Std20 p f K K' J S R R' W V z t) {g : G}
    (hg : g ∈ (S : Subgroup G)) : g * t * g⁻¹ = t ∨ g * t * g⁻¹ = z * t := by
  exact d.late_toG.late_S_act_t hg

theorem Std20.late_members_of_inv (d : Std20 p f K K' J S R R' W V z t) {m e : G}
    (hme : m * z * m⁻¹ = e) {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K)
    (hLe : IsUniqueInvolution L e) : L = conjSub m K ∨ L = conjSub m K' := by
  exact d.late_toG.late_members_of_inv hme hL hLe

theorem Std20.late_member_data (d : Std20 p f K K' J S R R' W V z t) (m : G) :
    conjSub m K ∈ CoreAssembly.conjClass K ∧ conjSub m K' ∈ CoreAssembly.conjClass K ∧
      conjSub m K ≠ conjSub m K' ∧ IsUniqueInvolution (conjSub m K) (m * z * m⁻¹) ∧
      IsUniqueInvolution (conjSub m K') (m * z * m⁻¹) := by
  exact d.late_toG.late_member_data m

end Std

section Pure

variable {G : Type} [Group G]

theorem late_klein_trich {z t : G} (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : z * t = t * z)
    {a ε₁ ε₂ : G} (ha : a = z ∨ a = t ∨ a = z * t)
    (h₁ : ε₁ = 1 ∨ ε₁ = z ∨ ε₁ = t ∨ ε₁ = z * t) (h₂ : ε₂ = 1 ∨ ε₂ = z ∨ ε₂ = t ∨ ε₂ = z * t)
    (h₂1 : ε₂ ≠ 1) (h₂a : ε₂ ≠ a) (h₁1 : ε₁ ≠ 1) (h₁a : ε₁ ≠ a) :
    ε₁ = ε₂ ∨ ε₁ = ε₂ * a := by
  exact late_klein_trichE hz2 ht2 hzt ha h₁ h₂ h₂1 h₂a h₁1 h₁a

end Pure

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20.late_two_lines (d : Std20 p f K K' J S R R' W V z t) {a₀ α b₁ b₂ : G}
    (ha₀ : a₀ ≠ 1) (ha₀2 : a₀ * a₀ = 1) (hα : α ∈ W) (hb₁ : b₁ ∈ W) (hb₂ : b₂ ∈ W)
    (hαa : α * α = a₀) (hb₁a : b₁ * b₁ = a₀) (hb₂a : b₂ * b₂ = a₀)
    (hne : Subgroup.zpowers b₁ ≠ Subgroup.zpowers b₂) :
    Subgroup.zpowers α = Subgroup.zpowers b₁ ∨ Subgroup.zpowers α = Subgroup.zpowers b₂ := by
  exact d.late_toG.late_two_lines d.late_zt_comm ha₀ ha₀2 hα hb₁ hb₂ hαa hb₁a hb₂a hne

theorem Std20.late_swap_J (d : Std20 p f K K' J S R R' W V z t) {σ ρ : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσt : σ * t * σ⁻¹ = t) (hρ : ρ ∈ R)
    (hσJ : conjSub σ (conjSub ρ J) = conjSub ρ J) : False := by
  exact d.late_toG.late_swap_J hσ hσK hσt hρ hσJ

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
