module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapSylowT

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

theorem false_of_symSym [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hC : CentData z ι) (hN : NoSwapConj z ι) {x₁ : G}
    {π₁ : ↥(centralizer ({x₁} : Set G)) →* Perm (Fin 10)} (hOS₁ : OneSided z ι x₁ π₁)
    {ι' : Perm (Fin 10) →* G} (h1 : ∀ σ, sign σ = 1 → ι' σ = ι σ)
    (h2 : ∀ σ, sign σ = -1 → ι' σ = z * ι σ) {x₂ : G}
    {π₂ : ↥(centralizer ({x₂} : Set G)) →* Perm (Fin 10)} (hOS₂ : OneSided z ι' x₂ π₂) :
    False := by
  have hC' : CentData z ι' := hC.of_twist h1 h2
  obtain ⟨κ₁, hκ₁⟩ := exists_retraction hC hOS₁
  obtain ⟨κ₂, hκ₂⟩ := exists_retraction hC' hOS₂
  obtain ⟨Q, hQ⟩ := exists_goodQ
  have hTidx : ¬ 2 ∣ (Tgrp z ι Q).index :=
    not_two_dvd_index_Tgrp hC hN hOS₁ hκ₁ h1 h2 hOS₂ hκ₂ hQ
  have hconj : ∀ g : G, g⁻¹ * z * g ∉ Q.map ι := by
    intro g hg
    obtain ⟨q, _hq, hqq⟩ := Subgroup.mem_map.1 hg
    exact not_isConj_z_ι hC hN hOS₁ hκ₁ q
      (isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]; exact hqq.symm⟩)
  exact false_of_thompson_involution hnonab (T := Tgrp z ι Q) (U := Q.map ι)
    (Tgrp_isPGroup hC hQ.pgroup) hTidx (map_le_Tgrp Q) (relIndex_map_Tgrp hC Q)
    hC.order (z_mem_Tgrp Q) (z_notMem_map hC Q) hconj

end CFSG.OddStandard.AltStdSec.SwapPattern
