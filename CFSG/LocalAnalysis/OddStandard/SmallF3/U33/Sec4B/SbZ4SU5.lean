module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SU1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SU4

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem isPGroup_U : IsPGroup 2 (ctxU t tau x₁ x₂ lam) := hp.U_sylow.2.1

theorem card_U_lt : Nat.card (ctxU t tau x₁ x₂ lam) < 2 ^ 11 := by
  have h1 : Nat.card (ctxU t tau x₁ x₂ lam) ∣ Nat.card (ctxM t tau x₁ x₂) :=
    Subgroup.card_dvd_of_le hp.U_sylow.1
  rw [hp.card_M] at h1
  have h2 := Nat.le_of_dvd (by norm_num) h1
  omega

end Z4Pre

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem U_not_sylow_L (hglob : Sec4Glob G)
    (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹)
    {V' : Subgroup G} {v₁ v₂ : G} (hV : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂) :
    ¬ IsSylowIn 2 (ctxU t tau x₁ x₂ lam) (ctxNQ t tau x₁ x₂ rho) :=
  z4_not_isSylowIn_of_normalizes hg.toZ4Pre.isPGroup_U
    (fun _ hn => hg.mem_ctxNQ_of_normalizes_U htau hV hn) hg.toZ4Pre.card_U_lt hglob.dvd

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
