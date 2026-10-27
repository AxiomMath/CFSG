module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PI1XAux2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6p_B1p_mem_X (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {b : ↥(omegaProj hQ)} (hb : b ∈ ffB1p hQ fr) :
    b ∈ twoPrimeRes (twoRes (ffFix hQ h2 (ffTs fr))) :=
  ffOutFF6PI1X_B1p_mem_X hQ hdim hsgn h2 fr hb

theorem ff6p_hat_mem_X (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {τ : Equiv.Perm (Fin 5)} (hτ : τ ^ 2 = 1)
    (hs : Equiv.Perm.sign τ = 1) :
    omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩ ∈
      twoPrimeRes (twoRes (ffFix hQ h2 (ffTs fr))) :=
  ffOutFF6PI1X_hat_mem_X hQ hdim hsgn h2 fr hτ hs

theorem ff6p_cent_X (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    (hB : ∀ b ∈ ffB1p hQ fr, z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z)
    (hτ : ∀ τ : Equiv.Perm (Fin 5), τ ^ 2 = 1 → Equiv.Perm.sign τ = 1 →
      z * ffOmegaToSim hQ (omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩) =
        ffOmegaToSim hQ (omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩) * z) :
    z = 1 ∨ z = ffTs fr :=
  ffOutFF6PI1X_cent_X hQ hdim hsgn h2 fr hB hτ

end CFSG.OddStandard.SmallF3.Omega
