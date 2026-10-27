module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import Certificates.Certificate26081

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut

theorem cd_pow (g : AutA6) (n : ℕ) : cd (g ^ n) = Core.cpow (cd g) n := by
  unfold cd
  rw [← code_pow]
  rfl

theorem autA6_pow_eight (hD : A6OrdData) (g : AutA6) (h : g ^ 16 = 1) : g ^ 8 = 1 := by
  have hc : cd g ∈ Core.autL := code_mem_autL g.2
  have h1 : Core.cpow (cd g) 16 = Core.cid := by rw [← cd_pow, h, cd_one]
  have h2 := (hD (cd g) hc).1 h1
  apply cd_injective
  rw [cd_pow, h2, cd_one]

theorem autA6_eq_pow (hD : A6OrdData) (g : AutA6) (h8 : g ^ 8 = 1) (h4 : g ^ 4 ≠ 1) (d : AutA6)
    (hd : d * g = g * d) : ∃ k < 8, d = g ^ k := by
  have hc : cd g ∈ Core.autL := code_mem_autL g.2
  have hdc : cd d ∈ Core.autL := code_mem_autL d.2
  have e8 : Core.cpow (cd g) 8 = Core.cid := by rw [← cd_pow, h8, cd_one]
  have e4 : Core.cpow (cd g) 4 ≠ Core.cid := by
    rw [← cd_pow, ← cd_one]
    intro h
    exact h4 (cd_injective h)
  have ecomm : Core.cmul (cd d) (cd g) = Core.cmul (cd g) (cd d) := by
    rw [← cd_mul, ← cd_mul, hd]
  obtain ⟨k, hk, hdk⟩ := ((hD (cd g) hc).2 e8 e4) (cd d) hdc ecomm
  exact ⟨k, hk, cd_injective (by rw [hdk, cd_pow])⟩


theorem mulAut_alt6_pow_eight (f : MulAut (alternatingGroup (Fin 6))) (h : f ^ 16 = 1) :
    f ^ 8 = 1 := by
  have h1 : thetaEquiv.symm f ^ 16 = 1 := by rw [← map_pow, h, map_one]
  have h2 := autA6_pow_eight Certificates.certificate26081 _ h1
  calc f ^ 8 = thetaEquiv (thetaEquiv.symm f ^ 8) := by rw [map_pow, MulEquiv.apply_symm_apply]
    _ = 1 := by rw [h2, map_one]

theorem mulAut_alt6_eq_pow (u : MulAut (alternatingGroup (Fin 6))) (h8 : u ^ 8 = 1)
    (h4 : u ^ 4 ≠ 1) (v : MulAut (alternatingGroup (Fin 6))) (hv : v * u = u * v) :
    ∃ k < 8, v = u ^ k := by
  have h8' : thetaEquiv.symm u ^ 8 = 1 := by rw [← map_pow, h8, map_one]
  have h4' : thetaEquiv.symm u ^ 4 ≠ 1 := by
    intro h
    apply h4
    calc u ^ 4 = thetaEquiv (thetaEquiv.symm u ^ 4) := by
          rw [map_pow, MulEquiv.apply_symm_apply]
      _ = 1 := by rw [h, map_one]
  have hv' : thetaEquiv.symm v * thetaEquiv.symm u = thetaEquiv.symm u * thetaEquiv.symm v := by
    rw [← map_mul, ← map_mul, hv]
  obtain ⟨k, hk, hvk⟩ := autA6_eq_pow Certificates.certificate26081 _ h8' h4' _ hv'
  refine ⟨k, hk, ?_⟩
  calc v = thetaEquiv (thetaEquiv.symm v) := (MulEquiv.apply_symm_apply _ _).symm
    _ = thetaEquiv (thetaEquiv.symm u ^ k) := by rw [hvk]
    _ = u ^ k := by rw [map_pow, MulEquiv.apply_symm_apply]

end CFSG.EvenSporadicStandard.Fin76b
