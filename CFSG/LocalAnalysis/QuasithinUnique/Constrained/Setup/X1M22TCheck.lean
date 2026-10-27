module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Check
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightGen
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Check
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TA
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public meta import CFSG.Sporadic.Schreier.M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TCheckInputs
public import Certificates.Certificate4070
public import CFSG.LieType.CurtisTits.Recognition
public meta import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem a2_sylow_check :
    a2rl.length = 2 ^ 8 ∧ a2rl.Nodup ∧ (1 : ↥m22A) ∈ a2rl ∧
      (∀ x ∈ a2rl, ∀ g ∈ a2rg, x * g ∈ a2rl) ∧ (∀ x ∈ a2rl, x ^ (2 ^ 8) = 1) :=
  Certificates.certificate4070.1

theorem a2_rel_check :
    (∀ i : Fin 5, bE i * bE i = 1) ∧ (∀ i j : Fin 5, bE i * bE j = bE j * bE i) ∧
      (∀ i : Fin 5, cE * bE i * cE⁻¹ = bE (i + 1)) ∧
      (∀ i : Fin 5, dE * bE i * dE⁻¹ = bE (2 * i)) ∧
      cE ^ 5 = 1 ∧ cE ≠ 1 ∧ dE ^ 4 = 1 ∧ dE * cE * dE⁻¹ = cE ^ 2 ∧
      cE * tE * cE⁻¹ = tE ∧ dE * tE * dE⁻¹ = tE :=
  Certificates.certificate4070.2.1

theorem a2_e5_check :
    a2e5.length = 32 ∧ a2e5.Nodup ∧ (1 : ↥m22A) ∈ a2e5 ∧
      (∀ x ∈ a2e5, ∀ y ∈ a2e5, x * y ∈ a2e5) ∧ (∀ x ∈ a2e5, x ∈ a2rl) ∧
      (∀ i : Fin 5, bE i ∈ a2e5) :=
  Certificates.certificate4070.2.2.1

theorem a2_e5_sq_check : ∀ x ∈ a2e5, x * x = 1 :=
  Certificates.certificate4070.2.2.2.1

theorem a2_heavy_check : a2heavy.length < 16 :=
  Certificates.certificate4070.2.2.2.2.1

theorem a2_wit_check :
    (tE * (yT * tE * yT⁻¹)) ^ 11 = 1 ∧ tE * (yT * tE * yT⁻¹) ≠ 1 ∧
      (bE 0 * (y0 * bE 0 * y0⁻¹)) ^ 11 = 1 ∧ bE 0 * (y0 * bE 0 * y0⁻¹) ≠ 1 :=
  Certificates.certificate4070.2.2.2.2.2.1

theorem a2_inner_check :
    ((x2M : NativeSporadic.M22) : Equiv.Perm (Fin 22)) = ((bE 0 * bE 1 : ↥m22A) : Equiv.Perm (Fin 22)) ∧
      ((x4M : NativeSporadic.M22) : Equiv.Perm (Fin 22)) =
        ((bE 0 * bE 1 * bE 2 * bE 3 : ↥m22A) : Equiv.Perm (Fin 22)) ∧
      bE 0 * bE 1 ≠ 1 ∧ bE 0 * bE 1 * bE 2 * bE 3 ≠ 1 :=
  Certificates.certificate4070.2.2.2.2.2.2.1

theorem m22_fg_check :
    fgOK m22FG = true ∧
      (m22G2.all fun e => m22FG.any fun f => f.1 == e.1 && f.2.1 == e.2.1) = true :=
  Certificates.certificate4070.2.2.2.2.2.2.2

end CFSG.QuasithinUnique.Setup.X1
