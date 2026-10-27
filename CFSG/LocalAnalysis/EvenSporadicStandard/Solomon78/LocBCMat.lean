module

public import CFSG.Sporadic.Co1Block.TwoBComp
public import CFSG.Sporadic.Co1Block.Classes
public import CFSG.Sporadic.Schreier.Co1Generation
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCExtra
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCSylow
public import Certificates.Certificate26683
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLemma39N
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Co1.Module.InvAssemble
public import CFSG.Sporadic.Schreier.Co1SplitLocalSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

local notation "RowsT" => CFSG.Sporadic.Co1Schreier.Native.Rows
local notation "rmul" => CFSG.Sporadic.Co1Schreier.Native.mul
local notation "rone" => CFSG.Sporadic.Co1Schreier.Native.one
local notation "rinv" => CFSG.Sporadic.Co1Schreier.Native.inv
local notation "rpow" => CFSG.Sporadic.Co1Schreier.Native.pow
local notation "rword" => CFSG.Sporadic.Co1Schreier.Native.word
local notation "rdag" => CFSG.Sporadic.Co1Schreier.Native.dag
local notation "raR" => CFSG.Sporadic.Co1Schreier.Native.aR
local notation "rbR" => CFSG.Sporadic.Co1Schreier.Native.bR

section Mat

abbrev co1xC : C₁ := d₂C twoBXY.1

abbrev co1yC : C₁ := d₂C twoBXY.2

@[expose] def co1A : GA := ((co1yC : C₁) : GA)

@[expose] def co1B : GA := ((co1xC : C₁) : GA) * co1A * ((co1xC : C₁) : GA)

theorem co1x_sq : ((co1xC : C₁) : GA) * ((co1xC : C₁) : GA) = 1 :=
  Subtype.ext Certificates.certificate26683.1

theorem co1A_pow : co1A ^ 5 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact Certificates.certificate26683.2.1

theorem co1A_mem : co1A ∈ C₁ := (co1yC : C₁).2

theorem co1B_mem : co1B ∈ C₁ := C₁.mul_mem (C₁.mul_mem (co1xC : C₁).2 co1A_mem) (co1xC : C₁).2

theorem co1B_pow : co1B ^ 5 = 1 := by
  have hx : ((co1xC : C₁) : GA)⁻¹ = ((co1xC : C₁) : GA) := inv_eq_of_mul_eq_one_right co1x_sq
  have : co1B = ((co1xC : C₁) : GA) * co1A * ((co1xC : C₁) : GA)⁻¹ := by
    rw [hx]
    rfl
  rw [this, conj_pow, co1A_pow]
  simp only [mul_one, mul_inv_cancel]

theorem triHom_co1A : triHom (⟨co1A, co1A_mem⟩ : C₁) = yBar := rfl

theorem triHom_co1B : triHom (⟨co1B, co1B_mem⟩ : C₁) = xBar * yBar * xBar := by
  have : (⟨co1B, co1B_mem⟩ : C₁) = co1xC * co1yC * co1xC := rfl
  rw [this, map_mul, map_mul]

theorem co1A_memE : ((co1A : GA) : GL24) ∈ GA ⊓ Subgroup.centralizer {A₁} :=
  coe_mem_C₁ co1yC

theorem co1B_memE : ((co1B : GA) : GL24) ∈ GA ⊓ Subgroup.centralizer {A₁} :=
  coe_mem_C₁ ⟨co1B, co1B_mem⟩

theorem co1_mat_facts :
    ∃ (Z l : GL24) (hZ : Z ∈ GA ⊓ Subgroup.centralizer {A₁}),
      Z ∈ Subgroup.closure {((co1A : GA) : GL24), ((co1B : GA) : GL24)} ∧ Z * Z = 1 ∧ Z ≠ 1 ∧
      l ∈ GA ∧ l * A₁ * l⁻¹ = A₁ * Z ∧
      GA ≤ Subgroup.closure {((co1A : GA) : GL24), ((co1B : GA) : GL24),
        l * ((co1A : GA) : GL24) * l⁻¹, l * ((co1B : GA) : GL24) * l⁻¹} ∧
      (∀ x ∈ GA, x * A₁ * x⁻¹ ≠ Z) ∧
      ∃ S : Subgroup (Equiv.Perm (Fin 1365)), S ≤ twoBD ∧ Nat.card S = 4096 ∧
        (∀ x ∈ S, x * triHom (liftC Z hZ) = triHom (liftC Z hZ) * x) ∧
        ∀ x ∈ S, x * x = 1 → x ≠ 1 → (∀ s ∈ S, x * s = s * x) →
          ∃ c ∈ twoBD, c * triHom (liftC Z hZ) * c⁻¹ = x :=
  Certificates.certificate26683.2.2.1

end Mat

end CFSG.EvenSporadicStandard.Solomon78
