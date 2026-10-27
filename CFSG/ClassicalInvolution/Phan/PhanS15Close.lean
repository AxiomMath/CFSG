module

public import CFSG.ClassicalInvolution.Phan.PhanS14Step
import CFSG.ClassicalInvolution.Phan.PhanS13A3Main
import CFSG.ClassicalInvolution.Phan.PhanS13BMain
import CFSG.ClassicalInvolution.Phan.PhanS13CMain

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan

section Close

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))} (S : Setup M E D)

include S

theorem planeClose : PlaneClose E D := by
  intro g hg hl
  obtain ⟨u, hu, l₁, l₂, l₃, n₁, n₂, n₃, hd, h₁, h₂, h₃⟩ :=
    exists_diag_of_lineFix S (fun g hg => piDetOne_of_mem_sup S hg) hg hl
  have hT : u⁻¹ * g ∈ torusSub E := mem_torusSub_of_diag S n₁ n₂ n₃ hd h₁ h₂ h₃
  have hg' : g = u * (u⁻¹ * g) := by group
  rw [hg']
  exact mul_mem (Lsup_le_parab {1} (by rw [Lsup_singleton]; exact hu))
    (torusSub_le_parab {1} hT)

theorem planeBase : PlaneBase E D :=
  planeBase_of_close S (planeClose S)

end Close

end CFSG.ClassicalInvolution.PhanB3.S
