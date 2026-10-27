module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q11Core
public import CFSG.GH74.Generic.BProg.B2.GenLocU4QFrame2
public import CFSG.GH74.Generic.BProg.B2.GenLocU4QAsm

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic GenLocU4QLift GenLocU4QClass GenLocU4QHyp GenLocU4Q CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits

namespace GenLocU4Q11

open GenLocU4Q11Sg

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

omit [Finite K] in
theorem comm_conj {P r x D : GL (Fin 4) K} (hD : P⁻¹ * x * P = D)
    (h : (r : Matrix (Fin 4) (Fin 4) K) * (D : Matrix (Fin 4) (Fin 4) K) =
      (D : Matrix (Fin 4) (Fin 4) K) * (r : Matrix (Fin 4) (Fin 4) K)) :
    (P * r * P⁻¹) * x = x * (P * r * P⁻¹) := by
  have h' : r * D = D * r := Units.ext (by simpa [Units.val_mul] using h)
  have e : x = P * D * P⁻¹ := by rw [← hD]; group
  calc P * r * P⁻¹ * x = P * r * P⁻¹ * (P * D * P⁻¹) := by rw [← e]
    _ = P * (r * D) * P⁻¹ := by group
    _ = P * (D * r) * P⁻¹ := by rw [h']
    _ = (P * D * P⁻¹) * (P * r * P⁻¹) := by group
    _ = x * (P * r * P⁻¹) := by rw [← e]

variable [Fact p.Prime] [CharP K p]

theorem gammaAct_class11 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A) (hr : pRank 2 A = 3)
    (T : Triple α 1 1 (-1)) : gammaAct α = ⊤ := by
  obtain ⟨a, b, c, x, y, z, hax, hby, hcz, hx, hy, hz, hxy, hxz, hyz, hzn⟩ := T
  have hH := hypPlanes_of_data hp hp2 hK α hA hr hax hby hcz hx hy hz hxy hxz hyz hzn
  obtain ⟨P, hP, hxP, hyP, hzP⟩ := GenLocU4QFrame2.frame11 hp hp2 hK hq x y z hax.1 hby.1 hcz.1 (gl_sq_one hx)
    (gl_sq_one hy) (gl_sq_neg_one hz) hxy hxz hyz hzn
  let Γ₁ : Subgroup (Su K p f 4) := (gammaAct α).comap (GenLocU4Gen.frameConj (GenLocU4Gen.fieldData hK) P hP)
  have hDx : ((P⁻¹ * x * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Dx11 := by rw [hxP, diagonal_eq_Dx11]
  have hDy : ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Dy11 := hyP
  have hDz : ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Dz11 := hzP
  have hDyz : ((P⁻¹ * (y * z) * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Dy11 * Dz11 := by
    have : P⁻¹ * (y * z) * P = (P⁻¹ * y * P) * (P⁻¹ * z * P) := by group
    rw [this, Units.val_mul, hDy, hDz]
  have hDxz : ((P⁻¹ * (x * z) * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Dx11 * Dz11 := by
    have : P⁻¹ * (x * z) * P = (P⁻¹ * x * P) * (P⁻¹ * z * P) := by group
    rw [this, Units.val_mul, hDx, hDz]
  have hDxy : ((P⁻¹ * (x * y) * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Dx11 * Dy11 := by
    have : P⁻¹ * (x * y) * P = (P⁻¹ * x * P) * (P⁻¹ * y * P) := by group
    rw [this, Units.val_mul, hDx, hDy]
  have key : ∀ (r : Su K p f 4) (u v : GL (Fin 4) K) (Du Dv : Matrix (Fin 4) (Fin 4) K),
      ((P⁻¹ * u * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Du →
      ((P⁻¹ * v * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Dv →
      ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Du = Du * ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →
      ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Dv = Dv * ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →
      (∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * u = u * g → (g : GL (Fin 4) K) * v = v * g →
        g ∈ gammaAct α) → r ∈ Γ₁ := by
    intro r u v Du Dv hu hv hru hrv hmem
    refine hmem _ ?_ ?_
    · rw [GenLocU4Gen.coe_frameConj]
      exact comm_conj (D := P⁻¹ * u * P) rfl (by rw [hu]; exact hru)
    · rw [GenLocU4Gen.coe_frameConj]
      exact comm_conj (D := P⁻¹ * v * P) rfl (by rw [hv]; exact hrv)
  have h1 : ∀ (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
      (hc : unitaryInvolution K p f c = -c), sgElt1 ι c hι hσι hc ∈ Γ₁ := fun ι c hι hσι hc =>
    key _ x y _ _ hDx hDy (Sg1_comm_Dx ι c) (Sg1_comm_Dy ι c) hH.1
  have hY : ∀ (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
      (hc : unitaryInvolution K p f c = -c), sgEltY ι c hι hσι hc ∈ Γ₁ := fun ι c hι hσι hc =>
    key _ x (y * z) _ _ hDx hDyz (SgY_comm_Dx ι c) (SgY_comm_Dyz ι c) hH.2.2.2.1
  have hZ : ∀ (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
      (hc : unitaryInvolution K p f c = -c), sgEltZ ι c hι hσι hc ∈ Γ₁ := fun ι c hι hσι hc =>
    key _ y (x * z) _ _ hDy hDxz (SgZ_comm_Dy ι c) (SgZ_comm_Dxz ι c) hH.2.2.2.2.1
  have hX : ∀ (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
      (hc : unitaryInvolution K p f c = c), sgEltX ι c hι hσι hc ∈ Γ₁ := fun ι c hι hσι hc =>
    key _ (x * y) (x * z) _ _ hDxy hDxz (SgX_comm_Dxy ι c) (SgX_comm_Dxz ι c) hH.2.2.2.2.2.2
  have htop := siegel_top hp hp2 hK hq Γ₁ h1 hY hZ hX
  rw [eq_top_iff]
  intro g _
  obtain ⟨x', rfl⟩ := GenLocU4Gen.frameConj_surjective (GenLocU4Gen.fieldData hK) P hP g
  have hx' : x' ∈ Γ₁ := by
    rw [htop]
    trivial
  exact hx'

end GenLocU4Q11

end CFSG.GH74.Generic.BProg.B2
