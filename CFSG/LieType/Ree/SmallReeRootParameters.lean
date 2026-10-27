module

public import CFSG.LieType.Ree.G2PrimeFieldWords
public import CFSG.LieType.Ree.SmallReeCoordinateData

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}

theorem G2_relationExponent :
    G2.relationExponent a ⟨0, by decide⟩ = 3 ^ a ∧
      G2.relationExponent a ⟨1, by decide⟩ = 3 * 3 ^ a := by
  refine ⟨?_, ?_⟩
  · rw [relationExponent, ite_eq_left (by decide)]
    rfl
  · rw [relationExponent, ite_eq_right (by decide), pow_succ, mul_comm]
    rfl

theorem finiteReeAut_pinnedX_single
    (j : Fin G2.tag.rank) (c : K) :
    G2.finiteReeAut K a ⟨pinnedX G2.tag K (Pi.single j 1) c, pinnedX_mem_adjointGroup _ c⟩ =
      ⟨pinnedX G2.tag K (Pi.single (G2.perm j) 1) (c ^ G2.relationExponent a j),
        pinnedX_mem_adjointGroup _ _⟩ :=
  finiteReeAut_pinnedX (pinnedData_single j) (by rw [pinnedData_single]; rfl) c

theorem small_Ree_positive_root_F_parameters
    (K : Type) [Field K] [Finite K] [CharP K G2.prime]
    (a : ℕ) (t : K) :
    G2.finiteReeAut K a ⟨smallReeX K 0 t, pinnedX_mem_adjointGroup _ t⟩ =
        ⟨smallReeX K 1 (smallReeSigma a t), pinnedX_mem_adjointGroup _ _⟩ ∧
      G2.finiteReeAut K a ⟨smallReeX K 1 t, pinnedX_mem_adjointGroup _ t⟩ =
        ⟨smallReeX K 0 (t ^ 3 ^ a), pinnedX_mem_adjointGroup _ _⟩ ∧
      G2.finiteReeAut K a ⟨smallReeX K 2 t, pinnedX_mem_adjointGroup _ t⟩ =
        ⟨smallReeX K 4 (smallReeSigma a t), pinnedX_mem_adjointGroup _ _⟩ ∧
      G2.finiteReeAut K a ⟨smallReeX K 4 t, pinnedX_mem_adjointGroup _ t⟩ =
        ⟨smallReeX K 2 (t ^ 3 ^ a), pinnedX_mem_adjointGroup _ _⟩ ∧
      G2.finiteReeAut K a ⟨smallReeX K 3 t, pinnedX_mem_adjointGroup _ t⟩ =
        ⟨smallReeX K 5 (smallReeSigma a t), pinnedX_mem_adjointGroup _ _⟩ ∧
      G2.finiteReeAut K a ⟨smallReeX K 5 t, pinnedX_mem_adjointGroup _ t⟩ =
        ⟨smallReeX K 3 (t ^ 3 ^ a), pinnedX_mem_adjointGroup _ _⟩ := by
  obtain ⟨e0, e1⟩ := G2_relationExponent (a := a)
  have h1 := finiteReeAut_pinnedX_single (K := K) (a := a) ⟨1, by decide⟩ t
  have h0 := finiteReeAut_pinnedX_single (K := K) (a := a) ⟨0, by decide⟩ t
  have h3 := finiteReeAut_pinnedX (K := K) (a := a) (β := g2Root13) pinnedData_g2Root11
    (by rw [pinnedData_g2Root13]; rfl) t
  have h5 := finiteReeAut_pinnedX (K := K) (a := a) (β := g2Root11) pinnedData_g2Root13
    (by rw [pinnedData_g2Root11]; rfl) t
  have h4 := finiteReeAut_pinnedX (K := K) (a := a) (β := g2Root23) pinnedData_g2Root12
    (by rw [pinnedData_g2Root23]; rfl) t
  have h6 := finiteReeAut_pinnedX (K := K) (a := a) (β := g2Root12) pinnedData_g2Root23
    (by rw [pinnedData_g2Root12]; rfl) t
  have s0 : (Pi.single ⟨1, by decide⟩ 1 : Fin G2.tag.rank → ℤ) = smallReeRoot 0 := by
    funext i
    fin_cases i <;> rfl
  have s1 : (Pi.single ⟨0, by decide⟩ 1 : Fin G2.tag.rank → ℤ) = smallReeRoot 1 := by
    funext i
    fin_cases i <;> rfl
  have p1 : G2.perm ⟨1, by decide⟩ = ⟨0, by decide⟩ := by decide
  have p0 : G2.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  rw [e1, p1, s0, s1] at h1
  rw [e0, p0, s0, s1] at h0
  rw [e1] at h3 h4
  rw [e0] at h5 h6
  exact ⟨h1, h0, h3, h5, h4, h6⟩

end ReeTag

end CFSG.LieType.Ree
