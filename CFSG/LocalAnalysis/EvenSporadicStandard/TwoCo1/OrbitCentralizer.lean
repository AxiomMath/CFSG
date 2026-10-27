module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.OrbitSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreCentralizers

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2 CFSG.Blueprint

attribute [local irreducible] eps0 ga gb regCov rrCov epsRows

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem theta_mem_centralizer_iff
    (s : SM24) (y : Multiplicative (Fin 11 → ZMod 2)) :
    theta s ∈ Subgroup.centralizer ({epsHom y} : Set NativeSporadic.Co1) ↔
      rho s.right (Multiplicative.toAdd y) = Multiplicative.toAdd y := by
  rw [Subgroup.mem_centralizer_singleton_iff, theta_apply]
  have hcomm : epsHom s.left * epsHom y = epsHom y * epsHom s.left := by
    rw [← map_mul, ← map_mul, mul_comm]
  have key : epsHom s.left * iota s.right * epsHom y = epsHom y * (epsHom s.left * iota s.right) ↔
      iota s.right * epsHom y = epsHom y * iota s.right := by
    constructor
    · intro h
      refine mul_left_cancel (a := epsHom s.left) ?_
      calc epsHom s.left * (iota s.right * epsHom y)
          = epsHom s.left * iota s.right * epsHom y := (mul_assoc _ _ _).symm
        _ = epsHom y * (epsHom s.left * iota s.right) := h
        _ = epsHom y * epsHom s.left * iota s.right := (mul_assoc _ _ _).symm
        _ = epsHom s.left * epsHom y * iota s.right := by rw [hcomm]
        _ = epsHom s.left * (epsHom y * iota s.right) := mul_assoc _ _ _
    · intro h
      calc epsHom s.left * iota s.right * epsHom y
          = epsHom s.left * (iota s.right * epsHom y) := mul_assoc _ _ _
        _ = epsHom s.left * (epsHom y * iota s.right) := by rw [h]
        _ = epsHom s.left * epsHom y * iota s.right := (mul_assoc _ _ _).symm
        _ = epsHom y * epsHom s.left * iota s.right := by rw [hcomm]
        _ = epsHom y * (epsHom s.left * iota s.right) := mul_assoc _ _ _
  rw [key, ← mul_inv_eq_iff_eq_mul, iota_conj, epsHom_injective.eq_iff]
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simpa using this
  · intro h
    rw [h]
    exact ofAdd_toAdd y

theorem card_centralizer_inf_theta_range
    (y : Multiplicative (Fin 11 → ZMod 2)) :
    Nat.card ↥(Subgroup.centralizer ({epsHom y} : Set NativeSporadic.Co1) ⊓ theta.range) =
      2 ^ 11 * Nat.card {p : PM24 // rho p (Multiplicative.toAdd y) = Multiplicative.toAdd y} := by
  set C := Subgroup.centralizer ({epsHom y} : Set NativeSporadic.Co1) with hC
  have h1 : (C.comap theta).map theta = theta.range ⊓ C := Subgroup.map_comap_eq theta C
  rw [inf_comm, ← h1, Subgroup.card_map_of_injective theta_injective]
  let e : ↥(C.comap theta) ≃ Multiplicative (Fin 11 → ZMod 2) ×
      {p : PM24 // rho p (Multiplicative.toAdd y) = Multiplicative.toAdd y} :=
    { toFun := fun s => (s.1.left, ⟨s.1.right, (theta_mem_centralizer_iff s.1 y).1 s.2⟩)
      invFun := fun q => ⟨⟨q.1, q.2.1⟩, (theta_mem_centralizer_iff ⟨q.1, q.2.1⟩ y).2 q.2.2⟩
      left_inv := fun s => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e, Nat.card_prod]
  congr 1
  rw [Nat.card_congr (Multiplicative.ofAdd :
    (Fin 11 → ZMod 2) ≃ Multiplicative (Fin 11 → ZMod 2)).symm]
  simp [Nat.card_eq_fintype_card]

theorem card_centralizer_Theta_epsC :
    Nat.card ↥(Subgroup.centralizer ({epsMask eMaskC} : Set NativeSporadic.Co1) ⊓ theta.range) =
      389283840 := by
  have h := card_centralizer_inf_theta_range (Multiplicative.ofAdd (toVecD 11 eMaskC))
  rw [toAdd_ofAdd, card_stab_xC] at h
  exact h.trans (by norm_num)

theorem centralizer_epsC_le_theta_range :
    Subgroup.centralizer ({epsMask eMaskC} : Set NativeSporadic.Co1) ≤ theta.range := by
  have : Finite NativeSporadic.Co1 := (CFSG.Sporadic.Co1.fam_co1_simplicity).1
  have h1 := card_centralizer_epsC
  have h2 := card_centralizer_Theta_epsC
  have heq : Subgroup.centralizer ({epsMask eMaskC} : Set NativeSporadic.Co1) ⊓ theta.range =
      Subgroup.centralizer ({epsMask eMaskC} : Set NativeSporadic.Co1) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, h2])
  rw [← heq]
  exact inf_le_right

theorem card_centralizer_Theta_epsA :
    Nat.card ↥(Subgroup.centralizer ({epsMask eMaskA} : Set NativeSporadic.Co1) ⊓ theta.range) =
      660602880 := by
  have h := card_centralizer_inf_theta_range (Multiplicative.ofAdd (toVecD 11 eMaskA))
  rw [toAdd_ofAdd, card_stab_xA] at h
  exact h.trans (by norm_num)

end CFSG.EvenSporadicStandard.TwoCo1
