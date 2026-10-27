module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsLifts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsTarget

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Matrix

section Data

variable {K : Type} [Field K]

@[expose] def IsIrred (K : Type) [Field K] (y : GL (Fin 3) K) : Prop :=
  ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
    W = ⊥ ∨ W = ⊤

structure IsTypeThree (π : Bool) (q : ℕ) (K : Type) [Field K] (y : GL (Fin 3) K) : Prop where
  mem : y ∈ glPi π 3 q K
  irred : IsIrred K y
  cube : y ^ 3 ∈ zPi π 3 q K
  cyclic : IsCyclic ↥(slPi π 3 q K ⊓ Subgroup.centralizer {y})
  card : Nat.card ↥(slPi π 3 q K ⊓ Subgroup.centralizer {y}) = qSubPi π (q ^ 3) / qSubPi π q
  exists_w : ∃ w ∈ slPi π 3 q K, orderOf w = 3 ∧
    w ∉ slPi π 3 q K ⊓ Subgroup.centralizer {y} ∧
    centMod (slPi π 3 q K) y = (slPi π 3 q K ⊓ Subgroup.centralizer {y}) ⊔ Subgroup.zpowers w ∧
    Nat.card ↥(slPi π 3 q K ⊓ Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K))) = 3

theorem not_isIrred_of_mem_statedScalars {y : GL (Fin 3) K} (hy : y ∈ StatedScalars (Fin 3) K) :
    ¬ IsIrred K y := by
  obtain ⟨c, rfl⟩ := hy
  refine not_irreducible_of_diag (g := 1) (z := 1) (one_mem _) (d := fun _ => (c : K)) ?_
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

variable {π : Bool} {p f : ℕ}

theorem exists_lift_cases (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K)
    (hyZ : y ∉ zPi π 3 (p ^ f) K) (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K) :
    ∃ y' : GL (Fin 3) K, (∃ z ∈ zPi π 3 (p ^ f) K, y' = y * z) ∧
      ((∃ g ∈ glPi π 3 (p ^ f) K, g⁻¹ * y' * g = diagTau hτ) ∨
        (∃ g ∈ glPi π 3 (p ^ f) K, ∃ e : Kˣ, ((e : K) = τ ∨ (e : K) = τ ^ 2) ∧
          g⁻¹ * y' * g = diagE e) ∨
        IsTypeThree π (p ^ f) K y') := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := fun h => by
    subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨y', ⟨z, hz, rfl⟩, h⟩ := rank3II_4_10_one hK hq hτ hτ1 hyH hyZ hy3
  refine ⟨y * z, ⟨z, hz, rfl⟩, ?_⟩
  rcases h with ⟨hD, -, -⟩ | ⟨hD, -, -⟩ | ⟨-, -, hirr, hcyc, hcard, hw⟩
  · exact Or.inl hD
  · exact Or.inr (Or.inl hD)
  · have hzH : z ∈ glPi π 3 (p ^ f) K := by
      rw [zPi_eq hπ hq' hτ hτ1] at hz
      exact (Subgroup.mem_inf.1 hz).1
    have hz' := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
    refine Or.inr (Or.inr ⟨mul_mem hyH hzH, hirr, ?_, hcyc, hcard, hw⟩)
    have hc := commute_of_mem_statedScalars hz' y
    rw [Commute.mul_pow (show Commute y z from hc) 3]
    exact mul_mem hy3 (pow_mem hz 3)

theorem IsTypeThree.not_isInnerMat (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) : ¬ IsInnerMat π (p ^ f) K y := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := fun h => by
    subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  rintro ⟨l, hl, z, hz, rfl⟩
  have hyZ : l * z ∉ zPi π 3 (p ^ f) K := fun h =>
    not_isIrred_of_mem_statedScalars (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h) hT.irred
  have hin : ∃ l' ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K,
      l * z * m * (l * z)⁻¹ = l' * m * l'⁻¹ := by
    refine ⟨l, hl, fun m _ => ?_⟩
    have hc := commute_of_mem_statedScalars hz m
    calc l * z * m * (l * z)⁻¹ = l * (z * m) * z⁻¹ * l⁻¹ := by group
      _ = l * (m * z) * z⁻¹ * l⁻¹ := by rw [hc]
      _ = l * m * l⁻¹ := by group
  rcases (rank3II_4_10_two hK hq hτ hτ1 hT.mem hyZ hT.cube).1 hin with
      ⟨y', ⟨z', hz', rfl⟩, g, -, hD⟩ | ⟨⟨y', ⟨z', hz', rfl⟩, g, -, e, -, hD⟩, -⟩
  · exact not_irreducible_of_diag (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz')
      (d := ![τ, τ ^ 2, 1]) (by rw [hD, coe_diagTau_eq_diagonal]) hT.irred
  · exact not_irreducible_of_diag (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz')
      (d := ![(e : K), 1, 1]) (by rw [hD, coe_diagE]) hT.irred

theorem IsTypeThree.not_cube (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) :
    ∃ ℓ : Kˣ, (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ℓ : K) • 1 ∧ ∀ μ : K, μ ^ 3 ≠ ℓ := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨ℓ, -, hℓ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hT.cube
  have hys : y ∉ StatedScalars (Fin 3) K := fun h => not_isIrred_of_mem_statedScalars h hT.irred
  refine ⟨ℓ, by rw [← Units.val_pow_eq_pow_val, ← hℓ, coe_scalar_eq_smul], fun μ hμ => ?_⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    exact ℓ.ne_zero hμ.symm
  have hμ' : y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0 ^ 3) := by
    rw [← hℓ]
    congr 1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ])
  obtain ⟨y', ⟨z, hz, rfl⟩, g, -, hD⟩ := exists_diag_normal_form hK hq hτ hτ1 hT.mem hys hμ'
  rcases hD with hD | ⟨e, -, hD⟩
  · exact not_irreducible_of_diag (g := g) (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
      (d := ![τ, τ ^ 2, 1]) (by rw [hD, coe_diagTau_eq_diagonal]) hT.irred
  · exact not_irreducible_of_diag (g := g) (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
      (d := ![(e : K), 1, 1]) (by rw [hD, coe_diagE]) hT.irred

theorem IsTypeThree.card_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (h2 : 2 < p ^ f)
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) :
    ∃ m : ℕ, Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) = 3 * m ∧ 6 < m ∧
      ¬ 3 ∣ m := by
  have h0 := qSubPi_ne_zero hK hq
  refine ⟨3 * ((p ^ f) / 3) ^ 2 + 3 * ((p ^ f) / 3) + 1, ?_, ?_, by omega⟩
  · rw [hT.card, qSubPi_cube_eq hq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h0)]
  · have : 1 ≤ (p ^ f) / 3 := by
      have : 3 ≤ p ^ f := by omega
      omega
    nlinarith

end Data

section Inner

variable {X : Type} [Group X] {L : Subgroup X} [L.Normal] {π : Bool} {p f : ℕ} {K : Type}
  [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem LModel.not_inv_mul_mem_centralizer (M : LModel L π p f K ν) {x : X} {y : GL (Fin 3) K}
    (hx : IsLiftAt ν x y) (hT : IsTypeThree π (p ^ f) K y) :
    ∀ l ∈ L, l⁻¹ * x ∉ centralizer (L : Set X) := by
  intro l hl hc
  obtain ⟨s, hs⟩ := M.surj ⟨l, hl⟩
  have hsl : ((ν s : ↥L) : X) = l := by rw [hs]
  have h1 := (isLiftAt_of_mem M s).mul M (isLiftAt_one_of_mem_centralizer hc)
  rw [hsl, mul_one, mul_inv_cancel_left] at h1
  have h2 := hx.inv_mul_mem_zPi M h1
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  have h3 := mem_statedScalars_of_mem_zPi M.piField M.modThree hτ hτ1 h2
  refine hT.not_isInnerMat M.piField M.modThree ⟨s, s.2, (y⁻¹ * s)⁻¹, inv_mem h3, ?_⟩
  group

theorem LModel.inducesInnDiagNonInner_of_isTypeThree (M : LModel L π p f K ν)
    (hcore : GLAPPrimeCore 3 ↥L = ⊥) {x : X} {y : GL (Fin 3) K} (hx : IsLiftAt ν x y)
    (hT : IsTypeThree π (p ^ f) K y) : InducesInnDiagNonInner L x :=
  inducesInnDiagNonInner_of_isLiftAt M hcore hx (M.not_inv_mul_mem_centralizer hx hT)

theorem LModel.not_mem_of_isTypeThree (M : LModel L π p f K ν) {x : X} {y : GL (Fin 3) K}
    (hx : IsLiftAt ν x y) (hT : IsTypeThree π (p ^ f) K y) : x ∉ L := fun hxL =>
  M.not_inv_mul_mem_centralizer hx hT x hxL (by rw [inv_mul_cancel]; exact one_mem _)

end Inner

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
