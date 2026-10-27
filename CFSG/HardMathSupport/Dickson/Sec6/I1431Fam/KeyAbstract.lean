module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrbitFamily

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open CFSG.RankThree.PartOne.KCUnitary (commutator_self_le)
open scoped commutatorElement

theorem key_of_sq_mem {Xs : Type} [Group Xs] {F N : Subgroup Xs} (hN : N ≤ F)
    (hsq : ∀ g ∈ F, ∃ n ∈ N, ∃ z ∈ F, (∀ m ∈ F, z * m = m * z) ∧ g ^ 2 = n * z) {b : Xs}
    (hb : b ∈ F) (hb3 : ∀ m ∈ F, b ^ 3 * m = m * b ^ 3) :
    ∃ s ∈ N, ∀ m ∈ N, b * m * b⁻¹ = s * m * s⁻¹ := by
  obtain ⟨n, hn, z, hzF, hzc, hbz⟩ := hsq b hb
  have hb3F : b ^ 3 ∈ F := F.pow_mem hb 3
  set c : Xs := b ^ 3 * z⁻¹ with hc
  have hcF : c ∈ F := F.mul_mem hb3F (F.inv_mem hzF)
  have hcc : ∀ m ∈ F, c * m = m * c := by
    intro m hm
    have hzinv : z⁻¹ * m = m * z⁻¹ := by
      have := hzc m hm
      calc z⁻¹ * m = z⁻¹ * (m * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * m) * z⁻¹ := by rw [this]
        _ = m * z⁻¹ := by group
    calc c * m = b ^ 3 * (z⁻¹ * m) := by rw [hc, mul_assoc]
      _ = b ^ 3 * (m * z⁻¹) := by rw [hzinv]
      _ = (b ^ 3 * m) * z⁻¹ := by rw [mul_assoc]
      _ = (m * b ^ 3) * z⁻¹ := by rw [hb3 m hm]
      _ = m * c := by rw [hc, mul_assoc]
  have hbc : b = c * n⁻¹ := by
    have h1 : b ^ 2 = n * z := hbz
    calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
      _ = b ^ 3 * (n * z)⁻¹ := by rw [h1]
      _ = b ^ 3 * (z⁻¹ * n⁻¹) := by rw [mul_inv_rev]
      _ = c * n⁻¹ := by rw [hc, mul_assoc]
  refine ⟨n⁻¹, N.inv_mem hn, fun m hm => ?_⟩
  have hmF : n⁻¹ * m * n ∈ F :=
    F.mul_mem (F.mul_mem (F.inv_mem (hN hn)) (hN hm)) (hN hn)
  have h2 : c * (n⁻¹ * m * n) = (n⁻¹ * m * n) * c := hcc _ hmF
  calc b * m * b⁻¹ = c * (n⁻¹ * m * n) * c⁻¹ := by rw [hbc]; group
    _ = (n⁻¹ * m * n) * c * c⁻¹ := by rw [h2]
    _ = n⁻¹ * m * n⁻¹⁻¹ := by group

theorem lift_blocks_of_orbit_family_sq {Xs : Type} [Group Xs] [Finite Xs] (q : ℕ) (a : Xs)
    {ι : Type} [Finite ι] (F : ι → Subgroup Xs)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, Commute x y)
    (hjoin : ⨆ i, F i = Subgroup.centralizer ({a} : Set Xs))
    (htame : ∀ i, CFSG.IsQuasisimple ↥⁅F i, F i⁆ ∨ Group.IsSolvable ↥(F i))
    (hsq : ∀ i, CFSG.IsQuasisimple ↥⁅F i, F i⁆ → IsTypeL2 q ↥⁅F i, F i⁆ →
      ∀ g ∈ F i, ∃ n ∈ ⁅F i, F i⁆, ∃ z ∈ F i, (∀ m ∈ F i, z * m = m * z) ∧ g ^ 2 = n * z) :
    ∃ (ι' : Type) (_ : Finite ι') (N : ι' → Subgroup Xs),
      (∀ i, N i ≤ Subgroup.centralizer ({a} : Set Xs)) ∧
      (∀ i, ∀ g ∈ Subgroup.centralizer ({a} : Set Xs), ∀ m ∈ N i, g * m * g⁻¹ ∈ N i) ∧
      (∀ i, CFSG.IsQuasisimple (N i)) ∧
      (∃ k : ℕ, ∀ g ∈ derivedSeries ↥(Subgroup.centralizer ({a} : Set Xs)) k,
        (g : Xs) ∈ ⨆ i, N i) ∧
      (∀ i, IsTypeL2 q (N i) → ∀ b ∈ Subgroup.centralizer ({a} : Set Xs), b ^ 3 = 1 →
        ∃ s ∈ N i, ∀ m ∈ N i, b * m * b⁻¹ = s * m * s⁻¹) :=
  lift_blocks_of_orbit_family q a F hc hjoin htame fun i hq hT b hb hb3 =>
    key_of_sq_mem (commutator_self_le (F i)) (hsq i hq hT) hb hb3

end CFSG.HardMathSupport.Dickson.Sec6.I1431
