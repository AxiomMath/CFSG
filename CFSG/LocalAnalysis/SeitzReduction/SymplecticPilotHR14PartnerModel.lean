module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerB1

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longRootSp2)

section Toral

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_perfect_le_centralizer_of_odd (hK : 4 ≤ Nat.card K) {m : ℕ} (p : Fin (m + 1))
    {S : Subgroup (StatedSp (m + 1) K)}
    (hS : S ≤ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)))
    (hodd : Odd (Nat.card S)) :
    ∃ P : Subgroup (StatedSp (m + 1) K), P ≤ centralizer (S : Set (StatedSp (m + 1) K)) ∧
      ⁅P, P⁆ = P ∧ siegDiag K p 1 ∈ P ∧
        ¬ P ≤ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSup : S ≤ complSp K p ⊔ transvRadical K p := by
    rw [sup_comm, ← centralizer_siegDiag_eq_sup]
    exact hS
  have hcop : Nat.Coprime 2 (Nat.card S) := Nat.coprime_two_left.2 hodd
  obtain ⟨u, hu, hle⟩ := F4Pilot.exists_mem_map_conj_le_of_le_sup isPGroup_transvRadical
    complSp_le_normalizer_transvRadical (disjoint_iff.1 disjoint_transvRadical_complSp) hSup hcop
  have huz : u * siegDiag K p 1 = siegDiag K p 1 * u :=
    mem_centralizer_singleton_iff.1 (transvRadical_le_centralizer hu)
  refine ⟨(longRootSp2 K (m + 1) p).map (MulAut.conj u⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro s hs
    have hus : u * s * u⁻¹ ∈ complSp K p := hle ⟨s, hs, rfl⟩
    have hc := (commute_of_mem_longRootSp2_of_mem_complSp hy hus).eq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc s * (u⁻¹ * y * u) = u⁻¹ * ((u * s * u⁻¹) * y) * u := by group
      _ = u⁻¹ * (y * (u * s * u⁻¹)) * u := by rw [hc]
      _ = u⁻¹ * y * u * s := by group
  · rw [← Subgroup.map_commutator, commutator_longRootSp2 hK p]
  · refine ⟨siegDiag K p 1, siegDiag_mem_longRootSp2 p 1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc u⁻¹ * siegDiag K p 1 * u = u⁻¹ * (u * siegDiag K p 1) := by rw [huz]; group
      _ = siegDiag K p 1 := by group
  · intro hP
    obtain ⟨κ, hκ⟩ := exists_units_ne_one hK
    have hh : rootTorusHom K (m + 1) p κ ∈ longRootSp2 K (m + 1) p :=
      rootTorusSp_le_longRootSp2 p ⟨κ, rfl⟩
    have h1 := hP ⟨_, hh, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    have h2 : rootTorusHom K (m + 1) p κ ∈
        centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) := by
      rw [mem_centralizer_singleton_iff]
      have h3 := mem_centralizer_singleton_iff.1 h1
      calc rootTorusHom K (m + 1) p κ * siegDiag K p 1 =
          u * ((u⁻¹ * rootTorusHom K (m + 1) p κ * u) * siegDiag K p 1) * u⁻¹ := by
            rw [show u * ((u⁻¹ * rootTorusHom K (m + 1) p κ * u) * siegDiag K p 1) * u⁻¹ =
              rootTorusHom K (m + 1) p κ * (u * siegDiag K p 1 * u⁻¹) by group, huz]
            group
        _ = u * (siegDiag K p 1 * (u⁻¹ * rootTorusHom K (m + 1) p κ * u)) * u⁻¹ := by rw [h3]
        _ = siegDiag K p 1 * rootTorusHom K (m + 1) p κ := by
            rw [show u * (siegDiag K p 1 * (u⁻¹ * rootTorusHom K (m + 1) p κ * u)) * u⁻¹ =
              (u * siegDiag K p 1 * u⁻¹) * rootTorusHom K (m + 1) p κ by group, huz]
            group
    have h4 := (mem_centralizer_siegDiag_iff.1 h2) (Sum.inl p)
    simp only [mat_rootTorusHom_apply, ↓reduceIte, Matrix.one_apply_eq,
      diagSpEntry_mulSingle_inl_self] at h4
    exact hκ (Units.ext h4)

end Toral

section Embedding

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem siegDiag_one_mul_self {n : ℕ} (p : Fin n) : siegDiag K p 1 * siegDiag K p 1 = 1 := by
  rw [siegDiag_mul, CharTwo.add_self_eq_zero, siegDiag_zero]

end Embedding

end CFSG.SeitzReduction.SymplecticPilot
