module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaSpA
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp coe_fieldSp)

section Rep

variable {K : Type} [Field K]

theorem spARep_ne_one {n j : ℕ} (hj : 1 ≤ j) (hjn : 2 * j ≤ n) :
    spARep n j ≠ (1 : StatedSp n K) := by
  intro h
  have h1 := congrArg (fun g => mat n K g (Sum.inl ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩)) h
  have hc : (⟨0, by omega⟩ : Fin n).val / 2 = (⟨1, by omega⟩ : Fin n).val / 2 ∧
      (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ ∧ (⟨0, by omega⟩ : Fin n).val < 2 * j ∧
        (⟨1, by omega⟩ : Fin n).val < 2 * j :=
    ⟨by simp, fun h' => absurd (congrArg Fin.val h') (by simp), by simp; omega, by simp; omega⟩
  have h2 : mat n K (spARep n j) (Sum.inl ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩) = 1 := by
    rw [spARep, mat_upperUnipotentSp, fromBlocks_apply₁₂, spARepMat, of_apply, ite_eq_left hc]
  have h3 : mat n K (1 : StatedSp n K) (Sum.inl ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩) = 0 := by
    rw [map_one, Matrix.one_apply_ne (by simp)]
  have h4 : (1 : K) = 0 := by
    rw [← h2, ← h3]
    exact h1
  exact one_ne_zero h4

theorem fieldSp_spARep (σ : K ≃+* K) (n j : ℕ) : fieldSp n K σ (spARep n j) = spARep n j := by
  apply mat_injective
  change (mat n K (spARep n j)).map σ = mat n K (spARep n j)
  ext a b
  rw [Matrix.map_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [spARep, mat_upperUnipotentSp, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, spARepMat,
      of_apply] <;> (try split_ifs) <;> simp

variable [Finite K] [CharP K 2]

theorem card_centralizer_spARep_lt {n j : ℕ} (hj : 1 ≤ j) (hjn : 2 * j ≤ n) :
    Nat.card (centralizer ({spARep n j} : Set (StatedSp n K))) < Nat.card (StatedSp n K) := by
  refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun h => ?_
  have htop := Subgroup.card_eq_iff_eq_top _ |>.1 h
  have hz : spARep n j ∈ center (StatedSp n K) := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := htop ▸ mem_top g
    exact mem_centralizer_singleton_iff.1 hg
  rw [center_statedSp_eq_bot, mem_bot] at hz
  exact spARep_ne_one hj hjn hz

end Rep

section Torus

variable (K : Type) [Field K]

@[expose] def spATorusParam (n j : ℕ) : Subgroup (Fin n → Kˣ) where
  carrier := {t | ∀ a b : Fin n, a.val / 2 = b.val / 2 → a ≠ b → a.val < 2 * j → b.val < 2 * j →
    t a * t b = 1}
  one_mem' := fun a b _ _ _ _ => by simp
  mul_mem' := fun {t s} ht hs a b h1 h2 h3 h4 => by
    simp only [Pi.mul_apply]
    rw [mul_mul_mul_comm, ht a b h1 h2 h3 h4, hs a b h1 h2 h3 h4, mul_one]
  inv_mem' := fun {t} ht a b h1 h2 h3 h4 => by
    simp only [Pi.inv_apply]
    rw [← mul_inv, ht a b h1 h2 h3 h4, inv_one]

@[expose] noncomputable def spATorus (n j : ℕ) : Subgroup (StatedSp n K) :=
  (spATorusParam K n j).map (diagSp K n)

variable {K}

theorem spATorus_le_centralizer (n j : ℕ) :
    spATorus K n j ≤ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply mat_injective
  rw [map_mul, map_mul, mat_diagSp, spARep, mat_upperUnipotentSp]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.one_apply, Matrix.zero_apply, spARepMat, of_apply, diagSpEntry_inl, diagSpEntry_inr]
  · split_ifs with h <;> simp [h]
  · split_ifs with h
    · have h1 := ht a b h.1 h.2.1 h.2.2.1 h.2.2.2
      have h3 : ((t b)⁻¹ : Kˣ) = t a := by
        rw [inv_eq_iff_mul_eq_one, mul_comm, h1]
      rw [h3, mul_one, one_mul]
    · simp
  · simp
  · split_ifs with h <;> simp [h]

theorem odd_card_spATorus [Finite K] {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (n j : ℕ) :
    Odd (Nat.card (spATorus K n j)) := by
  have hU : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hKc]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hpi : Odd (Nat.card (Fin n → Kˣ)) := by
    rw [Nat.card_fun]
    exact hU.pow
  have h1 : Nat.card (spATorus K n j) ∣ Nat.card (spATorusParam K n j) :=
    Subgroup.card_map_dvd _ (diagSp K n)
  have h2 : Nat.card (spATorusParam K n j) ∣ Nat.card (Fin n → Kˣ) :=
    Subgroup.card_subgroup_dvd_card _
  exact Odd.of_dvd_nat hpi (h1.trans h2)

end Torus

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def SpOmegaBShape {n : ℕ} (e : L ≃* StatedSp n K) (θ α : MulAut (spGlobal e)) (j : ℕ) :
    Prop :=
  1 ≤ j ∧ 2 * j ≤ n ∧ ∃ (ψ : StatedSp n K →* spGlobal e) (η : MulAut (spGlobal e)),
    Function.Injective ψ ∧ α = MulAut.conj (ψ (spARep n j)) * η ∧
    fixedSubgroup η = ψ.range ∧
    fixedSubgroup α = (centralizer ({spARep n j} : Set (StatedSp n K))).map ψ ∧
    (∃ z : spGlobal e, η = MulAut.conj z * θ * (MulAut.conj z)⁻¹) ∧
    (θ * α = α * θ → fixedSubgroup α ≤ fixedSubgroup θ → θ = η)

end Defs

@[expose] def SpAToralInput : Prop :=
  ∀ (n j : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → 1 ≤ j → 2 * j ≤ n →
    ∀ S : Subgroup (StatedSp n K), S ≤ centralizer ({spARep n j} : Set (StatedSp n K)) →
      Odd (Nat.card S) →
      ∃ P : Subgroup (StatedSp n K), P ≤ centralizer (S : Set (StatedSp n K)) ∧ ⁅P, P⁆ = P ∧
        ¬ P ≤ centralizer ({spARep n j} : Set (StatedSp n K))

end CFSG.SeitzReduction.SymplecticPilot
