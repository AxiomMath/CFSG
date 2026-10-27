module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

open Equiv

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426E27

def cyc3 (a b c : Fin 10) : Perm (Fin 10) := swap a b * swap b c

def c0 : Perm (Fin 10) := cyc3 0 1 2
def c1 : Perm (Fin 10) := cyc3 3 4 5
def c2 : Perm (Fin 10) := cyc3 6 7 8

theorem c0_mem : c0 ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]
  unfold c0 cyc3
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  norm_num

theorem c1_mem : c1 ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]
  unfold c1 cyc3
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  norm_num

theorem c2_mem : c2 ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]
  unfold c2 cyc3
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  norm_num

theorem c0_cube : c0 ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

theorem c1_cube : c1 ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

theorem c2_cube : c2 ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

theorem c01 : c0 * c1 = c1 * c0 := by
  ext i
  fin_cases i <;> decide

theorem c02 : c0 * c2 = c2 * c0 := by
  ext i
  fin_cases i <;> decide

theorem c12 : c1 * c2 = c2 * c1 := by
  ext i
  fin_cases i <;> decide

theorem isElemAbelian_closure {G : Type} [Group G] {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (h3 : ∀ x ∈ S, x ^ 3 = 1) : CFSG.Open.IsElemAbelian 3 (Subgroup.closure S) := by
  have hgen : ∀ x ∈ Subgroup.closure S, ∀ s ∈ S, x * s = s * x := by
    intro x hx s hs
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hS y hy s hs
    | one => simp
    | mul y z _ _ hy hz =>
      rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
    | inv y _ hy =>
      have : y * s = s * y := hy
      calc y⁻¹ * s = y⁻¹ * (s * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * s) * y⁻¹ := by rw [this]
        _ = s * y⁻¹ := by group
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem s hs => exact hgen x hx s hs
    | one => simp
    | mul u v _ _ hu hv =>
      rw [← mul_assoc, hu, mul_assoc, hv, mul_assoc]
    | inv u _ hu =>
      calc x * u⁻¹ = u⁻¹ * (u * x) * u⁻¹ := by group
        _ = u⁻¹ * (x * u) * u⁻¹ := by rw [hu]
        _ = u⁻¹ * x := by group
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h3 y hy
  | one => simp
  | mul u v hu hv hu' hv' =>
    have hc : Commute u v := hcomm u hu v hv
    rw [hc.mul_pow, hu', hv', one_mul]
  | inv u hu hu' =>
    rw [inv_pow, hu', inv_one]

def g0 : ↥(alternatingGroup (Fin 10)) := ⟨c0, c0_mem⟩
def g1 : ↥(alternatingGroup (Fin 10)) := ⟨c1, c1_mem⟩
def g2 : ↥(alternatingGroup (Fin 10)) := ⟨c2, c2_mem⟩

def W10 : Subgroup ↥(alternatingGroup (Fin 10)) := Subgroup.closure {g0, g1, g2}

theorem W10_elemAbelian : CFSG.Open.IsElemAbelian 3 W10 := by
  apply isElemAbelian_closure
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · rfl
    · apply Subtype.ext; exact c01
    · apply Subtype.ext; exact c02
    · apply Subtype.ext; exact c01.symm
    · rfl
    · apply Subtype.ext; exact c12
    · apply Subtype.ext; exact c02.symm
    · apply Subtype.ext; exact c12.symm
    · rfl
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · apply Subtype.ext; exact c0_cube
    · apply Subtype.ext; exact c1_cube
    · apply Subtype.ext; exact c2_cube

theorem c_prod_inj : ∀ x y : Fin 3 × Fin 3 × Fin 3,
    c0 ^ (x.1 : ℕ) * c1 ^ (x.2.1 : ℕ) * c2 ^ (x.2.2 : ℕ) =
      c0 ^ (y.1 : ℕ) * c1 ^ (y.2.1 : ℕ) * c2 ^ (y.2.2 : ℕ) → x = y := by
  decide

theorem card_W10_ge : 27 ≤ Nat.card W10 := by
  have hmem : ∀ x : Fin 3 × Fin 3 × Fin 3,
      g0 ^ (x.1 : ℕ) * g1 ^ (x.2.1 : ℕ) * g2 ^ (x.2.2 : ℕ) ∈ W10 := by
    intro x
    unfold W10
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ _) (Subgroup.pow_mem _ ?_ _))
      (Subgroup.pow_mem _ ?_ _)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  let f : Fin 3 × Fin 3 × Fin 3 → ↥W10 := fun x => ⟨_, hmem x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : g0 ^ (x.1 : ℕ) * g1 ^ (x.2.1 : ℕ) * g2 ^ (x.2.2 : ℕ) =
        g0 ^ (y.1 : ℕ) * g1 ^ (y.2.1 : ℕ) * g2 ^ (y.2.2 : ℕ) := congrArg Subtype.val hxy
    have h2 : c0 ^ (x.1 : ℕ) * c1 ^ (x.2.1 : ℕ) * c2 ^ (x.2.2 : ℕ) =
        c0 ^ (y.1 : ℕ) * c1 ^ (y.2.1 : ℕ) * c2 ^ (y.2.2 : ℕ) := by
      have := congrArg (fun z : ↥(alternatingGroup (Fin 10)) => (z : Equiv.Perm (Fin 10))) h1
      simpa [g0, g1, g2] using this
    exact c_prod_inj x y h2
  have := Nat.card_le_card_of_injective f hf
  simpa using this

end CFSG.LocalAnalysis.GLTheoremA.KD1426E27

end
