module

public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.ParabolicRootFactorData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false

@[expose] def iθ : (τ : Tag) → Fin τ.rank
  | .G2 => (0 : Fin 2)
  | .F4 => (0 : Fin 4)
  | .D4 => (2 : Fin 4)
  | .E6 => (1 : Fin 6)
  | .E7 => (0 : Fin 7)
  | .E8 => (7 : Fin 8)

@[expose] def degθ (τ : Tag) (β : Fin τ.rank → ℤ) : ℤ := β (iθ τ)

@[expose] def Jθ (τ : Tag) : Set (Fin τ.rank) := {i | i ≠ iθ τ}

@[expose] def Deg1 (τ : Tag) : Set (Fin τ.rank → ℤ) := {β | IsRoot τ β ∧ degθ τ β = 1}

@[expose] def conjSub {G : Type*} [Group G] (g : G) (A : Subgroup G) : Subgroup G :=
  A.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub_iff {G : Type*} [Group G] {g x : G} {A : Subgroup G} :
    x ∈ conjSub g A ↔ g⁻¹ * x * g ∈ A := by
  unfold conjSub
  constructor
  · rintro ⟨a, ha, rfl⟩
    have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
    exact ha
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conjSub_mul {G : Type*} [Group G] (a b : G) (A : Subgroup G) :
    conjSub (a * b) A = conjSub a (conjSub b A) := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjSub_one {G : Type*} [Group G] (A : Subgroup G) : conjSub (1 : G) A = A := by
  unfold conjSub
  ext x
  simp

theorem conjSub_mono {G : Type*} [Group G] (g : G) {A B : Subgroup G} (h : A ≤ B) :
    conjSub g A ≤ conjSub g B :=
  Subgroup.map_mono h

theorem conjSub_conjSub_inv {G : Type*} [Group G] (g : G) (A : Subgroup G) :
    conjSub g (conjSub g⁻¹ A) = A := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem mem_normalizer_of_forall_mul_eq {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (h : ∀ x ∈ A, g * x = x * g) : g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor <;> intro hx
  · have : g * x * g⁻¹ = x := by rw [h x hx]; group
    rw [this]
    exact hx
  · have hy := h (g * x * g⁻¹) hx
    have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    have hy' : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := by
      calc g⁻¹ * (g * x * g⁻¹) * g = g⁻¹ * (g * x * g⁻¹ * g) := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [← hy]
        _ = g * x * g⁻¹ := by group
    rw [hx', hy']
    exact hx


theorem mem_normalizer_of_conjSub_eq {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (h : conjSub g A = A) : g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : g * x * g⁻¹ ∈ conjSub g A ↔ x ∈ A := by
    rw [mem_conjSub_iff]
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e]
  rw [h] at h1
  exact h1.symm

@[expose] def cθ (τ : Tag) : ℤ := iform (highRoot τ) (Pi.single (iθ τ) 1)

section Facts

theorem reflect_highRoot_of_ne (τ : Tag) : ∀ j : Fin τ.rank, j ≠ iθ τ →
    reflect τ j (highRoot τ) = highRoot τ := by
  cases τ <;> decide +kernel

theorem iform_highRoot_single (τ : Tag) : ∀ j : Fin τ.rank,
    iform (highRoot τ) (Pi.single j 1) = if j = iθ τ then cθ τ else 0 := by
  cases τ <;> decide +kernel

theorem cθ_ne_zero (τ : Tag) : cθ τ ≠ 0 := by
  cases τ <;> decide +kernel

theorem iform_eq_sum_single {τ : Tag} (x y : Fin τ.rank → ℤ) :
    iform x y = ∑ j, iform x (Pi.single j 1) * y j := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem iform_highRoot_apply (τ : Tag) (v : Fin τ.rank → ℤ) :
    iform (highRoot τ) v = cθ τ * v (iθ τ) := by
  rw [iform_eq_sum_single]
  simp only [iform_highRoot_single, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

end Facts

section Groups

variable (τ : Tag) (K : Type) [Field K]

abbrev Pθ : Subgroup (ModGL τ K) := parabolicSubgroup τ K (Jθ τ)

abbrev Qθ : Subgroup (ModGL τ K) := parabolicRadical τ K (Jθ τ)

abbrev Lθ : Subgroup (ModGL τ K) := parabolicLevi τ K (Jθ τ)

abbrev Uθ : Subgroup (ModGL τ K) := rootSubgroup τ K (highRoot τ)

abbrev Uneg : Subgroup (ModGL τ K) := rootSubgroup τ K (-highRoot τ)

@[expose] def Pneg : Subgroup (ModGL τ K) :=
  adjointGroup τ K ⊓ Subgroup.normalizer (Uneg τ K : Set (ModGL τ K))

@[expose] def IsLongRootSubgroup (A : Subgroup (ModGL τ K)) : Prop :=
  ∃ g ∈ adjointGroup τ K, A = conjSub g (Uθ τ K)

end Groups

@[expose] def IsLongRoot (τ : Tag) (β : Fin τ.rank → ℤ) : Prop :=
  iform β β = iform (highRoot τ) (highRoot τ)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
