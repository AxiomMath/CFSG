module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU22
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU38
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU35
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU34

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Faithful

open CFSG.ClassicalInvolution.Q8P.P24 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Balance

variable {n : ℕ}

@[expose] def P23LiftSubF (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ →
      SecNoExit R e → SecNoExit R u →
      SecOrthLift R e 6 (piSign 3 1) → YOrth R u →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
      ∀ M M' : Subgroup Y,
        Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M (u * e) →
        Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M' (u * e) →
        conjSub g (tightCore R) ≤ M → conjSub g K' ≤ M' → (∀ a ∈ M, ∀ b ∈ M', a * b = b * a) →
          IsSubnormal M (Subgroup.centralizer ({u * e} : Set Y)) ∧
          IsSubnormal M' (Subgroup.centralizer ({u * e} : Set Y))

theorem p23LiftLF_of_subF (hE : TwinThmE.TwinThmEP n) (hT : TwinThmE.T4Supply)
    (hD4 : ModelFactD42) (hM12 : ModelFactM12) (hSub : P23LiftSubF n) :
    CIT3Below n → TL4.TightBelowRPlus 3 n →
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
      (u e g : Y), P23Cfg n Y R S t K' W u e g →
        alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ →
        SecNoExit R e → SecNoExit R u →
        SecOrthLift R e 6 (piSign 3 1) → YOrth R u →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
          ∃ Λ : Subgroup Y → Subgroup Y,
            (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
              J ≤ Λ J ∧ IsClassicalMember3 (Λ J) t) ∧
            (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
              ∀ J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), J ≠ J' →
                ∀ x ∈ Λ J, ∀ y ∈ Λ J', x * y = y * x) := by
  intro hcit hP Y _ _ R S t K' W u e g hc hα hno hnoU hEo hYo hodd
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hY : YType R u e := by
    rcases hYo with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  obtain ⟨-, halpha⟩ := p23Alpha_proved hD4 hM12 hT hcit hP Y R S t K' W u e g hc hY
  have hTwo := p23TwoN_of_fuseN hE hcit hP (p23FuseN hP) Y R S t K' W u e g hc hno
  have hOu := p23_oddCoreIn_cu_eq_bot hD4 hT hcit hP hc hno hα halpha hTwo hodd
  obtain ⟨M, M', hM, hM', hJM, hJ'M', hcomm⟩ := p23_sectionLifts hP hc hno hnoU hα hOu
  obtain ⟨sM, sM'⟩ := hSub hcit hP Y R S t K' W u e g hc hα hno hnoU hEo hYo hodd M M'
    hM hM' hJM hJ'M' hcomm
  have cM : IsClassicalMember3 M (u * e) := ⟨hM.orderOf_eq_two, hM.mem, sM, hM.nonempty_equiv⟩
  have cM' : IsClassicalMember3 M' (u * e) := ⟨hM'.orderOf_eq_two, hM'.mem, sM', hM'.nonempty_equiv⟩
  have hinv : g⁻¹ * (u * e) * g⁻¹⁻¹ = t := by
    rw [← hd.hgt]; group
  have c1 : IsClassicalMember3 (conjSub g⁻¹ M) t := by
    have := cM.conj g⁻¹
    rwa [hinv] at this
  have c2 : IsClassicalMember3 (conjSub g⁻¹ M') t := by
    have := cM'.conj g⁻¹
    rwa [hinv] at this
  have hle : ∀ {J : Subgroup Y} {M₀ : Subgroup Y}, conjSub g J ≤ M₀ → J ≤ conjSub g⁻¹ M₀ := by
    intro J M₀ h x hx
    rw [mem_conjSub_iff]
    simpa using h (conj_mem_conjSub hx)
  have hmem : ∀ {M₀ : Subgroup Y} {x : Y}, x ∈ conjSub g⁻¹ M₀ → g * x * g⁻¹ ∈ M₀ := by
    intro M₀ x hx
    rw [mem_conjSub_iff] at hx
    simpa using hx
  have hpair := twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne
  classical
  refine ⟨fun J => if J = tightCore R then conjSub g⁻¹ M else conjSub g⁻¹ M', ?_, ?_⟩
  · intro J hJ
    rw [hpair] at hJ
    rcases hJ with rfl | rfl
    · simp only [if_true]
      exact ⟨hle hJM, c1⟩
    · simp only [if_neg hc.std.hne]
      exact ⟨hle hJ'M', c2⟩
  · intro J hJ J' hJ' hne x hx y hy
    rw [hpair] at hJ hJ'
    have key : ∀ x ∈ conjSub g⁻¹ M, ∀ y ∈ conjSub g⁻¹ M', x * y = y * x := by
      intro x hx y hy
      have h := hcomm _ (hmem hx) _ (hmem hy)
      have h2 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
          _ = (g * y * g⁻¹) * (g * x * g⁻¹) := h
          _ = g * (y * x) * g⁻¹ := by group
      simpa using h2
    rcases hJ with rfl | rfl <;> rcases hJ' with rfl | rfl
    · exact absurd rfl hne
    · simp only [if_true, if_neg hc.std.hne] at hx hy
      exact key x hx y hy
    · simp only [if_true, if_neg hc.std.hne] at hx hy
      exact (key y hy x hx).symm
    · exact absurd rfl hne

@[expose] def P23LiftCentF (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ →
      SecNoExit R e → SecNoExit R u →
      SecOrthLift R e 6 (piSign 3 1) → YOrth R u →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
      ∀ M M' : Subgroup Y,
        Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M (u * e) →
        Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M' (u * e) →
        conjSub g (tightCore R) ≤ M → conjSub g K' ≤ M' → (∀ a ∈ M, ∀ b ∈ M', a * b = b * a) →
          (∀ c ∈ Subgroup.centralizer ({u * e} : Set Y), ∀ m ∈ M, m * (c * u * c⁻¹) = (c * u * c⁻¹) * m) ∧
          (∀ c ∈ Subgroup.centralizer ({u * e} : Set Y), ∀ m ∈ M', m * (c * u * c⁻¹) = (c * u * c⁻¹) * m)

theorem p23LiftSubF_of_centF (h : P23LiftCentF n) : P23LiftSubF n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hα hno hnoU hEo hYo hodd M M' hM hM' hJM hJ'M' hcomm
  obtain ⟨h1, h2⟩ := h hcit hP Y R S t K' W u e g hc hα hno hnoU hEo hYo hodd M M' hM hM' hJM hJ'M'
    hcomm
  exact ⟨isSubnormal_of_cent_class hM h1, isSubnormal_of_cent_class hM' h2⟩

@[expose] def P23YExitNE' (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R u → SecNoExit R e →
      SecOrthLift R e 6 (piSign 3 1) → False

end Faithful

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
