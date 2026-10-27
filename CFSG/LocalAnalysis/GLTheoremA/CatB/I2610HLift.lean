module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFixInf
import CFSG.HardMathSupport.Solomon.Coordinator.FixSubgroupInf
import CFSG.LinearAlgebra.ProjectivePrimePlane
import TauCeti.GroupTheory.Commutator
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Fischer CFSG.StandardType CFSG.Assembly
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.HardMathSupport.Solomon.Coordinator
  (fixSubgroup mem_fixSubgroup iInf_fixSubgroup_closure)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open scoped commutatorElement

private def Induces (B : GL (Fin 6) F4) (β : MulAut S6) : Prop :=
  ∀ u v : M6, (v : GL (Fin 6) F4) = B * (u : GL (Fin 6) F4) * B⁻¹ →
    β (QuotientGroup.mk u) = QuotientGroup.mk v

private theorem induces_one : Induces (1 : GL (Fin 6) F4) (1 : MulAut S6) := by
  intro u v huv
  have hv : v = u := Subtype.ext (by simpa using huv)
  subst hv
  rfl

private theorem induces_scalar (c : F4ˣ) :
    Induces (Matrix.GeneralLinearGroup.scalar (Fin 6) c) (1 : MulAut S6) := by
  intro u v huv
  have hv : v = u := Subtype.ext (by
    rw [huv]
    rw [(commute_scalar c (u : GL (Fin 6) F4)).eq.symm]
    group)
  subst hv
  rfl

private theorem semilin_mem_M6 {C : GL (Fin 6) F4}
    (hC : C ∈ primeFormUnitary hF4 (idGram F4 6)) (u : M6) :
    C * (u : GL (Fin 6) F4) * C⁻¹ ∈ StatedSU 6 (2 ^ 1) F4 := by
  let u' : GL (Fin 6) F4 := (u : GL (Fin 6) F4)
  change C * u' * C⁻¹ ∈ StatedSU 6 (2 ^ 1) F4
  have hEq : gramSU hF4 (idGram F4 6) = unitarySU 2 1 F4 6 := by
    rw [unitarySU_eq_gramSU hF4 6]
    simp [idGram]
  rw [← gramSU_idGram_six, hEq]
  simpa [u'] using InndiagSU.semilin_mem hF4 hC 1 u

private theorem induces_mul {B C : GL (Fin 6) F4} {β γ : MulAut S6}
    (hB : Induces B β) (hC : Induces C γ)
    (hCmem : C ∈ primeFormUnitary hF4 (idGram F4 6)) :
    Induces (B * C) (β * γ) := by
  intro u v huv
  let w : M6 := ⟨C * (u : GL (Fin 6) F4) * C⁻¹, semilin_mem_M6 hCmem u⟩
  have hw : (w : GL (Fin 6) F4) = C * (u : GL (Fin 6) F4) * C⁻¹ := rfl
  have h1 : γ (QuotientGroup.mk u) = QuotientGroup.mk w := hC u w hw
  have h2 : β (QuotientGroup.mk w) = QuotientGroup.mk v := by
    refine hB w v ?_
    rw [huv, hw]
    group
  rw [MulAut.mul_apply, h1, h2]

private theorem induces_inv {B : GL (Fin 6) F4} {β : MulAut S6}
    (hB : Induces B β) : Induces B⁻¹ β⁻¹ := by
  intro u v huv
  have h1 : β (QuotientGroup.mk v) = QuotientGroup.mk u := by
    refine hB v u ?_
    rw [huv]
    group
  change β.symm (QuotientGroup.mk u) = QuotientGroup.mk v
  rw [← h1]
  simp

private theorem induces_pow {B : GL (Fin 6) F4} {β : MulAut S6}
    (hB : Induces B β) (hBmem : B ∈ primeFormUnitary hF4 (idGram F4 6)) :
    ∀ k : ℕ, Induces (B ^ k) (β ^ k)
  | 0 => by simpa using induces_one
  | k + 1 => by
      rw [pow_succ, pow_succ]
      exact induces_mul (induces_pow hB hBmem k) hB hBmem

private theorem induces_unique {B : GL (Fin 6) F4} {β γ : MulAut S6}
    (hβ : Induces B β) (hγ : Induces B γ)
    (hB : B ∈ primeFormUnitary hF4 (idGram F4 6)) : β = γ := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  let v : M6 := ⟨B * (u : GL (Fin 6) F4) * B⁻¹, semilin_mem_M6 hB u⟩
  exact (hβ u v rfl).trans (hγ u v rfl).symm

private theorem cube_mul_eq_of_commutator_scalar {G : Type*} [Group G] {x y z : G}
    (hz : ∀ g : G, z * g = g * z) (hz3 : z ^ 3 = 1)
    (h : y * x = z * (x * y)) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hcomm : ⁅y, x⁆ = z := by
    rw [commutatorElement_def, h]
    group
  have hcx : Commute x ⁅y, x⁆ := by
    rw [hcomm]
    exact (hz x).symm
  have hcy : Commute y ⁅y, x⁆ := by
    rw [hcomm]
    exact (hz y).symm
  have hpow := Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two
    (a := x) (b := y) hcx hcy 3
  simpa [hcomm, hz3] using hpow

private theorem mul_mul_eq_scalar_mul_mul {x y S : GL (Fin 6) F4}
    (h : x * y = S * (y * x)) (hS : ∀ g : GL (Fin 6) F4, S * g = g * S) :
    (x * y) * y = S * (y * (x * y)) := by
  have hyx : y * x = S⁻¹ * (x * y) := by
    have h' := congrArg (fun t => S⁻¹ * t) h
    rw [← mul_assoc S⁻¹ S (y * x), inv_mul_cancel, one_mul] at h'
    exact h'.symm
  calc (x * y) * y = S * (S⁻¹ * ((x * y) * y)) := by group
    _ = S * ((S⁻¹ * (x * y)) * y) := by group
    _ = S * ((y * x) * y) := by rw [hyx]
    _ = S * (y * (x * y)) := by group

private theorem exists_scalar_commutator {B₁ B₂ : GL (Fin 6) F4} {β₁ β₂ : MulAut S6}
    (hB₁ : Induces B₁ β₁) (hB₂ : Induces B₂ β₂)
    (hB₁mem : B₁ ∈ primeFormUnitary hF4 (idGram F4 6))
    (hB₂mem : B₂ ∈ primeFormUnitary hF4 (idGram F4 6))
    (hcomm : β₁ * β₂ = β₂ * β₁) :
    ∃ s : F4ˣ, B₁ * B₂ = Matrix.GeneralLinearGroup.scalar (Fin 6) s * (B₂ * B₁) := by
  have hNmem : B₁⁻¹ * B₂⁻¹ * B₁ * B₂ ∈ primeFormUnitary hF4 (idGram F4 6) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ hB₁mem) (Subgroup.inv_mem _ hB₂mem)) hB₁mem) hB₂mem
  have hNind : Induces (B₁⁻¹ * B₂⁻¹ * B₁ * B₂) (β₁⁻¹ * β₂⁻¹ * β₁ * β₂) := by
    have h1 : Induces (B₁⁻¹ * B₂⁻¹) (β₁⁻¹ * β₂⁻¹) :=
      induces_mul (induces_inv hB₁) (induces_inv hB₂) (Subgroup.inv_mem _ hB₂mem)
    have h2 : Induces ((B₁⁻¹ * B₂⁻¹) * B₁) ((β₁⁻¹ * β₂⁻¹) * β₁) :=
      induces_mul h1 hB₁ hB₁mem
    have h3 : Induces (((B₁⁻¹ * B₂⁻¹) * B₁) * B₂) (((β₁⁻¹ * β₂⁻¹) * β₁) * β₂) :=
      induces_mul h2 hB₂ hB₂mem
    simpa [mul_assoc] using h3
  have hprod : β₁⁻¹ * β₂⁻¹ * β₁ * β₂ = 1 := by
    calc β₁⁻¹ * β₂⁻¹ * β₁ * β₂ = β₁⁻¹ * β₂⁻¹ * (β₁ * β₂) := by group
      _ = β₁⁻¹ * β₂⁻¹ * (β₂ * β₁) := by rw [hcomm]
      _ = 1 := by group
  have hNind1 : Induces (B₁⁻¹ * B₂⁻¹ * B₁ * B₂) 1 := by
    simpa [hprod] using hNind
  have hsem : InndiagSU.IsSemilin (InndiagSU.projU 1 6 F4) (1 : MulAut S6)
      (B₁⁻¹ * B₂⁻¹ * B₁ * B₂) 1 := by
    intro u v huv
    exact hNind1 u v (by simpa using huv)
  have hP : (1 : GL (Fin 6) F4) ∈ primeFormUnitary hF4 (idGram F4 6) :=
    Subgroup.one_mem _
  have hfr : InndiagSU.IsSemilin (InndiagSU.frameMk hF4 1 hP) (1 : MulAut S6)
      (B₁⁻¹ * B₂⁻¹ * B₁ * B₂) 1 := by
    simpa using hsem.frame hF4 1 hP
  have hd : 3 ≤ 6 := by norm_num
  have hsc := InndiagSU.mem_scalars_of_isSemilin_one hF4 hF4card hd (by decide)
    Nat.prime_three (by norm_num) 1 hP hNmem hfr
  obtain ⟨s, hs⟩ := hsc
  refine ⟨s, ?_⟩
  have hN : B₁⁻¹ * B₂⁻¹ * B₁ * B₂ = Matrix.GeneralLinearGroup.scalar (Fin 6) s := by
    simpa [LargeEvenScalars, StatedScalars] using hs.symm
  have h1 : B₂⁻¹ * B₁ * B₂ = B₁ * Matrix.GeneralLinearGroup.scalar (Fin 6) s := by
    calc B₂⁻¹ * B₁ * B₂ = B₁ * (B₁⁻¹ * B₂⁻¹ * B₁ * B₂) := by group
      _ = B₁ * Matrix.GeneralLinearGroup.scalar (Fin 6) s := by rw [hN]
  have h2 : B₁ * B₂ = B₂ * B₁ * Matrix.GeneralLinearGroup.scalar (Fin 6) s := by
    calc B₁ * B₂ = B₂ * (B₂⁻¹ * B₁ * B₂) := by group
      _ = B₂ * (B₁ * Matrix.GeneralLinearGroup.scalar (Fin 6) s) := by rw [h1]
      _ = B₂ * B₁ * Matrix.GeneralLinearGroup.scalar (Fin 6) s := by group
  calc B₁ * B₂ = B₂ * B₁ * Matrix.GeneralLinearGroup.scalar (Fin 6) s := h2
    _ = Matrix.GeneralLinearGroup.scalar (Fin 6) s * (B₂ * B₁) :=
      (commute_scalar s (B₂ * B₁)).eq

private theorem closure_mul_pow_pair {G : Type*} [Group G] (x y : G) (m : ℕ) :
    Subgroup.closure ({x * y ^ m, y} : Set G) = Subgroup.closure ({x, y} : Set G) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz1 | hz2
    · rw [hz1]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) m)
    · rw [hz2]
      exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le _).2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz1 | hz2
    · rw [hz1]
      have h1 : x * y ^ m ∈ Subgroup.closure ({x * y ^ m, y} : Set G) :=
        Subgroup.subset_closure (by simp)
      have h2 : y ∈ Subgroup.closure ({x * y ^ m, y} : Set G) :=
        Subgroup.subset_closure (by simp)
      have h3 : (x * y ^ m) * (y ^ m)⁻¹ ∈
          Subgroup.closure ({x * y ^ m, y} : Set G) :=
        Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.pow_mem _ h2 m))
      have hx : (x * y ^ m) * (y ^ m)⁻¹ = x := by group
      rw [hx] at h3
      exact h3
    · rw [hz2]
      exact Subgroup.subset_closure (by simp)

private theorem card_le_three_of_le_zpowers {A : Subgroup (MulAut S6)} {g : MulAut S6}
    (hg : g ^ 3 = 1) (h : A ≤ Subgroup.zpowers g) : Nat.card A ≤ 3 := by
  have hle : Nat.card A ≤ Nat.card (Subgroup.zpowers g) := Subgroup.card_le_of_le h
  rw [Nat.card_zpowers] at hle
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg
  have h3 : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private structure PairData (A : Subgroup (MulAut S6)) where
  X : primeFormUnitary hF4 (idGram F4 6)
  Y : primeFormUnitary hF4 (idGram F4 6)
  γ : MulAut S6
  δ : MulAut S6
  indX : Induces (X : GL (Fin 6) F4) γ
  indY : Induces (Y : GL (Fin 6) F4) δ
  gen : Subgroup.closure ({γ, δ} : Set (MulAut S6)) = A
  X3 : (X : GL (Fin 6) F4) ^ 3 = 1
  Y3 : ∃ c : F4ˣ, (Y : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c
  comm : ∃ t : F4ˣ, (X : GL (Fin 6) F4) * (Y : GL (Fin 6) F4) =
    Matrix.GeneralLinearGroup.scalar (Fin 6) t * ((Y : GL (Fin 6) F4) * (X : GL (Fin 6) F4))

private theorem exists_pair_data {A : Subgroup (MulAut S6)} (hA : IsElemAbelian 3 A)
    (h9 : Nat.card A = 3 ^ 2) : Nonempty (PairData A) := by
  obtain ⟨a, haA, b, hbA, hgen⟩ :=
    CFSG.LinearAlgebra.ProjectivePrimePlane.exists_closure_pair_eq Nat.prime_three hA.2 h9
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hb3 : b ^ 3 = 1 := hA.2 b hbA
  obtain ⟨B₁, hB₁mem, ⟨c₁, hc₁⟩, hB₁ind⟩ := exists_unitary_of_pow_three a ha3
  obtain ⟨B₂, hB₂mem, ⟨c₂, hc₂⟩, hB₂ind⟩ := exists_unitary_of_pow_three b hb3
  have hab : a * b = b * a := isElemAbelian_commute hA haA hbA
  obtain ⟨s, hs⟩ := exists_scalar_commutator hB₁ind hB₂ind hB₁mem hB₂mem hab
  set S : GL (Fin 6) F4 := Matrix.GeneralLinearGroup.scalar (Fin 6) s with hSdef
  have hcube : ∀ c : F4ˣ, c ^ 3 = 1 := by decide
  have hS3 : S ^ 3 = 1 := by
    rw [hSdef, ← map_pow, hcube s, map_one]
  have hSc : ∀ g : GL (Fin 6) F4, S * g = g * S := by
    intro g
    rw [hSdef]
    exact (commute_scalar s g).eq.symm
  have hSinv3 : S⁻¹ ^ 3 = 1 := by
    rw [hSdef, ← map_inv, ← map_pow, hcube s⁻¹, map_one]
  have hSinvc : ∀ g : GL (Fin 6) F4, S⁻¹ * g = g * S⁻¹ := by
    intro g
    rw [hSdef]
    exact (commute_scalar s⁻¹ g).eq.symm
  have hrel : (B₂ : GL (Fin 6) F4) * (B₁ : GL (Fin 6) F4) =
      S⁻¹ * ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) := by
    have h' : S⁻¹ * ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) =
        (B₂ : GL (Fin 6) F4) * (B₁ : GL (Fin 6) F4) := by
      rw [hs]
      group
    exact h'.symm
  let X₁ : primeFormUnitary hF4 (idGram F4 6) := ⟨B₁, hB₁mem⟩
  let X₂ : primeFormUnitary hF4 (idGram F4 6) := ⟨B₂, hB₂mem⟩
  have hcase : c₁ = 1 ∨ c₂ = 1 ∨ c₁ * c₂ = 1 ∨ c₁ * c₂ ^ 2 = 1 := by
    by_cases h1 : c₁ = 1
    · exact Or.inl h1
    by_cases h2 : c₂ = 1
    · exact Or.inr (Or.inl h2)
    by_cases h3 : c₁ * c₂ = 1
    · exact Or.inr (Or.inr (Or.inl h3))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have h4 : ∀ u v : F4ˣ, u ≠ 1 → v ≠ 1 → u * v ≠ 1 → v = u ∧ u * v ^ 2 = 1 := by
        decide
      exact (h4 c₁ c₂ h1 h2 h3).2
  rcases hcase with h1 | h2 | h3 | h4
  ·
    exact ⟨{ X := X₁
             Y := X₂
             γ := a
             δ := b
             indX := hB₁ind
             indY := hB₂ind
             gen := hgen
             X3 := by
               change B₁ ^ 3 = 1
               rw [hc₁, h1]
               exact map_one _
             Y3 := ⟨c₂, hc₂⟩
             comm := ⟨s, by simpa [hSdef] using hs⟩ }⟩
  ·
    have hgen' : Subgroup.closure ({b, a} : Set (MulAut S6)) = A := by
      simpa [Set.pair_comm] using hgen
    exact ⟨{ X := X₂
             Y := X₁
             γ := b
             δ := a
             indX := hB₂ind
             indY := hB₁ind
             gen := hgen'
             X3 := by
               change B₂ ^ 3 = 1
               rw [hc₂, h2]
               exact map_one _
             Y3 := ⟨c₁, hc₁⟩
             comm := ⟨s⁻¹, by simpa [hSdef] using hrel⟩ }⟩
  ·
    have hXind : Induces ((X₁ * X₂ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4)
        (a * b) := by
      simpa using induces_mul hB₁ind hB₂ind hB₂mem
    have hgen' : Subgroup.closure ({a * b, b} : Set (MulAut S6)) = A := by
      simpa using (closure_mul_pow_pair a b 1).trans hgen
    have hcubeB : ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) ^ 3 =
        (B₁ : GL (Fin 6) F4) ^ 3 * (B₂ : GL (Fin 6) F4) ^ 3 :=
      cube_mul_eq_of_commutator_scalar hSinvc hSinv3 hrel
    have hX3 : ((X₁ * X₂ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) ^ 3 = 1 := by
      change ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) ^ 3 = 1
      rw [hcubeB, hc₁, hc₂, ← map_mul, h3, map_one]
    have hcommX : ((X₁ * X₂ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) *
          (X₂ : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) s *
          ((X₂ : GL (Fin 6) F4) *
            ((X₁ * X₂ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4)) := by
      change ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) * (B₂ : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) s *
          ((B₂ : GL (Fin 6) F4) * ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)))
      simpa [hSdef] using mul_mul_eq_scalar_mul_mul hs hSc
    exact ⟨{ X := X₁ * X₂
             Y := X₂
             γ := a * b
             δ := b
             indX := hXind
             indY := hB₂ind
             gen := hgen'
             X3 := hX3
             Y3 := ⟨c₂, hc₂⟩
             comm := ⟨s, hcommX⟩ }⟩
  ·
    have hB₂2ind : Induces ((X₂ ^ 2 : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4)
        (b ^ 2) := by
      simpa using induces_pow hB₂ind hB₂mem 2
    have hXind : Induces ((X₁ * X₂ ^ 2 : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4)
        (a * b ^ 2) := by
      have := induces_mul hB₁ind hB₂2ind (Subgroup.pow_mem _ hB₂mem 2)
      simpa using this
    have hgen' : Subgroup.closure ({a * b ^ 2, b} : Set (MulAut S6)) = A := by
      simpa using (closure_mul_pow_pair a b 2).trans hgen
    have hrel2 : (B₂ : GL (Fin 6) F4) * ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) =
        S⁻¹ * (((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) * (B₂ : GL (Fin 6) F4)) := by
      calc (B₂ : GL (Fin 6) F4) * ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4))
          = ((B₂ : GL (Fin 6) F4) * (B₁ : GL (Fin 6) F4)) * (B₂ : GL (Fin 6) F4) := by group
        _ = (S⁻¹ * ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4))) * (B₂ : GL (Fin 6) F4) := by
            rw [hrel]
        _ = S⁻¹ * (((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) * (B₂ : GL (Fin 6) F4)) := by
            group
    have hK : ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) ^ 3 =
        (B₁ : GL (Fin 6) F4) ^ 3 * (B₂ : GL (Fin 6) F4) ^ 3 :=
      cube_mul_eq_of_commutator_scalar hSinvc hSinv3 hrel
    have hK2 : (((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) * (B₂ : GL (Fin 6) F4)) ^ 3 =
        ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) ^ 3 *
          (B₂ : GL (Fin 6) F4) ^ 3 :=
      cube_mul_eq_of_commutator_scalar hSinvc hSinv3 hrel2
    have hbase : (B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4) ^ 2 =
        ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) * (B₂ : GL (Fin 6) F4) := by
      rw [pow_two]
      group
    have hX3 : ((X₁ * X₂ ^ 2 : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) ^ 3 = 1 := by
      change ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4) ^ 2) ^ 3 = 1
      rw [hbase, hK2, hK, hc₁, hc₂]
      rw [← map_mul, ← map_mul,
        show c₁ * c₂ * c₂ = c₁ * c₂ ^ 2 by rw [pow_two]; group, h4, map_one]
    have hxy' : ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) * (B₂ : GL (Fin 6) F4) =
        S * ((B₂ : GL (Fin 6) F4) * ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4))) := by
      calc ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4)) * (B₂ : GL (Fin 6) F4)
          = (S * ((B₂ : GL (Fin 6) F4) * (B₁ : GL (Fin 6) F4))) * (B₂ : GL (Fin 6) F4) := by
            rw [hs]
        _ = S * ((B₂ : GL (Fin 6) F4) * ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4))) := by
            group
    have hcomm2 := mul_mul_eq_scalar_mul_mul (x := (B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4))
      (y := (B₂ : GL (Fin 6) F4)) (S := S) hxy' hSc
    have hcommX : ((X₁ * X₂ ^ 2 : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) *
          (X₂ : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) s *
          ((X₂ : GL (Fin 6) F4) *
            ((X₁ * X₂ ^ 2 : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4)) := by
      change ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4) ^ 2) * (B₂ : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) s *
          ((B₂ : GL (Fin 6) F4) * ((B₁ : GL (Fin 6) F4) * (B₂ : GL (Fin 6) F4) ^ 2))
      rw [hbase]
      simpa [hSdef] using hcomm2
    exact ⟨{ X := X₁ * X₂ ^ 2
             Y := X₂
             γ := a * b ^ 2
             δ := b
             indX := hXind
             indY := hB₂ind
             gen := hgen'
             X3 := hX3
             Y3 := ⟨c₂, hc₂⟩
             comm := ⟨s, hcommX⟩ }⟩

theorem exists_pair_of_elemAbelian_nine {A : Subgroup (MulAut S6)} (hA : IsElemAbelian 3 A)
    (h9 : Nat.card A = 3 ^ 2) {I : Subgroup S6}
    (hI : GLAPComponent 3 (⨅ f ∈ A, fixSubgroup f) I) :
    ∃ X Y : primeFormUnitary hF4 (idGram F4 6), X ^ 3 = 1 ∧
      (∃ c : F4ˣ, (Y : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) ∧
      (∃ t : F4ˣ, (X : GL (Fin 6) F4) * (Y : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) t * ((Y : GL (Fin 6) F4) * (X : GL (Fin 6) F4))) ∧
      (¬ ∃ c : F4ˣ, (X : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c) ∧
      (∀ (k : ℕ) (c : F4ˣ), (Y : GL (Fin 6) F4) ≠
        Matrix.GeneralLinearGroup.scalar (Fin 6) c * (X : GL (Fin 6) F4) ^ k) ∧
      ∃ J : Subgroup M6,
        GLAPComponent 3 (CenD (X : GL (Fin 6) F4) ⊓ CenD (Y : GL (Fin 6) F4)) J ∧
        Nonempty (PSimple 3 I ≃* PSimple 3 J) := by
  obtain ⟨P⟩ := exists_pair_data hA h9
  obtain ⟨X, Y, γ, δ, hXind, hYind, hgen, hX3, hY3, hcomm⟩ := P
  have hγ3 : γ ^ 3 = 1 := by
    have hγA : γ ∈ A := by
      rw [← hgen]
      exact Subgroup.subset_closure (by simp)
    exact hA.2 γ hγA
  have hδ3 : δ ^ 3 = 1 := by
    have hδA : δ ∈ A := by
      rw [← hgen]
      exact Subgroup.subset_closure (by simp)
    exact hA.2 δ hδA
  have hγ1 : γ ≠ 1 := by
    intro hγ
    have hAle : A ≤ Subgroup.zpowers δ := by
      rw [← hgen]
      exact (Subgroup.closure_le _).2 (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hzγ | hzδ
        · rw [hzγ, hγ]
          exact Subgroup.one_mem _
        · rw [hzδ]
          exact Subgroup.mem_zpowers δ)
    have hle := card_le_three_of_le_zpowers hδ3 hAle
    omega
  have hXns : ¬ ∃ c : F4ˣ,
      (X : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rintro ⟨c, hc⟩
    have hind1 : Induces (X : GL (Fin 6) F4) (1 : MulAut S6) := by
      rw [hc]
      exact induces_scalar c
    exact hγ1 (induces_unique hXind hind1 X.2)
  have hYcond : ∀ (k : ℕ) (c : F4ˣ), (Y : GL (Fin 6) F4) ≠
      Matrix.GeneralLinearGroup.scalar (Fin 6) c * (X : GL (Fin 6) F4) ^ k := by
    intro k c hEq
    have hpow : Induces ((X : GL (Fin 6) F4) ^ k) (γ ^ k) := induces_pow hXind X.2 k
    have hYind' : Induces (Y : GL (Fin 6) F4) (γ ^ k) := by
      rw [hEq]
      have := induces_mul (induces_scalar c) hpow (Subgroup.pow_mem _ X.2 k)
      simpa using this
    have hδeq : δ = γ ^ k := induces_unique hYind hYind' Y.2
    have hAle : A ≤ Subgroup.zpowers γ := by
      rw [← hgen]
      exact (Subgroup.closure_le _).2 (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hzγ | hzδ
        · rw [hzγ]
          exact Subgroup.mem_zpowers γ
        · rw [hzδ, hδeq]
          exact Subgroup.pow_mem _ (Subgroup.mem_zpowers γ) k)
    have hle := card_le_three_of_le_zpowers hγ3 hAle
    omega
  have hfix : (⨅ f ∈ A, fixSubgroup f) = fixSubgroup γ ⊓ fixSubgroup δ := by
    rw [← hgen, iInf_fixSubgroup_closure, iInf_pair]
  set π : M6 →* S6 :=
    QuotientGroup.mk' ((StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4)) with hπ
  have hker : π.ker ≤ Subgroup.center M6 := by
    intro z hz
    rw [hπ, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hz
    obtain ⟨c, hc⟩ := hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : GL (Fin 6) F4) * z = z * g
    rw [← hc]
    exact (commute_scalar c (g : GL (Fin 6) F4)).eq
  let α : Bool → MulAut M6 := fun i => cond i (conjM6 X) (conjM6 Y)
  let β : Bool → MulAut S6 := fun i => cond i γ δ
  have hαβ : ∀ i k, π (α i k) = β i (π k) := by
    intro i k
    cases i
    · simpa [α, β, hπ, QuotientGroup.mk'_apply] using (hYind k (conjM6 Y k) rfl).symm
    · simpa [α, β, hπ, QuotientGroup.mk'_apply] using (hXind k (conjM6 X k) rfl).symm
  have hβfix : (⨅ i : Bool, fixSubgroup (β i)) = fixSubgroup γ ⊓ fixSubgroup δ := by
    rw [iInf_bool_eq]
    rfl
  have hIβ : GLAPComponent 3 (⨅ i : Bool, fixSubgroup (β i)) I := by
    rw [hβfix, ← hfix]
    exact hI
  obtain ⟨J, hJ, hJmap⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_map_iInf_fixSubgroup
      π hker α β hαβ (QuotientGroup.mk'_surjective _) Nat.prime_three hIβ
  have hαfix : (⨅ i : Bool, fixSubgroup (α i)) =
      CenD (X : GL (Fin 6) F4) ⊓ CenD (Y : GL (Fin 6) F4) := by
    rw [iInf_bool_eq]
    simp [α, fixSubgroup_conjM6]
  have hJ' : GLAPComponent 3
      (CenD (X : GL (Fin 6) F4) ⊓ CenD (Y : GL (Fin 6) F4)) J := by
    rw [← hαfix]
    exact hJ
  have hJmapcomp : GLAPComponent 3 (⨅ f ∈ A, fixSubgroup f) (J.map π) := by
    rw [hJmap]
    exact hI
  obtain ⟨e⟩ := nonempty_pSimple_equiv_map Nat.prime_three π hJ' hJmapcomp
  rw [hJmap] at e
  have hX3' : X ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hX3
  exact ⟨X, Y, hX3', hY3, hcomm, hXns, hYcond, J, hJ', ⟨e.symm⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610
