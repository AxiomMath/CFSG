module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSquare
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveToralBasis
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveToralTriple

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq
open CFSG.RankThree.E6 (charVal)

set_option linter.unusedSectionVars false

theorem exists_column_of_mem {K : Type} [Field K] [Finite K] {ω : (AlgebraicClosure K)ˣ}
    (hω : orderOf ω = 5) {E₀ : Subgroup (adjointGroup Tag.E8 K)}
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (D : LangPlaneData Tag.E8 K E₀)
    {x : adjointGroup Tag.E8 K} (hx : x ∈ E₀) :
    ∃ k : Fin Tag.E8.rank → ℕ, rootDiagUnit Tag.E8 (fun l => ω ^ k l) = diagMap D x := by
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
  have h5 := pow_five_eq_one_of_rootDiagUnit_eq hE₀p D hx ha
  choose k hk using fun i =>
    exists_pow_eq_of_orderOf_five hω (by simpa using congrFun h5 i)
  refine ⟨k, ?_⟩
  rw [← ha]
  congr 1
  funext l
  exact (hk l).symm

theorem kills_of_columns {K : Type} [Field K] [Finite K] {ω : (AlgebraicClosure K)ˣ}
    (hω : orderOf ω = 5) {E₀ : Subgroup (adjointGroup Tag.E8 K)}
    (D : LangPlaneData Tag.E8 K E₀) {x₀ x₁ x₂ : adjointGroup Tag.E8 K}
    (hgen : E₀ ≤ Subgroup.closure {x₀, x₁, x₂}) {k₀ k₁ k₂ : Fin Tag.E8.rank → ℕ}
    (ha₀ : rootDiagUnit Tag.E8 (fun l => ω ^ k₀ l) = diagMap D x₀)
    (ha₁ : rootDiagUnit Tag.E8 (fun l => ω ^ k₁ l) = diagMap D x₁)
    (ha₂ : rootDiagUnit Tag.E8 (fun l => ω ^ k₂ l) = diagMap D x₂)
    {α : Fin Tag.E8.rank → ℤ}
    (h₀ : charVal (fun i => ((k₀ i : ℕ) : ZMod 5)) α = 0)
    (h₁ : charVal (fun i => ((k₁ i : ℕ) : ZMod 5)) α = 0)
    (h₂ : charVal (fun i => ((k₂ i : ℕ) : ZMod 5)) α = 0) : D.Kills α := by
  set Sg : Subgroup (adjointGroup Tag.E8 K) :=
    ((rootCharHom (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom Tag.E8 (AlgebraicClosure K))).comap (diagMap D) with hSg
  have hmemS : ∀ (x : adjointGroup Tag.E8 K) (a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit Tag.E8 a = diagMap D x → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hα1
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, ?_, hax⟩)
    exact hα1
  have hx₀S : x₀ ∈ Sg :=
    hmemS x₀ _ ha₀ (rootChar_eq_one_of_charVal_eq_zero hω (fun _ => rfl) h₀)
  have hx₁S : x₁ ∈ Sg :=
    hmemS x₁ _ ha₁ (rootChar_eq_one_of_charVal_eq_zero hω (fun _ => rfl) h₁)
  have hx₂S : x₂ ∈ Sg :=
    hmemS x₂ _ ha₂ (rootChar_eq_one_of_charVal_eq_zero hω (fun _ => rfl) h₂)
  have hAS : E₀ ≤ Sg := hgen.trans ((Subgroup.closure_le Sg).2 (by
    rintro y (rfl | rfl | rfl)
    · exact hx₀S
    · exact hx₁S
    · exact hx₂S))
  intro x hx
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hx))
  exact ⟨a, by rw [← diagMap_apply]; exact hax, ha⟩

theorem exists_cubeColumns {K : Type} [Field K] [Finite K] {ω : (AlgebraicClosure K)ˣ}
    (hω : orderOf ω = 5) {E₀ : Subgroup (adjointGroup Tag.E8 K)}
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀m : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a)
    (hE₀c : Nat.card E₀ = 5 ^ 3) (D : LangPlaneData Tag.E8 K E₀)
    (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) :
    ∃ x₀ ∈ E₀, ∃ x₁ ∈ E₀, ∃ x₂ ∈ E₀,
      (∀ i j k : ℕ, x₀ ^ i * x₁ ^ j * x₂ ^ k = 1 → 5 ∣ i ∧ 5 ∣ j ∧ 5 ∣ k) ∧
      ∃ k₀ k₁ k₂ : Fin Tag.E8.rank → ℕ,
        rootDiagUnit Tag.E8 (fun l => ω ^ k₀ l) = diagMap D x₀ ∧
        rootDiagUnit Tag.E8 (fun l => ω ^ k₁ l) = diagMap D x₁ ∧
        rootDiagUnit Tag.E8 (fun l => ω ^ k₂ l) = diagMap D x₂ ∧
        ∀ α, IsRoot Tag.E8 α → charVal (fun i => ((k₀ i : ℕ) : ZMod 5)) α = 0 →
          charVal (fun i => ((k₁ i : ℕ) : ZMod 5)) α = 0 →
          charVal (fun i => ((k₂ i : ℕ) : ZMod 5)) α = 0 → False := by
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, hgen, hrel⟩ := exists_basis_of_cube hE₀m hE₀p hE₀c
  obtain ⟨k₀, ha₀⟩ := exists_column_of_mem hω hE₀p D hx₀
  obtain ⟨k₁, ha₁⟩ := exists_column_of_mem hω hE₀p D hx₁
  obtain ⟨k₂, ha₂⟩ := exists_column_of_mem hω hE₀p D hx₂
  exact ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, hrel, k₀, k₁, k₂, ha₀, ha₁, ha₂,
    fun α hα h₀ h₁ h₂ => hreg α hα (kills_of_columns hω D hgen ha₀ ha₁ ha₂ h₀ h₁ h₂)⟩

theorem exists_eigenTriple_of_langPlaneData {K : Type} [Field K] [Finite K]
    (hpK : ¬ 5 ∣ Nat.card K) {E₀ : Subgroup (adjointGroup Tag.E8 K)}
    (hE₀ : CFSG.Open.IsElemAbelian 5 E₀) (hE₀c : Nat.card E₀ = 5 ^ 3)
    (D : LangPlaneData Tag.E8 K E₀) (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) :
    ∃ z : Fin 3 → Fin Tag.E8.rank → ZMod 5,
      EigenTriple D.w ((Nat.card K : ℕ) : ZMod 5) z := by
  have hE₀p : ∀ x ∈ E₀, x ^ 5 = 1 := hE₀.2
  have hE₀m : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_five_of_not_dvd hpK
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, hrel, k₀, k₁, k₂, ha₀, ha₁, ha₂, hreg'⟩ :=
    exists_cubeColumns hω hE₀p hE₀m hE₀c D hreg
  set a₀ : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ := fun l => ω ^ k₀ l
  set a₁ : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ := fun l => ω ^ k₁ l
  set a₂ : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ := fun l => ω ^ k₂ l
  have hk₀ : ∀ i, a₀ i = ω ^ k₀ i := fun _ => rfl
  have hk₁ : ∀ i, a₁ i = ω ^ k₁ i := fun _ => rfl
  have hk₂ : ∀ i, a₂ i = ω ^ k₂ i := fun _ => rfl
  have h5 : ω ^ 5 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  refine ⟨![fun i => (k₀ i : ZMod 5), fun i => (k₁ i : ZMod 5), fun i => (k₂ i : ZMod 5)],
    ⟨?_, ?_, ?_⟩⟩
  ·
    intro b₀ b₁ b₂ hb
    have hone : a₀ ^ b₀.val * a₁ ^ b₁.val * a₂ ^ b₂.val = 1 := by
      funext l
      have hl := congrFun hb l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val] at hl
      have hdvd : 5 ∣ k₀ l * b₀.val + k₁ l * b₁.val + k₂ l * b₂.val := by
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
          Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        linear_combination hl
      obtain ⟨m, hm⟩ := hdvd
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.one_apply]
      rw [hk₀ l, hk₁ l, hk₂ l, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, hm, pow_mul,
        h5, one_pow]
    have hrel' : x₀ ^ b₀.val * x₁ ^ b₁.val * x₂ ^ b₂.val = 1 := by
      apply diagMap_injective D
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, ← ha₀, ← ha₁, ← ha₂, map_one]
      have e : rootDiagUnit Tag.E8 (a₀ ^ b₀.val * a₁ ^ b₁.val * a₂ ^ b₂.val) =
          rootDiagUnit Tag.E8 a₀ ^ b₀.val * rootDiagUnit Tag.E8 a₁ ^ b₁.val *
            rootDiagUnit Tag.E8 a₂ ^ b₂.val := by
        have h : (rootDiagUnitHom Tag.E8 (AlgebraicClosure K))
            (a₀ ^ b₀.val * a₁ ^ b₁.val * a₂ ^ b₂.val) =
            (rootDiagUnitHom Tag.E8 (AlgebraicClosure K) a₀) ^ b₀.val *
              (rootDiagUnitHom Tag.E8 (AlgebraicClosure K) a₁) ^ b₁.val *
              (rootDiagUnitHom Tag.E8 (AlgebraicClosure K) a₂) ^ b₂.val := by
          rw [map_mul, map_mul, map_pow, map_pow, map_pow]
        exact h
      rw [← e, hone]
      exact map_one (rootDiagUnitHom Tag.E8 (AlgebraicClosure K))
    obtain ⟨h₀, h₁, h₂⟩ := hrel _ _ _ hrel'
    have hv : ∀ b : ZMod 5, 5 ∣ b.val → b = 0 := fun b hb => by
      have hlt := ZMod.val_lt b
      have : b.val = 0 := by omega
      exact (ZMod.val_eq_zero b).1 this
    exact ⟨hv b₀ h₀, hv b₁ h₁, hv b₂ h₂⟩
  · intro i v
    fin_cases i
    · exact charVal_eq_of_rootChar_eq_pow hω hk₀ (rootChar_smul_eq_pow_of_mem D hx₀ ha₀ v)
    · exact charVal_eq_of_rootChar_eq_pow hω hk₁ (rootChar_smul_eq_pow_of_mem D hx₁ ha₁ v)
    · exact charVal_eq_of_rootChar_eq_pow hω hk₂ (rootChar_smul_eq_pow_of_mem D hx₂ ha₂ v)
  · intro α hα h
    exact hreg' α hα (h 0) (h 1) (h 2)

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
