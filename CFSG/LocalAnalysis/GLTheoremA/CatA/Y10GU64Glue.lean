module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Assembly CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem model_A {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) {lab : GLALabel}
    (hl : HasLabel S (fun l : GLALabel => l = lab)) (ht : lab.tag = .A) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ lab.n ∧
      Nonempty (S ≃* LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K)) := by
  obtain ⟨_, lab', _, hraw⟩ := hl
  obtain ⟨_, _, _, _, _, _, θ, hEq⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hEq' : lab' = lab := hEq
  rw [hEq'] at hraw
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  rw [ht] at hraw
  dsimp only at hraw
  unfold CFSG.Assembly.LargeEvenRecipeLinear at hraw
  obtain ⟨K, hK, hKf, hcard, hQ⟩ := hraw
  obtain ⟨_, _, θ', -⟩ := hQ
  refine ⟨K, hK, hKf, hcard, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ'

theorem model_twA {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) {lab : GLALabel}
    (hl : HasLabel S (fun l : GLALabel => l = lab)) (ht : lab.tag = .twA) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ lab.n) ^ 2 ∧
      Nonempty (S ≃* StatedProj (StatedSU (lab.rank + 1) (2 ^ lab.n) K)) := by
  obtain ⟨_, lab', _, hraw⟩ := hl
  obtain ⟨_, _, _, _, _, _, θ, hEq⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hEq' : lab' = lab := hEq
  rw [hEq'] at hraw
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  rw [ht] at hraw
  dsimp only at hraw
  unfold CFSG.Assembly.LargeEvenRecipeUnitary at hraw
  obtain ⟨K, hK, hKf, hcard, hQ⟩ := hraw
  obtain ⟨_, _, θ', -⟩ := hQ
  refine ⟨K, hK, hKf, hcard, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ'

theorem fixSubgroup_map_congr {S R : Type} [Group S] [Group R] (e : S ≃* R) (β : MulAut S) :
    (fixSubgroup β).map e.toMonoidHom = fixSubgroup (MulAut.congr e β) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : β y = y := hy
    show MulAut.congr e β (e y) = e y
    simp [MulAut.congr, hy']
  · intro hx
    have hx' : e (β (e.symm x)) = x := hx
    refine ⟨e.symm x, ?_, by simp⟩
    show β (e.symm x) = e.symm x
    apply e.injective
    rw [hx', MulEquiv.apply_symm_apply]

theorem glaPComponent_transport {S R : Type} [Group S] [Group R] [Finite S] (e : S ≃* R) (β : MulAut S)
    {J : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    GLAPComponent 3 (fixSubgroup (MulAut.congr e β)) (J.map e.toMonoidHom) := by
  rw [← fixSubgroup_map_congr e β]
  exact (glaPComponent_map_iff Nat.prime_three e.injective).2 hJ

theorem hasLabel_transport {S R : Type} [Group S] [Group R] (e : S ≃* R) {J : Subgroup S}
    {T : GLALabel → Prop} (hJ : HasLabel ↥J T) : HasLabel ↥(J.map e.toMonoidHom) T :=
  (hasLabel_congr (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective) T).1 hJ

theorem unitaryFieldData_of_card {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Nat.card K = (2 ^ n) ^ 2) : UnitaryFieldData 2 n K :=
  ⟨Nat.prime_two, hn, by rw [hcard, ← pow_mul, Nat.mul_comm]⟩

theorem unitary_decomp {K : Type} [Field K] {d n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hd : 5 ≤ d) (β : MulAut (StatedProj (StatedSU d (2 ^ n) K))) (hβ : β ^ 3 = 1) :
    ∃ (A : uU (unitaryFieldData_of_card hn hcard) d) (φ : K ≃+* K),
      β = uConjAut (unitaryFieldData_of_card hn hcard) (by omega) A *
        uFieldAut (unitaryFieldData_of_card hn hcard) (by omega) φ ∧
      (φ = 1 ∨ orderOf φ = 3) := by
  have hd3 : 3 ≤ d := by omega
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := fun H => by have := H.1; omega
  obtain ⟨A, φ, hβeq⟩ := exists_uConjAut_mul_uFieldAut (unitaryFieldData_of_card hn hcard) hd3 hq β
  refine ⟨A, φ, hβeq, ?_⟩
  have h3 : φ ^ 3 = 1 := by
    have := congrArg (uFactor (unitaryFieldData_of_card hn hcard) hd3 hq) hβ
    rw [map_pow, map_one, hβeq, uFactor_apply] at this
    exact this
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h1 | h1
  · exact Or.inl (orderOf_eq_one_iff.1 h1)
  · exact Or.inr h1

theorem uConjAut_mem_inner {K : Type} [Field K] {d n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hd : 1 ≤ d) (A : uU (unitaryFieldData_of_card hn hcard) d) :
    U64IsInner d (2 ^ n) K (uConjAut (unitaryFieldData_of_card hn hcard) hd A) := by
  refine ⟨(A : GL (Fin d) K), ?_, ?_⟩
  · refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    rw [one_smul]
    exact (mem_uU (unitaryFieldData_of_card hn hcard)).1 A.2
  · intro g g' hg'
    have hg'eq : g' = ⟨(A : GL (Fin d) K) * (g : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹,
        uConjSU_mem (unitaryFieldData_of_card hn hcard) A g⟩ := Subtype.ext hg'
    rw [hg'eq]
    exact uConjAut_proj (unitaryFieldData_of_card hn hcard) hd A g

theorem uFieldAut_mem_field {K : Type} [Field K] {d n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hd : 1 ≤ d) (φ : K ≃+* K) :
    U64IsField d (2 ^ n) K (uFieldAut (unitaryFieldData_of_card hn hcard) hd φ) := by
  refine ⟨φ, ?_⟩
  intro g g' hg'
  have hg'eq : g' = ⟨glAut φ (g : GL (Fin d) K), uFieldSU_mem (unitaryFieldData_of_card hn hcard) φ g⟩ := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_glAut]
    exact hg'
  rw [hg'eq]
  exact uFieldAut_proj (unitaryFieldData_of_card hn hcard) hd φ g

end CFSG.LocalAnalysis.GLTheoremA.Y10F
