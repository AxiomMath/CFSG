module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinAux
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

variable {n d : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

theorem normOne_commute {z : ↥(gramSU h (idGram K d))}
    (hz : z ∈ normOneScalars h (gramSU h (idGram K d)) d) (g : ↥(gramSU h (idGram K d))) : Commute z g :=
  (Subgroup.mem_center_iff.1 (normOneScalars_le_center h _ d hz) g).symm

theorem normOne_eq_one_of_sq (hd : 0 < d) {z : ↥(gramSU h (idGram K d))}
    (hz : z ∈ normOneScalars h (gramSU h (idGram K d)) d) (hz2 : z ^ 2 = 1) : z = 1 := by
  haveI : CharP K 2 := h.charP
  obtain ⟨c, -, -, hc⟩ := hz
  have h1 : ((z ^ 2 : ↥(gramSU h (idGram K d))) : GL (Fin d) K) = 1 := by
    rw [hz2]
    rfl
  rw [SubgroupClass.coe_pow, hc, ← map_pow, SD.Lin.scalar_eq_one_iff hd] at h1
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h3 : (c : K) * (c : K) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) h1
    simpa [pow_two] using this
  have h5 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
    linear_combination h3 + (1 - (c : K)) * h2
  have h6 : c = 1 := Units.ext (sub_eq_zero.1 (mul_self_eq_zero.1 h5))
  apply Subtype.ext
  rw [hc, h6, map_one]
  rfl

theorem normOne_eq_one_of_two_pow (hd : 0 < d) {z : ↥(gramSU h (idGram K d))}
    (hz : z ∈ normOneScalars h (gramSU h (idGram K d)) d) (a : ℕ) (hza : z ^ (2 ^ a) = 1) : z = 1 := by
  induction a generalizing z with
  | zero => simpa using hza
  | succ a ih =>
    refine ih hz ?_
    have hw : z ^ (2 ^ a) ∈ normOneScalars h (gramSU h (idGram K d)) d :=
      (normOneScalars h (gramSU h (idGram K d)) d).pow_mem hz _
    refine normOne_eq_one_of_sq h hd hw ?_
    rw [← pow_mul, ← pow_succ]
    exact hza

theorem eq_of_mk_eq_of_two_pow (hd : 0 < d) {g g' : ↥(gramSU h (idGram K d))} {a : ℕ}
    (hg : g ^ (2 ^ a) = 1) (hg' : g' ^ (2 ^ a) = 1)
    (hgg : (g : primeFormP h (idGram K d)) = (g' : primeFormP h (idGram K d))) : g = g' := by
  have hz : g⁻¹ * g' ∈ normOneScalars h (gramSU h (idGram K d)) d := QuotientGroup.eq.1 hgg
  have hc : Commute g (g⁻¹ * g') := (normOne_commute h hz g).symm
  have h1 : (g⁻¹ * g') ^ (2 ^ a) = 1 := by
    have h3 : g' ^ (2 ^ a) = g ^ (2 ^ a) * (g⁻¹ * g') ^ (2 ^ a) := by
      rw [← hc.mul_pow, mul_inv_cancel_left]
    rw [hg, one_mul] at h3
    rw [← h3]
    exact hg'
  exact inv_mul_eq_one.1 (normOne_eq_one_of_two_pow h hd hz a h1)

variable [Finite K]

theorem exists_lift_two_pow (hd : 0 < d) {y : primeFormP h (idGram K d)} {a : ℕ} (hy : y ^ (2 ^ a) = 1) :
    ∃ g : ↥(gramSU h (idGram K d)), (g : primeFormP h (idGram K d)) = y ∧ g ^ (2 ^ a) = 1 := by
  classical
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hw : g₀ ^ (2 ^ a) ∈ normOneScalars h (gramSU h (idGram K d)) d := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hy
  have hwinv : (g₀ ^ (2 ^ a))⁻¹ ∈ normOneScalars h (gramSU h (idGram K d)) d :=
    (normOneScalars h (gramSU h (idGram K d)) d).inv_mem hw
  let f : ↥(normOneScalars h (gramSU h (idGram K d)) d) → ↥(normOneScalars h (gramSU h (idGram K d)) d) :=
    fun z => z ^ (2 ^ a)
  have hfinj : Function.Injective f := by
    intro z₁ z₂ hz
    have h' : (z₁ : ↥(gramSU h (idGram K d))) ^ (2 ^ a) = (z₂ : ↥(gramSU h (idGram K d))) ^ (2 ^ a) :=
      congrArg Subtype.val hz
    have hc : Commute (z₁ : ↥(gramSU h (idGram K d))) (z₂ : ↥(gramSU h (idGram K d)))⁻¹ :=
      normOne_commute h z₁.2 _
    have h1 : ((z₁ : ↥(gramSU h (idGram K d))) * (z₂ : ↥(gramSU h (idGram K d)))⁻¹) ^ (2 ^ a) = 1 := by
      rw [hc.mul_pow, inv_pow, h', mul_inv_cancel]
    have h3 := normOne_eq_one_of_two_pow h hd
      ((normOneScalars h (gramSU h (idGram K d)) d).mul_mem z₁.2
        ((normOneScalars h (gramSU h (idGram K d)) d).inv_mem z₂.2)) a h1
    exact Subtype.ext (mul_inv_eq_one.1 h3)
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hfinj
  obtain ⟨z, hz⟩ := hfsurj ⟨(g₀ ^ (2 ^ a))⁻¹, hwinv⟩
  have hz' : (z : ↥(gramSU h (idGram K d))) ^ (2 ^ a) = (g₀ ^ (2 ^ a))⁻¹ := congrArg Subtype.val hz
  refine ⟨(z : ↥(gramSU h (idGram K d))) * g₀, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 z.2, one_mul]
  · rw [(normOne_commute h z.2 g₀).mul_pow, hz', inv_mul_cancel]

omit [Finite K] in
theorem mk_primeFormConjSU (A : primeFormUnitary h (idGram K d)) (g : ↥(gramSU h (idGram K d))) :
    ((primeFormConjSU h (idGram K d) A g : ↥(gramSU h (idGram K d))) : primeFormP h (idGram K d)) =
      primeFormConjHom h (idGram K d) A (g : primeFormP h (idGram K d)) :=
  (primeFormConjHom_mk h (idGram K d) A g).symm

omit [Finite K] in
theorem lift_mem_fix (hd : 0 < d) (A : primeFormUnitary h (idGram K d)) {w : primeFormP h (idGram K d)}
    (hw : w ∈ fixSubgroup (primeFormConjHom h (idGram K d) A)) {g : ↥(gramSU h (idGram K d))}
    (hgw : (g : primeFormP h (idGram K d)) = w) {a : ℕ} (hga : g ^ (2 ^ a) = 1) :
    g ∈ fixSubgroup (primeFormConjSU h (idGram K d) A) := by
  rw [mem_fixSubgroup]
  refine eq_of_mk_eq_of_two_pow h hd (a := a) ?_ hga ?_
  · rw [← map_pow, hga, map_one]
  · rw [mk_primeFormConjSU, hgw]
    exact mem_fixSubgroup.1 hw

omit [Finite K] in
theorem lift_mem_unitaryCentralizer (hd : 0 < d) (A : primeFormUnitary h (idGram K d))
    {w : primeFormP h (idGram K d)} (hw : w ∈ fixSubgroup (primeFormConjHom h (idGram K d) A))
    {g : ↥(gramSU h (idGram K d))} (hgw : (g : primeFormP h (idGram K d)) = w) {a : ℕ}
    (hga : g ^ (2 ^ a) = 1) :
    toLinSU h d g ∈ unitaryCentralizer (idForm h d)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) :=
  toLinSU_mem_unitaryCentralizer A rfl (lift_mem_fix h hd A hw hgw hga)

omit [Finite K] in
theorem eq_one_of_conj_eq_mul (hd : 0 < d) {t f z : ↥(gramSU h (idGram K d))} {a : ℕ}
    (ht : t ^ (2 ^ a) = 1) (hz : z ∈ normOneScalars h (gramSU h (idGram K d)) d)
    (hconj : t * f * t⁻¹ = z * f) : z = 1 := by
  have hk : ∀ k : ℕ, t ^ k * f * (t ^ k)⁻¹ = z ^ k * f := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzt : t * z ^ k * t⁻¹ = z ^ k :=
        mul_inv_eq_iff_eq_mul.2 ((normOne_commute h ((normOneScalars h _ d).pow_mem hz k) t).eq.symm)
      calc t ^ (k + 1) * f * (t ^ (k + 1))⁻¹ = t * (t ^ k * f * (t ^ k)⁻¹) * t⁻¹ := by group
        _ = t * (z ^ k * f) * t⁻¹ := by rw [ih]
        _ = (t * z ^ k * t⁻¹) * (t * f * t⁻¹) := by group
        _ = z ^ k * (z * f) := by rw [hzt, hconj]
        _ = z ^ (k + 1) * f := by rw [pow_succ, mul_assoc]
  have h1 := hk (2 ^ a)
  rw [ht, one_mul, inv_one, mul_one] at h1
  have h2 : z ^ (2 ^ a) = 1 := by
    have := congrArg (· * f⁻¹) h1
    simpa using this.symm
  exact normOne_eq_one_of_two_pow h hd hz a h2

omit [Finite K] in
theorem pow_scalar_of_conj_pow (hd : 3 ≤ d) (A : primeFormUnitary h (idGram K d)) {p : ℕ}
    (hA : primeFormConjHom h (idGram K d) A ^ p = 1) :
    ∃ c : Kˣ, (A : GL (Fin d) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  have hC : IsPrimeFormGram (1 : GL (Fin d) K) := isPrimeFormGram_idGram
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC hd (A := A ^ p) (by rw [map_pow, hA])
  exact ⟨c, by rw [← hc, Subgroup.coe_pow]⟩

omit [Finite K] in
theorem comm_scalar_of_conj_comm (hd : 3 ≤ d) {A B : primeFormUnitary h (idGram K d)}
    (hBA : primeFormConjHom h (idGram K d) B * primeFormConjHom h (idGram K d) A =
      primeFormConjHom h (idGram K d) A * primeFormConjHom h (idGram K d) B) :
    ∃ ζ : Kˣ, (B : GL (Fin d) K) * A * (B : GL (Fin d) K)⁻¹ * (A : GL (Fin d) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin d) ζ := by
  have hC : IsPrimeFormGram (1 : GL (Fin d) K) := isPrimeFormGram_idGram
  have h1 : primeFormConjHom h (idGram K d) (B * A * B⁻¹ * A⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hBA
  obtain ⟨ζ, -, hζ⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC hd h1
  exact ⟨ζ, by rw [← hζ]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]⟩

omit [Finite K] in
theorem primaryData_of_conj_pow (hd : 3 ≤ d) (A : primeFormUnitary h (idGram K d)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hA : primeFormConjHom h (idGram K d) A ^ p = 1) :
    UnitaryPrimaryData h.bar (idForm h d) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) := by
  obtain ⟨c, hc⟩ := pow_scalar_of_conj_pow h hd A hA
  exact primaryData_toLin' h A.2 hp hp2 hc

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
