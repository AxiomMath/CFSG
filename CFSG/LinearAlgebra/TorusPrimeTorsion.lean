module

public import CFSG.LinearAlgebra.TorusWeightComodule
public import CFSG.Mathlib.RingTheory.UnitOrderOf

public noncomputable section

namespace CFSG.LinearAlgebra

open TauCeti Matrix Module WithConv

universe u

theorem torusCharacter_eq_of_torsion
    {K κ : Type*} [Field K] [Fintype κ] [DecidableEq κ]
    {l : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ l)
    {μ ν : κ → ℤ} (hbound : ∀ i, (μ i - ν i).natAbs < l)
    (h : ∀ s : κ → Kˣ, s ^ l = 1 → torusCharacter s μ = torusCharacter s ν) : μ = ν := by
  funext i
  let s : κ → Kˣ := Pi.mulSingle i ζ
  have hs : s ^ l = 1 := by
    funext j
    by_cases hij : j = i
    · subst j
      simpa [s] using hζ.pow_eq_one
    · simp [s, hij]
  have he := h s hs
  rw [torusCharacter_mulSingle, torusCharacter_mulSingle] at he
  have hz : ζ ^ (μ i - ν i) = 1 := by rw [zpow_sub, he, mul_inv_cancel]
  have hd : (l : ℤ) ∣ μ i - ν i := (hζ.zpow_eq_one_iff_dvd _).1 hz
  have hzero : μ i - ν i = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hbound i)
  exact sub_eq_zero.mp hzero

theorem commuting_basisWeightTorus_of_torsion
    {K ι κ V : Type*} [Field K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (wt : ι → κ → ℤ)
    {l : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ l)
    (hbound : ∀ i j c, (wt i c - wt j c).natAbs < l)
    (A : V →ₗ[K] V)
    (hA : ∀ s : κ → Kˣ, s ^ l = 1 →
      A.comp (basisWeightTorus b wt s).toLinearMap =
        (basisWeightTorus b wt s).toLinearMap.comp A) :
    ∀ s : κ → Kˣ, A.comp (basisWeightTorus b wt s).toLinearMap =
      (basisWeightTorus b wt s).toLinearMap.comp A := by
  have hwt (i j : ι) (ha : b.repr (A (b j)) i ≠ 0) : wt i = wt j := by
    apply torusCharacter_eq_of_torsion hζ (hbound i j)
    intro s hs
    apply Units.ext
    have h := congrArg (fun e : V →ₗ[K] V => b.repr (e (b j)) i) (hA s hs)
    change b.repr (A (basisWeightTorus b wt s (b j))) i =
      b.repr (basisWeightTorus b wt s (A (b j))) i at h
    rw [basisWeightTorus_basis, map_smul, map_smul, Finsupp.smul_apply,
      basisWeightTorus_apply, repr_basisDiagonal, smul_eq_mul] at h
    exact (mul_right_cancel₀ ha h).symm
  intro s
  apply b.ext
  intro j
  apply b.repr.injective
  ext i
  change b.repr (A (basisWeightTorus b wt s (b j))) i =
    b.repr (basisWeightTorus b wt s (A (b j))) i
  rw [basisWeightTorus_basis, map_smul, map_smul, Finsupp.smul_apply,
    basisWeightTorus_apply, repr_basisDiagonal, smul_eq_mul]
  by_cases ha : b.repr (A (b j)) i = 0
  · rw [ha, mul_zero, mul_zero]
  · rw [hwt i j ha]

theorem exists_basisWeightTorus_torsion_detector
    {K ι κ V : Type*} [Field K] [IsAlgClosed K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module K V] (b : Basis ι K V) (wt : ι → κ → ℤ)
    {m : ℕ} (hm0 : m ≠ 0) (hmK : (m : K) ≠ 0)
    (hbound : ∀ i j c, (wt i c - wt j c).natAbs < m)
    (hzero : ∀ i c, (wt i c).natAbs < m) :
    ∃ F : Subgroup (κ → Kˣ), Finite F ∧ Nat.card F = m ^ Fintype.card κ ∧
      (∀ s : κ → Kˣ, s ∈ F ↔ s ^ m = 1) ∧
      (∀ v : V, (∀ s ∈ F, basisWeightTorus b wt s v = v) ↔
        (∀ s : κ → Kˣ, basisWeightTorus b wt s v = v)) ∧
      ∀ A : V →ₗ[K] V,
        (∀ s ∈ F, A.comp (basisWeightTorus b wt s).toLinearMap =
          (basisWeightTorus b wt s).toLinearMap.comp A) ↔
        (∀ s : κ → Kˣ, A.comp (basisWeightTorus b wt s).toLinearMap =
          (basisWeightTorus b wt s).toLinearMap.comp A) := by
  classical
  obtain ⟨ζ, hζo⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed hmK
  have hζ : IsPrimitiveRoot ζ m := IsPrimitiveRoot.iff_orderOf.mpr hζo
  have hcomm : ∀ A : V →ₗ[K] V,
      (∀ s : κ → Kˣ, s ^ m = 1 → A.comp (basisWeightTorus b wt s).toLinearMap =
        (basisWeightTorus b wt s).toLinearMap.comp A) ↔
      (∀ s : κ → Kˣ, A.comp (basisWeightTorus b wt s).toLinearMap =
        (basisWeightTorus b wt s).toLinearMap.comp A) := fun A =>
    ⟨commuting_basisWeightTorus_of_torsion b wt hζ hbound A, fun h s _ => h s⟩
  let : NeZero m := ⟨hm0⟩
  let F := (powMonoidHom m : (κ → Kˣ) →* (κ → Kˣ)).ker
  let e : F ≃ (κ → rootsOfUnity m K) :=
    { toFun := fun s i => ⟨s.val i, (mem_rootsOfUnity m (s.val i)).2 (by
        have h := MonoidHom.mem_ker.mp s.property
        change s.val ^ m = 1 at h
        exact congrFun h i)⟩
      invFun := fun s => ⟨fun i => (s i).val, MonoidHom.mem_ker.mpr (by
        change (fun i => (s i).val) ^ m = 1
        funext i
        exact (mem_rootsOfUnity m (s i).val).1 (s i).property)⟩
      left_inv := fun s => Subtype.ext rfl
      right_inv := fun s => by funext i; rfl }
  let : Finite F := Finite.of_equiv (κ → rootsOfUnity m K) e.symm
  have hcard : Nat.card F = m ^ Fintype.card κ := by
    rw [Nat.card_congr e, Nat.card_fun, hζ.card_rootsOfUnity', Nat.card_eq_fintype_card]
  refine ⟨F, inferInstance, hcard, fun s => MonoidHom.mem_ker, ?_, hcomm⟩
  intro v
  refine ⟨fun hv s => ?_, fun hv s _ => hv s⟩
  apply b.repr.injective
  ext i
  rw [basisWeightTorus_apply, repr_basisDiagonal]
  by_cases hvi : b.repr v i = 0
  · rw [hvi, mul_zero]
  · have hweight : wt i = 0 := by
      apply torusCharacter_eq_of_torsion hζ (by simpa using hzero i)
      intro t ht
      apply Units.ext
      have hh := congrArg (fun w : V => b.repr w i) (hv t ht)
      rw [basisWeightTorus_apply, repr_basisDiagonal] at hh
      rw [torusCharacter_zero]
      exact (mul_right_cancel₀ hvi (hh.trans (one_mul _).symm))
    rw [hweight, torusCharacter_zero, Units.val_one, one_mul]

theorem exists_pow_gt_weight_sub_natAbs
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (wt : ι → κ → ℤ) {p : ℕ} (hp : 1 < p) :
    ∃ e : ℕ, 0 < e ∧ ∀ i j c, (wt i c - wt j c).natAbs < p ^ e := by
  classical
  let N := ∑ i : ι, ∑ j : ι, ∑ c : κ, (wt i c - wt j c).natAbs
  refine ⟨N + 1, Nat.add_pos_right N Nat.zero_lt_one, ?_⟩
  intro i j c
  apply lt_of_le_of_lt _ ((Nat.lt_add_one N).trans (Nat.lt_pow_self hp))
  apply le_trans (Finset.single_le_sum (f := fun d => (wt i d - wt j d).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
  apply le_trans (Finset.single_le_sum (f := fun a => ∑ d : κ, (wt i d - wt a d).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  exact Finset.single_le_sum (f := fun a => ∑ b : ι, ∑ d : κ, (wt a d - wt b d).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem exists_primePower_basisWeightTorus_detector
    {K ι κ V : Type*} [Field K] [IsAlgClosed K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module K V] (b : Basis ι K V) (wt : ι → κ → ℤ)
    {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    ∃ (e : ℕ) (F : Subgroup (κ → Kˣ)), 0 < e ∧ Finite F ∧
      Nat.card F = (p ^ e) ^ Fintype.card κ ∧
      (∀ s : κ → Kˣ, s ∈ F ↔ s ^ (p ^ e) = 1) ∧
      (∀ v : V, (∀ s ∈ F, basisWeightTorus b wt s v = v) ↔
        (∀ s : κ → Kˣ, basisWeightTorus b wt s v = v)) ∧
      ∀ A : V →ₗ[K] V,
        (∀ s ∈ F, A.comp (basisWeightTorus b wt s).toLinearMap =
          (basisWeightTorus b wt s).toLinearMap.comp A) ↔
        (∀ s : κ → Kˣ, A.comp (basisWeightTorus b wt s).toLinearMap =
          (basisWeightTorus b wt s).toLinearMap.comp A) := by
  classical
  let wt0 : Option ι → κ → ℤ := fun i => match i with | none => 0 | some j => wt j
  obtain ⟨e, he, hbound⟩ := exists_pow_gt_weight_sub_natAbs wt0 hp.one_lt
  obtain ⟨F, hF⟩ := exists_basisWeightTorus_torsion_detector b wt
    (pow_ne_zero _ hp.ne_zero) (by simpa only [Nat.cast_pow] using pow_ne_zero e hpK)
    (fun i j c => hbound (some i) (some j) c)
    (fun i c => by simpa [wt0] using hbound (some i) none c)
  exact ⟨e, F, he, hF⟩

theorem exists_primePower_basePointsRepresentation_detector
    {K V : Type u} [Field K] [IsAlgClosed K] {r : ℕ}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [Comodule K (MonoidAlgebra K (Multiplicative (Fin r →₀ ℤ))) V] {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    ∃ (e : ℕ) (F : Subgroup (Fin r → Kˣ)), 0 < e ∧
      Finite F ∧ Nat.card F = (p ^ e) ^ r ∧
      (∀ s : Fin r → Kˣ, s ∈ F ↔ s ^ (p ^ e) = 1) ∧
      (∀ v : V,
        (∀ s ∈ F, Comodule.basePointsRepresentation
          (H := MonoidAlgebra K (Multiplicative (Fin r →₀ ℤ))) V
            (SplitTorus.pointsMulEquiv.symm s) v = v) ↔
        (∀ s : Fin r → Kˣ, Comodule.basePointsRepresentation
          (H := MonoidAlgebra K (Multiplicative (Fin r →₀ ℤ))) V
            (SplitTorus.pointsMulEquiv.symm s) v = v)) ∧
      ∀ A : V →ₗ[K] V,
        (∀ s ∈ F, A.comp (Comodule.basePointsRepresentation
          (H := MonoidAlgebra K (Multiplicative (Fin r →₀ ℤ))) V
            (SplitTorus.pointsMulEquiv.symm s)) =
          (Comodule.basePointsRepresentation (H := MonoidAlgebra K (Multiplicative (Fin r →₀ ℤ))) V
            (SplitTorus.pointsMulEquiv.symm s)).comp A) ↔
        (∀ s : Fin r → Kˣ, A.comp (Comodule.basePointsRepresentation
          (H := MonoidAlgebra K (Multiplicative (Fin r →₀ ℤ))) V
            (SplitTorus.pointsMulEquiv.symm s)) =
          (Comodule.basePointsRepresentation (H := MonoidAlgebra K (Multiplicative (Fin r →₀ ℤ))) V
            (SplitTorus.pointsMulEquiv.symm s)).comp A) := by
  classical
  obtain ⟨ι, hι, b, wt, hwt⟩ := CFSG.LinearAlgebra.exists_basisWeightTorus_eq_basePointsRepresentation
    (k := K) (r := r) (V := V)
  let : Fintype ι := hι
  obtain ⟨e, F, he, hF, hcard, hmem, hfix, hcomm⟩ :=
    exists_primePower_basisWeightTorus_detector b wt hp hpK
  have heq (s : Fin r → Kˣ) : (basisWeightTorus b wt s).toLinearMap =
      Comodule.basePointsRepresentation (H := MonoidAlgebra K (Multiplicative (Fin r →₀ ℤ))) V
        (SplitTorus.pointsMulEquiv.symm s) := LinearMap.ext (hwt s)
  refine ⟨e, F, he, hF, by simpa using hcard, hmem, ?_, ?_⟩
  · intro v
    constructor
    · intro hv s
      rw [← hwt s v]
      exact (hfix v).1 (fun t ht => (hwt t v).trans (hv t ht)) s
    · intro hv s hs
      rw [← hwt s v]
      exact (hfix v).2 (fun t => (hwt t v).trans (hv t)) s hs
  · intro A
    simpa only [← heq] using hcomm A

end CFSG.LinearAlgebra
