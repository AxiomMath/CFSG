module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesDecomp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

@[expose] def planeStep (p q r s : ZMod 3) (v : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (p * v.1 + q * v.2, r * v.1 + s * v.2)

theorem plane_isometry_pow_four : ∀ (a b p q r s : ZMod 3), a ≠ 0 → b ≠ 0 →
    (∀ x y : ZMod 3, a * ((p * x + q * y) * (p * x + q * y)) +
      b * ((r * x + s * y) * (r * x + s * y)) = a * (x * x) + b * (y * y)) →
    ∀ v : ZMod 3 × ZMod 3, planeStep p q r s (planeStep p q r s (planeStep p q r s
      (planeStep p q r s v))) = v := by
  decide +kernel

theorem pow_four_eq_one_of_weightedSumSquares (w : Fin 2 → (ZMod 3)ˣ)
    (g : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3))
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup
      (weightedSumSquares (ZMod 3) fun i => (w i : ZMod 3))) : g ^ 4 = 1 := by
  have hv : ∀ x : Fin 2 → ZMod 3, x = x 0 • (Pi.single 0 1 : Fin 2 → ZMod 3) +
      x 1 • (Pi.single 1 1 : Fin 2 → ZMod 3) := by
    intro x
    funext i
    fin_cases i <;> simp
  have hlin : ∀ x : Fin 2 → ZMod 3,
      g x = x 0 • g (Pi.single 0 1) + x 1 • g (Pi.single 1 1) := by
    intro x
    conv_lhs => rw [hv x]
    rw [map_add, map_smul, map_smul]
  obtain ⟨p, hp⟩ : ∃ p, p = g (Pi.single 0 1) 0 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = g (Pi.single 0 1) 1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = g (Pi.single 1 1) 0 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = g (Pi.single 1 1) 1 := ⟨_, rfl⟩
  have hgx : ∀ x : Fin 2 → ZMod 3,
      g x 0 = p * x 0 + q * x 1 ∧ g x 1 = r * x 0 + s * x 1 := by
    intro x
    rw [hlin x, hp, hq, hr, hs]
    constructor <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  have hiso : ∀ x y : ZMod 3, (w 0 : ZMod 3) * ((p * x + q * y) * (p * x + q * y)) +
      (w 1 : ZMod 3) * ((r * x + s * y) * (r * x + s * y)) =
        (w 0 : ZMod 3) * (x * x) + (w 1 : ZMod 3) * (y * y) := by
    intro x y
    have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg ![x, y]
    rw [weightedSumSquares_apply, weightedSumSquares_apply] at h
    simp only [Fin.sum_univ_two, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      (hgx ![x, y]).1, (hgx ![x, y]).2] at h
    exact h
  have hcheck := plane_isometry_pow_four (w 0 : ZMod 3) (w 1 : ZMod 3) p q r s (w 0).ne_zero
    (w 1).ne_zero hiso
  have hstep : ∀ x : Fin 2 → ZMod 3, ((g x) 0, (g x) 1) =
      planeStep p q r s (x 0, x 1) := fun x => Prod.ext (hgx x).1 (hgx x).2
  have hpow : ∀ n : ℕ, ∀ x : Fin 2 → ZMod 3, (((g ^ n) x) 0, ((g ^ n) x) 1) =
      (planeStep p q r s)^[n] (x 0, x 1) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, LinearEquiv.mul_apply, ih (g x), hstep x, Function.iterate_succ_apply]
  apply LinearEquiv.ext
  intro x
  have h4 := hpow 4 x
  have h4' : (planeStep p q r s)^[4] (x 0, x 1) = (x 0, x 1) := hcheck (x 0, x 1)
  rw [h4'] at h4
  funext i
  fin_cases i
  · exact congrArg Prod.fst h4
  · exact congrArg Prod.snd h4

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem exists_isometryEquiv_weightedSumSquares_two (hQ : Q.Nondegenerate)
    (h : Module.finrank (ZMod 3) V = 2) :
    ∃ w : Fin 2 → (ZMod 3)ˣ,
      Nonempty (Q.IsometryEquiv (weightedSumSquares (ZMod 3) fun i => (w i : ZMod 3))) := by
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  generalize hm : Module.finrank (ZMod 3) V = m at w e
  have hm2 : m = 2 := hm.symm.trans h
  subst hm2
  exact ⟨w, ⟨e⟩⟩

theorem isPGroup_two_oGroup_of_finrank_two (hQ : Q.Nondegenerate)
    (h : Module.finrank (ZMod 3) V = 2) : IsPGroup 2 (OGroup Q) := by
  obtain ⟨w, ⟨e⟩⟩ := exists_isometryEquiv_weightedSumSquares_two hQ h
  intro g
  refine ⟨2, ?_⟩
  let φ := TauCeti.QuadraticMap.orthogonalGroupCongr e
  have h4 := pow_four_eq_one_of_weightedSumSquares w _ (φ g).2
  show g ^ 4 = 1
  apply φ.injective
  rw [map_pow, map_one]
  exact Subtype.ext (by simpa using h4)

end CFSG.OddStandard.SmallF3.Omega

