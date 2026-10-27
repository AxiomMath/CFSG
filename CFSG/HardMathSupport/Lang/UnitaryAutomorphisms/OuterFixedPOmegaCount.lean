module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.PartOne.KCOrthogonalSubfield

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}

theorem card_subfieldFixedGroup_dvd (Q₀ : QuadraticForm k (Fin d → k))
    (Q : QuadraticForm K (Fin d → K)) (S : Subgroup (matrixIsometries Q₀))
    (hS : ∀ x : matrixIsometries Q₀, glIncl k (x : GL (Fin d) k) ∈ matrixDerived Q → x ∈ S) :
    Nat.card (subfieldFixedGroup k Q₀ Q) ∣ Nat.card S := by
  classical
  set ι : matrixIsometries Q₀ →* GL (Fin d) K := (glIncl k).comp (Subgroup.subtype _) with hι
  set X : Subgroup (GL (Fin d) K) := S.map ι with hX
  have hinj : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    have := congrArg (fun z : GL (Fin d) K => (z : Matrix (Fin d) (Fin d) K) i j) hxy
    simpa [hι, glIncl_val] using this
  have hXcard : Nat.card X = Nat.card S := Subgroup.card_map_of_injective hinj
  let f : subfieldIsometries k Q₀ Q →* X :=
    (((matrixDerived Q).subtype).comp (Subgroup.subtype _)).codRestrict X (by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := (Subgroup.mem_subgroupOf.mp hy : (y : GL (Fin d) K) ∈
        (matrixIsometries Q₀).map (glIncl k))
      refine ⟨⟨x, hx⟩, hS ⟨x, hx⟩ ?_, hxy⟩
      change glIncl k x ∈ _
      rw [hxy]
      exact y.2)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : X => (z : GL (Fin d) K)) hab
  have h1 : Nat.card (subfieldIsometries k Q₀ Q) ∣ Nat.card X :=
    Subgroup.card_dvd_of_injective f hf
  have h2 : Nat.card (subfieldFixedGroup k Q₀ Q) ∣ Nat.card (subfieldIsometries k Q₀ Q) := by
    let g : subfieldIsometries k Q₀ Q →* subfieldFixedGroup k Q₀ Q :=
      ((matrixProjectiveProjection Q).comp (Subgroup.subtype (subfieldIsometries k Q₀ Q))).codRestrict
        (subfieldFixedGroup k Q₀ Q) fun x => ⟨x.1, x.2, rfl⟩
    have hg : Function.Surjective g := by
      rintro ⟨_, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    exact Subgroup.card_dvd_of_surjective hg
  rw [← hXcard]
  exact h2.trans h1

theorem det_glIncl (x : GL (Fin d) k) :
    Matrix.GeneralLinearGroup.det (glIncl k x) =
      Units.map k.subtype.toMonoidHom (Matrix.GeneralLinearGroup.det x) := by
  apply Units.ext
  change Matrix.det ((x : Matrix (Fin d) (Fin d) k).map k.subtype) = k.subtype (Matrix.det (x : Matrix (Fin d) (Fin d) k))
  exact (RingHom.map_det k.subtype (x : Matrix (Fin d) (Fin d) k)).symm

theorem det_eq_one_of_mem_matrixDerived (Q : QuadraticForm K (Fin d → K)) {y : GL (Fin d) K}
    (hy : y ∈ matrixDerived Q) : Matrix.GeneralLinearGroup.det y = 1 := by
  have : matrixDerived Q ≤ (Matrix.GeneralLinearGroup.det : GL (Fin d) K →* Kˣ).ker := by
    rw [matrixDerived, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp
  exact this hy

theorem two_mul_card_subfieldFixedGroup_dvd (Q₀ : QuadraticForm k (Fin d → k))
    (Q : QuadraticForm K (Fin d → K)) (g : matrixIsometries Q₀)
    (hg : ((Matrix.GeneralLinearGroup.det (g : GL (Fin d) k) : kˣ) : k) = -1) (h2 : (2 : k) ≠ 0) :
    2 * Nat.card (subfieldFixedGroup k Q₀ Q) ∣ Nat.card (matrixIsometries Q₀) := by
  classical
  set δ : matrixIsometries Q₀ →* kˣ :=
    (Matrix.GeneralLinearGroup.det : GL (Fin d) k →* kˣ).comp (Subgroup.subtype _) with hδ
  have hdvd : Nat.card (subfieldFixedGroup k Q₀ Q) ∣ Nat.card δ.ker := by
    apply card_subfieldFixedGroup_dvd k Q₀ Q δ.ker
    intro x hx
    have h1 := det_eq_one_of_mem_matrixDerived Q hx
    rw [det_glIncl] at h1
    rw [MonoidHom.mem_ker]
    apply Units.ext
    have h3 := congrArg (fun u : Kˣ => (u : K)) h1
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h3
    have h4 : ((Matrix.GeneralLinearGroup.det (x : GL (Fin d) k) : kˣ) : k) = 1 :=
      Subtype.ext (by simpa using h3)
    simpa [hδ] using h4
  have hrange : 2 ∣ Nat.card δ.range := by
    have hne : (⟨δ g, g, rfl⟩ : δ.range) ≠ 1 := by
      intro h
      have h' : δ g = 1 := congrArg Subtype.val h
      have h'' : ((δ g : kˣ) : k) = 1 := by rw [h']; rfl
      have : ((Matrix.GeneralLinearGroup.det (g : GL (Fin d) k) : kˣ) : k) = 1 := h''
      rw [hg] at this
      apply h2
      linear_combination -this
    have hsq : (⟨δ g, g, rfl⟩ : δ.range) ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      have : ((Matrix.GeneralLinearGroup.det (g : GL (Fin d) k) : kˣ) : k) = -1 := hg
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
      change ((δ g : kˣ) : k) ^ 2 = 1
      change ((Matrix.GeneralLinearGroup.det (g : GL (Fin d) k) : kˣ) : k) ^ 2 = 1
      rw [this]
      norm_num
    have hord : orderOf (⟨δ g, g, rfl⟩ : δ.range) = 2 := orderOf_eq_prime hsq hne
    rw [← hord]
    exact orderOf_dvd_natCard _
  rw [← Subgroup.card_ker_mul_card_range δ, mul_comm 2]
  exact mul_dvd_mul hdvd hrange |>.trans (by rw [mul_comm])

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
