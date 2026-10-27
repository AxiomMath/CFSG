module

public import CFSG.RankThree.PartOne.FOC.UnitarySplit
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.LinearPerfect

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.FOC

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

noncomputable def orbitDet (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (x : LinearMap.GeneralLinearGroup K V)
    (a : K[X]) : orbitFactor B x a →* (AdjoinRoot a)ˣ :=
  (blockDetHom x a).comp (Subgroup.inclusion orbitFactor_le_gl_centralizer)

theorem map_ker_orbitDet (a : K[X]) :
    (orbitDet B x a).ker.map (orbitFactor B x a).subtype = specialBlock B x a := by
  ext g
  rw [mem_specialBlock, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨g', hg'⟩, hk, rfl⟩
    exact ⟨hg', orbitFactor_le_gl_centralizer hg', hk⟩
  · rintro ⟨hg, hgc, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem card_specialBlock_eq (a : K[X]) :
    Nat.card (specialBlock B x a) = Nat.card (orbitDet B x a).ker := by
  rw [← map_ker_orbitDet (B := B) (x := x) a]
  exact (Subgroup.card_map_of_injective (f := (orbitFactor B x a).subtype)
    (Subgroup.subtype_injective _))

theorem card_orbitFactor_eq (a : K[X]) :
    Nat.card (orbitFactor B x a) =
      Nat.card (orbitDet B x a).ker * Nat.card (orbitDet B x a).range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (orbitDet B x a).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (orbitDet B x a)).toEquiv, mul_comm]

theorem card_range_orbitDet_dvd (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a) :
    Nat.card (orbitDet B x (a : K[X])).range ∣ (ℓ ^ f) ^ (a : K[X]).natDegree + 1 := by
  have := hK.finite
  have hS := selfDualPrimaryBlock H a hself
  have : Finite (AdjoinRoot (a : K[X])) := by
    have : Module.Finite K (AdjoinRoot (a : K[X])) := inferInstance
    exact Module.finite_of_finite K
  have hcyc : IsCyclic (orbitDet B x (a : K[X])).range := inferInstance
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun u => ?_
  obtain ⟨⟨g, hg⟩, hu⟩ := u.2
  have h1 := selfDual_det_pow hself hS hg
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hu]
  apply Units.ext
  simp only [orbitDet, blockDetHom, MonoidHom.comp_apply, Units.val_pow_eq_pow_val,
    Units.val_one]
  exact h1

theorem three_dvd_sq_sub_one {ℓ k : ℕ} (hℓ : ℓ.Prime) (h3 : ℓ ≠ 3) :
    (3 : ℤ) ∣ ((ℓ ^ k : ℕ) : ℤ) ^ 2 - 1 := by
  have hnd : ¬ 3 ∣ ℓ ^ k := fun h =>
    h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have h1 : (ℓ ^ k) % 3 = 1 ∨ (ℓ ^ k) % 3 = 2 := by omega
  have h2 : ((ℓ ^ k : ℕ) : ℤ) % 3 = 1 ∨ ((ℓ ^ k : ℕ) : ℤ) % 3 = 2 := by omega
  have e : ((ℓ ^ k : ℕ) : ℤ) ^ 2 - 1 = (((ℓ ^ k : ℕ) : ℤ) - 1) * (((ℓ ^ k : ℕ) : ℤ) + 1) := by ring
  rw [e]
  rcases h2 with h | h
  · exact Dvd.dvd.mul_right (by omega) _
  · exact Dvd.dvd.mul_left (by omega) _

theorem three_dvd_card_specialBlock_selfDual (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a)
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) (h3 : ℓ ≠ 3) :
    3 ∣ Nat.card (specialBlock B x (a : K[X])) := by
  have hℓ := hK.prime
  have := hK.finite
  have : Finite (AdjoinRoot (a : K[X])) := by
    have : Module.Finite K (AdjoinRoot (a : K[X])) := inferInstance
    exact Module.finite_of_finite K
  set Q : ℕ := (ℓ ^ f) ^ (a : K[X]).natDegree with hQ
  have hQ' : Q = ℓ ^ (f * (a : K[X]).natDegree) := by rw [hQ, pow_mul]
  have hG := card_orbitFactor_selfDual H a hself
  rw [← hQ'] at hG
  set m := primaryMultiplicity (x : Module.End K V) (a : K[X])
  have hdvdP : ((Q : ℤ) + 1) * ((Q : ℤ) ^ 2 - 1) ∣
      ∏ i ∈ Finset.Icc 1 m, (((Q : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 m := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_Icc]; omega
    refine (?_ : _ ∣ ∏ i ∈ ({1, 2} : Finset ℕ), (((Q : ℕ) : ℤ) ^ i - (-1) ^ i)).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    rw [Finset.prod_pair (by norm_num)]
    simp
  have hGdvd : ((Q : ℤ) + 1) * ((Q : ℤ) ^ 2 - 1) ∣ (Nat.card (orbitFactor B x (a : K[X])) : ℤ) := by
    rw [hG]; exact hdvdP.mul_left _
  rw [card_orbitFactor_eq] at hGdvd
  obtain ⟨c, hc⟩ := card_range_orbitDet_dvd H a hself
  rw [card_specialBlock_eq]
  have hrpos : 0 < Nat.card (orbitDet B x (a : K[X])).range := Nat.card_pos
  push_cast at hGdvd
  set k := Nat.card (orbitDet B x (a : K[X])).ker
  set r := Nat.card (orbitDet B x (a : K[X])).range
  have hc' : ((Q : ℤ) + 1) = r * c := by exact_mod_cast hc
  rw [hc'] at hGdvd
  have : (r : ℤ) * ((c : ℤ) * ((Q : ℤ) ^ 2 - 1)) ∣ (r : ℤ) * (k : ℤ) := by
    have e1 : (r : ℤ) * ((c : ℤ) * ((Q : ℤ) ^ 2 - 1)) = ((r : ℤ) * c) * ((Q : ℤ) ^ 2 - 1) := by
      ring
    rw [e1, mul_comm (r : ℤ) (k : ℤ)]
    exact hGdvd
  have h4 := (mul_dvd_mul_iff_left (by exact_mod_cast hrpos.ne')).1 this
  have h5 : ((Q : ℤ) ^ 2 - 1) ∣ (k : ℤ) := (dvd_mul_left _ _).trans h4
  have h6 : (3 : ℤ) ∣ (Q : ℤ) ^ 2 - 1 := by
    rw [hQ']; exact three_dvd_sq_sub_one hℓ h3
  exact_mod_cast h6.trans h5

theorem three_dvd_card_specialBlock_paired (a : primaryFactors (x : Module.End K V))
    (hP : PairedPrimaryBlock hK B x a)
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) (h3 : (3 : K) ≠ 0) :
    3 ∣ Nat.card (specialBlock B x (a : K[X])) := by
  have := hK.finite
  have : Finite (AdjoinRoot (a : K[X])) := by
    have : Module.Finite K (AdjoinRoot (a : K[X])) := inferInstance
    exact Module.finite_of_finite K
  set E := AdjoinRoot (a : K[X])
  set m := primaryMultiplicity (x : Module.End K V) (a : K[X])
  obtain ⟨φ₀, ψ₀, hφ₀, -, hdet₀, -⟩ := hP.factor
  let φ : orbitFactor B x (a : K[X]) ≃* blockGL (x : Module.End K V) (a : K[X]) := φ₀
  let ψ : orbitFactor B x (a : K[X]) ≃* Matrix.GeneralLinearGroup (Fin m) E := ψ₀
  have hφ : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (φ g) v hv = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
    hφ₀
  have hdet : ∀ g : orbitFactor B x (a : K[X]),
      Matrix.det ((ψ g : Matrix.GeneralLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
        LinearMap.det ((φ g : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End E (primaryComponent (x : Module.End K V) (a : K[X]))) := hdet₀
  have hcomp : orbitDet B x (a : K[X]) =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ).comp
        (ψ : _ →* _) := by
    ext g
    have hres : blockRestrict x (a : K[X]) ⟨(g : LinearMap.GeneralLinearGroup K V),
        orbitFactor_le_gl_centralizer g.2⟩ = φ g := by
      refine blockGL_ext fun v hv => ?_
      rw [blockApply_blockRestrict, hφ g v hv]
    have h1 := hdet g
    simp only [orbitDet, blockDetHom, MonoidHom.comp_apply, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom, Matrix.GeneralLinearGroup.val_det_apply,
      blockGLDet, Units.coe_map, MonoidHom.coe_coe]
    change LinearMap.det ((blockRestrict x (a : K[X]) ⟨(g : LinearMap.GeneralLinearGroup K V),
        orbitFactor_le_gl_centralizer g.2⟩ : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End E (primaryComponent (x : Module.End K V) (a : K[X]))) = _
    rw [hres, ← h1]
  have hker : (orbitDet B x (a : K[X])).ker =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ).ker.comap
        (ψ : _ →* _) := by
    rw [hcomp]; rfl
  rw [card_specialBlock_eq, hker, Subgroup.comap_equiv_eq_map_symm,
    Subgroup.card_map_of_injective ψ.symm.injective]
  have h3E : (3 : E) ≠ 0 := by
    intro h
    apply h3
    have h' : algebraMap K E 3 = algebraMap K E 0 := by
      rw [map_zero, map_ofNat]; exact h
    exact (algebraMap K E).injective h'
  have := three_dvd_card_SL h3E hm
  rwa [Nat.card_congr (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin m) (R := E)).toEquiv]
    at this

end CFSG.HardMathSupport.Malle.E27Lie
