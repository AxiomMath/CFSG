module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.UnitaryBlockCard
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SLOrder

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.HardMathSupport.Malle.E27Lie

theorem dvd_card_adjoinRoot_sub_one_of_ne {K : Type*} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) {a : K[X]} [Fact (Irreducible a)] (hmon : a.Monic) (hd : a ∣ X ^ p - 1)
    (hne : a ≠ X - C 1) : p ∣ Nat.card (AdjoinRoot a) - 1 := by
  have : Module.Finite K (AdjoinRoot a) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible a).ne_zero).finite
  have : Finite (AdjoinRoot a) := Module.finite_of_finite K
  have : Fact p.Prime := ⟨hp⟩
  set ω : AdjoinRoot a := AdjoinRoot.root a with hω
  have hpow : ω ^ p = 1 := by
    have h0 : AdjoinRoot.mk a (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.2 hd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h0
    exact h0
  have hω1 : ω ≠ 1 := by
    intro h1
    have h0 : AdjoinRoot.mk a (X - C 1) = 0 := by
      rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
      change ω - algebraMap K (AdjoinRoot a) 1 = 0
      rw [h1, map_one, sub_self]
    have hdv : a ∣ X - C 1 := AdjoinRoot.mk_eq_zero.1 h0
    have hass := (Fact.out : Irreducible a).associated_of_dvd (irreducible_X_sub_C 1) hdv
    exact hne (eq_of_monic_of_associated hmon (monic_X_sub_C 1) hass)
  have hω0 : ω ≠ 0 := fun h0 => hω1 (by
    have := hpow
    rw [h0, zero_pow hp.ne_zero] at this
    exact absurd this zero_ne_one)
  let u : (AdjoinRoot a)ˣ := Units.mk0 ω hω0
  have hu : orderOf u = p := by
    refine orderOf_eq_prime ?_ ?_
    · ext; simpa [u] using hpow
    · intro h1; exact hω1 (by simpa [u] using congrArg Units.val h1)
  rw [← Nat.card_units, ← hu]
  exact orderOf_dvd_natCard u

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem dvd_card_specialBlock_selfDual (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a)
    {p j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]))
    (hpj : (p : ℤ) ∣ (((ℓ ^ f) ^ (a : K[X]).natDegree : ℕ) : ℤ) ^ j - (-1) ^ j) :
    p ∣ Nat.card (specialBlock B x (a : K[X])) := by
  have := hK.finite
  have : Finite (AdjoinRoot (a : K[X])) := by
    have : Module.Finite K (AdjoinRoot (a : K[X])) := inferInstance
    exact Module.finite_of_finite K
  set Q : ℕ := (ℓ ^ f) ^ (a : K[X]).natDegree with hQ
  have hQ' : Q = ℓ ^ (f * (a : K[X]).natDegree) := by rw [hQ, pow_mul]
  have hG := card_orbitFactor_selfDual H a hself
  rw [← hQ'] at hG
  set m := primaryMultiplicity (x : Module.End K V) (a : K[X])
  have hdvdP : ((Q : ℤ) + 1) * ((Q : ℤ) ^ j - (-1) ^ j) ∣
      ∏ i ∈ Finset.Icc 1 m, (((Q : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    have hsub : ({1, j} : Finset ℕ) ⊆ Finset.Icc 1 m := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_Icc]
      omega
    refine (?_ : _ ∣ ∏ i ∈ ({1, j} : Finset ℕ), (((Q : ℕ) : ℤ) ^ i - (-1) ^ i)).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    rw [Finset.prod_pair (by omega), pow_one, pow_one, sub_neg_eq_add]
  have hGdvd : ((Q : ℤ) + 1) * ((Q : ℤ) ^ j - (-1) ^ j) ∣
      (Nat.card (orbitFactor B x (a : K[X])) : ℤ) := by
    rw [hG]
    exact hdvdP.mul_left _
  rw [card_orbitFactor_eq] at hGdvd
  obtain ⟨c, hc⟩ := card_range_orbitDet_dvd H a hself
  rw [card_specialBlock_eq]
  have hrpos : 0 < Nat.card (orbitDet B x (a : K[X])).range := Nat.card_pos
  push_cast at hGdvd
  set k := Nat.card (orbitDet B x (a : K[X])).ker
  set r := Nat.card (orbitDet B x (a : K[X])).range
  have hc' : ((Q : ℤ) + 1) = r * c := by exact_mod_cast hc
  rw [hc'] at hGdvd
  have : (r : ℤ) * ((c : ℤ) * ((Q : ℤ) ^ j - (-1) ^ j)) ∣ (r : ℤ) * (k : ℤ) := by
    have e1 : (r : ℤ) * ((c : ℤ) * ((Q : ℤ) ^ j - (-1) ^ j)) =
        ((r : ℤ) * c) * ((Q : ℤ) ^ j - (-1) ^ j) := by ring
    rw [e1, mul_comm (r : ℤ) (k : ℤ)]
    exact hGdvd
  have h4 := (mul_dvd_mul_iff_left (by exact_mod_cast hrpos.ne')).1 this
  have h5 : ((Q : ℤ) ^ j - (-1) ^ j) ∣ (k : ℤ) := (dvd_mul_left _ _).trans h4
  exact_mod_cast hpj.trans h5

@[expose] noncomputable def orbitBlockDet (B : V →ₛₗ[hK.bar] V →ₗ[K] K)
    (x : LinearMap.GeneralLinearGroup K V) (a : K[X]) : orbitFactor B x a →* (AdjoinRoot a)ˣ :=
  (blockDetHom x a).comp (Subgroup.inclusion orbitFactor_le_gl_centralizer)

omit [FiniteDimensional K V] in
theorem card_specialBlock_eq_ker (a : K[X]) :
    Nat.card (specialBlock B x a) = Nat.card (orbitBlockDet B x a).ker := by
  have hmap : (orbitBlockDet B x a).ker.map (orbitFactor B x a).subtype = specialBlock B x a := by
    ext g
    rw [mem_specialBlock, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨g', hg'⟩, hk, rfl⟩
      exact ⟨hg', orbitFactor_le_gl_centralizer hg', hk⟩
    · rintro ⟨hg, hgc, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  rw [← hmap]
  exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)

theorem dvd_card_specialBlock_paired (a : primaryFactors (x : Module.End K V))
    (hP : PairedPrimaryBlock hK B x a)
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) {p : ℕ} (hp : p.Prime)
    (hpE : p ∣ Nat.card (AdjoinRoot (a : K[X])) - 1) :
    p ∣ Nat.card (specialBlock B x (a : K[X])) := by
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
  have hcomp : orbitBlockDet B x (a : K[X]) =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ).comp
        (ψ : _ →* _) := by
    ext g
    have hres : blockRestrict x (a : K[X]) ⟨(g : LinearMap.GeneralLinearGroup K V),
        orbitFactor_le_gl_centralizer g.2⟩ = φ g := by
      refine blockGL_ext fun v hv => ?_
      rw [blockApply_blockRestrict, hφ g v hv]
    have h1 := hdet g
    simp only [orbitBlockDet, blockDetHom, MonoidHom.comp_apply,
      Matrix.GeneralLinearGroup.val_det_apply, blockGLDet, Units.coe_map, MonoidHom.coe_ofClass]
    change LinearMap.det ((blockRestrict x (a : K[X]) ⟨(g : LinearMap.GeneralLinearGroup K V),
        orbitFactor_le_gl_centralizer g.2⟩ : blockGL (x : Module.End K V) (a : K[X])) :
          Module.End E (primaryComponent (x : Module.End K V) (a : K[X]))) = _
    rw [hres, ← h1]
  have hker : (orbitBlockDet B x (a : K[X])).ker =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ).ker.comap
        (ψ : _ →* _) := by
    rw [hcomp]; rfl
  rw [card_specialBlock_eq_ker, hker, Subgroup.comap_equiv_eq_map_symm,
    Subgroup.card_map_of_injective ψ.symm.injective]
  have := dvd_card_SL_of_dvd_card_sub_one (E := E) hp hm hpE
  rwa [Nat.card_congr (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin m) (R := E)).toEquiv]
    at this

end CFSG.HardMathSupport.Timmesfeld.CrossChar
