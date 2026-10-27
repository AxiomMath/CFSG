module

public import CFSG.CharacterTheory.DefectZeroSylow.Spherical
public import CFSG.ThirdParty.BrauerInduction.Background.Group.DoubleCoset
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Coset
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open scoped Classical

namespace CFSG.DefectZeroSylow

variable {G : Type*} [Group G]

theorem mul_mem_doubleCoset_iff {Q : Subgroup G} {g x h : G} (hh : h ∈ Q) :
    x * h ∈ DoubleCoset.doubleCoset g (Q : Set G) Q ↔
      x ∈ DoubleCoset.doubleCoset g (Q : Set G) Q := by
  simp only [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨u, hu, v * h⁻¹, Q.mul_mem hv (Q.inv_mem hh), ?_⟩
    rw [← mul_assoc, ← huv, mul_inv_cancel_right]
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v * h, Q.mul_mem hv hh, by simp only [mul_assoc]⟩

variable [Fintype G]

@[expose] noncomputable def conjInterCard (Q : Subgroup G) (g : G) : ℕ :=
  Nat.card ↥(Q ⊓ Q.map (MulAut.conj g).toMonoidHom)

theorem conjInterCard_pos (Q : Subgroup G) (g : G) : 0 < conjInterCard Q g :=
  Nat.card_pos

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

variable (ρ : Representation ℂ G V) (Q : Subgroup G) in
@[expose] noncomputable def doubleCosetEigenvalue (g : G) : ℂ :=
  (Nat.card Q : ℂ) / conjInterCard Q g * sphericalFunction ρ Q g

variable {ρ : Representation ℂ G V} {Q : Subgroup G}

theorem sum_doubleCoset_sphericalFunction_mul_inv (g : G) :
    ∑ x ∈ (DoubleCoset.doubleCoset g (Q : Set G) Q).toFinset,
        sphericalFunction ρ Q x * sphericalFunction ρ Q x⁻¹ =
      conjInterCard Q g⁻¹ * (doubleCosetEigenvalue ρ Q g * doubleCosetEigenvalue ρ Q g⁻¹) := by
  rw [DoubleCoset.sum_eq_sum_over_product]
  have hpar : ∀ p : Q × Q, sphericalFunction ρ Q (DoubleCoset.parameterization Q g p) *
      sphericalFunction ρ Q (DoubleCoset.parameterization Q g p)⁻¹ =
        sphericalFunction ρ Q g * sphericalFunction ρ Q g⁻¹ := by
    intro p
    simp only [DoubleCoset.parameterization, mul_inv_rev, inv_inv]
    rw [sphericalFunction_mul_mul (Q.inv_mem p.1.2) (Q.inv_mem p.2.2), ← mul_assoc,
      sphericalFunction_mul_mul p.2.2 p.1.2]
  rw [Finset.sum_congr rfl (fun p _ => hpar p), Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, ← Nat.card_eq_fintype_card, nsmul_eq_mul, doubleCosetEigenvalue,
    doubleCosetEigenvalue]
  change (conjInterCard Q g : ℂ)⁻¹ * _ = _
  have hc : (conjInterCard Q g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (conjInterCard_pos Q g).ne'
  have hc' : (conjInterCard Q g⁻¹ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (conjInterCard_pos Q g⁻¹).ne'
  field_simp
  push_cast
  ring

theorem sum_sphericalFunction_mul_inv_eq_sum_doubleCosets :
    letI : Fintype (DoubleCoset.Quotient (Q : Set G) Q) :=
      Quotient.fintype (DoubleCoset.setoid (Q : Set G) (Q : Set G))
    ∑ g : G, sphericalFunction ρ Q g * sphericalFunction ρ Q g⁻¹ =
      ∑ d : DoubleCoset.Quotient (Q : Set G) Q, (conjInterCard Q (Quotient.out d)⁻¹ : ℂ) *
        (doubleCosetEigenvalue ρ Q (Quotient.out d) *
          doubleCosetEigenvalue ρ Q (Quotient.out d)⁻¹) := by
  rw [DoubleCoset.sum_over_G_eq_sum_double_cosets Q]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [DoubleCoset.quotToDoubleCoset_eq_doubleCoset_out,
    sum_doubleCoset_sphericalFunction_mul_inv]

variable [FiniteDimensional ℂ V]

section Eigenvalue

variable (htr : LinearMap.trace ℂ V (averageOperator ρ Q) = 1)
include htr

theorem sum_doubleCoset_sphericalFunction_mul (b g : G) :
    ∑ x ∈ (DoubleCoset.doubleCoset g (Q : Set G) Q).toFinset, sphericalFunction ρ Q (b * x) =
      Nat.card Q * (doubleCosetEigenvalue ρ Q g * sphericalFunction ρ Q b) := by
  rw [DoubleCoset.sum_eq_sum_over_product]
  have hpar : ∀ p : Q × Q, sphericalFunction ρ Q (b * DoubleCoset.parameterization Q g p) =
      sphericalFunction ρ Q (b * (p.1 : G)⁻¹ * g) := by
    intro p
    simp only [DoubleCoset.parameterization]
    rw [← mul_assoc, ← mul_assoc, sphericalFunction_mul_right _ (Q.inv_mem p.2.2)]
  rw [Finset.sum_congr rfl (fun p _ => hpar p), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  have hinv : ∑ u : Q, sphericalFunction ρ Q (b * (u : G)⁻¹ * g) =
      ∑ u : Q, sphericalFunction ρ Q (b * (u : G) * g) :=
    Fintype.sum_equiv (Equiv.inv Q) _ _ (fun u => rfl)
  rw [hinv, sum_sphericalFunction_mul htr, ← Nat.card_eq_fintype_card, doubleCosetEigenvalue]
  change (conjInterCard Q g : ℂ)⁻¹ * _ = _
  have hc : (conjInterCard Q g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (conjInterCard_pos Q g).ne'
  field_simp

theorem doubleCosetEigenvalue_mul_mem_span (b g : G) :
    doubleCosetEigenvalue ρ Q g * sphericalFunction ρ Q b ∈
      Submodule.span ℤ (Set.range (sphericalFunction ρ Q)) := by
  have hQ : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let f : G → ℂ := fun y =>
    if b⁻¹ * y ∈ DoubleCoset.doubleCoset g (Q : Set G) Q then sphericalFunction ρ Q y else 0
  have h1 : ∑ x ∈ (DoubleCoset.doubleCoset g (Q : Set G) Q).toFinset,
      sphericalFunction ρ Q (b * x) = ∑ y : G, f y := by
    rw [← Set.filter_mem_univ_eq_toFinset, Finset.sum_filter]
    refine (Fintype.sum_equiv (Equiv.mulLeft b⁻¹) _ _ (fun y => ?_)).symm
    simp only [f, Equiv.coe_mulLeft, mul_inv_cancel_left]
  have h2 : ∑ y : G, f y = Nat.card Q * ∑ q : G ⧸ Q, f q.out := by
    refine Subgroup.sum_of_left_coset_constant Q f (fun y h => ?_)
    simp only [f, ← mul_assoc, mul_mem_doubleCoset_iff h.2, sphericalFunction_mul_right _ h.2]
  have h3 : doubleCosetEigenvalue ρ Q g * sphericalFunction ρ Q b = ∑ q : G ⧸ Q, f q.out := by
    apply mul_left_cancel₀ hQ
    rw [← sum_doubleCoset_sphericalFunction_mul htr, h1, h2]
  rw [h3]
  refine Submodule.sum_mem _ (fun q _ => ?_)
  simp only [f]
  split_ifs
  · exact Submodule.subset_span ⟨_, rfl⟩
  · exact Submodule.zero_mem _

theorem isIntegral_doubleCosetEigenvalue (g : G) : IsIntegral ℤ (doubleCosetEigenvalue ρ Q g) := by
  let N := Submodule.span ℤ (Set.range (sphericalFunction ρ Q))
  refine isIntegral_of_smul_mem_submodule N ?_ (Submodule.fg_span (Set.finite_range _)) _ ?_
  · intro hN
    have h1 : (1 : ℂ) ∈ N := by
      rw [← sphericalFunction_one htr]
      exact Submodule.subset_span ⟨1, rfl⟩
    rw [hN, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · intro n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact doubleCosetEigenvalue_mul_mem_span htr b g
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact N.add_mem hx hy
    | smul a x _ hx =>
      rw [smul_comm]
      exact N.smul_mem a hx

end Eigenvalue

theorem dvd_of_natCast_eq_mul {n p : ℕ} (hp : p ≠ 0) {γ : ℂ} (hγ : IsIntegral ℤ γ)
    (h : (n : ℂ) = p * γ) : p ∣ n := by
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hγ' : γ = algebraMap ℚ ℂ ((n : ℚ) / p) := by
    rw [eq_ratCast]
    push_cast
    rw [h]
    field_simp
  rw [hγ'] at hγ
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_algebraMap_iff.mp hγ)
  have hy' : (y : ℚ) = (n : ℚ) / p := hy
  have hq0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hn : ((n : ℤ) : ℚ) = ((p * y : ℤ) : ℚ) := by
    push_cast
    rw [hy']
    field_simp
  exact Int.natCast_dvd_natCast.mp ⟨y, by exact_mod_cast hn⟩

theorem exists_inf_map_conj_eq_bot {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
    (htrP : LinearMap.trace ℂ V (averageOperator ρ P) = 1) (hirr : ρ.IsIrreducible)
    (hdim : Module.finrank ℂ V = Nat.card P) :
    ∃ g : G, (P : Subgroup G) ⊓ (P : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊥ := by
  by_contra hcon
  push Not at hcon
  have hdvd : ∀ g : G, p ∣ conjInterCard (P : Subgroup G) g := by
    intro g
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (P.isPGroup'.to_le
      (inf_le_left (b := (P : Subgroup G).map (MulAut.conj g).toMonoidHom)))
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hcon g (Subgroup.card_eq_one.mp (by simpa using hk))
    rw [conjInterCard, hk]
    exact dvd_pow_self p hk0
  have hindex : ((P : Subgroup G).index : ℂ) =
      ∑ g : G, sphericalFunction ρ P g * sphericalFunction ρ P g⁻¹ := by
    rw [sum_sphericalFunction_mul_inv htrP hirr, hdim, ← (P : Subgroup G).card_mul_index]
    have : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    push_cast
    field_simp
  let : Fintype (DoubleCoset.Quotient ((P : Subgroup G) : Set G) (P : Subgroup G)) :=
    Quotient.fintype (DoubleCoset.setoid ((P : Subgroup G) : Set G) (P : Subgroup G))
  rw [sum_sphericalFunction_mul_inv_eq_sum_doubleCosets] at hindex
  let γ : ℂ := ∑ d : DoubleCoset.Quotient ((P : Subgroup G) : Set G) (P : Subgroup G),
    ((conjInterCard P (Quotient.out d)⁻¹ / p : ℕ) : ℂ) *
      (doubleCosetEigenvalue ρ P (Quotient.out d) * doubleCosetEigenvalue ρ P (Quotient.out d)⁻¹)
  have hγ : IsIntegral ℤ γ := by
    refine IsIntegral.sum _ (fun d _ => ?_)
    have hm := isIntegral_algebraMap (R := ℤ) (A := ℂ)
      (x := ((conjInterCard P (Quotient.out d)⁻¹ / p : ℕ) : ℤ))
    rw [eq_intCast, Int.cast_natCast] at hm
    exact hm.mul ((isIntegral_doubleCosetEigenvalue htrP (Quotient.out d)).mul
      (isIntegral_doubleCosetEigenvalue htrP (Quotient.out d)⁻¹))
  have hsplit : ((P : Subgroup G).index : ℂ) = p * γ := by
    rw [hindex, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← mul_assoc (p : ℂ), ← Nat.cast_mul, Nat.mul_div_cancel' (hdvd _)]
  exact P.not_dvd_index (dvd_of_natCast_eq_mul hp.out.ne_zero hγ hsplit)

end CFSG.DefectZeroSylow
