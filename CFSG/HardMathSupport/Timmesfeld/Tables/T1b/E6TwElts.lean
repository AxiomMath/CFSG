module

public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6Local

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.RankThree.PartTwo.Census.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
open scoped MatrixGroups

section SL2

variable {F : Type*} [Field F]

@[expose] def twA {a b : F} (h : a ^ 2 + a + 1 + b ^ 2 = 0) : SL(2, F) :=
  ⟨!![a, b; b, -1 - a], by rw [Matrix.det_fin_two_of]; linear_combination -h⟩

@[expose] def twB : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

theorem coe_twA {a b : F} (h : a ^ 2 + a + 1 + b ^ 2 = 0) :
    ((twA h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -1 - a] := rfl

theorem coe_twB : ((twB : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem twA_sq {a b : F} (h : a ^ 2 + a + 1 + b ^ 2 = 0) :
    ((twA h ^ 2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![-1 - a, -b; -b, a] := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_twA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination h

theorem twA_pow_three {a b : F} (h : a ^ 2 + a + 1 + b ^ 2 = 0) : twA h ^ 3 = 1 := by
  ext i j
  rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, twA_sq, coe_twA]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination h | linear_combination -h

theorem twB_mul_twA {a b : F} (h : a ^ 2 + a + 1 + b ^ 2 = 0) :
    twB * twA h = twA h ^ 2 * twB := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, twA_sq, coe_twA,
    coe_twB]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem twB_conj_twA {a b : F} (h : a ^ 2 + a + 1 + b ^ 2 = 0) :
    twB * twA h * twB⁻¹ = (twA h)⁻¹ := by
  rw [twB_mul_twA, mul_inv_cancel_right]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, twA_pow_three]

theorem twA_ne_one {a b : F} (h : a ^ 2 + a + 1 + b ^ 2 = 0) (h3 : (3 : F) ≠ 0) :
    twA h ≠ 1 := by
  intro h1
  have h00 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  have h11 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 1 1) h1
  simp only [coe_twA, Matrix.SpecialLinearGroup.coe_one] at h00 h11
  simp at h00 h11
  apply h3
  linear_combination -h11 - h00

theorem exists_twParams (r : ℕ) [Fact r.Prime] : ∃ a b : ZMod r, a ^ 2 + a + 1 + b ^ 2 = 0 := by
  rcases (Fact.out : r.Prime).eq_two_or_odd' with rfl | hodd
  · exact ⟨0, 1, by decide +revert⟩
  · open Polynomial in
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := ZMod r)
      (f := X ^ 2 + X + 1) (g := X ^ 2) (by compute_degree!) (by compute_degree!)
      (by rw [ZMod.card]; exact Nat.odd_iff.mp hodd)
    exact ⟨a, b, by simpa using hab⟩

end SL2

section Twisted

variable {k : Type*} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def twT05 : kˣ →* fixedGroup k θ :=
  (hPairE θ (nd 0) (nd 5)).codRestrict _ fun t => hHatE_le_fixedGroup θ hθ (nf 3) (by
    change _ ∈ (hPairE θ (nd 0) (nd 5)).range
    exact ⟨t, rfl⟩)

@[expose] noncomputable def twT24 : kˣ →* fixedGroup k θ :=
  (hPairE θ (nd 2) (nd 4)).codRestrict _ fun t => hHatE_le_fixedGroup θ hθ (nf 2) (by
    change _ ∈ (hPairE θ (nd 2) (nd 4)).range
    exact ⟨t, rfl⟩)

theorem twT05_eq_te6Torus (t : kˣ) : twT05 θ hθ t = te6Torus θ hθ t := rfl

theorem twT05_commute_twT24 (s t : kˣ) : Commute (twT05 θ hθ s) (twT24 θ hθ t) := by
  refine Subtype.ext ?_
  change (e6Data_valid.hm k (nd 0) s * e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) s)) *
      (e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map (θ : k →* k) t)) =
    (e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map (θ : k →* k) t)) *
      (e6Data_valid.hm k (nd 0) s * e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) s))
  exact (((hm_commute _ _ _ _).mul_right (hm_commute _ _ _ _)).mul_left
    ((hm_commute _ _ _ _).mul_right (hm_commute _ _ _ _))).eq

theorem hPairE_conj_xm' (a b : Fin (Tag.rank .E6)) (t : kˣ) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (c : k) :
    hPairE θ a b t * e6Data_valid.xm k γ c * (hPairE θ a b t)⁻¹ =
      e6Data_valid.xm k γ (((t ^ MinData.toWeight γ a *
        Units.map (θ : k →* k) t ^ MinData.toWeight γ b : kˣ) : k) * c) := by
  have e : ∀ a b x : e6Data_valid.minGroup k, a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ :=
    fun a b x => by group
  change e6Data_valid.hm k a t * e6Data_valid.hm k b (Units.map (θ : k →* k) t) *
      e6Data_valid.xm k γ c * (e6Data_valid.hm k a t *
        e6Data_valid.hm k b (Units.map (θ : k →* k) t))⁻¹ = _
  rw [e, e6Data_valid.hm_conj_xm k hγ, e6Data_valid.hm_conj_xm k hγ, ← mul_assoc,
    ← Units.val_mul]

theorem te6Roots_weight_24 : ∀ i : Fin 4,
    MinData.toWeight (te6Roots i) (nd 2) = MinData.toWeight (te6Roots i) (nd 4) ∧
      MinData.toWeight (-te6Roots i) (nd 2) = MinData.toWeight (-te6Roots i) (nd 4) := by
  decide +kernel

variable {F : Type*} [Field F] (j : F →+* k) (hj : ∀ x, θ (j x) = j x)

theorem hPairE_commute_te6SL2 (a b : Fin (Tag.rank .E6)) {t : kˣ}
    (ht : t * Units.map (θ : k →* k) t = 1) (i : Fin 4)
    (hw : MinData.toWeight (te6Roots i) a = MinData.toWeight (te6Roots i) b ∧
      MinData.toWeight (-te6Roots i) a = MinData.toWeight (-te6Roots i) b) (A : SL(2, F)) :
    hPairE θ a b t * (te6SL2 θ j hj i A : e6Data_valid.minGroup k) =
      (te6SL2 θ j hj i A : e6Data_valid.minGroup k) * hPairE θ a b t := by
  have hle : ∀ {γ : Fin (Tag.rank .E6) → ℤ}, IsRoot .E6 γ →
      MinData.toWeight γ a = MinData.toWeight γ b →
      e6Data_valid.rootGroup k γ ≤
        Subgroup.centralizer ({hPairE θ a b t} : Set (e6Data_valid.minGroup k)) := by
    intro γ hγ hw x hx
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hPairE_conj_xm' θ a b t hγ c
    rw [← hw, ← mul_zpow, ht, one_zpow, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hmem := (sup_le (hle (isRoot_te6Roots i) hw.1)
    (hle (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_te6Roots i)) hw.2)) (te6SL2_mem θ j hj i A)
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  exact hmem.symm

theorem twT05_commute_te6SL2 {t : kˣ} (ht : t * Units.map (θ : k →* k) t = 1) (i : Fin 4)
    (A : SL(2, F)) : Commute (twT05 θ hθ t) (te6SL2 θ j hj i A) :=
  Subtype.ext (hPairE_commute_te6SL2 θ j hj (nd 0) (nd 5) ht i (te6_check.2.2.2.2 i) A)

theorem twT24_commute_te6SL2 {t : kˣ} (ht : t * Units.map (θ : k →* k) t = 1) (i : Fin 4)
    (A : SL(2, F)) : Commute (twT24 θ hθ t) (te6SL2 θ j hj i A) :=
  Subtype.ext (hPairE_commute_te6SL2 θ j hj (nd 2) (nd 4) ht i (te6Roots_weight_24 i) A)

theorem nm_conj_hm_of_cartan_eq_zero {j l : Fin (Tag.rank .E6)} (h : Tag.cartan .E6 l j = 0)
    (t : kˣ) :
    e6Data_valid.nm k j * e6Data_valid.hm k l t * (e6Data_valid.nm k j)⁻¹ =
      e6Data_valid.hm k l t := by
  rw [e6Data_valid.nm_conj_hm, h, neg_zero, zpow_zero, e6Data_valid.hm_one, mul_one]

theorem nm_conj_hm_self (j : Fin (Tag.rank .E6)) (t : kˣ) :
    e6Data_valid.nm k j * e6Data_valid.hm k j t * (e6Data_valid.nm k j)⁻¹ =
      (e6Data_valid.hm k j t)⁻¹ := by
  rw [e6Data_valid.nm_conj_hm, Tag.cartan_self, ← e6Data_valid.hm_mul]
  calc e6Data_valid.hm k j (t * t ^ (-2 : ℤ)) = e6Data_valid.hm k j t⁻¹ := by
        congr 1
        group
    _ = (e6Data_valid.hm k j t)⁻¹ := map_inv (e6Data_valid.hHom k j) t

theorem nHat_conj_twT05 (t : kˣ) :
    nHat θ (nf 3) * twT05 θ hθ t * (nHat θ (nf 3))⁻¹ = (twT05 θ hθ t)⁻¹ := by
  refine Subtype.ext ?_
  set n0 := e6Data_valid.nm k (nd 0)
  set n5 := e6Data_valid.nm k (nd 5)
  set h0 := e6Data_valid.hm k (nd 0) t
  set h5 := e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) t)
  change n0 * n5 * (h0 * h5) * (n0 * n5)⁻¹ = (h0 * h5)⁻¹
  have e1 : n0 * n5 * (h0 * h5) * (n0 * n5)⁻¹ =
      (n0 * (n5 * h0 * n5⁻¹) * n0⁻¹) * (n0 * (n5 * h5 * n5⁻¹) * n0⁻¹) := by group
  have c1 : n5 * h0 * n5⁻¹ = h0 := nm_conj_hm_of_cartan_eq_zero (by decide) t
  have c2 : n5 * h5 * n5⁻¹ = h5⁻¹ := nm_conj_hm_self (nd 5) _
  have c3 : n0 * h0 * n0⁻¹ = h0⁻¹ := nm_conj_hm_self (nd 0) t
  have c4 : n0 * h5⁻¹ * n0⁻¹ = h5⁻¹ := by
    have e : h5⁻¹ = e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) t)⁻¹ :=
      (map_inv (e6Data_valid.hHom k (nd 5)) _).symm
    rw [e]
    exact nm_conj_hm_of_cartan_eq_zero (by decide) _
  rw [e1, c1, c2, c3, c4, mul_inv_rev]
  exact ((hm_commute _ _ _ _).inv_inv).symm.eq

end Twisted

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
