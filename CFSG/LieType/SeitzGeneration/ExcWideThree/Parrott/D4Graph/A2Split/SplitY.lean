module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.Torus3

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K : Type} [Field K]

@[expose] def vS : Fin Tag.D4.rank → ℤ :=
  fun j => if j.val = 1 then 2 else if j.val = 3 then 1 else 0

@[expose] def vH : Fin Tag.D4.rank → ℤ := fun j => Tag.D4.cartan ⟨2, by decide⟩ j

@[expose] def vD : Fin Tag.D4.rank → ℤ :=
  fun j => Tag.D4.cartan ⟨0, by decide⟩ j - Tag.D4.cartan ⟨1, by decide⟩ j

theorem vS_facts :
    (∀ j, (permM.mulVec vS j + vH j - (weylG2M ^ 4).mulVec vH j) % 3 = vS j % 3) ∧
    (∀ j, (vS j + (weylG2M ^ 4).mulVec vS j + (weylG2M ^ 8).mulVec vS j) % 3 = 0 % 3) ∧
    (weylG2M ^ 4).mulVec vD = vD ∧
    ¬ ((weylG2M ^ 4).mulVec vH ⟨0, by decide⟩ - vH ⟨0, by decide⟩) % 3 = 0 ∧
    ¬ ((weylG2M ^ 8).mulVec vH ⟨0, by decide⟩ - vH ⟨0, by decide⟩) % 3 = 0 := by
  decide

@[expose] noncomputable def sElt {ω : Kˣ} (hω : ω ^ 3 = 1) : ↥(adjointGroup Tag.D4 K) :=
  ⟨rootDiagUnit Tag.D4 (fun j => ω ^ vS j), rootDiagUnit_mem_of_sq (fun j =>
    ⟨ω ^ (2 * vS j), by
      rw [pow_two, ← zpow_add]
      exact zpow_eq_of_three hω (by omega)⟩)⟩

@[expose] noncomputable def yP {ω : Kˣ} (hω : ω ^ 3 = 1) : ↥(adjointGroup Tag.D4 K) :=
  sElt hω * (weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4

theorem yP_pow_conj_diag {ω : Kˣ} (hω : ω ^ 3 = 1) (k : ℕ) {g : ↥(adjointGroup Tag.D4 K)}
    {a : Fin Tag.D4.rank → Kˣ} (hga : (g : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) :
    (((yP hω ^ k * g * (yP hω ^ k)⁻¹ : ↥(adjointGroup Tag.D4 K))) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (tupAct (weylG2M ^ (4 * k)) a) := by
  induction k generalizing g a with
  | zero =>
    simp only [pow_zero, one_mul, inv_one, mul_one, Nat.mul_zero, hga]
    rw [tupAct_one]
  | succ k ih =>
    have hstep : ∀ {g' : ↥(adjointGroup Tag.D4 K)} {b : Fin Tag.D4.rank → Kˣ},
        (g' : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 b →
        ((yP hω * g' * (yP hω)⁻¹ : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
          rootDiagUnit Tag.D4 (tupAct (weylG2M ^ 4) b) := by
      intro g' b hg'
      have h1 := weylG2_pow_conj_rootDiagUnit (K := K) 4 b
      rw [← hg'] at h1
      unfold yP
      rw [mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_inv,
        show ((sElt hω : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) *
            (((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4 : ↥(adjointGroup Tag.D4 K)) :
              ModGL Tag.D4 K) * (g' : ModGL Tag.D4 K) *
            ((((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4 : ↥(adjointGroup Tag.D4 K)) :
              ModGL Tag.D4 K)⁻¹ * ((sElt hω : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁻¹) =
          ((sElt hω : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) *
            ((((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4 : ↥(adjointGroup Tag.D4 K)) :
              ModGL Tag.D4 K) * (g' : ModGL Tag.D4 K) *
            (((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4 : ↥(adjointGroup Tag.D4 K)) :
              ModGL Tag.D4 K)⁻¹) * ((sElt hω : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁻¹ by
          group, h1]
      show rootDiagUnit Tag.D4 (fun j => ω ^ vS j) * rootDiagUnit Tag.D4 (tupAct (weylG2M ^ 4) b) *
          (rootDiagUnit Tag.D4 (fun j => ω ^ vS j))⁻¹ = _
      rw [rootDiagUnit_commute, mul_inv_cancel_right]
    rw [pow_succ', mul_inv_rev,
      show yP hω * yP hω ^ k * g * ((yP hω ^ k)⁻¹ * (yP hω)⁻¹) =
        yP hω * (yP hω ^ k * g * (yP hω ^ k)⁻¹) * (yP hω)⁻¹ by group,
      hstep (ih hga), tupAct_tupAct, ← pow_add, show 4 + 4 * k = 4 * (k + 1) by ring]

theorem gammaP_HSL_diag (ω : Kˣ) {g : ↥(adjointGroup Tag.D4 K)} {a : Fin Tag.D4.rank → Kˣ}
    (hga : (g : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) :
    ((gammaP K (HSL ω) g : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (tupAct permM a) := by
  rw [gammaP, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, d4Graph_one_torusSub hga, sl2At_HSL, coe_torusElement,
    rootDiagUnit_commute, mul_inv_cancel_right]

theorem d4Graph_one_weylG2_pow (n : ℕ) :
    d4Graph K 1 ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ n) = weylG2 ^ n := by
  rw [map_pow, d4Graph_one_weylG2]

theorem gammaP_HSL_yP {ω : Kˣ} (hω : ω ^ 3 = 1) : gammaP K (HSL ω) (yP hω) = yP hω := by
  set h := sl2At K ⟨2, by decide⟩ (HSL ω) with hh
  set y3 := (weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4 with hy3
  have hαs : ((gammaP K (HSL ω) (sElt hω) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (tupAct permM (fun j => ω ^ vS j)) := gammaP_HSL_diag ω rfl
  have hαy : gammaP K (HSL ω) y3 = h * y3 * h⁻¹ := by
    rw [gammaP, MulAut.mul_apply, MulAut.conj_apply, hy3, d4Graph_one_weylG2_pow]
  have hcoe_h : (h : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 (fun j => ω ^ vH j) := by
    rw [hh, sl2At_HSL, coe_torusElement]
    rfl
  have hyh : ((y3 * h⁻¹ * y3⁻¹ : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (tupAct (weylG2M ^ 4) (fun j => ω ^ vH j)⁻¹) := by
    have h1 := weylG2_pow_conj_rootDiagUnit (K := K) 4 (fun j => ω ^ vH j)⁻¹
    rw [← rootDiagUnit_inv, ← hcoe_h] at h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hy3]
    exact h1
  have htor : gammaP K (HSL ω) (sElt hω) * h * (y3 * h⁻¹ * y3⁻¹) = sElt hω := by
    refine Subtype.ext ?_
    show _ = rootDiagUnit Tag.D4 (fun j => ω ^ vS j)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hαs, hcoe_h, hyh, ← rootDiagUnit_mul,
      ← rootDiagUnit_mul]
    simp only [tupAct_inv, tupAct_zpow]
    congr 1
    funext j
    simp only [Pi.mul_apply, Pi.inv_apply, ← zpow_neg, ← zpow_add]
    exact zpow_eq_of_three hω (by have := vS_facts.1 j; omega)
  show gammaP K (HSL ω) (sElt hω * y3) = sElt hω * y3
  rw [map_mul, hαy]
  conv_rhs => rw [← htor]
  group

theorem yP_pow_three [Finite K] {ω : Kˣ} (hω : ω ^ 3 = 1) : yP hω ^ 3 = 1 := by
  have hy33 : ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4) ^ 3 = 1 := by
    rw [← pow_mul, weylG2_pow_twelve]
  have e : yP hω ^ 3 = sElt hω * ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4 * sElt hω *
      ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4)⁻¹) *
      (((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4) ^ 2 * sElt hω *
        (((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4) ^ 2)⁻¹) *
      ((weylG2 : ↥(adjointGroup Tag.D4 K)) ^ 4) ^ 3 := by
    rw [show yP hω ^ 3 = yP hω * yP hω * yP hω by rw [pow_succ, pow_two]]
    unfold yP
    group
  rw [e, hy33, mul_one, ← pow_mul, show 4 * 2 = 8 from rfl]
  have hs : ((sElt hω : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (fun j => ω ^ vS j) := rfl
  have h1 := weylG2_pow_conj_rootDiagUnit (K := K) 4 (fun j => ω ^ vS j)
  have h2 := weylG2_pow_conj_rootDiagUnit (K := K) 8 (fun j => ω ^ vS j)
  rw [← hs] at h1 h2
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
  rw [h1, h2, hs, ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_one]
  simp only [tupAct_zpow]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.one_apply, ← zpow_add]
  rw [show (1 : Kˣ) = ω ^ (0 : ℤ) from (zpow_zero ω).symm]
  exact zpow_eq_of_three hω (by have := vS_facts.2.1 j; omega)

theorem coe_dTorus (l : Kˣ) :
    ((torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹ :
      ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 (fun j => l ^ vD j) := by
  rw [Subgroup.coe_mul, coe_torusElement, coe_torusElement, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, vD, inv_zpow', ← zpow_add, sub_eq_add_neg]

theorem yP_commute_dTorus {ω : Kˣ} (hω : ω ^ 3 = 1) (l : Kˣ) :
    yP hω * (torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹) =
      (torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹) *
        yP hω := by
  set d := torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹
  have h := yP_pow_conj_diag hω 1 (coe_dTorus l)
  rw [pow_one, tupAct_zpow, vS_facts.2.2.1, ← coe_dTorus l] at h
  have h' := Subtype.ext h
  calc yP hω * d = yP hω * d * (yP hω)⁻¹ * yP hω := by group
    _ = d * yP hω := by rw [h']

theorem yP_pow_not_diag {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω : orderOf ω = 3) {k : ℕ}
    (hk : k = 1 ∨ k = 2) {a : Fin Tag.D4.rank → Kˣ}
    (ha : ((yP hω3 ^ k : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) :
    False := by
  set h := torusElement Tag.D4 K ⟨2, by decide⟩ ω
  have hh : (h : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 (fun j => ω ^ vH j) := by
    rw [coe_torusElement]
    rfl
  have hc := yP_pow_conj_diag hω3 k hh
  have hcomm : yP hω3 ^ k * h = h * yP hω3 ^ k := commute_of_diag ha hh
  have hfix : yP hω3 ^ k * h * (yP hω3 ^ k)⁻¹ = h := by rw [hcomm, mul_inv_cancel_right]
  rw [hfix, hh, tupAct_zpow] at hc
  have h0 := congrFun (rootDiagUnit_injective_D4 hc) ⟨0, by decide⟩
  have hmod := (zpow_eq_zpow_iff_modEq).1 h0
  rw [hω] at hmod
  have hdiv := Int.ModEq.dvd hmod
  rcases hk with rfl | rfl
  · simp only [Nat.mul_one] at hdiv
    exact vS_facts.2.2.2.1 (by omega)
  · simp only [show 4 * 2 = 8 from rfl] at hdiv
    exact vS_facts.2.2.2.2 (by omega)

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
