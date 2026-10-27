module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LieType.Chevalley.RankOneBruhat
public import CFSG.LieType.Chevalley.SimpleRootSubgroups
public import CFSG.LieType.Chevalley.BorelWeylIntersection
public import CFSG.LieType.Chevalley.BorelCoreCenter

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] def xUnitHom
    (i : Fin τ.rank) : Multiplicative K →* ModGL τ K where
  toFun c := xUnit τ K i c.toAdd
  map_one' := xUnit_zero i
  map_mul' c d := xUnit_add i c.toAdd d.toAdd

variable (τ K) in
@[expose] def torusEltHom
    (i : Fin τ.rank) : Kˣ →* ModGL τ K where
  toFun t := torusElt τ K i t
  map_one' := torusElt_one i
  map_mul' t u := torusElt_mul i t u

theorem weylElt_one_conj_xUnit
    (i : Fin τ.rank) (c : K) :
    weylElt τ K i 1 * xUnit τ K i c * (weylElt τ K i 1)⁻¹ = yUnit τ K i (-c) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit,
    (simple_weyl_rank_one_conjugation (τ := τ) (R := K) i 1 c).1]
  simp

theorem yUnit_eq_conj
    (i : Fin τ.rank) (c : K) :
    yUnit τ K i c = weylElt τ K i 1 * xUnit τ K i (-c) * (weylElt τ K i 1)⁻¹ := by
  rw [weylElt_one_conj_xUnit, neg_neg]

theorem weylElt_eq_yUnit_mul
    (i : Fin τ.rank) :
    weylElt τ K i 1 = yUnit τ K i (-1) * xUnit τ K i 1 * yUnit τ K i (-1) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit,
    (simple_weyl_rank_one_conjugation (τ := τ) (R := K) i 1 1).2.2]
  simp

theorem weylElt_mul_torusElt_mul_inv
    (i : Fin τ.rank) (t : Kˣ) :
    weylElt τ K i 1 * torusElt τ K i t * (weylElt τ K i 1)⁻¹ = torusElt τ K i t⁻¹ := by
  rw [weylElt_mul_torusElt, mul_inv_cancel_right, Tag.cartan_self, ← torusElt_mul]
  congr 1
  rw [zpow_neg, zpow_ofNat, ← mul_inv_cancel_left t t⁻¹, sq, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel, one_mul]

theorem torusElt_mul_xUnit_mul_inv
    (i : Fin τ.rank) (t : Kˣ) (s : K) :
    torusElt τ K i t * xUnit τ K i s * (torusElt τ K i t)⁻¹ = xUnit τ K i ((t : K) ^ 2 * s) := by
  rw [(simple_torus_root_conjugation τ K i i t s).1, Tag.cartan_self]
  simp

theorem weylElt_mul_xUnit_mul_weylElt
    (i : Fin τ.rank) {s : K} (hs : s ≠ 0) :
    weylElt τ K i 1 * xUnit τ K i s * weylElt τ K i 1 =
      xUnit τ K i (-s⁻¹) * torusElt τ K i (Units.mk0 (-s⁻¹) (neg_ne_zero.2 (inv_ne_zero hs))) *
        weylElt τ K i 1 * xUnit τ K i (-s⁻¹) := by
  have h := (simple_rank_one_bruhat_identity.{0, 0} τ K).1 i (Units.mk0 s hs)
  simp only [Units.val_mk0] at h
  have hu : -(Units.mk0 s hs)⁻¹ = Units.mk0 (-s⁻¹) (neg_ne_zero.2 (inv_ne_zero hs)) :=
    Units.ext (by simp)
  rw [h, hu, Units.val_inv_eq_inv_val, Units.val_mk0, yUnit_eq_conj]
  group

theorem weylElt_not_mem_borelGroup
    (i : Fin τ.rank) : weylElt τ K i 1 ∉ borelGroup τ K := by
  intro h
  have hN := weylElt_mem_monomialSubgroup (τ := τ) (R := K) i
  have hH : weylElt τ K i 1 ∈ torusGroup τ K := by
    rw [← (borel_weyl_intersection τ K).1]
    exact Subgroup.mem_inf.2 ⟨h, hN⟩
  have h1 := (mapsRootLines_of_mem_torusGroup hH).unique (mapsRootLines_weylElt (R := K) i)
  have hl := congrArg (coxeterSystem τ).length h1
  rw [CoxeterSystem.length_one, CoxeterSystem.length_simple] at hl
  exact absurd hl (by norm_num)

theorem sq_eq_one_of_torusElt_eq_one
    (i : Fin τ.rank) {a : Kˣ} (h : torusElt τ K i a = 1) :
    (a : K) ^ 2 = 1 := by
  have hv := congrArg (fun g : ModGL τ K =>
    (g : Module.End K (RootModule τ K)) (rootVec τ K (Pi.single i 1))) h
  simp only [torusElt_rootVec i a (isRoot_single τ i), sum_cartan_mul_single, Units.val_one,
    Module.End.one_apply] at hv
  rw [rootVec_eq_single_of_isRoot (isRoot_single τ i)] at hv
  have hv' := congrArg (fun v : RootModule τ K => v (Sum.inr ⟨_, isRoot_single τ i⟩)) hv
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hv'
  rw [← hv']
  simp

variable (τ K) in
theorem exceptional_ordinary_rank_one_central_image
    (i : Fin τ.rank) :
    ∃ ρ : SL2 K →* ModGL τ K,
      (∀ c, ρ (uSL c) = xUnit τ K i c) ∧ (∀ c, ρ (vSL c) = yUnit τ K i c) ∧
      (∀ t, ρ (HSL t) = torusElt τ K i t) ∧ ρ WSL = weylElt τ K i 1 ∧
      ρ.range = Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) ∧
      (∀ g ∈ ρ.ker, ∃ l : Kˣ, (l : K) ^ 2 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ∧
      Function.Injective (xUnit τ K i) ∧ Function.Injective (yUnit τ K i) := by
  have hn2 : weylElt τ K i 1 ^ 2 = torusEltHom τ K i (-1) := weylElt_one_sq τ K i
  obtain ⟨ρ, ⟨hu, hH, hW⟩, -, hrange, hclos, hv, hcell0, hcell⟩ :=
    exceptional_rank_one_Gaussian_realization (xUnitHom τ K i) (torusEltHom τ K i)
      (weylElt τ K i 1) (fun t s => torusElt_mul_xUnit_mul_inv i t s) hn2
      (fun t => weylElt_mul_torusElt_mul_inv i t)
      (fun s hs => weylElt_mul_xUnit_mul_weylElt i hs)
  have hx : ∀ c, xUnitHom τ K i (Multiplicative.ofAdd c) = xUnit τ K i c := fun c => rfl
  have hinjx : Function.Injective (xUnit τ K i) := fun c d h =>
    xOp_injective i (by rw [← coe_xUnit, ← coe_xUnit, h])
  have hinjy : Function.Injective (yUnit τ K i) := fun c d h =>
    yOp_injective i (by rw [← coe_yUnit, ← coe_yUnit, h])
  refine ⟨ρ, fun c => by rw [hu, hx], fun c => ?_, fun t => by rw [hH]; rfl, hW, ?_,
    fun g hg => ?_, hinjx, hinjy⟩
  · rw [hv, hx, yUnit_eq_conj]
  · rw [hrange, hclos]
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | h)
      · exact Subgroup.subset_closure (Or.inl ⟨c.toAdd, rfl⟩)
      · rw [Set.mem_singleton_iff] at h
        rw [h, weylElt_eq_yUnit_mul]
        exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inr ⟨-1, rfl⟩))
          (Subgroup.subset_closure (Or.inl ⟨1, rfl⟩))) (Subgroup.subset_closure (Or.inr ⟨-1, rfl⟩))
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact Subgroup.subset_closure (Or.inl ⟨Multiplicative.ofAdd c, rfl⟩)
      · rw [yUnit_eq_conj]
        have hn : weylElt τ K i 1 ∈ Subgroup.closure (Set.range (xUnitHom τ K i) ∪
            {weylElt τ K i 1}) := Subgroup.subset_closure (Or.inr rfl)
        exact mul_mem (mul_mem hn (Subgroup.subset_closure
          (Or.inl ⟨Multiplicative.ofAdd (-c), rfl⟩))) (inv_mem hn)
  · rw [MonoidHom.mem_ker] at hg
    by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    · rw [hcell0 g hc] at hg
      set a := Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc)
      have hxu : xUnitHom τ K i (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 0 1 /
          (g : Matrix (Fin 2) (Fin 2) K) 0 0)) = (torusEltHom τ K i a)⁻¹ :=
        eq_inv_of_mul_eq_one_right hg
      have hU : xUnitHom τ K i (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 0 1 /
          (g : Matrix (Fin 2) (Fin 2) K) 0 0)) ∈ torusGroup τ K ⊓ posUnipotent τ K := by
        refine Subgroup.mem_inf.2 ⟨?_, xUnit_mem_posUnipotent i _⟩
        rw [hxu]
        exact inv_mem (torusElt_mem_torusGroup i a)
      rw [(triangular_borel_structure.{0, 0} τ K).2.2.2.1, Subgroup.mem_bot] at hU
      have hb : (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 :=
        hinjx (hU.trans (xUnit_zero i).symm)
      have hb0 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
        rcases div_eq_zero_iff.1 hb with h | h
        · exact h
        · exact absurd h (SL2_apply_zero_zero_ne_zero hc)
      have ha1 : torusElt τ K i a = 1 := by
        rw [hU, mul_one] at hg
        exact hg
      have ha2 := sq_eq_one_of_torusElt_eq_one i ha1
      have hdet := det_SL2 g
      rw [hc, hb0, mul_zero, sub_zero] at hdet
      refine ⟨a, ha2, ?_⟩
      have hd : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = (a : K) := by
        have ha : (a : K) = (g : Matrix (Fin 2) (Fin 2) K) 0 0 := rfl
        have h2 : (a : K) * (a : K) = 1 := by rw [← sq]; exact ha2
        calc (g : Matrix (Fin 2) (Fin 2) K) 1 1 =
              (a : K) * ((g : Matrix (Fin 2) (Fin 2) K) 0 0 *
                (g : Matrix (Fin 2) (Fin 2) K) 1 1) := by
              rw [← mul_assoc, ← ha, h2, one_mul]
          _ = (a : K) := by rw [hdet, mul_one]
      ext p q
      fin_cases p <;> fin_cases q <;> simp [hc, hb0, hd]
      rfl
    · exfalso
      rw [hcell g hc] at hg
      apply weylElt_not_mem_borelGroup (τ := τ) (K := K) i
      have hBx : ∀ c : K, xUnit τ K i c ∈ borelGroup τ K := fun c =>
        Subgroup.mem_sup_right (xUnit_mem_posUnipotent i c)
      have hBh : ∀ t : Kˣ, torusElt τ K i t ∈ borelGroup τ K := fun t =>
        Subgroup.mem_sup_left (torusElt_mem_torusGroup i t)
      have e : weylElt τ K i 1 =
          (xUnitHom τ K i (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 0 0 /
              (g : Matrix (Fin 2) (Fin 2) K) 1 0)) *
            torusEltHom τ K i (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
              (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)))⁻¹ *
            (xUnitHom τ K i (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 1 1 /
              (g : Matrix (Fin 2) (Fin 2) K) 1 0)))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        apply eq_inv_of_mul_eq_one_right
        rw [← hg]
        group
      rw [e]
      exact mul_mem (inv_mem (mul_mem (hBx _) (hBh _))) (inv_mem (hBx _))

end CFSG.LieType.Chevalley
